import array

from sage.arith.functions import lcm
from sage.arith.misc import GCD as gcd
from sage.arith.misc import power_mod
from sage.arith.misc import previous_prime
from sage.functions.log import exp
from sage.functions.other import (
    binomial,
    ceil,
    factorial,
    frac,
)
from sage.interfaces.magma import magma
from sage.matrix.constructor import matrix
from sage.matrix.special import identity_matrix
from sage.misc.cachefunc import cached_method
from sage.misc.lazy_attribute import lazy_attribute
from sage.misc.misc_c import prod
from sage.modular.hypergeometric_motive import HypergeometricData
from sage.rings.finite_rings.integer_mod_ring import IntegerModRing
from sage.rings.integer_ring import ZZ
from sage.rings.padics.factory import Qp
from sage.rings.power_series_ring import PowerSeriesRing
from sage.rings.rational_field import QQ

from pyrforest import remainder_forest

from .gamma_expansions import (
    pAdicLogGammaCache,
)
from .hgm_misc import (
    fast_hgm_sum,
    gammas_to_displacements,
    mbound_dict_c,
    moddiv,
    moddiv_int,
    prime_range_by_residues,
    recenter_mod,
    truncated_exp,
    truncated_log_mod,
)



def interpolation_polys(e, x):
    r"""
    Return the Lagrange interpolation polynomials in `x` for `e` evaluation points, multiplied by (e-1)!.

    This works integrally in characteristic not less than `e`.

    INPUT:

    - ``e`` -- a positive integer
    - ``x`` -- the generator of a univariate polynomial ring

    OUTPUT:

    A list of integral polynomials [f_0, ..., f_{e-1}] of degree e-1 so that f_i(j) = 0 for 0 <= j < e with j != i.

    EXAMPLES::

        sage: R.<x> = ZZ[]
        sage: L = interpolation_polys(3, x); L
        [x^2 - 3*x + 2, -2*x^2 + 4*x, x^2 - x]
        sage: all(L[i](j) == 0 for i in range(3) for j in range(3) if i != j)
        True

    The values f_i(i) are all the same, and e-smooth:

        sage: L = interpolation_polys(11, x)
        sage: all(L[i](i) == 3628800 for i in range(11))
        True
        sage: factor(3628800)
        2^8 * 3^4 * 5^2 * 7
    """
    if e == 1:
        return [x.parent().one()]
    return [(factorial(e-1)//prod(i-j for j in range(e) if j != i))*prod(x-j for j in range(e) if j != i) for i in range(e)]

class AmortizingHypergeometricData(HypergeometricData):
    r"""
    Class for computing Frobenius traces of a hypergeometric motive for all primes up to given bound `N`.

    INPUT:

    three possibilities are offered, each describing a quotient of
    products of cyclotomic polynomials.

    * ``cyclotomic`` -- a pair of lists of nonnegative integers, each
      integer k represents a cyclotomic polynomial \Phi_k

    * ``alpha_beta`` -- a pair of lists of rationals, each rational
      represents a root of unity

    * ``gamma_list`` -- a pair of lists of nonnegative integers, each
      integer n represents a polynomial x^n - 1

    * ``gamma_cache`` -- a pAdicLogGammaCache object, which can be reused
      across different hypergeometric data.

    In the last case, it is also allowed to send just one list of
    signed integers where signs indicate to which part the integer
    belongs to.

    EXAMPLES:

    We create a hypergeometric datum for a given alpha and beta::

        sage: H = AmortizingHypergeometricData(cyclotomic=([4,4,2,2], [3,3,3]))

    The precision needed to uniquely determine the traces is::

        sage: e = 1 + H.weight() // 2; e
        2

    We can compute Frobenius traces at a given value of t for good p up to 1000::

        sage: values = H.amortized_padic_H_values(t=1337, N=1000, e=e)
        sage: values[997]
        -11067

    Small primes are excluded, but can be computed separately::

        sage: 2 in values
        False
        sage: H.padic_H_value(p=5, f=1, t=1337)
        -9

    Sage doesn't currently support tame and wild primes, though Magma does::

        sage: H.padic_H_value(p=3, f=1, t=1337)
        Traceback (most recent call last):
        ...
        NotImplementedError: p is wild
        sage: H.padic_H_value(p=7, f=1, t=1337)
        Traceback (most recent call last):
        ...
        NotImplementedError: p is tame
    """
    def __init__(self, cyclotomic=None, alpha_beta=None, gamma_list=None, e=None):
        HypergeometricData.__init__(self, cyclotomic, alpha_beta, gamma_list)
        alpha, beta = self.alpha(), self.beta()
        self.denom = lcm(i for j in self.cyclotomic_data() for i in j)

        self.breaks = breaks = sorted(set(alpha + beta + [QQ(0), QQ(1)]))
        self.starts = starts = breaks[:-1]
        self.ends = ends = breaks[1:]
        xi = beta.count(0)
        self.D = (self.weight() + 1 - xi) // 2

        # Compute the sign and power of p in sigma_i (between two breakpoints).
        # These also apply to tau_i (at breakpoints) when p mod b != 1.
        self.interval_mults = {gamma: (ZZ(-1) if self.zigzag(gamma)%2 else ZZ(1),
            self.zigzag(gamma) + self.D + xi) for gamma in starts}
        self.break_mults = {end: self.interval_mults[start] for (start, end) in zip(starts, ends)}
        self.break_mults[0] = (1, self.D)

        # Compute the sign and power of tau_i (at breakpoints) when p mod b == 1.
        self.break_mults_p1 = {}
        for brk in self.starts:
            eta_m = self.zigzag(brk) + self.beta().count(brk) - self.alpha().count(brk)
            xi_m = self.beta().count(0) - self.beta().count(brk)
            ps = eta_m + xi_m + self.D
            assert (ps >= 0)
            sign = ZZ(-1) if eta_m%2 else ZZ(1)
            self.break_mults_p1[brk] = (sign, ps)

        if e is None:
            e = self.weight()//2 + 1
        self.e = e
        self.gammas_cache = pAdicLogGammaCache(e)
        self.zero_offsets = {}

    def truncated_starts_ends(self, e=None):
        r"""
        List starts and ends of intervals, omitting those at the end which do not contribute
        to the trace mod p**e.

        INPUT:

        - ``e`` -- a positive integer, the precision

        OUTPUT:

        A list of pairs (start, end) giving endpoints for intervals between 0 and 1.

        EXAMPLES::

            sage: H = AmortizingHypergeometricData(cyclotomic=([5], [2,2,2,2]))

        We need all intervals at precision 2::

            sage: H.truncated_starts_ends(2)
            [(0, 1/5), (1/5, 2/5), (2/5, 1/2), (1/2, 3/5), (3/5, 4/5), (4/5, 1)]

        But the last interval is irrelevant at precision 1::

            sage: H.truncated_starts_ends(1)
            [(0, 1/5), (1/5, 2/5), (2/5, 1/2), (1/2, 3/5), (3/5, 4/5)]
            sage: H.break_mults[4/5]
            (-1, 1)
            sage: H.break_mults_p1[4/5]
        """
        if e is None:
            e = self.e
        tmp = list(zip(self.starts, self.ends))
        while tmp:
            start, end = tmp[-1]
            if self.break_mults[start][1] < e or self.break_mults_p1[start][1] < e:
                break
            del tmp[-1]
        return tmp

    @staticmethod
    def tame_primes(t):
        r"""
        Given `t`, construct the set of primes at which every hypergeometric motive
        with parameter `t` has bad reduction.

        INPUT:

        - ``t`` -- a rational number

        OUTPUT:

        The set of primes dividing the numerator or denominator of `t` or `t-1`.

        EXAMPLES::

            sage: H = AmortizingHypergeometricData(cyclotomic=([5], [2,2,2,2]))
            sage: H.tame_primes(380/117)
            {2, 3, 5, 13, 19, 263}
        """
        s = set()
        for m in (t, ~t, t-1):
            for p in m.numerator().prime_divisors():
                s.add(p)
        return s

    @cached_method
    def _prime_range(self, t, N):
        r"""
        Compute ranges of primes up to `N` sorted into congruence classes.

        This excludes tame primes, wild primes, and primes which are too small for the
        amortized computation.

        INPUT:

        - ``t`` -- a rational number
        - ``N`` -- a positive integer, the upper bound on primes

        OUTPUT:

        A dictionary of dictionaries, with outer keys given by denominators of break points,
        inner keys given by invertible residue classes modulo the denominator, and values the
        list of good primes up to N in that residue class.

        Primes are good if the are not tame, not wild, and larger than `d(d-1)` for the largest
        denominator d of any break point.

        EXAMPLES::

            sage: H = AmortizingHypergeometricData(cyclotomic=([5,4], [7]))
            sage: H._prime_range(t=52/5, N=100)
            {1: {0: [43, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]},
             4: {1: [53, 61, 73, 89, 97], 3: [43, 59, 67, 71, 79, 83]},
             5: {1: [61, 71], 2: [67, 97], 3: [43, 53, 73, 83], 4: [59, 79, 89]},
             7: {1: [43, 71], 2: [79], 3: [59, 73], 4: [53, 67], 5: [61, 89], 6: [83, 97]}}
        """
        ds = set([elt.denominator() for elt in self.starts])
        ds.add(1)
        s = set(self.wild_primes())
        s = s.union(self.tame_primes(t))
        # Exclude other small primes to avoid edge cases.
        d = max(i.denominator() for i in self._alpha + self._beta)
        lower_bound = d*(d-1)+1
        return prime_range_by_residues(lower_bound, N, ds, s)

    @lazy_attribute
    def _starts_to_rationals(self):
        """
        OUTPUT:

        A dictionary
            a/b -> {k -> l/b}
        where a/b is a start of an interval and
            floor(a/b*(p - 1)) = l/b mod p,
        for all p mod b = k and gcd(p, b) = 1

        EXAMPLES::

            sage: H = AmortizingHypergeometricData(cyclotomic=([5,4], [7]))
            sage: D = H._starts_to_rationals; D
            {0: {0: 0},
             1/7: {1: -1/7, 2: -2/7, 3: -3/7, 4: -4/7, 5: -5/7, 6: -6/7},
             1/5: {1: -1/5, 2: -2/5, 3: -3/5, 4: -4/5},
             1/4: {1: -1/4, 3: -3/4},
             2/7: {1: -2/7, 2: -4/7, 3: -6/7, 4: -8/7, 5: -3/7, 6: -5/7},
             2/5: {1: -2/5, 2: -4/5, 3: -6/5, 4: -3/5},
             3/7: {1: -3/7, 2: -6/7, 3: -9/7, 4: -5/7, 5: -8/7, 6: -4/7},
             4/7: {1: -4/7, 2: -8/7, 3: -5/7, 4: -9/7, 5: -6/7, 6: -10/7},
             3/5: {1: -3/5, 2: -6/5, 3: -4/5, 4: -7/5},
             5/7: {1: -5/7, 2: -10/7, 3: -8/7, 4: -6/7, 5: -11/7, 6: -9/7},
             3/4: {1: -3/4, 3: -5/4},
             4/5: {1: -4/5, 2: -8/5, 3: -7/5, 4: -6/5},
             6/7: {1: -6/7, 2: -12/7, 3: -11/7, 4: -10/7, 5: -9/7, 6: -8/7},
             1: {0: 0}}
             sage: all(floor(gam * (p-1)) % p == D[gam][p % gam.denominator()] % p for gam in D for p in prime_range(20) if gam != 1 and gam.denominator() % p != 0)
             True
        """
        answer = {}
        for start in self.breaks:
            a, b = start.numerator(), start.denominator()
            resab = {}
            if b == 1: # start = 0
                resab[0] = QQ(0)
            for pclass in range(1, b):
                if b.gcd(pclass) == 1:
                    v = (a*(pclass - 1)) % b
                    resab[pclass] = (-a-v)/b
            answer[start] = resab
        return answer

    @cached_method
    def _numden_factors(self, start, pclass):
        r"""
        Compute the constants of the linear factors contributing to the accumulating product.

        INPUT:

        - ``start`` -- a break point: a rational number a/b between 0 and 1 with appropriate denominator
        - ``pclass`` -- an integer between 0 and b-1 that is relatively prime to b-1

        OUTPUT:

        A dictionary of the form ``{t: (i, j)}`` where ``t`` is the constant term of a
        linear factor, ``i`` is its multiplicity (positive or negative), and ``j`` is 1 if this factor
        arises from ``start`` and 0 otherwise.

        EXAMPLES::

            sage: H = AmortizingHypergeometricData(cyclotomic=([5,4], [7]))
            sage: H._numden_factors(2/7, 3)
            {12/35: (1, 0),
             11/28: (1, 0),
             -16/35: (1, 0),
             -9/35: (1, 0),
             -3/28: (1, 0),
             -2/35: (1, 0),
             2/7: (-1, 0),
             3/7: (-1, 1),
             -3/7: (-1, 0),
             -2/7: (-1, 0),
             -1/7: (-1, 0),
             0: (-1, 0)}
        """
        # First count frequencies.
        flgl = {}
        for a in self.alpha():
            if a in flgl:
                flgl[a] += 1
            else:
                flgl[a] = 1
        for b in self.beta():
            if b in flgl:
                flgl[b] -= 1
            else:
                flgl[b] = -1
        # We shift the term corresponding to a or b by 1 because we're taking
        # the fractional part of a negative number when less than start.
        # We also need to separately indicate any values equal to start.
        shift = self._starts_to_rationals[start][pclass]
        flgl = {QQ(i + shift + (1 if i <= start else 0)): (ZZ(j), ZZ(1) if i == start else ZZ(0))
                for i,j in flgl.items()}
        return flgl

    @cached_method
    def gamma_denoms(self, e=None):
        r"""
        Return the denominators of pairwise differences between elements of alpha+beta.

        INPUT:

        - ``e`` -- a precision.  This only plays a role occasionally, when the last (few) intervals
          might be omitted, possibly changing the set of denominators.

        OUTPUT:

        The set of denominators of rational numbers of the form ``gamma0 - gamma1``,
        each an element of ``alpha`` or ``beta``.

        EXAMPLES::

            sage: H = AmortizingHypergeometricData(cyclotomic=([5,4], [7]))
            sage: H.alpha_beta()
            ([1/5, 1/4, 2/5, 3/5, 3/4, 4/5], [1/7, 2/7, 3/7, 4/7, 5/7, 6/7])
            sage: H.gamma_denoms(2)
            {1, 2, 4, 5, 7, 20, 28, 35}
        """
        if e is None:
            e = self.e
        dens = set([1])
        for (start, _) in self.truncated_starts_ends(e):
            d = start.denominator()
            for pclass in range(d):
                if d.gcd(pclass) == 1:
                    # r = start.numerator()*(pclass-1) % d
                    flgl = self._numden_factors(start, pclass)
                    for i in flgl:
                        dens.add(i.denominator())
        return dens

    def verify_summand(self, p, t, m, e=None):
        r"""
        Compute a summand of the hypergeometric trace formula for debugging.

        INPUT:

        - ``p`` -- a prime that is not tame or wild
        - ``t`` -- a rational number
        - ``m`` -- an integer between 0 and p-2
        - ``e`` -- a positive integer, the precision

        OUTPUT:

        The summand corresponding to m in the formula for ``H_p(alpha, beta | t) mod p^e``.

        EXAMPLES::

            sage: H = AmortizingHypergeometricData(cyclotomic=([5,4], [7]))
            sage: H.verify_summand(97, 52/5, 58, 2)
            2968
        """
        if e is None:
            e = self.e
        F = Qp(p)
        R = IntegerModRing(p**e)
        tmult = power_mod(t, p**(e-1), p**e)
        return (R(tmult)**m *
            prod(R(F(frac(i+m/(1-p))).gamma()) for i in self._alpha) /
            prod(R(F(frac(i)).gamma()) for i in self._alpha) /
            prod(R(F(frac(i+m/(1-p))).gamma()) for i in self._beta) *
            prod(R(F(frac(i)).gamma()) for i in self._beta))

    def precompute_gammas(self, N, chained=False):
        r"""
        Precompute series expansion of p-adic Gamma needed for hypergeometric traces.

        The result is cached in self.gammas_cache.

        INPUT:

        - ``N`` -- a positive integer, the upper bound on the primes
        - ``e`` -- a positive integer, the p-adic precision
        - ``chained`` -- a boolean, only used to disable the computation in the case that e=1 and chained is true (when an older algorithm is used)

        OUTPUT:

        A dictionary, with keys (a, b, p), and values (c, i, f) so that
        the power series expansion of Gamma_p(x) around a/b to precision e is
        c^i exp(f), where i is 1 or -1 and c is an integer.

        EXAMPLES::

            sage: H = AmortizingHypergeometricData(cyclotomic=([5,4], [7]))
            sage: H.gammas(100, 2)[9, 28, 89]
            (1928, -1, 1424*x - 1602)
        """
        e = self.e
        if e == 1 and chained:
            return None
        self.gammas_cache.increase_N(N)
        dens = self.gamma_denoms()
        p = previous_prime(N)
        for d in dens:
            for b in range(d//2+1):
                if gcd(b, d) == 1:
                    _ = self.gammas_cache.expansion((b, d, p))

    @cached_method
    def displacements(self, N, start, pclass, index):
        r"""
        Precompute p-adic displacements using Gamma values.

        These represent the value of P_{m_i} and P_{m_i+k} for k>0, assuming z=1.
        """
        e = self.e
        gammas = self.gammas_cache
        # n = self.degree()
        R1 = ZZ['k1'] # k1 stands for k-1
        numden_factors = self._numden_factors(start, pclass)
        if index == 0:
            # Contribute P_{m_i} assuming z == 1.
            _, ps = self.break_mults_p1[start] if pclass == 1 else self.break_mults[start]
            if start == 0: # Need initial value modulo p**e for normalization.
                ps = 0
            inter_polys = []
            flgl1 = {i-j[1]: j[0] for i, j in numden_factors.items()}
        else:
            # Contribute P_{m_i+1} assuming z == 1, multiplied by an associated series.
            _, ps = self.interval_mults[start]
            inter_polys = interpolation_polys(e-ps, R1.gen())
            flgl1 = {i+1: j[0] for i, j in numden_factors.items()}
        if ps >= e:
            return None
        ei = e-ps
        d = start.denominator()
        r = start.numerator()*(pclass-1) % d

        # Precompute the effect of integer shifts away from [0,1].
        flgl = {}
        tmp = QQ(1)
        R1 = QQ['x1']
        x1 = R1.gen()
        tmp2 = R1(0)
        for i,j in flgl1.items():
            if i < 0:
                tmp /= (-i)**j
                tmp2 += j*sum((-x1/i)**k/k for k in range(1,e))
                flgl[(i+1).as_integer_ratio()] = j
            elif i > 1:
                tmp *= (1-i)**j
                tmp2 -= j*sum((-x1/(i-1))**k/k for k in range(1,e))
                flgl[(i-1).as_integer_ratio()] = j
            else:
                flgl[i.as_integer_ratio()] = j
        tmp2 = tuple(tmp2[e-1-i].as_integer_ratio() for i in range(e))

        R = ZZ['x']
        l = (gammas, flgl, tmp.numer(), tmp.denom(), tmp2, index, R.gen(), r, d, ei, factorial(ZZ(ei-1)), inter_polys)
        ans = {p: gammas_to_displacements(l, p)
                    for p in self._prime_range(ZZ(-1), N)[d][pclass]} #inner loop
        # If start==index==0, we need to extract a normalization factor.
        if start==0 and index==0:
            self.zero_offsets[N] = ans
        return ans

    def amortized_padic_H_values_ferry(self, t, start, pclass):
        r"""
        Compute the matrix T_i(p) mod p. This is only used when e=1.
        """
        y1, ps1 = self.break_mults_p1[start] if pclass == 1 else self.break_mults[start]
        if ps1:
            y1 = 0
        multiplier = lambda x: -x if x else ZZ(-1)
        flgl = self._numden_factors(start, pclass)
        feq_seed = t * prod(multiplier(i-k)**j[0] for i,j in flgl.items() for k in range(j[1]+1))
        feq_seed_num = feq_seed.numer()
        feq_seed_den = feq_seed.denom()
        return matrix(ZZ, 2, 2, [feq_seed_den, 0, feq_seed_den*y1, feq_seed_num])

    def amortized_padic_H_values_step(self, vectors, t, N, start, pclass, multlifts, debug=False):
        r"""
        Given a dict `vectors` indexed by primes `p`, update `vectors` via
           vectors[p] += P'_{m_i}
        where m_i = floor(p*start), for primes `p` in the residue class
        `pclass` modulo the denominator of `start`.

        If e>1, we assume that `multlifts` is a dict whose entry at `p` is a series in `k-1`
        computing the multiplicative lift of t^(k-1) modulo p**e.
        """
        e = self.e
        y1, ps1 = self.break_mults_p1[start] if pclass == 1 else self.break_mults[start]
        if ps1 >= e:
            # We still need to compute displacements if start==0, in order to set up zero_offsets.
            if start == 0:
                displacements = self.displacements(N, start, pclass, 0)
            return None
        ei1 = e-ps1

        d = start.denominator()
        indices = self._prime_range(t, N)[d][pclass]

        # Retrieve precomputation results.
        displacements = self.displacements(N, start, pclass, 0)

        for p in indices:
            pe = p if ei1==1 else p**ei1
            mi = (start*(p-1)).floor()
            tpow = (t%pe).powermod(mi, pe) # faster than power_mod(t, mi, pe)
            if ei1>1:
                tpow *= multlifts[p](mi)
            tmp = tpow*displacements[p]%pe
            vectors[p] += tmp * y1*p**ps1

            if debug:
                print("comparing step", start, p)
                assert tmp == self.verify_summand(p, t, mi, ei)

    def amortized_padic_H_values_matrix(self, t, N, ei, y, start, end, pclass,
                                        V=None, ans=None, debug=False):
        r"""
        Compute the amortized matrix product for a range of the hypergeometric sum.

        If V is specified, each product is premultiplied by V.

        If ans is specified, instead of returning the results, we use them to update ans.
        """
        d = start.denominator()
        r = start.numerator()*(pclass-1) % d
        flgl = self._numden_factors(start, pclass)

        RQ = QQ['k']
        k = RQ.gen()
        K = RQ.fraction_field()

        M = matrix(K, 2*ei, 2*ei)
        # Top left quadrant of M is a scalar matrix.
        for i in range(ei):
            M[i,i] = 1
        # Bottom left quadrant of M represents the substitution on x.
        for i in range(ei):
            M[ei+i,i] = y*(k-r/d)**(ei-1-i)
        # Bottom right quadrant of M represents the accumulating product.
        R1 = K['x']
        x = R1.gen()
        E1 = t*prod((i+k+x)**j[0] for i,j in flgl.items() if j[0] > 0)
        E2 = prod((i+k+x)**-j[0] for i,j in flgl.items() if j[0] < 0)
        E = E1.multiplication_trunc(E2.inverse_series_trunc(ei), ei)
        for i in range(ei):
            for j in range(i+1):
                M[ei+i, ei+j] = E[i-j]

        # Clear polynomial denominators.
        M = M*lcm(M[i,j].denominator() for i in range(2*ei) for j in range(2*ei))
        M = M.change_ring(RQ)
        # Clear integer denominators.
        M = M*lcm(M[i,j].denominator() for i in range(2*ei) for j in range(2*ei))
        RZ = ZZ['k']
        M = M.change_ring(RZ)
        # Remove content from M.
        den = gcd(M[i,j] for i in range(2*ei) for j in range(2*ei))
        M = M.apply_map(lambda x,den=den: x//den)

        # Prepend a matrix V to pick out the relevant rows of the product.
        # This saves a lot of overhead in the remainder forest calculation.
        if V is None:
            V = matrix(ZZ, ei+1, 2*ei)
            V[0,0] = 1
            for i in range(1,ei+1):
                V[-i,-i] = 1

        # Compute the amortized matrix product.
        indices = self._prime_range(t, N)[d][pclass]
        return remainder_forest(M,
                         lambda p, e=ei: p**ei,
                         mbound_dict_c(indices, start, end),
                         kbase=1, V=V,
                         indices=indices, ans=ans, projective=True)

    def amortized_padic_H_values_interval(self, vectors, t, N, start, end, pclass, multlifts, debug=False):
        r"""
        Given a dict `vectors` indexed by primes `p`, update `vectors` via
           vectors[p] += S_i(p)
        where start = gamma_i, end = gamma_{i+1} and we consider primes in the residue class
        `pclass` modulo the denominator of `start`.

        If e>1, we assume that `multlifts` is a dict whose entry at `p` is a series in `k-1`
        computing the multiplicative lift of t^(k-1) modulo p**e.
        """
        # Abort if this summand does not contribute modulo p**e; otherwise, determine the working precision.
        e = self.e
        y, ps = self.interval_mults[start]
        if ps >= e:
            return None
        ei = e-ps

        d = start.denominator()
        r = start.numerator()*(pclass-1) % d

        # Compute a matrix of values used in the inner loop.
        de = ZZ(d**(ei-1))
        mat = matrix(ZZ, [[binomial(h1,h3)*de*(r/d-1)**(h1-h3) for h3 in range(ei)] for h1 in range(ei)])
        mat_as_array = array.array('l', [0] * (ei*(ei+1)//2))
        i = 0
        for h3 in range(ei):
            for h1 in range(h3, ei):
                mat_as_array[i] = mat[h1, h3]
                i += 1

        # Retrieve precomputed values.
        displacements = self.displacements(N, start, pclass, 1)

        # Compute the amortized matrix product.
        ans = self.amortized_padic_H_values_matrix(t, N, ei, y, start, end, pclass)

        for p, tmp in ans.items(): #inner loop
            pe = p if ei==1 else p**ei

            # Update the precomputed series to include [z]^{mi+1}.
            w = displacements[p]
            mip = (start*(p-1)).floor()+1
            tpow = (t%pe).powermod(mip, pe) # faster than power_mod(t, mi, pe)
            if ei>1:
                tpow *= multlifts[p](mip)
                w = w.multiplication_trunc(multlifts[p], ei)

            if debug:
                # Verify the computed value of w(0).
                print("checking w", start, p, mip, ps)
                assert (w if e==1 else w(0)) == self.verify_summand(p, t, mip, ei)

            # Compute the sum using a Cython loop.
            pe1 = (pe-p).divide_knowing_divisible_by(p-1) # reduces to p/(1-p) mod pe
            w = (w,) if ei==1 else tuple(w)
            tmp2 = fast_hgm_sum(w, mat_as_array, tmp, pe1, ei)
            tmp2 = moddiv_int(tpow*tmp2, de*tmp[0,0], pe)

            if debug:
                # Verify that the sum, including the sign, is being computed correctly.
                mi1 = (end*(p-1)).floor()
                if p < 400:
                    print("checking sum", start, p, mip, mi1, ps)
                    assert tmp2 == y*sum(self.verify_summand(p, t, m, ei) for m in range(mi+1,mi1))

            # Include the variable power of p and accumulate the result.
            vectors[p] += tmp2*p**ps

    def amortized_padic_H_values(self, t, N, chained=None, debug=False):
        """
        INPUT:

        - `t` -- a rational number
        - `N` -- a positive integer

        OUTPUT:

        - a dictionary with inputs `p` and outputs the p-adic H value at `t` mod `p^e`.

        """
        e = self.e
        if chained is None: # Chained products only available for e=1, use them by default.
            chained = (e==1)
        if e > 1:
            chained = False

        # Precompute Gamma values.
        self.gammas_cache.increase_N(N)

        # Compute the series expansions of ([t]/t)^k1.
        if e == 1:
            multlifts = None
        else:
            P = ZZ['k1']
            k1 = P.gen()
            den = factorial(ZZ(e-1))
            multlifts = []
            for p in self._prime_range(t, N)[1][0]:
                pe = p**e
                tmp = (t%pe).powermod(p-1, pe) # Faster than power_mod(t, p-1, pe)
                tmp2 = moddiv_int(truncated_log_mod(tmp, e, pe), 1-p, pe)
                w1 = moddiv(truncated_exp(tmp2*k1, e), den, pe)
                multlifts.append((p, w1))
            multlifts = dict(multlifts)

        if debug:
            assert all(power_mod(t*multlifts[p](1),p**e-1,p**e) == 1 for p in self._prime_range(t, N)[1][0])
            assert all(multlifts[p](1)%p == 1 for p in multlifts)

        tmp = identity_matrix(2) if chained else 0
        vectors = {p: tmp for p in self._prime_range(t, N)[1][0]}
        for start, end in self.truncated_starts_ends():
            d = start.denominator()
            for pclass in range(d):
                if d.gcd(pclass) == 1:
                    if e == 1 and chained:
                        # Construct the matrix T_i.
                        Ti = self.amortized_padic_H_values_ferry(t, start, pclass)
                        # Update vectors by multiplying by T_i*S_i(p).
                        y, ps = self.interval_mults[start]
                        self.amortized_padic_H_values_matrix(t, N, 1, 0 if ps else y, start, end, pclass, V=Ti, ans=vectors, debug=debug)
                    else:
                        # Update vectors with P_{m_i}.
                        self.amortized_padic_H_values_step(vectors, t, N, start, pclass, multlifts, debug)
                        # Update vectors with P_{m_i+1}, ..., P_{m_{i+1}}.
                        self.amortized_padic_H_values_interval(vectors, t, N, start, end, pclass, multlifts, debug)

        # Extract results.
        ans = []
        if e == 1 and chained:
            for p, mat in vectors.items():
                ans.append((p, recenter_mod(moddiv_int(mat[1,0], mat[0,0], p), p)))
        else:
            zero_offsets = self.zero_offsets[N]
            for p, tmp in vectors.items():
                pe = p**e
                ans.append((p, recenter_mod(moddiv_int(tmp, (1-p)*zero_offsets[p], pe), pe)))
        return dict(ans)

    def check_functional_equation(self, t, N, bad_factors=None, chained=None, verbose=False):
        r"""
        Run Magma's CheckFunctionalEquation on a hypergeometric L-series.

        We use the amortized method to produce Frobenius traces at good primes;
        Sage's internal function to compute Frobenius traces at powers of good primes;
        and Magma's internal functions for tame conductor exponents, tame Euler factors,
        and the sign. Wild conductor exponents and Euler factors default to guesses provided
        by Magma, but can be overridden by specifying pairs in bad_factors.
        """
        # Create Magma hypergeometric data.
        Hmagma = magma.HypergeometricData(self.alpha_beta())
        if verbose:
            print("Created Magma hypergeometric data")

        wild_primes = set(H.wild_primes())
        tame_primes = set(H.tame_primes(t))

        # Collect prime Frobenius traces.
        prime_traces = self.amortized_padic_H_values(t, N, chained=chained)
        if verbose:
            print("Computed prime Frobenius traces")

        # Collect prime power Frobenius traces.
        s = wild_primes.union(tame_primes)
        n = self.degree()
        tmp = []
        for q in range(N):
            p, f = ZZ(q).is_prime_power(get_data=True)
            if f > 1 and f <= n and p not in s:
                tmp.append((q,p,f))
        prime_power_traces = {q: self.padic_H_value(p=p,f=f,t=t) for (q,p,f) in tmp}
        if verbose:
            print("Computed prime power Frobenius traces")

        # Compile Euler factors at good primes.
        P = PowerSeriesRing(QQ, name='T')
        T = P.gen()
        euler_factors = {}
        for p in prime_traces:
            m = min(ceil(log(N,p)), n)
            l = prime_traces[p]*T + sum(prime_power_traces[p**f]*T**f/f for f in range(2, m))
            l = l + O(T**m)
            euler_factors[p] = exp(-l).polynomial()
        if verbose:
            print("Computed good Euler factors")

        # Need to compile guesses for wild conductors and Euler factors.
        # Magma will fill in the tame ones from a built-in formula.

        bad_euler_factors = bad_factors if bad_factors else {}

        # Write Euler factors to a temporary file to be read in my Magma.
        with open("/tmp/eulerfactors.m", "w") as f:
            f.write("P<T> := PolynomialRing(Integers());\n");
            f.write("EF := [")
            comma = False
            for p,b in euler_factors.items():
                if comma:
                    f.write(",")
                comma = True
                f.write("<{},{},{}>".format(p,0,b))
            for p,b in bad_euler_factors.items():
                f.write(",<{},{},{}>".format(p,b[0],b[1]))
            f.write("];")
        if verbose:
            print("Wrote good Euler factors to file")

        # Use Magma to read the temporary file.
        magma.load("/tmp/eulerfactors.m")
        euler_factors_magma = magma("EF")
        if verbose:
            print("Loaded good Euler factors into Magma")

        # Create the L-series in Magma.
        LSmagma = Hmagma.LSeries(1/t, BadPrimes=euler_factors_magma)
        if verbose:
            print("Created L-series in Magma")

        # Ask Magma to check the functional equation.
        return LSmagma.CFENew()

def compare(log2N, t, e=1, chained=None, vssage=True, vsmagma=True, higher_powers_sage=False, higher_powers_magma=False, extra_cache=True, **kwds):
    r"""
        e.g: compare(15, 1337, vssage=False, cyclotomic=([4,4,2,2], [3,3,3]))
    """
    import resource
    def get_utime():
        return resource.getrusage(resource.RUSAGE_SELF).ru_utime

    for i in range(12,log2N + 1):
        print("2^%s" % i)
        H = AmortizingHypergeometricData(e=e, **kwds)
        if e>1 or not chained:
            start = get_utime()
            H.precompute_gammas(2**i, False if chained is None else chained)
            print("Amortized Gamma: %.2f s" % (get_utime()-start))
            if extra_cache:
                start = get_utime()
                for (s, _) in H.truncated_starts_ends(e):
                    d = s.denominator()
                    for pclass in range(d):
                        if gcd(d, pclass) == 1:
                            for j in range(2):
                                H.displacements(2**i, s, pclass, j)
                print("Additional precomputation: %.2f s" % (get_utime()-start))
        start = get_utime()
        foo = H.amortized_padic_H_values(t, 2**i, chained)
        print("Amortized HG: %.2f s" % (get_utime()-start))
        H.gammas_cache.clear_cache()
        #print_maxrss()
        if vssage:
            start = get_utime()
            bar = {p: H.padic_H_value(p=p,f=1,t=t,prec=e) for p in foo}
            print("Sage:      %.2f s" % (get_utime()-start))
            H._gauss_table = {}
            H.padic_H_value.clear_cache()
            #print_maxrss()
            assert all(foo[p] % p**e == bar[p] % p**e for p in foo if p in bar)
        if vsmagma:
            magma.quit()
            magma.eval('ps := %s;' % sorted(foo))
            magma.eval('H := HypergeometricData(%s, %s);' % H.alpha_beta())
            z = 1/t
            start_magma = magma.Cputime()
            magma.eval('foo := [HypergeometricTrace(H, %s, p) : p in ps];' % z)
            print("Magma:     %.2f s" % (magma.Cputime(start_magma)))
            bar = dict((p, k) for p,k in zip(sorted(foo), eval(magma.eval('foo;'))))
#            print([p for p in foo if p in bar and foo[p] % p**e != bar[p] % p**e])
            assert all(foo[p] % p**e == bar[p] % p**e for p in foo if p in bar)
        if higher_powers_sage or higher_powers_magma:
            s = set(H.wild_primes())
            s = s.union(H.tame_primes(t))
            foo2 = []
            n = self.degree()
            for q in range(2**i):
                p, f = ZZ(q).is_prime_power(get_data=True)
                if f > 1 and f <= n and p not in s:
                    foo2.append((q,p,f))
        if higher_powers_sage:
            start = get_utime()
            bar2 = {q: H.padic_H_value(p=p,f=f,t=t,prec=e) for (q,p,f) in foo2}
            print("Sage higher powers:      %.2f s" % (get_utime()-start))
            H._gauss_table = {}
            H.padic_H_value.clear_cache()
        if higher_powers_magma:
            magma.quit()
            magma.eval('ps := %s;' % sorted([q for (q,p,f) in foo2]))
            magma.eval('H := HypergeometricData(%s, %s);' % H.alpha_beta())
            z = 1/t
            start_magma = magma.Cputime()
            magma.eval('foo2 := [HypergeometricTrace(H, %s, p) : p in ps];' % z)
            print("Magma higher powers:     %.2f s" % (magma.Cputime(start_magma)))
            if higher_powers_sage:
                bar2 = dict((q, k) for q,k in zip(sorted(foo2), eval(magma.eval('foo2;'))))
                assert all(foo2[q] == bar2[q]  for q in foo if q in bar2)
        print("")

