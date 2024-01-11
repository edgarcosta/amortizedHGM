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
    gamma_expansion_product,
    gammas_to_displacements,
    hgm_matmult,
    mbound_dict_c,
    moddiv_int,
    multiplicative_lift,
    p_over_1_minus_p,
    prime_range_by_residues
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

        sage: from amortizedHGM.hgm_modpe import interpolation_polys
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

    * ``e`` -- a positive integer; computations will be done modulo p^e.

    For ``gamma_list``, it is also allowed to provide just one list of
    signed integers where signs indicate to which part the integer
    belongs to.

    EXAMPLES:

    We create a hypergeometric datum for a given alpha and beta::

        sage: from amortizedHGM import AmortizingHypergeometricData
        sage: H = AmortizingHypergeometricData(cyclotomic=([4,4,2,2], [3,3,3]))

    The precision needed to uniquely determine the traces is::

        sage: (H.e, 1 + H.weight() // 2)
        (2, 2)

    We can compute Frobenius traces at a given value of t for good p up to 1000::

        sage: values = H.amortized_padic_H_values(t=1337, N=1000)
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
    def __init__(self, x=None, cyclotomic=None, alpha_beta=None, gamma_list=None, e=None):
        if isinstance(x, HypergeometricData):
            HypergeometricData.__init__(self, alpha_beta=x.alpha_beta())
        else:
            HypergeometricData.__init__(self, cyclotomic, alpha_beta, gamma_list)
        alpha, beta = self.alpha(), self.beta()
        if 0 in alpha:
            # The trace formula we are using breaks when alpha contains 0.
            # We instead compute with alpha and beta swapped.
            self.swap = AmortizingHypergeometricData(self.swap_alpha_beta(), e=e)
        else:
            self.swap = None
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
            eta_m = self.zigzag(brk) + beta.count(brk) - alpha.count(brk)
            xi_m = beta.count(0) - beta.count(brk)
            ps = eta_m + xi_m + self.D
            assert (ps >= 0)
            sign = ZZ(-1) if eta_m%2 else ZZ(1)
            self.break_mults_p1[brk] = (sign, ps)

        if e is None:
            e = self.weight()//2 + 1
        self.e = e
        self.gammas_cache = pAdicLogGammaCache(e)
        self.zero_offsets = {}

    def break_mults_by_pclass(self, start, pclass):
        return self.break_mults_p1[start] if pclass == 1 else self.break_mults[start]

    @cached_method
    def truncated_starts_ends(self):
        r"""
        List starts and ends of intervals, omitting those at the end which do not contribute
        to the trace mod p**e.

        INPUT:

        - ``e`` -- a positive integer, the precision

        OUTPUT:

        A list of pairs (start, end) giving endpoints for intervals between 0 and 1.

        EXAMPLES::

            sage: from amortizedHGM import AmortizingHypergeometricData
            sage: H = AmortizingHypergeometricData(cyclotomic=([5], [2,2,2,2]))

        We need all intervals at precision 2::

            sage: H.truncated_starts_ends()
            [(0, 1/5), (1/5, 2/5), (2/5, 1/2), (1/2, 3/5), (3/5, 4/5), (4/5, 1)]

        But the last interval is irrelevant at precision 1::

            sage: H = AmortizingHypergeometricData(cyclotomic=([5], [2,2,2,2]), e=1)
            sage: H.truncated_starts_ends()
            [(0, 1/5), (1/5, 2/5), (2/5, 1/2), (1/2, 3/5), (3/5, 4/5)]
            sage: H.break_mults[4/5]
            (-1, 1)
            sage: H.break_mults_p1[4/5]
            (-1, 1)
        """
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

            sage: from amortizedHGM import AmortizingHypergeometricData
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

            sage: from amortizedHGM import AmortizingHypergeometricData
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
        # Exclude other small primes to avoid edge cases.
        d = max(i.denominator() for i in self._alpha + self._beta)
        t = QQ(t)
        m = t.numerator()*t.denominator()*(t-1).numerator()
        lower_bound = max(self.e+1, d*(d-1)+1)
        return prime_range_by_residues(lower_bound, N, ds, m, s)

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

            sage: from amortizedHGM import AmortizingHypergeometricData
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
        - ``pclass`` -- an integer between 0 and `b-1` that is relatively prime to `b`

        OUTPUT:

        A dictionary of the form ``{t: (i, j)}`` where ``t`` is the constant term of a
        linear factor, ``i`` is its multiplicity (positive or negative), and ``j`` is 1 if this factor
        arises from ``start`` and 0 otherwise.

        EXAMPLES::

            sage: from amortizedHGM import AmortizingHypergeometricData
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
        freq = {}
        for a in self.alpha():
            freq[a] = freq.get(a, 0) + 1
        for b in self.beta():
            freq[b] = freq.get(b, 0) - 1
        # We shift the term corresponding to a or b by 1 because we're taking
        # the fractional part of a negative number when less than start.
        # We also need to separately indicate any values equal to start.
        shift = self._starts_to_rationals[start][pclass]
        flgl = {QQ(i + shift + (1 if i <= start else 0)): (ZZ(j), ZZ(1) if i == start else ZZ(0))
                for i,j in freq.items()}
        return flgl

    @cached_method
    def gamma_denoms(self):
        r"""
        Return the denominators of pairwise differences between elements of alpha+beta.

        OUTPUT:

        The set of denominators of rational numbers of the form ``gamma0 - gamma1``,
        each an element of ``alpha`` or ``beta``.

        EXAMPLES::

            sage: from amortizedHGM import AmortizingHypergeometricData
            sage: H = AmortizingHypergeometricData(cyclotomic=([5,4], [7]))
            sage: H.alpha_beta()
            ([1/5, 1/4, 2/5, 3/5, 3/4, 4/5], [1/7, 2/7, 3/7, 4/7, 5/7, 6/7])
            sage: H.gamma_denoms()
            {1, 2, 4, 5, 7, 20, 28, 35}
        """
        e = self.e
        dens = set([1])
        for (start, _) in self.truncated_starts_ends():
            d = start.denominator()
            for pclass in range(d):
                if d.gcd(pclass) == 1:
                    # r = start.numerator()*(pclass-1) % d
                    for i in self._numden_factors(start, pclass):
                        dens.add(i.denominator())
        return dens

    def verify_summand(self, p, t, m, ei):
        r"""
        Compute a summand of the hypergeometric trace formula for debugging.

        INPUT:

        - ``p`` -- a prime that is not tame or wild
        - ``t`` -- a rational number
        - ``m`` -- an integer between 0 and p-2
        - ``ei`` -- a positive integer, the precision

        OUTPUT:

        The summand corresponding to m in the formula for ``H_p(alpha, beta | t) mod p^ei``.

        EXAMPLES::

            sage: from amortizedHGM import AmortizingHypergeometricData
            sage: H = AmortizingHypergeometricData(cyclotomic=([5,4], [7]))
            sage: H.verify_summand(97, 52/5, 58, 2)
            2968
        """
        F = Qp(p)
        R = IntegerModRing(p**ei)
        tmult = power_mod(t, p**(ei-1), p**ei)
        return (R(tmult)**m *
            prod(R(F(frac(i+m/(1-p))).gamma()) for i in self._alpha) /
            prod(R(F(frac(i)).gamma()) for i in self._alpha) /
            prod(R(F(frac(i+m/(1-p))).gamma()) for i in self._beta) *
            prod(R(F(frac(i)).gamma()) for i in self._beta))

    def precompute_gammas(self, N, chained=False):
        r"""
        Precompute series expansion of p-adic Gamma needed for hypergeometric traces.

        The result is cached in self.gammas_cache.  Note that calling this function
        is not required before computing displacements, but it is included in order
        to separate the time used for precomputation from the time used for later steps.

        INPUT:

        - ``N`` -- a positive integer, the upper bound on the primes
        - ``chained`` -- a boolean, only used to disable the computation in the case that e=1 and chained is true (when an older algorithm is used)

        EXAMPLES::

            sage: from amortizedHGM import AmortizingHypergeometricData
            sage: H = AmortizingHypergeometricData(cyclotomic=([5], [2,2,2,2]))
            sage: H.precompute_gammas(100)
            sage: H.gammas_cache.expansion((9, 28, 89))
            (1928, -1, [-16, 1602])
        """
        e = self.e
        if e == 1 and chained:
            return None
        self.gammas_cache.increase_N(N)
        for b in self.gamma_denoms():
            self.gammas_cache._set_expansion_at_offset(b)

    @cached_method
    def displacements(self, N, start, pclass):
        r"""
        Precompute p-adic displacements using Gamma values.

        These represent the value of P_{m_i} and P_{m_i+k} for k>0, assuming z=1.

        INPUT:

        - ``N`` -- a positive integer, the upper bound on the primes computed
        - ``start`` -- a gamma value `a/b` (one of the alpha or betas), representing the start of the interval
        - ``pclass`` -- an integer between 0 and b-1 that is relatively prime to b

        OUTPUT:

        If this interval contributes nothing (because the base valuation is larger than e),
        return ``None``.  Otherwise, a dictionary indexed by primes congruent to ``pclass``
        modulo the denominator of ``start``, with value a pair representing 
        `P_{m_i}` and `P_{m_i+1}`.

        EXAMPLES::

            sage: from amortizedHGM import AmortizingHypergeometricData
            sage: H = AmortizingHypergeometricData(cyclotomic=([5], [2,2,2,2]))
            sage: H.displacements(50, 1/2, 1, 1)
            {23: 23*k1 + 206,
             29: 638*k1 + 316,
             31: 341*k1 + 615,
             37: 1258*k1 + 1288,
             41: 902*k1 + 1193,
             43: 1548*k1 + 1056,
             47: 329*k1 + 722}
            sage: H.displacements(50, 3/5, 2, 0)
            {37: 624, 47: 106}
        """
        e = self.e
        _, ps1 = self.break_mults_by_pclass(start, pclass)
        _, ps = self.interval_mults[start]
        if start == 0: 
            # Need initial value modulo p**e for normalization.
            # In the balanced case, we only need it modulo p.
            ps1 = min(e-1, ps1)
        if ps1 >= e and ps >= e:
            return None

        # Precompute the effect of integer shifts away from (0,1].
        flgl = {}
        tmp = [QQ(1), QQ(1)]
        R1 = QQ['x1']
        x1 = R1.gen()
        tmp2 = [R1(0), R1(0)]
        for i0, j0 in self._numden_factors(start, pclass).items():
            i,j = i0[0], j0[0]
            flgl[(i+1-i.ceil()).as_integer_ratio()] = j
            for index in range(2):
                i = i0 + (1 if index else -j0[1])
                if i < 0:
                    tmp[index] /= (-i)**j
                    tmp2[index] += j*sum((-x1/i)**k/k for k in range(1,e))
                elif i > 1:
                    tmp[index] *= (1-i)**j
                    tmp2[index] -= j*sum((-x1/(i-1))**k/k for k in range(1,e))
                elif i == 0:
                    tmp[index] *= (-QQ(1))**j
        tmp2 = [tuple(t[i].as_integer_ratio() for i in range(e)) for t in tmp2]

        gammas = self.gammas_cache
        ei1 = e-ps1
        ei = e-ps
        eimax = max(ei1, ei)
        gammasum = None if eimax==1 else [0 for i in range(eimax)]
        l0 = (gammas, gammas.cache, gammas.e, flgl, gammasum)
        
        d = start.denominator()
        r = start.numerator()*(pclass-1) % d
        R1 = ZZ['k1'] # k1 stands for k-r/d
        inter_polys = interpolation_polys(ei, R1.gen())
        tmp = tuple(t.as_integer_ratio() for t in tmp)
        l = None if max(ei1, ei) <= 1 else (tmp2, r, d, 
            1 if ei1 < 1 else factorial(ZZ(ei1-1)), 
            1 if ei<1 else factorial(ZZ(ei-1))**3, inter_polys, R1.gen())

        ans = {p: gammas_to_displacements(p, ei1, ei,
               *gamma_expansion_product(l0, p, eimax), tmp, l)
               for p in self._prime_range(ZZ(-1), N)[d][pclass]} #inner loop
        # If start==0, we need to extract a normalization factor.
        if start == 0:
            if ei1 == e:
                self.zero_offsets[N] = {p: i[0] for p, i in ans.items()}
            else:
                self.zero_offsets[N] = {p: i[0]*multiplicative_lift(i[0], p, e, p_over_1_minus_p(p, e))%p**e for p, i in ans.items()}
        return ans

    def amortized_padic_H_values_ferry(self, t, start, pclass):
        r"""
        Compute the matrix T_i(p) mod p. This is only used when e=1.

        INPUT:

        - ``t`` -- a rational number, the parameter of the hypergeometric motive
        - ``start`` -- the left endpoint of an interval, `a/b` (one of the alpha or betas)
        - ``pclass`` -- an integer `c` between 0 and `b`, relatively prime to `b`

        OUTPUT:

        The matrix T_i(p) from (5.22) of [CKR20], rescaled to be integral.

        EXAMPLES::

            sage: from amortizedHGM import AmortizingHypergeometricData
            sage: H = AmortizingHypergeometricData(cyclotomic=([5,4], [7]))
            sage: H.amortized_padic_H_values_ferry(1, 3/5, 4)
            [  43776       0]
            [ -43776 1529437]
        """
        y1, ps1 = self.break_mults_by_pclass(start, pclass)
        y1 *= 0**ps1
        multiplier = lambda x: -x if x else ZZ(-1)
        flgl = self._numden_factors(start, pclass)
        feq_seed = t * prod(multiplier(i-k)**j[0] for i,j in flgl.items() for k in range(j[1]+1))
        feq_seed_num, feq_seed_den = feq_seed.as_integer_ratio()
        return matrix(ZZ, 2, 2, [feq_seed_den, 0, feq_seed_den*y1, feq_seed_num])

    def amortized_padic_H_values_matrix(self, t, N, ei, y, start, end, pclass,
                                        V=None, ans=None, chained=False):
        r"""
        Calls the rforest library to compute an amortized matrix product
        used for computing a part of the trace formula.

        INPUT:

        - ``t`` -- a rational number, the parameter of the hypergeometric motive.
        - ``N`` -- the upper bound on primes
        - ``ei`` -- the precision for this interval, which may be less than the
          overall precision `e` for this hypergeometric data
        - ``y`` -- a sign (0, 1 or -1), used to scale off-diagonal matrix entries and
          coming from `interval_mults`.  It is `\bar{\sigma}_i` in [CKR23].
        - ``start`` -- a rational number `a/b`, the left endpoint of the interval
        - ``end`` -- a rational number, the right endpoint of the interval
        - ``pclass`` -- an integer between 0 and `b`, coprime to `b`,
          specifying the congruence class of primes to be summed
        - ``V`` -- if specified, each product is premultiplied by V
          (ignored if ``chained`` is False).
        - ``ans`` -- (optional) a dictionary, indexed by primes `p`.  If specified,
          it will be updated with the results instead of returning them.
        - ``chained`` -- If True, use the chained algorithm described in [CKR20].
          Otherwise, some rows and columns are removed from the output.

        OUTPUT:

        If ``ans`` is not provided, returns the output of a call to ``remainder_forest``,
        which will be a dictionary keyed by primes with `e_i+1` by `e_i` matrix values

        EXAMPLES::

            sage: from amortizedHGM import AmortizingHypergeometricData
            sage: H = AmortizingHypergeometricData(cyclotomic=([5], [2,2,2,2]))
            sage: ei = 2
            sage: N = 1000
            sage: t = 381/117
            sage: start, end = 1/2, 3/5
            sage: vectors = H.amortized_padic_H_values_matrix(t, N, ei, 1, start, end, 1)
            sage: len(vectors)
            159
            sage: vectors[997]
            [878914      0]
            [157867      0]
            [500805 119104]
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
        if not chained:
            V = matrix(ZZ, ei+1, 2*ei)
            for i in range(1,ei+2):
                V[-i,-i] = 1

        # Compute the amortized matrix product.
        # We use cutoff to pick out the relevant columns of the product.
        indices = self._prime_range(t, N)[d][pclass]
        return remainder_forest(M,
                         lambda p, e=ei: p**ei,
                         mbound_dict_c(indices, start, end),
                         kbase=1, V=V,
                         indices=indices, ans=ans, projective=True,
                         cutoff=None if chained else ei)

    def amortized_padic_H_values_step(self, vectors, t, N, start, pclass, multlifts, debug=False):
        r"""
        Adds terms to the trace formula sum corresponding to break points, where
        the functional equation used in the interior of the intervals does not apply.

        INPUT:

        - ``vectors`` -- a dictionary, indexed by primes `p`
        - ``t`` -- a rational number, the parameter for the hypergeometric motive
        - ``N`` -- the upper bound on primes
        - ``start`` -- a rational number `a/b`, the left endpoint of an interval
          (ie one of the alpha or beta)
        - ``pclass`` -- an integer between 0 and `b`, relatively prime to `b`,
          specifying which primes should be updated
        - ``multlifts`` -- A dictionary whose entry at `p` is a series in `k-1`
          computing the multiplicative lift of `t^{k-1}` modulo `p^e` (only used for `e>1`)
        - ``debug`` -- whether to perform debugging checks

        OUTPUT:

        None, but updates `vectors` via
            vectors[p] += P'_{m_i},
        where m_i = floor(p*start), for primes `p` in the residue class
        `pclass` modulo the denominator of `start`.

        EXAMPLES::

            sage: from amortizedHGM import AmortizingHypergeometricData
            sage: from amortizedHGM.hgm_misc import multiplicative_lift
            sage: from collections import defaultdict
            sage: H = AmortizingHypergeometricData(cyclotomic=([5], [2,2,2,2]))
            sage: e = H.e; e
            2
            sage: N = 1000
            sage: t = 381/117
            sage: start = 3/5
            sage: P.<k1> = ZZ[]
            sage: vectors = defaultdict(ZZ)
            sage: multlifts = {p: multiplicative_lift(t, p, e, k1) for p in H._prime_range(t, N)[1][0]}
            sage: H.amortized_padic_H_values_step(vectors, t, N, start, 1, multlifts)
            sage: len(vectors)
            39
            sage: vectors[751]
            163263
        """
        e = self.e
        y1, ps1 = self.break_mults_by_pclass(start, pclass)
        if ps1 >= e:
            return
        ei1 = e - ps1

        # Retrieve precomputation results.
        displacements = self.displacements(N, start, pclass)

        d = start.denominator()

        def debug_check():
            print("checking step", start, p, mi, ps1)
            assert tmp == y1*self.verify_summand(p, t, mi, ei1)*self.zero_offsets[N][p]

        if ei1 == 1: # Abbreviated version of the general case.
            for p in self._prime_range(t, N)[d][pclass]:
                mi = (start*(p-1)).floor()
                tpow = (t%p).powermod(mi, p) # faster than power_mod(t, mi, p)
                tmp = y1*(tpow*displacements[p][0]%p)
                if debug:
                    debug_check()
                if ps1:
                    tmp *= p if ps1==1 else p**ps1
                vectors[p] += tmp
        else:
            for p in self._prime_range(t, N)[d][pclass]:
                mi = (start*(p-1)).floor()
                pe = p**ei1
                tpow = (t%pe).powermod(mi, pe) * multlifts[p](mi*p_over_1_minus_p(p, e))
                tmp = y1*(tpow*displacements[p][0]%pe)
                if debug:
                    debug_check()
                if ps1:
                    tmp *= p if ps1==1 else p**ps1
                vectors[p] += tmp

    def amortized_padic_H_values_interval(self, vectors, t, N, start, end, pclass, multlifts, debug=False):
        r"""
        Uses an amortized matrix product to compute a piece of the trace formula
        corresponding to an interval between two break points, simultaneously for
        all primes in a given congruence class.

        INPUT:

        - ``vectors`` -- a dictionary, indexed by primes `p`
        - ``t`` -- a rational number, the parameter for the hypergeometric motive
        - ``N`` -- the upper bound on primes
        - ``start`` -- a rational number `a/b`, the left endpoint of an interval
          (ie one of the alpha or beta)
        - ``end`` -- the right endpoint of an interval
        - ``pclass`` -- an integer between 0 and `b`, relatively prime to `b`,
          specifying which primes should be updated
        - ``multlifts`` -- A dictionary whose entry at `p` is a series in `k-1`
          computing the multiplicative lift of `t^{k-1}` modulo `p^e` (only used for `e>1`)
        - ``debug`` -- whether to perform debugging checks

        OUTPUT:

        None, but updates `vectors` via
           vectors[p] += sum_{m = floor(start*p)+1}^{floor(end*p)-1} P'_m
        where start = gamma_i, end = gamma_{i+1} and we consider primes in the residue class
        `pclass` modulo the denominator of `start`.

        EXAMPLES::

            sage: from amortizedHGM import AmortizingHypergeometricData
            sage: from amortizedHGM.hgm_misc import multiplicative_lift
            sage: from collections import defaultdict
            sage: H = AmortizingHypergeometricData(cyclotomic=([5], [2,2,2,2]))
            sage: e = H.e; e
            2
            sage: N = 1000
            sage: t = 381/117
            sage: start = 1/2
            sage: end = 3/5
            sage: P.<k1> = ZZ[]
            sage: vectors = defaultdict(ZZ)
            sage: multlifts = {p: multiplicative_lift(t, p, e, k1) for p in H._prime_range(t, N)[1][0]}
            sage: H.amortized_padic_H_values_interval(vectors, t, N, start, end, 1, multlifts)
            sage: len(vectors)
            159
            sage: vectors[997]
            20959
        """
        # Abort if this summand does not contribute modulo p**e; otherwise, determine the working precision.
        e = self.e
        y, ps = self.interval_mults[start]
        if ps >= e:
            return
        ei = e-ps

        d = start.denominator()
        r = start.numerator()*(pclass-1) % d

        # Retrieve precomputed values.
        displacements = self.displacements(N, start, pclass)

        # Compute the amortized matrix product.
        ans = self.amortized_padic_H_values_matrix(t, N, ei, y, start, end, pclass)

        def debug_check():
            # Verify that the sum, including the sign, is being computed correctly.
            mi1 = (end*(p-1)).floor()
            print("checking sum", start, p, mi+1, mi1, ps)
            assert tmp2 == y*sum(self.verify_summand(p, t, m, ei) for m in range(mi+1,mi1))*self.zero_offsets[N][p]

        if ei == 1: # Abbreviated version of the general case.
            for p, tmp in ans.items(): #inner loop
                w = displacements[p][1]
                mi = (start*(p-1)).floor()
                tpow = (t%p).powermod(mi+1, p) # faster than power_mod(t, mi, p)
                tmp2 = moddiv_int(tpow*w*tmp[-1,0], tmp[0,-1], p)
                if debug:
                    debug_check()
                if ps:
                    tmp2 *= p if ps==1 else p**ps
                vectors[p] += tmp2
        else:
            for p, tmp in ans.items(): #inner loop
                p_minus_1 = p-1
                w0, w = displacements[p][1]
                mi = (start*p_minus_1).floor()
                pe = p**ei
                pe1 = p_over_1_minus_p(p, ei)

                # Compute the c_{i,h}(p) by combining precomputed values with [z]^{mi+1}.
                arg = mi*pe1 if not r else p*(moddiv_int(d*mi+r, d, p) if ei==2 else moddiv_int(d*mi+r, -d*p_minus_1, p**(ei-1)))
                tpow = w0 * (t%pe).powermod(mi+1, pe) * multlifts[p](arg)
                w = w.multiplication_trunc(multlifts[p], ei)

                # Compute the sum using a matrix multiplication implemented directly in Cython.
                tmp2 = moddiv_int(tpow*hgm_matmult(w, tmp, pe1, ei), tmp[0,-1], pe)

                if debug:
                    debug_check()

                # Include the variable power of p and accumulate the result.
                if ps:
                    tmp2 *= p if ps==1 else p**ps
                vectors[p] += tmp2

    def amortized_padic_H_values(self, t, N, chained=None, debug=False):
        """
        Return the `p`-adic trace of Frobenius for (sufficiently large) primes up to `N`
        using the algorithms described in [CKR20] and [CKR23].

        The precision `e` is determined at creation for the ``AmortizingHypergeometricData``.

        INPUT:

        - ``t`` -- a rational number, the parameter of the hypergeometric motive
        - ``N`` -- a positive integer, an upper bound on the primes computed
        - ``chained`` -- a boolean, whether to use the chained algorithm from [CKR20]
          in the `e=1` case (default).  Ignored for `e>1`.
        - ``debug`` -- whether to perform debuggin checks

        OUTPUT:

        - a dictionary with inputs `p` and outputs the p-adic H value at `t` mod `p^e`.

        EXAMPLES::

            sage: from amortizedHGM import AmortizingHypergeometricData
            sage: H = AmortizingHypergeometricData(cyclotomic=([5], [2,2,2,2]))
            sage: N = 1000
            sage: t = 381/117
            sage: traces = H.amortized_padic_H_values(t, N)
            sage: min(traces) # small primes are skipped
            23
            sage: traces[23] == H.padic_H_value(23, 1, t)
            True
        """
        if self.swap is not None:
            return self.swap.amortized_padic_H_values(1/t, N, chained, debug)
        e = self.e
        if e > 1: # Chained products only available for e=1.
            chained = False
        elif chained is None: # For e=1, default to chained products.
            chained = True

        # Compute the series expansions of ([t]/t)^k1.
        if e == 1:
            multlifts = None
        else:
            P = ZZ['k1']
            k1 = P.gen()
            multlifts = {p: multiplicative_lift(t, p, e, k1) for p in self._prime_range(t, N)[1][0]}

            if debug:
                for p in multlifts:
                    pe = p**e
                    pe1 = p_over_1_minus_p(p, e) # reduces to p/(1-p) mod pe
                    assert power_mod(t*multlifts[p](pe1),pe-1,pe) == 1
                    assert multlifts[p](pe1)%p == 1

        if chained:
            tmp = identity_matrix(2)
        else:
            # Precompute Gamma values and zero offsets.
            self.gammas_cache.increase_N(N)
            self.displacements(N, ZZ(0), ZZ(0))
            tmp = ZZ(0)
        vectors = {p: tmp for p in self._prime_range(t, N)[1][0]}
        for start, end in self.truncated_starts_ends():
            d = start.denominator()
            for pclass in range(d):
                if d.gcd(pclass) == 1:
                    if chained: # Forces e==1
                        # Construct the matrix T_i.
                        Ti = self.amortized_padic_H_values_ferry(t, start, pclass)
                        # Update vectors by multiplying by T_i*S_i(p).
                        y, ps = self.interval_mults[start]
                        self.amortized_padic_H_values_matrix(t, N, 1, 0 if ps else y, start, end, pclass, V=Ti, ans=vectors, chained=True)
                    else:
                        # Update vectors with P'_{m_i}.
                        self.amortized_padic_H_values_step(vectors, t, N, start, pclass, multlifts, debug)
                        # Update vectors with P'_{m_i+1}, ..., P'_{m_{i+1}}.
                        self.amortized_padic_H_values_interval(vectors, t, N, start, end, pclass, multlifts, debug)

        # Extract results.
        if chained: # Forces e==1
            return {p: moddiv_int(mat[1,0], mat[0,0], p) for p, mat in vectors.items()}
        zero_offsets = self.zero_offsets[N]
        return {p: moddiv_int(tmp, (1-p)*zero_offsets[p], p**e) for p, tmp in vectors.items()}

    def check_functional_equation(self, t, N, bad_factors=None, chained=None, verbose=False):
        # TODO: improve this (Edgar)
        r"""
        This is experimental!

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

        # Collect prime Frobenius traces.
        prime_traces = self.amortized_padic_H_values(t, N, chained=chained)
        if verbose:
            print("Computed prime Frobenius traces")

        # Collect prime power Frobenius traces.
        m = QQ(t).numerator()*QQ(t).denominator()*QQ(t-1).numerator()
        n = self.degree()
        tmp = []

        for q in range(N):
            p, f = ZZ(q).is_prime_power(get_data=True)
            if f > 1 and f <= n and p not in wild_primes and m%p:
                tmp.append((q,p,f))
        prime_power_traces = {q: self.padic_H_value(p=p,f=f,t=t) for (q,p,f) in tmp}
        if verbose:
            print("Computed prime power Frobenius traces")

        # Compile Euler factors at good primes.
        P = PowerSeriesRing(QQ, name='T')
        T = P.gen()
        euler_factors = {}
        for p in prime_traces:
            mp = min(ceil(log(N,p)), n)
            l = prime_traces[p]*T + sum(prime_power_traces[p**f]*T**f/f for f in range(2, mp))
            l = l + O(T**mp)
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

    def compare(self, log2N, t, log2N_start=12, chained=None, vssage=True, vsmagma=True, higher_powers_sage=False, higher_powers_magma=False, extra_cache=True, debug=False):
        r"""
        INPUT:

        - ``log2N`` -- a positive integer, at least 12.  Computes traces for
          log_2(N) from 12 up to this bound.
        - ``t`` -- a rational number, the parameter for the hypergeometric motive
        - ``chained`` -- boolean, whether to use the algorithm from [CKR20], rather than the
          newer algorithm from [CKR23].  Defaults to True for e=1 and False otherwise.
        - ``vssage`` -- whether to compare to Sage's implementation of the trace formula
        - ``vsmagma`` -- whether to compare to Magma's implementation of the trace formula
        - ``higher_powers_sage`` -- whether to time the computation of prime powers up to N
          using Sage
        - ``higher_powers_magma`` -- whether to time the computation of prime powers up to N
          using Magma
        - ``extra_cache`` -- whether to time the computation of the displacements from the
          stored p-adic gamma values

        EXAMPLES::

            sage: H = AmortizingHypergeometricData(cyclotomic=([4,4,2,2], [3,3,3]))
            sage: H.compare(14, 1337, vssage=False) #random
            2^12
            Amortized Gamma: 0.26 s
            Additional precomputation: 0.05 s
            Amortized HG: 0.08 s
            Magma:     2.20 s

            2^13
            Amortized Gamma: 0.16 s
            Additional precomputation: 0.09 s
            Amortized HG: 0.08 s
            Magma:     8.59 s

            2^14
            Amortized Gamma: 0.32 s
            Additional precomputation: 0.17 s
            Amortized HG: 0.21 s
            Magma:     31.02 s
        """
        import resource
        def get_utime():
            return resource.getrusage(resource.RUSAGE_SELF).ru_utime

        def report(res, name, t):
            res[name] = t
            print(f"{name}: {t:.2f} s")
        e = self.e

        res = {}
        for i in range(log2N_start, log2N + 1):
            res[i] = {}
            self.gammas_cache.clear_cache()
            self.displacements.clear_cache()
            self.zero_offsets = {}
            # Don't worry about clearing caches for basic things like
            # truncated_starts_ends, _start_to_rationals, _numden_factors, gamma_denoms
            print("2^%s" % i)
            if e>1 or chained is False:
                start = get_utime()
                self.precompute_gammas(2**i, chained=False)
                report(res[i], "Amortized gamma", get_utime() - start)
                if extra_cache:
                    start = get_utime()
                    for (s, _) in self.truncated_starts_ends():
                        d = s.denominator()
                        for pclass in range(d):
                            if gcd(d, pclass) == 1:
                                self.displacements(2**i, s, pclass)

                    report(res[i], "Additional precomputation", get_utime()-start)
            start = get_utime()
            foo = self.amortized_padic_H_values(t, 2**i, chained, debug=debug)
            report(res[i], "Amortized HG", get_utime() - start)
            self.gammas_cache.clear_cache()
            #print_maxrss()
            if vssage:
                start = get_utime()
                bar = {p: self.padic_H_value(p=p,f=1,t=t,prec=e) for p in foo}
                report(res[i], "Sage", get_utime() - start)
                self._gauss_table = {}
                self.padic_H_value.clear_cache()
                #print_maxrss()
                assert all(foo[p] % p**e == bar[p] % p**e for p in foo if p in bar)
            if vsmagma:
                magma.quit()
                magma.eval('ps := %s;' % sorted(foo))
                magma.eval('H := HypergeometricData(%s, %s);' % self.alpha_beta())
                z = 1/t
                start_magma = magma.Cputime()
                magma.eval('foo := [HypergeometricTrace(H, %s, p) : p in ps];' % z)
                report(res[i], "Magma", magma.Cputime(start_magma))
                bar = dict((p, k) for p,k in zip(sorted(foo), eval(magma.eval('foo;'))))
                assert all(foo[p] % p**e == bar[p] % p**e for p in foo if p in bar)
            if higher_powers_sage or higher_powers_magma:
                s = set(self.wild_primes())
                m = QQ(t).numerator()*QQ(t).denominator()*QQ(t-1).numerator()
                foo2 = []
                n = self.degree()
                for q in range(2**i):
                    p, f = ZZ(q).is_prime_power(get_data=True)
                    if f > 1 and f <= n and p not in s and m%p:
                        foo2.append((q,p,f))
            if higher_powers_sage:
                start = get_utime()
                bar2 = {q: self.padic_H_value(p=p,f=f,t=t,prec=e) for (q,p,f) in foo2}
                report(res[i], "Sage higher powers", get_utime() - start)
                self._gauss_table = {}
                self.padic_H_value.clear_cache()
            if higher_powers_magma:
                magma.quit()
                magma.eval('ps := %s;' % sorted([q for (q,p,f) in foo2]))
                magma.eval('H := HypergeometricData(%s, %s);' % self.alpha_beta())
                z = 1/t
                start_magma = magma.Cputime()
                magma.eval('foo2 := [HypergeometricTrace(H, %s, p) : p in ps];' % z)
                report(res[i], "Magma higher powers", magma.Cputime(start_magma))
                if higher_powers_sage:
                    bar2 = dict((q, k) for q,k in zip(sorted(foo2), eval(magma.eval('foo2;'))))
                    assert all(foo2[q] == bar2[q]  for q in foo if q in bar2)
            print("")

        return res

