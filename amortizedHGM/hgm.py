from collections import defaultdict

from sage.arith.functions import lcm, LCM
from sage.arith.misc import previous_prime
from sage.functions.other import floor, factorial, frac as frac
from sage.interfaces.magma import magma
from sage.matrix.constructor import Matrix, matrix
from sage.matrix.special import block_matrix, zero_matrix, identity_matrix
from sage.misc.cachefunc import cached_method, cached_function
from sage.misc.lazy_attribute import lazy_attribute
from sage.misc.misc_c import prod
from sage.modular.hypergeometric_motive import enumerate_hypergeometric_data, HypergeometricData
from sage.modules.free_module_element import vector
from sage.rings.big_oh import O
from sage.rings.fast_arith import prime_range
from sage.rings.finite_rings.finite_field_constructor import FiniteField as GF
from sage.rings.integer_ring import ZZ
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.power_series_ring import PowerSeriesRing
from sage.rings.rational_field import QQ

from pyrforest import remainder_forest

from .hgm_misc import mbound_dict_c


@cached_function
def subsitution(e, g, scalar=1):
    r"""
    return a matrix M that represents the linear transformation:
        h(x) mod x^e -> h(g(x)) mod x^e
    explicitly, if
        h = a_0 + a_1*x + ... + a_{e-1}*x^(e-1)
    then
        vector([a_0, ..., a_{e-1}]) * M
    represents
        h(g(x)) mod x^e
    """
    base_ring = g.parent().base_ring()
    S = PolynomialRing(base_ring, e, 'a')
    R = PowerSeriesRing(S, 'x', default_prec=e)
    from_monomial = {tuple(1 if i == j else 0 for j in range(e)) : i for i in range(e)}
    x = R.gen()
    h = R(list(S.gens()))
    pol = R(scalar*h(g(x))).padded_list(e)
    res = []
    for elt in pol:
        reselt = [0]*e
        for m, v in elt.dict().items():
            reselt[from_monomial[tuple(m)]] = v
        res.append(reselt)
    return Matrix(base_ring, res).transpose()




def list_to_uppertriangular(v):
    v = list(v)
    e = len(v)
    return Matrix([[0]*i + v[:e - i] for i in range(e)])

def power_series_to_matrix(f, e):
    r"""
    convert a power series f(x) mod x^e to an e times e bandid matrix
    """
    return list_to_uppertriangular(f.padded_list(e))


def finitediff(k, M, a=0):
    """
    INPUT:

    - k, a positive integer
    - M, a vector with (n + 1) elements, representing M(Y) = M_0 + M_1 * Y + M_2 Y^2 + ... + M_n * Y^n

    OUTPUT:

    - an interator yielding M(a + i) for i = 0, ..., k - 1

    EXAMPLES::

        sage: [elt for elt in finitediff(10, [1, 2, 3, 4])]
        [1, 10, 49, 142, 313, 586, 985, 1534, 2257, 3178]

        sage: [elt for elt in finitediff(10, [1, 2, 3, 4, 5, 6, 7])]
        [1, 28, 769, 7108, 36409, 131836, 380713, 937924, 2054353, 4110364]

        sage: [elt for elt in finitediff(3, [1, 2, 3, 4, 5, 6, 7])]
        [1, 28, 769]
    """
    # degree of M
    n = len(M) - 1
    # Mfd[i] = M(i)
    Mfd = [None]*(n + 1)
    for i in range(min(k, n + 1)):
        res = 0
        aitoj = 1
        ai = a + i
        for j, Mj in enumerate(M):
            # aitoj = (a + i)^j
            res += Mj*aitoj
            aitoj *= ai
        Mfd[i] = res
        yield res
    if k > n + 1:
        # now update Mfd such that
        # M[n] = M(n)
        # M[n-1] = M(n) - M(n-1) = M[n-1, n]
        # ....
        # Mfd[n - l] = Mfd[a - l, a - l + 1, ..., a]
        #        = Mfd[a - l + 1, ..., a] - Mfd[a - l, ..., a - 1]
        # where a = n
        for l in range(0, n + 1):
            for j in range(0, n - l):
                Mfd[j] = Mfd[j + 1] - Mfd[j]

        for i in range(n + 1, k):
            # update Mfd
            # Mfd[0] = Mfd[a - n, a - n + 1, ..., a] is constant
            # and
            # Mfd[a - n, a - n + 1, ..., a, a + 1] = 0
            for l in range(1, n + 1):
                # We have
                # Mfd[l - 1] = M[(a + 1) - (n- l -1), ..., (a + 1)]
                # Mfd[l] = M[a - n -l, ..., a]
                # and
                #
                # M[(a + 1) - (n- l -1), ..., (a + 1)]  =
                #           M[(a + 1) - n -l, ..., a + 1] - M[a - n -l, ..., a]
                # Thus
                # M[(a + 1) - n -l, ..., a + 1] = Mfd[l] + Mfd[l - 1]
                Mfd[l] = Mfd[l] + Mfd[l-1]
            # Mfd[i]
            yield Mfd[n]











def print_bottom_tree(tree, levels=2, spaces=4, print_shift=0):
    """
    This utility function is used to print trees for visualization

    INPUT:

    - ``tree`` -- a list of even length; the 0th entry is ignored.
        The 1st entry is the root, then the children of the nth node are at 2n and 2n+1
    - ``levels`` -- how many levels of the tree to print (starting at the bottom)
    - ``spaces`` -- how many spaces are allocated to each entry along the bottom of the tree.
        Will look best if this is even
    - ``print_shift`` -- used for recursion; how many spaces to add at the beginning of the bottom line.

    EXAMPLES::

        sage: tree = build_tree(list(range(1,8)))
        sage: print_bottom_tree(tree)
          2       12      30      7
        1   2   3   4   5   6
        sage: print_bottom_tree(tree, levels=3)
              24              210
          2       12      30      7
        1   2   3   4   5   6
        sage: print_bottom_tree(tree, levels=4)
                      5040
              24              210
          2       12      30      7
        1   2   3   4   5   6
    """
    if levels > 0:
        n = len(tree) // 2
        shift = base_shift(n)
        print_bottom_tree(
            tree[:-shift], levels - 1, 2 * spaces, print_shift=print_shift + spaces // 2
        )
        print(
            " " * print_shift + "".join(str(elt).ljust(spaces) for elt in tree[-shift:])
        )


def product_layer(layer):
    """
    INPUT:

    - ``layer`` -- a list of even length

    OUTPUT:

    A list of half the length whose terms are the products of the consecutive terms of the input

    EXAMPLES::

        sage: layer = list(range(1,15))
        sage: product_layer(layer)
        [2, 12, 30, 56, 90, 132, 182]
    """
    return [
        layer[j] * layer[k]
        for (j, k) in zip(range(0, len(layer), 2), range(1, len(layer), 2))
    ]


def padic_gauss_sum(a, p, f, prec=20, factored=False, algorithm='pari', parent=None):
    # Copied from Sage
    from sage.rings.padics.factory import Zp
    from sage.rings.all import PolynomialRing

    q = p**f
    a = a % (q-1)
    if parent is None:
        R = Zp(p, prec)
    else:
        R = parent
    out = -R.one()
    if a != 0:
        t = R(1/(q-1))
        for i in range(f):
            out *= (a*t).gamma(algorithm)
            a = (a*p) % (q-1)
    s = sum(a.digits(base=p))
    if factored:
        return(s, out)
    X = PolynomialRing(R, name='X').gen()
    pi = R.ext(X**(p - 1) + p, names='pi').gen()
    out *= pi**s
    return out

class AmortizingHypergeometricData(HypergeometricData):
    """
    Class for computing Frobenius traces of a hypergeometric motive for all primes up to given bound `N`.

    INPUT:

    - ``alpha`` -- a list of rational numbers
    - ``beta`` -- a list of rational numbers
    - ``N`` -- a positive integer
    """
    def __init__(self, N, cyclotomic=None, alpha_beta=None, gamma_list=None):
        HypergeometricData.__init__(self, cyclotomic, alpha_beta, gamma_list)
        self.N = N
        alpha, beta = self.alpha(), self.beta()
        self.breaks = breaks = sorted(set(alpha + beta + [ZZ(0), ZZ(1)]))
        self.starts = starts = breaks[:-1]
        self.ends = ends = breaks[1:]
        xi = beta.count(0)
        self.D = (self.weight() + 1- xi) // 2
        self.pshift = pshift = [self.zigzag(gamma) + self.D + xi for gamma in starts]
        assert all(s >= 0 for s in pshift)
        # Now we only care if the pshift is 0 or positive.  In the case it's zero,
        # we get a global sign from the number of zeros in beta
        sign = ZZ(-1) if (self.D + beta.count(0))%2 else ZZ(1)
        self.interval_mults = {gamma: (sign if ps == 0 else ZZ(0)) for (gamma, ps) in zip(starts, pshift)}
        self.break_mults = {end: self.interval_mults[start] for (start, end) in zip(starts, ends)}
        self.break_mults[0] = ZZ(0) if self.D else ZZ(1)
        self.break_mults_p1 = {}
        for brk in self.starts:
            eta_m = self.zigzag(brk) + self.beta().count(brk) - self.alpha().count(brk)
            xi_m = self.beta().count(0) - self.beta().count(brk)
            sign = ZZ(-1) if eta_m%2 else ZZ(1)
            if eta_m + xi_m + self.D == 0:
                self.break_mults_p1[brk] = sign
            elif eta_m + xi_m + self.D > 0:
                self.break_mults_p1[brk] = ZZ(0)
            else:
                # FIXME check that this never occurs
                raise ValueError("Need more than one digit of precision")
        # TODO: skip over intermediate ranges with positive p-shift

    @lazy_attribute
    def _pbound(self):
        betabound = max(b.denominator() for b in self.beta())
        # b bound
        # we just need p to not divide the denominators
        if self.starts == [0]:
            pbound_denominators = 1
        else:
            pbound_denominators = max(sum((elt.denominator().prime_factors() for elt in self.starts), []))
        return max(pbound_denominators, betabound)

    @staticmethod
    def is_tame_prime(t):
        tn = t.numerator()
        td = t.denominator()
        return lambda p: not bool((td % p) and (tn % p) and ((tn - td) % p))

    def tame_primes(self, t):
        s = []
        for m in (t, ~t, t-1):
            for (p, _) in m.numerator().factor():
                s.append(p)
        return set(s)

    def anomalous_primes(self):
        s = []
        for g in set(self._alpha + self._beta):
            d = g.denom()
            for pclass in range(d):
                if d.gcd(pclass) > 1:
                    continue
                c = (d*g*(pclass-1)) % d
                for h in set(self._alpha + self._beta):
                    x = h-g-c/d
                    if h >= g and x != 0:
                        for (p,_) in x.numerator().factor():
                            if p%d == pclass and not p in s:
                                s.append(p)
                    if h <= g and x+1 != 0:
                        for (p,_) in (x+1).numerator().factor():
                            if p%d == pclass and not p in s:
                                s.append(p)
        return set(s)

    @cached_method
    def _prime_range(self, t):
        prime_ranges = defaultdict(lambda: defaultdict(list))
        ds = set([elt.denominator() for elt in self.starts])
        ds.add(1)
#        is_tame = self.is_tame_prime(t)
        s = self.anomalous_primes()
        tame = self.tame_primes(t)
        s = s.union(tame)
        for p in prime_range(self._pbound+1, self.N):
            if p not in s:
#            if not is_tame(p) and not (p in s):
                for d in ds:
                    #assert p not in prime_ranges[d][p % d]
                    prime_ranges[d][p % d].append(p)
        return prime_ranges

    @lazy_attribute
    def _starts_to_rationals(self):
        """
        Return a dictionary
            a/b -> {k -> (l/b, offset)}
        where a/b is a start of an interval and
            floor(a/b*(p - 1)) + offset = l/b mod p,
        for all on p mod b = k and gcd(p, b) = 1
        Note: the offset = 1 or 2
        """
        answer = {}
        # before we only looped over starts
        # now we loop over the breaks
        # FIXME?
        for start in self.breaks:
            a, b = start.numerator(), start.denominator()
            resab = {}
            if b == 1: # start = 0
                resab[0] = (QQ(1), 1)
            for pclass in range(1, b):
                if b.gcd(pclass) == 1:
                    v = (a*(pclass - 1)) % b
                    if v == 0:
                        # u + 1 = (a(p-1) + b)/b
                        # thus
                        # b*(u + 1) = b - a mod p
                        resab[pclass] = ((b-a)/b, 1)
                    elif a + v < b:
                        # u + 1 = (a(p-1) + b - v)/b
                        # thus
                        # b*(u + 1) = (b - a - v) mod p
                        resab[pclass] = ((b-a-v)/b, 1)
                    else: # a + v < 2*b
                        # u + 2 = (a(p-1) + 2*b - v)/b
                        resab[pclass] = ((2*b-a-v)/b, 2)
            answer[start] = resab
        return answer

    @cached_method
    def _numden(self, t, start=0, shift=0, offset=0, verbose=False):
        r"""
        Return f and g, such that
            P_{m+1} = f(k) / g(k) P_m
        where
            P_m = t^m \prod_i (alpha)_m / (beta)_m,
            shift mod p = floor(start*(p-1)) + offset,
            m = floor(start*(p-1)) + k,
            and
            1 <= k < floor(end*(p-1)) - floor(start*(p-1)).


        EXAMPLES::

            sage: H = AmortizingHypergeometricData(100, alpha_beta=([1/6,5/6],[0,0]))
            sage: start, end, p = 0, 1/6, 97
            sage: shift, offset = H._starts_to_rationals[start][p % start.denominator()]
            sage: f, g = H._numden(t=1, shift=shift, offset=offset, start=start)
            sage: f
            36*k^2 + 36*k + 5
            sage: g
            36*k^2 + 72*k + 36

        TESTS::

            sage: for cyca, cycb, start, end, p, t in [
            ....:     ([6], [1, 1], 0, 1/6, 97, 1),
            ....:     ([4, 2, 2], [3, 1, 1], 1/3, 1/2, 97, 1),
            ....:     ([22], [1, 1, 20], 3/20, 5/22, 1087, 1),
            ....:     ([22], [1, 1, 20], 3/20, 5/22, 1087, 1337/507734),
            ....:     ([22], [1, 1, 20], 3/20, 5/22, 1019, 1337/507734)]:
            ....:     H = AmortizingHypergeometricData(p+40, cyclotomic=(cyca, cycb))
            ....:     shift, offset = H._starts_to_rationals[start][p % start.denominator()]
            ....:     f, g = H._numden(t=t, shift=shift, offset=offset, start=start)
            ....:     for k in range(1, floor(end * (p-1)) - floor(start * (p-1))):
            ....:         m = floor(start * (p-1)) + k
            ....:         quoval = GF(p)(t) * H.pochhammer_quotient(p, m+1)/H.pochhammer_quotient(p, m)
            ....:         if GF(p)(f(k)/g(k)) != quoval:
            ....:             print((cyca, cycb), offset, (start, end), (floor(start * (p-1)), floor(end * (p-1))), m, p, t, GF(p)(f(k)/g(k)), quoval)

        """
        RQ = QQ['k']
        RZ = ZZ['k']
        k = RQ.gen() - offset
        # We shift the term corresponding to a or b by 1 because we're taking
        # the fractional part of a negative number when less than start.
        f = prod(a + shift +  k + (1 if a <= start else 0)  for a in self.alpha()) * t.numerator()
        g = prod(b + shift +  k + (1 if b <= start else 0) for b in self.beta()) * t.denominator()
        d = lcm(f.denominator(), g.denominator())

        return RZ(d*f), RZ(d*g)

    def _matrices(self, t, start, shift, offset, verbose=False):
        r"""
        Return lambda function, such that lambda(x) returns
            [M(1), ...., M(x + 1)]
        where
            M(k) = [ g(k)           0    ]
                   [ y * g(k)   f(k) ]
        and
            [S_m, P_{m + 1}] M(k) = g(k) [S_{m+1}, P_{m+2} ]
        where
            pmult = y,
            P_m = t^m \prod_i (alpha)_m / (beta)_m,
            S_m =  y * \sum_{0} ^{m} P_j,
            shift mod p = floor(start*(p-1)) + offset,
            m = floor(start*(p-1)) + k,
            and
            1 <= k < floor(end*(p-1)) - floor(start*(p-1)).
        """
        if verbose:
            print("_matrices(t=%s, start=%s, shift=%s, offset=%s)" % (t, start, shift, offset))
        f, g = self._numden(t=t, start=start, shift=shift, offset=offset)
        pmult = self.interval_mults[start]
        return f, g, lambda end: [matrix(ZZ, 2, 2, [den, 0, pmult*den, num])
                            for (num, den) in zip(finitediff(end, list(f), a=1),
                                                  finitediff(end, list(g), a=1))]

    def fix_break(self, t, brk, p, d, pclass, feq_seed):
        r"""
        EXAMPLES::
            sage: H = AmortizingHypergeometricData(100, cyclotomic=([22], [1, 1, 20]))
            sage: t, brk, p = 2312/231, 0, 101
            sage: M = H.fix_break(t=t, brk=brk, p=p)
            sage: GF(p)(M[1,1]/M[0,0]) == GF(p)(t)*H.pochhammer_quotient(p, 1)
            True

        """
        def multiplier(x):
            return -x if x else -1
        def functional_eqn(alpha, p, m):
            """
            Relates Gamma_p({alpha + (m+1)/(1-p)) and Gamma_p({alpha + m/(1-p)}
            """
            alphap1 = alpha*(p-1)
            tmp = R(alpha + m)
            if alphap1 < m:
                # Gamma_p({alpha + (m+1)/(1-p)) = Gamma_p(alpha + m + 2)
                # Gamma_p({alpha + m/(1-p)) = Gamma_p(alpha + m + 1)
                return multiplier(tmp+1)
            elif m + 1 <= alphap1:
                # Gamma_p({alpha + (m+1)/(1-p)) = Gamma_p(alpha + m + 1)
                # Gamma_p({alpha + m/(1-p)) = Gamma_p(alpha + m)
                return multiplier(tmp)
            else: # m <= alpha(p - 1) < m + 1
                # Gamma_p({alpha + (m+1)/(1-p)) = Gamma_p(alpha + m + 2)
                # Gamma_p({alpha + m/(1-p)) = Gamma_p(alpha + m)
                return multiplier(tmp) * multiplier(tmp+1)

        if feq_seed.numer()%p and feq_seed.denom()%p:
            return None
        print(p)
        #print(p, [(a, functional_eqn(a, p, m)) for a in self.alpha() + self.beta()])
        R = GF(p)
        m = floor(brk * (p-1))
        feq = R(t)*prod(functional_eqn(a, p, m) for a in self.alpha()) / prod(functional_eqn(b, p, m) for b in self.beta())
        feq = feq.lift()

#        d = brk.denominator()
#        pclass = p % d
        if pclass == 1:
            pmult = self.break_mults_p1[brk]
        else:
            pmult = self.break_mults[brk]
        A = matrix(QQ, 2, 2, [1, 0, pmult, feq])
        B = matrix(QQ, 2, 2, [1, 0, pmult, t*feq_seed])
        A = A*~B
        A *= (t*feq_seed).numer()
        return A.change_ring(ZZ)


    # We don't use this fcn at the moment
    def _my_zigzag(self, m, p):
        s = 0
        for alpha in self.alpha():
            s += frac(alpha + m/(1-p)) - frac(alpha)
        for beta in self.beta():
            s -= frac(beta + m/(1-p)) - frac(beta)
        return s

    def naive_padic_H_value(self, p, t, verbose=False):
        R = GF(p)
        t = R(t)
        interval_sums = {}
        denominator = self.pochhammer_numerator_alphas_betas(p, 0)
        interval_sums[0] = 0 if self.D else 1

        for i, v in enumerate(self.pshift):
            start = self.starts[i]
            end = self.ends[i]

            # deals with the start point
            m = start * (p - 1)
            if start > 0 and m.is_integer():
                m = ZZ(m)
                # FIXME do the math to assert that is true
                assert self.pshift[i-1] - self.beta().count(start) >= 0, "i = %s start = %s self.pshift[i-i] = %s, self.beta().count(start) = %s" % (i, start, self.pshift[i-1], self.beta().count(start))
                # eta at the end of the previous interval
                eta_m = self.zigzag(start) + self.beta().count(start) - self.alpha().count(start)
                xi_m = self.beta().count(0) - self.beta().count(start)
                #print("etaxi", start, end, m, eta_m, xi_m)
                if eta_m + xi_m + self.D == 0:
                    sign = -1 if eta_m%2 else 1
                    #print(start, sign)
                    interval_sums[start] = sign*self.pochhammer_numerator_alphas_betas(p, m, verbose) * t**m / denominator

            # deal with middle of the interval and the end point
            if v == 0:
                sign = -1 if self.zigzag(start)%2 else 1
                #print((start, end), sign)
                interval_sums[(start, end)] = self.naive_padic_H_value_interval_numerator(p, t, start, end, sign*denominator, verbose)

                # deals with the end point
                m = end*(p - 1)
                # if m.is_integer() then it is handled as a start
                if end != 1 and not m.is_integer():
                    m = floor(m)
                    interval_sums[end] = sign*self.pochhammer_numerator_alphas_betas(p, m, verbose) * t**m / denominator

        if verbose:
            print(interval_sums)
        return sum(interval_sums.values())



    @staticmethod
    def pochhammer_numerator(alpha, p, m, verbose=False):
        rational = frac(alpha + m/(1 - p))
        R = GF(p)
        k = R(rational).lift()
        if k == 0:
            if verbose:
                print("issue alpha=%s m=%s" % (alpha, m))
            return R(1)
        else:
            fact = R(factorial(k - 1))
            res = (p - fact) if k%2 else fact
            return res

    def pochhammer_numerator_alphas_betas(self, p, m, verbose=False):
        alphaprod = prod(self.pochhammer_numerator(alpha, p, m, verbose) for alpha in self.alpha())
        betaprod = prod(self.pochhammer_numerator(beta, p, m, verbose) for beta in self.beta())
        return alphaprod / betaprod

    def pochhammer_quotient(self, p, m, verbose=False):
        return self.pochhammer_numerator_alphas_betas(p, m, verbose)/self.pochhammer_numerator_alphas_betas(p, 0, verbose)

    def naive_padic_H_value_interval_numerator(self, p, t, start, end, denominator, verbose=False):
        r"""
        Return
            \sum_{m = floor(start(p-1)) + 1} ^{floor(end(p-1))-1} t^m \prod_i (alpha_i)_m ^* / (beta_i)_m ^* mod p
        """
        t = GF(p)(t)
        real_start = floor(start*(p - 1)) + 1
        real_end = floor(end*(p - 1))
        total = 0
        for m in range(real_start, real_end):
            term = self.pochhammer_numerator_alphas_betas(p, m, verbose) * t**m / denominator
            total += term
        return total

    def amortized_padic_H_values_interval(self, ans, t, start, end, pclass, fixbreak, testp=None, use_c=False):
        r"""
        Return a dictionary
            p -> M[p]

        (0, P_m0)*A[p] = A[p][0,0] (S, P_m1)
        where
        P_m = t^m \prod_i (alpha_i)_m ^* / (beta_i)_m ^* mod p,
        m0 = floor(start(p-1)) + 1,
        m1 = floor(end(p-1)),
        S = \sum_{m = m0} ^{m1 - 1} P_m


        EXAMPLES::

            sage: for cyca, cycb, start, end, p, t in [
            ....:     ([6], [1, 1], 0, 1/6, 97, 1),
            ....:     ([4, 2, 2], [3, 1, 1], 1/3, 1/2, 97, 1),
            ....:     ([22], [1, 1, 20], 3/20, 5/22, 1087, 1),
            ....:     ([22], [1, 1, 20], 3/20, 5/22, 1087, 1337/507734),
            ....:     ([22], [1, 1, 20], 3/20, 5/22, 1019, 1337/507734)]:
            ....:     H = AmortizingHypergeometricData(p+40, cyclotomic=(cyca, cycb))
            ....:     pclass = p % start.denominator()
            ....:     shift, offset = H._starts_to_rationals[start][pclass]
            ....:     amortized = H.amortized_padic_H_values_interval(t=t, start=start, end=end, pclass=pclass)
            ....:     t = GF(p)(t)
            ....:     naive_sum = 0
            ....:     for k in range(floor(start*(p-1))+1, floor(end * (p-1))):
            ....:         naive_sum += t**k * H.pochhammer_quotient(p, k)
            ....:     naive_res = vector(GF(p), (naive_sum, t**floor(end * (p-1)) * H.pochhammer_quotient(p, floor(end * (p-1) ))))
            ....:     M = matrix(GF(p), amortized[p])
            ....:     res = (vector(GF(p), [0,t**(floor(start*(p-1))+1) * H.pochhammer_quotient(p, floor(start*(p-1))+1 )])*M/M[0,0])
            ....:     if naive_res != res:
            ....:         print(cyca, cycb, start, end, p, t, naive_res, res)

        """
        d = start.denominator()
        shift, offset = self._starts_to_rationals[start][pclass]
        def mbound(p):
            # FIXME
            # in practice we are getting
            # prod up mbound - 1
            # there is something wrong with the Tree
            # once we fix that, we should fix the bound here
            return max((end * (p-1)).floor() - (start * (p-1)).floor(),1)

        f, g, mats = self._matrices(t=t, start=start, shift=shift, offset=offset)

        if use_c:
            k = f.parent().gen()
            y = self.interval_mults[start]
            M = matrix([[g, 0], [y*g, f]])
            indices = self._prime_range(t)[d][pclass]
            remainder_forest(M,
                             lambda p: p, #lambda p: mbound_c(p,start,end),
                             mbound_dict_c(indices, start, end),
                             kbase=1,
                             indices=indices,
                             V=fixbreak,
                             ans=ans)
        else:
            forest = AccRemForest(
                self.N,
                cut_functions={None: mbound},
                bottom_generator=mats,
                prec=1,
                primes=self._prime_range(t)[d][pclass],
            )
            bottom = forest.tree_bottom()
            # Now we have a formula for
            # (0, P_m0)*A[p] =  A[p][0,0] (\sum_{m = m0} ^{m1 - 1} P_m, P_m1)
            # with
            # m0 = floor(start * (p-1)) + 1
            # m1 = floor(end * (p-1))
            if testp in bottom:
                print("amortized_padic_H_values_interval(t=%s, start=%s, end=%s, pclass=%s)" % (t, start, end, pclass))
                p = testp
                R = GF(p)
                if bottom[testp] != 1:
                    M =  bottom[testp].change_ring(R)
                    # FIXME why the -1?  Probably because partial_factorial doesn't include right endpoint
                    assert M == prod(elt.change_ring(GF(R)) for elt in mats(floor(end * (p-1)) - floor(start * (p-1)) - 1))

                    t = R(t)
                    naive_sum = 0
                    pmult = self.interval_mults[start]
                    for k in range(floor(start*(p-1))+1, floor(end * (p-1))):
                        naive_sum += t**k * self.pochhammer_quotient(p, k)
                    naive_sum *= pmult
                    naive_res = vector(R, (naive_sum, t**floor(end * (p-1)) * self.pochhammer_quotient(p, floor(end * (p-1) ))))

                    res = vector(R, [0,t**(floor(start*(p-1))+1) * self.pochhammer_quotient(p, floor(start*(p-1))+1 )])*M/M[0,0]
                    assert naive_res == res, "%s != %s, M = %s" % (naive_res, res, M)
            # set ans
            for k, M in bottom.items():
                ans[k] = ans[k]*fixbreak*M




    def amortized_padic_H_values(self, t, testp=None, verbose=False, use_c=False):
        """
        INPUT:

        - `t` -- a rational number

        OUTPUT:

        - a dictionary with inputs `p` and outputs the corresponding p-adic H value at `t`.

        TESTS::

            sage: for cyca, cycb, t in [
            ...:    ([6], [1, 1], 331),
            ...:    ([4, 2, 2], [3, 1, 1],  3678),
            ...:    ([22], [1, 1, 20], 1337/507734),
            ...:    ([5],[1,1,1,1], 2313),
            ...:    ([12],[2,2,1,1], 313)
            ...:]:
            ...:    H = AmortizingHypergeometricData(1000, cyclotomic=(cyca, cycb))
            ...:    for p, v in H.amortized_padic_H_values(t).items():
            ...:        if v != H.naive_padic_H_value(t=t, p=p, verbose=False):
            ...:            print(p, cyca, cycb, t)
        """
        ## TODO: skip over intermediate ranges with positive p-shift
        #pshift = self.pshift
        #for last_zero, s in reversed(list(enumerate(pshift))):
        #    if s == 0:
        #        break
        #breaks = self.breaks[:last_zero+2] # also include the endpoint of the last interval
        #pshift = pshift[:last_zero+1]
        #starts = breaks[:-1]
        #ends = breaks[1:]
        # TODO: fix global sign from (-p)^eta
#        forests = {}
        tmp = identity_matrix(2)
        vectors = {p: tmp for p in self._prime_range(t)[1][0]}
#        def update(p, A):
#            # If the interval was empty we get A=1
#            if not (isinstance(A, Integer) and A == 1):
#                vectors[p][0] *= A
#                vectors[p][1] *= A[0,0]
#                vectors[p] %= p
        def multiplier(x):
            return -x if x else -1
        def functional_eqn(a, g, c, d):
            return (multiplier(a-g-c/d) if a >= g else 1) * (multiplier(a-g-c/d+1) if a <= g else 1)
#        feq_seed = prod(a if a else -1 for a in self._alpha) / prod(b if b else -1 for b in self._beta)
#        for p in self._prime_range(t)[1][0]:
#            R = vectors[p].base_ring()
#            update(p, self.fix_break(t, ZZ(0), p, R, feq_seed))
#            if p == testp:
#                P_start = R(t)**1 * H.pochhammer_quotient(p, 1)
#                assert vectors[p][1] == P_start, "brk = 0, %s != %s" % (vectors[p][1], P_start)
        for start, end in zip(self.starts, self.ends):
            d = start.denominator()
            for pclass in range(d):
                if d.gcd(pclass) != 1:
                    continue
                c = (d*start*(pclass-1)) % d
                feq_seed = t*prod(functional_eqn(a,start,c,d) for a in self._alpha) / prod(functional_eqn(b,start,c,d) for b in self._beta)
                feq_seed_num = feq_seed.numer()
                feq_seed_den = feq_seed.denom()
                if pclass == 1:
                    pmult = self.break_mults_p1[start]
                else:
                    pmult = self.break_mults[start]
                fixbreak = matrix(ZZ, 2, 2, [feq_seed_den, 0, feq_seed_den*pmult, feq_seed_num])
                # this updates vectors
                self.amortized_padic_H_values_interval(vectors,
                                                       t,
                                                       start,
                                                       end,
                                                       pclass,
                                                       fixbreak,
                                                       testp=testp,
                                                       use_c=use_c,
                                                       )
        return {p: (vectors[p][1,0]/vectors[p][0,0]) %p for p in vectors}


    def padic_H_values(self, t):
        res = self.amortized_padic_H_values(t)
        is_tame = self.is_tame_prime(t)
        for p in prime_range(self._pbound + 1):
            if not is_tame(p):
                res[p] = GF(p)(self.padic_H_value(p=p, f=1, t=t))
        return res


    def test_padic_H_values(self, ts, testp=None):
        print("alpha,beta = %s,%s" % (self.alpha(), self.beta()))
        for t in ts:
            am = self.amortized_padic_H_values(t, testp=testp)
            for p, val in am.items():
                assert(self.padic_H_value(t=t, p=p, f=1) == val)

class EAmortizingHypergeometricData(AmortizingHypergeometricData):
    """
    Compute traces modulo p^e rather than p.
    """
    def __init__(self, N, e, cyclotomic=None, alpha_beta=None, gamma_list=None):
        HypergeometricData.__init__(self, cyclotomic, alpha_beta, gamma_list)
        self.N = N
        self.e = e

    @lazy_attribute
    def R0(self):
        return PolynomialRing(ZZ, "y," + ",".join([f"w{i}" for i in range(1, self.e)]))

    @lazy_attribute
    def y(self):
        return self.R0.gens()[0]

    @lazy_attribute
    def w(self):
        """
        sage: H(3).W
        w2*x^2 + w1*x + 1
        """
        return dict(zip(range(1,self.e), self.R0.gens()[1:]))


    def to_matrix(self, poly):
        """
        sage: foo = H(e=3)
        sage: foo.to_matrix(foo.W)
        [ 1 w1 w2]
        [ 0  1 w1]
        [ 0  0  1]
        """
        return Matrix([[poly[i-j] for i in range(self.e)] for j in range(self.e)])

    @lazy_attribute
    def Phi(self):
        r"""
        return a matrix M that represents the linear transformation:
            h(x) mod x^e -> h((a + 1)x/(a + x)) mod x^e
        explicitly, if
            h = a_0 + a_1*x + ... + a_{e-1}*x^(e-1)
        then
            vector([a_0, ..., a_{e-1}]) * M
        represents
            h((a + 1)x/(a + x)) mod x^e
        TEST:: (fix test)
        sage: foo = H(e=3)
        sage: x = foo.x
        sage: a = 2
        sage: F = foo.W
        sage: rhs = a^(foo.e-1)*F((a + 1)*x/(a + x))
        sage: lhs = foo.R((foo.to_matrix(F)*foo.Phi(a)).row(0).list())
        sage: (rhs.denominator()*lhs - rhs.numerator() ) % x^foo.e
        0
        """

        S0 = PolynomialRing(ZZ, 1, 'a')
        a = S0.gen()
        S = PolynomialRing(S0, self.e, 'h')
        R = PowerSeriesRing(S.fraction_field(), 'x', default_prec=self.e)
        x = R.gen()
        # f = R(list(S.gens()))
        from_monomial = {tuple(1 if i == j else 0 for j in range(self.e)) : i for i in range(self.e)}
        x = R.gen()
        h = R(list(S.gens()))
        pol = (a**(self.e - 1)*h((a + 1)*x/(a + x) + O(x**self.e))).padded_list(self.e)
        res = []
        for elt in pol[:self.e]:
            assert elt.denominator() == 1
            elt = elt.numerator()
            reselt = [0]*self.e
            for m, v in elt.dict().items():
                reselt[from_monomial[tuple(m)]] = v
            res.append(reselt)
        return Matrix(S0, res).transpose()

    def recursion_matrix(self, z, kappa):
        """
        kappa = a + b x = [a, b]
        [eta, theta]
        [0  , phi]
        """
        # the return matrix will have coefficients in S
        S = PolynomialRing(self.R0, 'ell')
        ell = S.gen()
        R = PowerSeriesRing(S, 'x', default_prec=self.e)
        x = R.gen()


        # dealing with eta
        # f_ell is not necessarily integral
        kappa = kappa[0] + kappa[1]*x
        f_ell = kappa[0] + kappa[1] + ell
        Phi_f_ell = self.Phi(f_ell)
        gamma_prod = lambda gammas: prod(g + kappa(x) + ell + (kappa(x) + ell + 1)*x/(1-x) for g in gammas)
        beta_prod_den = prod(b + kappa(0) + ell for b in self.beta())
        alphabeta_prod = (gamma_prod(self.alpha())/(gamma_prod(self.beta())/beta_prod_den))
        d = LCM([elt.denominator().numerator() for elt in alphabeta_prod.list()])*LCM([elt.numerator().denominator() for elt in alphabeta_prod.list()])
        eta = Phi_f_ell * self.to_matrix((self.y + z) * d * alphabeta_prod)

        phi = self.to_matrix(R(f_ell**(self.e - 1)*d*beta_prod_den))


        w = 1 + sum(x**i * wi for i, wi in self.w.items())
        theta = Phi_f_ell * self.to_matrix(w( (ell + kappa(x))*x/(1-x) ))

        return block_matrix(S,
                 [[eta, theta],
                  [zero_matrix(self.e), phi]])



def eta(xvec, m, p, f=1):
    q = p**f
    return sum(frac(p**v * (x + m / (1-q))) - frac(p**v*x) for x in xvec for v in range(f))

def eta_breaks(alpha, beta, p, f=1, use_xi=True):
    q = p**f
    vals = []
    xi = beta.count(0)
    domains = [(None, 0)]
    oldval = eta(alpha, 1, p, f) - eta(beta, 1, p, f)
    for m in range(2, q-1):
        val = eta(alpha, m, p, f) - eta(beta, m, p, f)
        if val != oldval:
            vals.append(oldval)
            domains.append((domains[-1][1] + 1, m-1))
        oldval = val
    vals.append(oldval)
    domains.append((domains[-1][1] + 1, q-2))
    for domain, val in zip(domains[1:], vals):
        a,b = domain
        print("[%s,%s] -> %s" % (a, b, val+xi))
    return all(val >= -xi for val in vals)

def breaks_sample(d, weight=None, p=ZZ(101), f=1):
    ok_count = 0
    bad_count = 0
    for H in enumerate_hypergeometric_data(d, weight):
        A, B = H.alpha(), H.beta()
        print(A, B)
        ok1 = eta_breaks(A, B, p, f)
        H = H.twist()
        A, B = H.alpha(), H.beta()
        print(A, B)
        ok2 = eta_breaks(A, B, p, f)
        if ok1 or ok2:
            ok_count += 1
        else:
            bad_count += 1
    return ok_count, bad_count

def test_padic_H_values(d, weight=1, N=ZZ(100), ts=[ZZ(3)/17, ZZ(91)/55, ZZ(1)/1234567]):
    for H in enumerate_hypergeometric_data(d, weight):
        try:
            H = AmortizingHypergeometricData(N, alpha_beta=(H.alpha(), H.beta()))
        except NotImplementedError:
            continue
        H.test_padic_H_values(ts, testp=previous_prime(N))

def compare(log2N, t, use_c=False, vssage=True, vsmagma=True,**kwds):
    r"""
        e.g: compare(15, 1337, vssage=False, cyclotomic=([4,4,2,2], [3,3,3]))
    """
    import resource
    def get_utime():
        return resource.getrusage(resource.RUSAGE_SELF).ru_utime

    for i in range(10,log2N + 1):
        print("2^%s" % i)
        H = AmortizingHypergeometricData(2**i, **kwds)
        start = get_utime()
        foo = H.amortized_padic_H_values(t, use_c=use_c)
        print("Amortized: %.2f s" % (get_utime()-start))
        #print_maxrss()
        if vssage:
            start = get_utime()
            bar = {p: H.padic_H_value(p=p,f=1,t=t,prec=1)%p for p in foo}
            print("Sage:      %.2f s" % (get_utime()-start))
            H._gauss_table = {}
            H.padic_H_value.clear_cache()
            #print_maxrss()
            assert foo == bar
        if vsmagma:
            magma.quit()
            magma.eval('ps := %s;' % sorted(foo))
            magma.eval('H := HypergeometricData(%s, %s);' % H.alpha_beta())
            z = 1/t
            start_magma = magma.Cputime()
            magma.eval('foo := [HypergeometricTrace(H, %s, p) : p in ps];' % z)
            print("Magma:     %.2f s" % (magma.Cputime(start_magma)))
            bar = dict((p, k%p) for p,k in zip(sorted(foo), eval(magma.eval('foo;'))))
            assert foo == bar
        print("")

