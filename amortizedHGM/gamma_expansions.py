# Amortized computation of power series expansions of p-adic Gamma at rational arguments.

from sage.functions.other import binomial, factorial
from sage.arith.srange import srange
from sage.arith.misc import gcd
from sage.rings.fast_arith import prime_range
from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ
from sage.misc.lazy_attribute import lazy_attribute
from sage.misc.persist import loads, dumps
from sage.structure.unique_representation import UniqueRepresentation
from sage.matrix.constructor import matrix
from sage.modules.free_module_element import vector

from pyrforest import batch_harmonic, batch_factorial
from .hgm_misc import (
    moddiv_int,
    eval_poly_as_gen,
    truncated_log_mod,
    gamma_translate
)

class pAdicLogGammaCache(UniqueRepresentation):
    """
    This object caches logarithmic expansions of p-adic Gamma functions around rational numbers
    at a given precision `e` for `p > e`.  Values are cached in an amortized way,
    with all p up to a specified `N` computed simultaneously.  If the neccessary `N` increases,
    then they will be recomputed.

    The main interface is through the ``expansion`` method.

    INPUT:

    - ``e`` -- a positive integer, the precision

    EXAMPLES::

        sage: cache = pAdicLogGammaCache(2)
        sage: cache.expansion((3,4,97))
        (-7780, 1, 50*x + 3492)
    """
    def __init__(self, e):
        self.e = e
        self.N = e + 1
        self.cache = {}

    def increase_N(self, N):
        """
        Increase the bound on `p`.

        When computing for many `p`, it is helpful to call this in advance
        since otherwise `N` will be iteratively doubled.

        EXAMPLES::

            sage: cache = pAdicLogGammaCache(2)
            sage: cache.increase_N(100)
            sage: cache.expansion((3,4,97))
            (-7780, 1, 50*x + 3492)
        """
        if N > self.N:
            Nold = self.N
            self.N = N
            if self.e > 1:
                harmonics, den, mat = self._expansion0_prep()
                E0 = self._expansion_at_0
                for p in prime_range(Nold, N):
                    E0[p] = self._expansion0(p, harmonics, den, mat)

    def clear_cache(self):
        """
        This function deletes all saved values in order to free up memory.

        EXAMPLES::

            sage: cache = pAdicLogGammaCache(2)
            sage: len(cache.cache)
            0
            sage: val = cache.expansion((3,4,97))
            sage: len(cache.cache)
            48
            sage: cache.clear_cache()
            sage: len(cache.cache)
            0
        """
        self.N = self.e + 1
        self.cache = {}

    def save(self, filename):
        """
        Saves the cache to a file which can be loaded later, overwriting
        the contents of the file.

        EXAMPLES::

            sage: filename = tmp_filename()
            sage: cache = pAdicLogGammaCache(2)
            sage: cache.clear_cache()
            sage: val = cache.expansion((3,4,97))
            sage: len(cache.cache)
            48
            sage: cache.save(filename)
            sage: cache.clear_cache()
            sage: len(cache.cache)
            0
            sage: cache.load(filename)
            sage: len(cache.cache)
            48
            sage: os.remove(filename)
        """
        with open(filename, "wb") as fobj:
            fobj.write(dumps((self.e, self.N, self.cache), compress=True))

    def load(self, filename):
        """
        Load the cache from a previously saved file.
        This overwrites the current cache.

        Note that the value e1 for the saved file can be larger than this e,
        but in this case any p with e < p <= e1 will be missing.

        EXAMPLES::

            sage: filename = tmp_filename()
            sage: cache = pAdicLogGammaCache(3)
            sage: cache.clear_cache()
            sage: _ = cache.expansion((3,4,97))
            sage: cache.save(filename)
            sage: cache2 = pAdicLogGammaCache(2)
            sage: _ = cache2.expansion((3,4,97))
            sage: c2 = cache2.cache
            sage: cache2.load(filename)
            sage: set(c2).difference(set(cache2.cache))
            {(1, 4, 3), (3, 4, 3)}
            sage: all(c2[a,b,p][0] % p^2 == cache2.cache[a,b,p][0] and c2[a,b,p][1] == cache2.cache[a,b,p][1] and c2[a,b,p][2].map_coefficients(lambda u: (u % p^2)) == cache2.cache[a,b,p][2] for (a,b,p) in cache2.cache)
            True
            sage: os.remove(filename)
        """
        with open(filename, "rb") as fobj:
            e, N, cache = loads(fobj.read(), compress=True)
        if e < self.e:
            raise ValueError("Cannot load from file with lower precision")
        if e > self.e:
            e = self.e
            for (a, b, p), (c, i, f) in cache.items():
                pe = p**e
                c = c % pe
                f = f.map_coefficients(lambda u: (u % pe))
                cache[a,b,p] = (c, i, f)
        self.N = N
        self.cache = cache

    def expansion(self, abp):
        """
        INPUT:

        - ``abp`` -- a triple (a, b, p), where p > e is prime, 0 <= a < b and gcd(a,b) = 1.

        OUTPUT:

        - c -- an integer
        - i -- either 1 or -1
        - f -- a polynomial in x

        Then the power series expansion of Gamma_p(x) around a/b is c^i exp(f) modulo (p,x)^e.

        EXAMPLES::

            sage: e = 5
            sage: cache = pAdicLogGammaCache(e)
            sage: c, i, f = cache.expansion((5,7,83)); (c, i, f)
            (1378756068, -1, -38*x^4 + 5061*x^3 - 107687*x^2 + 24453648*x - 2520179713)
            sage: Zp(83)(5/7 + 3*83, e).gamma()
            46 + 72*83 + 14*83^2 + 71*83^3 + 30*83^4 + O(83^5)
            sage: c^i * Zp(83)(f(3*83), e).exp()
            46 + 72*83 + 14*83^2 + 71*83^3 + 30*83^4 + O(83^5)

        TESTS::

            sage: all(Zp(p)(a/b + 3*p, e).gamma() == c^i * Zp(p)(f(3*p), e).exp() for ((a,b,p),(c,i,f)) in cache.cache.items())
            True
        """
        try:
            return self.cache[abp]
        except KeyError:
            a, b, p = abp
            if p <= self.e:
                raise ValueError(f"Cache does not support primes smaller than {self.e+1}")
            if p >= self.N:
                N = max(p+1, 2*self.N)
                self.increase_N(N)
            self._set_expansion_at_offset(b)
            return self.cache[abp]

    def _expansion0_prep(self):
        """
        Creates the amortized inputs for the ``_expansion0`` method.

        OUTPUT:

        - ``harmonics`` -- a dictionary, indexed by `j` from 1 to ``max(e-2,1)``,
          with values the truncated harmonic sums output by the ``batch_harmonic`` method
        - ``den`` -- the factorial of e-1
        - ``mat`` -- a lower triangular (e-1)x(e-1) matrix of binomial coefficients,
          with (i,j) entry equal to (e-1)! times the entry of the matrix inverse of binomial(i+1, j)

        EXAMPLES::

            sage: cache = pAdicLogGammaCache(5)
            sage: cache.clear_cache()
            sage: cache.increase_N(20)
            sage: harmonics, den, mat = cache._expansion0_prep()
            sage: set(harmonics)
            {1, 2, 3}
            sage: set(harmonics[1])
            {2, 3, 5, 7, 11, 13, 17, 19}
            sage: harmonics[1][11]
            [160325  85678]
            sage: sum(k^-1 for k in srange(1, 11)) % 11^5
            125840
            sage: 160325/85678 % 11^5
            125840
            sage: harmonics[2][11]
            [1320  463]
            sage: sum(k^-2 for k in srange(1, 11)) % 11^3
            1078
            sage: 1320/463 % 11^3
            1078

            sage: den
            24
            sage: mat
            [ 24   0   0   0]
            [-12  12   0   0]
            [  4 -12   8   0]
            [  0   6 -12   6]
        """
        n, e = self.N, self.e
        harmonics = {j: batch_harmonic(n, e-j if j>1 else e, QQ(1), j, proj=True) for j in range(1,max(e-1,2))}
        mat0 = matrix(ZZ, [[binomial(i+1, j) if i>=j else 0 for j in range(e-1)] for i in range(e-1)])
        den = factorial(ZZ(e-1))
        mat = (~mat0*den).change_ring(ZZ)
        return harmonics, den, mat

    def _expansion0(self, p, harmonics, den, mat):
        """
        A helper function for ``_expansion_at_0`` that computes the expansion of Gamma_p(x) at 0
        without caching.

        EXAMPLES::

            sage: cache = pAdicLogGammaCache(5)
            sage: cache.clear_cache()
            sage: cache.increase_N(20)
            sage: harmonics, den, mat = cache._expansion0_prep()
            sage: cache._expansion0(17, harmonics, den, mat)
            [0, 72500, 0, 230, 0]
            sage: Zp(17)(3*17,5).gamma()
            1 + 2*17 + 12*17^2 + 2*17^3 + O(17^4)
            sage: Zp(17)(72500*(3*17) + 230*(3*17)^3, 4).exp()
            1 + 2*17 + 12*17^2 + 2*17^3 + O(17^4)
        """
        e = self.e
        pe = p**e
        logfac = truncated_log_mod(-harmonics[1][p][0,1], e, pe) # = log -(p-1)!
        tmp = vector([logfac] + [moddiv_int(-(-p)**j*harmonics[j][p][0,0], j*harmonics[j][p][0,1], pe) for j in range(1,e-1)])
        tmp *= mat
        return [moddiv_int(tmp[i], den, pe).divide_knowing_divisible_by(p**(i+1)) for i in range(e-2,-1,-1)] + [0]

    @lazy_attribute
    def _expansion_at_0(self):
        r"""
        Amortized computation of power series expansions of log of `p`-adic Gamma at 0.
        We exclude primes \leq e.

        OUTPUT:

        A dictionary, indexed by p between e+1 and N, with the value at p a list of integers
        giving the coefficients of the power series expansion of Gamma_p(x)

        EXAMPLES::

            sage: cache = pAdicLogGammaCache(5)
            sage: cache.clear_cache()
            sage: cache.increase_N(20)
            sage: cache._expansion_at_0[17]
            [0, 72500, 0, 230, 0]
            sage: Zp(17)(3*17,5).gamma()
            1 + 2*17 + 12*17^2 + 2*17^3 + O(17^4)
            sage: Zp(17)(72500*(3*17) + 230*(3*17)^3, 4).exp()
            1 + 2*17 + 12*17^2 + 2*17^3 + O(17^4)
        """
        harmonics, den, mat = self._expansion0_prep()
        return {p: self._expansion0(p, harmonics, den, mat) for p in prime_range(self.e+1, self.N)}

    def _set_expansion_at_offset(self, d, normalized=False):
        """
        Amortized computation of power series expansions of log `p`-adic Gamma around
        all rational numbers with denominator `d` between 0 and 1,
        for primes p up to the current bound `N`.

        INPUT:

        - `d` -- a positive integer, the denominator
        - ``normalized`` -- boolean, whether to omit constant terms for efficiency

        EXAMPLES::

            sage: cache = pAdicLogGammaCache(3)
            sage: cache.increase_N(20)
            sage: cache._set_expansion_at_offset(3)
            sage: cache.cache[2,3,7]
            (-2, 1, 2*x^2 + 14*x + 147)
        """
        n, e = self.N, self.e
        one, minusone = ZZ(1), ZZ(-1)
        if e == 1:
            if d == 1:
                for p in prime_range(3, n):
                    self.cache[0, 1, p] = (one, 1, None)
                    self.cache[1, 1, p] = (minusone, 1, None)
            else:
                for b in srange(1, d//2+1):
                    if gcd(b, d) == 1:
                        fac = batch_factorial(n, 1, b/d)
                        for p, f in fac.items(): # inner loop
                            if p<=d and not d%p:
                                continue
                            sgn, i = divmod(-b*p, d) # computes both quotient and remainder
                            self.cache[i, d, p] = (-f if sgn%2 else f, 1, None)
                            self.cache[d-i, d, p] = (f, -1, None)
        else:
            zero_exp = self._expansion_at_0
            R = ZZ['x']
            x = R.gen()
            if d == 1:
                for p, s in zero_exp.items():
                    s = eval_poly_as_gen(s, x)
                    self.cache[0, 1, p] = (one, 1, s)
                    self.cache[1, 1, p] = (minusone, 1, s)
            else:
                Z1 = ZZ(1)
                for b in srange(1, d//2+1):
                    if gcd(b, d) == 1:
                        harmonics = {j: batch_harmonic(n, e-j if (j>1 or normalized) else e, b/d, j, proj=True) for j in range(1, e)}
                        for p, s in zero_exp.items(): #inner loop
                            if p<=d and not d%p:
                                continue

                            # Combine the expansion at 0 with the contribution from harmonic sums,
                            # then recenter the log expansion.
                            l = s[::]
                            gamma_translate(l, p, harmonics, e, b, d, normalized)

                            # If not normalized, extract the constant term.
                            c0 = Z1 if normalized else harmonics[1][p][0,1]

                            # Return the computed expansion.
                            sgn, i = divmod(-b*p, d) # computes both quotient and remainder
                            self.cache[i, d, p] = (-c0 if sgn%2 else c0, 1, eval_poly_as_gen(l, x))

                            # Exploit the Legendre relation for Gamma_p to return another expansion for free.
                            self.cache[d-i, d, p] = (c0, -1, -eval_poly_as_gen(l, -x))
