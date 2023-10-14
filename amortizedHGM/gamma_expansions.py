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

from pyrforest import batch_harmonic, batch_factorial
from .hgm_misc import (
    expansion_from_cache,
    gamma_expansion_at_0,
    gamma_translate,
    moddiv_int,
    powers_list,
    truncated_log_mod,
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

        sage: from amortizedHGM.gamma_expansions import pAdicLogGammaCache
        sage: cache = pAdicLogGammaCache(2)
        sage: cache.expansion((3,4,97))
        (-7780, 1, [50, 3492])
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

            sage: from amortizedHGM.gamma_expansions import pAdicLogGammaCache
            sage: cache = pAdicLogGammaCache(2)
            sage: cache.increase_N(100)
            sage: cache.expansion((3,4,97))
            (-7780, 1, [50, 3492])
        """
        if N > self.N:
            Nold = self.N
            self.N = N
            if self.e > 1:
                self._expansion_at_0

    def clear_cache(self):
        """
        This function deletes all saved values in order to free up memory.

        EXAMPLES::

            sage: from amortizedHGM.gamma_expansions import pAdicLogGammaCache
            sage: cache = pAdicLogGammaCache(2)
            sage: cache.clear_cache()
            sage: len(cache.cache)
            0
            sage: val = cache.expansion((3,4,97))
            sage: len(cache.cache)
            24
            sage: cache.clear_cache()
            sage: len(cache.cache)
            0
        """
        self.N = self.e + 1
        self.cache = {}
        if hasattr(self, "_expansion_at_0"):
            # lazy_attributes store themselves as a normal attribute
            del self._expansion_at_0

    def save(self, filename):
        """
        Saves the cache to a file which can be loaded later, overwriting
        the contents of the file.

        EXAMPLES::

            sage: from amortizedHGM.gamma_expansions import pAdicLogGammaCache
            sage: filename = tmp_filename()
            sage: cache = pAdicLogGammaCache(2)
            sage: cache.clear_cache()
            sage: val = cache.expansion((3,4,97))
            sage: len(cache.cache)
            24
            sage: cache.save(filename)
            sage: cache.clear_cache()
            sage: len(cache.cache)
            0
            sage: cache.load(filename)
            sage: len(cache.cache)
            24
            sage: os.remove(filename)
        """
        with open(filename, "wb") as fobj:
            fobj.write(dumps((self.e, self.N, self.cache, self._expansion_at_0), compress=True))

    def load(self, filename):
        """
        Load the cache from a previously saved file,
        adding them to the current cache.

        Note that the value e1 for the saved file can be larger than this e,
        but in this case any p with e < p <= e1 will be missing.

        EXAMPLES::

            sage: from amortizedHGM.gamma_expansions import pAdicLogGammaCache
            sage: filename = tmp_filename()
            sage: cache = pAdicLogGammaCache(3)
            sage: cache.clear_cache()
            sage: _ = cache.expansion((3,4,97))
            sage: cache.save(filename)
            sage: cache2 = pAdicLogGammaCache(2)
            sage: _ = cache2.expansion((3,4,97))
            sage: c2 = cache2.cache
            sage: cache2.clear_cache()
            sage: cache2.load(filename)
            sage: set(c2).difference(set(cache2.cache))
            {(1, 4, 3)}
            sage: all(c2[a,b,p][0] % p^2 == cache2.cache[a,b,p][0] and c2[a,b,p][1] == cache2.cache[a,b,p][1] and [u % p^2 for u in c2[a,b,p][2]] == cache2.cache[a,b,p][2] for (a,b,p) in cache2.cache)
            True
            sage: os.remove(filename)
        """
        with open(filename, "rb") as fobj:
            e, N, cache, exp0 = loads(fobj.read(), compress=True)
        if N > self.N:
            self.N = N
            self._expansion_at_0.update(exp0)
        if e < self.e:
            raise ValueError("Cannot load from file with lower precision")
        if e > self.e:
            e = self.e
            peD = {}
            for (a, b, p), (c, d, f) in cache.items():
                if p not in peD:
                    peD[p] = powers_list(p, e)
                pe = peD[p]
                c = c % pe[-1]
                f = [f[i] % pe[i] for i in range(e)]
                cache[a,b,p] = (c, d, f)
        self.cache.update(cache)

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

            sage: from amortizedHGM.gamma_expansions import pAdicLogGammaCache
            sage: e = 5
            sage: cache = pAdicLogGammaCache(e)
            sage: c, i, f = cache.expansion((5,7,83)); (c, i, f)
            (1378756068, -1, [38, -5061, 107687, -24453648, 2520179713])
            sage: R = Zp(83)
            sage: S.<x> = R[]
            sage: Zp(83)(5/7 + 3*83, e).gamma()
            46 + 72*83 + 14*83^2 + 71*83^3 + 30*83^4 + O(83^5)
            sage: c^i * Zp(83)(S(list(reversed(f)))(3*83), e).exp() # FIXME
            46 + 72*83 + 14*83^2 + 71*83^3 + 30*83^4 + O(83^5)

        TESTS::

            sage: all(Zp(p)(a/b + 3*p, e).gamma() == c^i * Zp(p)(f(3*p), e).exp() for ((a,b,p),(c,i,f)) in cache.cache.items()) # FIXME
            True
        """
        try:
            return expansion_from_cache(self.cache, *abp, self.e)
        except KeyError:
            a, b, p = abp
            if p <= self.e:
                raise ValueError(f"Cache does not support primes smaller than {self.e+1}")
            if p >= self.N:
                N = max(p+1, 2*self.N)
                self.increase_N(N)
            self._set_expansion_at_offset(b)
            assert abp in self.cache or (b-a, b, p) in self.cache
            return self.expansion(abp)

    def _expansion0_prep(self):
        """
        Creates the amortized inputs for the ``_expansion0`` method.

        OUTPUT:

        - ``harmonics`` -- a dictionary, indexed by `j` from 1 to ``max(e-2,1)``,
          with values the truncated harmonic sums output by the ``batch_harmonic`` method
        - ``den`` -- the factorial of e-1
        - ``mat`` -- a lower triangular (e-1)x(e-1) matrix of binomial coefficients,
          with (i,j) entry equal to (e-1)! times the entry of the matrix inverse of binomial(i+1, j)
        - ``tmp`` -- a 1x(e-1) matrix of integers, initially 0

        EXAMPLES::

            sage: from amortizedHGM.gamma_expansions import pAdicLogGammaCache
            sage: cache = pAdicLogGammaCache(5)
            sage: cache.clear_cache()
            sage: cache.increase_N(20)
            sage: harmonics, den, mat, tmp = cache._expansion0_prep()
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
        tmp = matrix(ZZ, 1, e-1)
        return harmonics, den, mat, tmp

    def _expansion0(self, p, harmonics, den, mat, tmp):
        """
        A helper function for ``_expansion_at_0`` that computes the expansion of Gamma_p(x) at 0
        without caching.

        EXAMPLES::

            sage: from amortizedHGM.gamma_expansions import pAdicLogGammaCache
            sage: cache = pAdicLogGammaCache(5)
            sage: cache.clear_cache()
            sage: cache.increase_N(20)
            sage: harmonics, den, mat, tmp = cache._expansion0_prep()
            sage: cache._expansion0(17, harmonics, den, mat, tmp)
            [0, 72500, 0, 230, 0]
            sage: Zp(17)(3*17,5).gamma()
            1 + 2*17 + 12*17^2 + 2*17^3 + O(17^4)
            sage: Zp(17)(72500*(3*17) + 230*(3*17)^3, 4).exp()
            1 + 2*17 + 12*17^2 + 2*17^3 + O(17^4)
        """
        return gamma_expansion_at_0(p, self.e, harmonics, den, mat, tmp)

    @lazy_attribute
    def _expansion_at_0(self):
        r"""
        Amortized computation of power series expansions of log of `p`-adic Gamma at 0.
        We exclude primes \leq e.

        OUTPUT:

        A dictionary, indexed by p between e+1 and N, with the value at p a list of integers
        giving the coefficients of the power series expansion of Gamma_p(x)

        EXAMPLES::

            sage: from amortizedHGM.gamma_expansions import pAdicLogGammaCache
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
        harmonics, den, mat, tmp = self._expansion0_prep()
        return {p: self._expansion0(p, harmonics, den, mat, tmp) for p in prime_range(self.e+1, self.N)}

    def _set_expansion_at_offset(self, d):
        """
        Amortized computation of power series expansions of log `p`-adic Gamma around
        all rational numbers with denominator `d` between 0 and 1,
        for primes p up to the current bound `N`.

        FIXME: Add explanation for the storage format of the cache

        INPUT:

        - `d` -- a positive integer, the denominator

        EXAMPLES::

            sage: from amortizedHGM.gamma_expansions import pAdicLogGammaCache
            sage: cache = pAdicLogGammaCache(3)
            sage: cache.increase_N(20)
            sage: cache._set_expansion_at_offset(3)
            sage: cache.cache[2,3,7]
            (2, -1, [2, 14, 147])
        """
        def add_to_cache(b, d, p, c0):
            sgn, i = d.__rdivmod__(-b*p) # Same as divmod(-b*p, d)
            return ((i, d, p), (c0, -1 if sgn%2 else 1, None))

        n, e = self.N, self.e
        zero, one, minusone = ZZ(0), ZZ(1), ZZ(-1)
        if e == 1:
            if d == 1:
                self.cache.update(((zero, one, p), (minusone, minusone, None)) for p in prime_range(3, n))
            else:
                for b in srange(1, d//2+1):
                    if gcd(b, d) == 1:
                        fac = batch_factorial(n, 1, b/d)
                        self.cache.update(add_to_cache(b,d,p,f) for p,f in fac.items()) # inner loop
        else:
            zero_exp = self._expansion_at_0
            if d == 1:
                self.cache.update(((zero, one, p), (minusone, minusone, s)) for p, s in zero_exp.items())
            else:
                for b in srange(1, d//2+1):
                    if gcd(b, d) == 1:
                        harmonics = {j: batch_harmonic(n, e-j if j>1 else e, 
                            b/d, j, proj=True) for j in range(1, e)}
                        # Combine the expansion at 0 with the contribution from
                        # harmonic sums, then recenter the log expansion.
                        self.cache.update(gamma_translate(s, p, harmonics, e, b, d) 
                                for p,s in zero_exp.items() if p>d or d%p) # inner loop

