from sage.functions.other import factorial, ceil
from sage.arith.misc import power_mod, gcd
from sage.rings.fast_arith import prime_range
from sage.rings.integer_ring import ZZ
from sage.rings.padics.factory import Zp
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.matrix.constructor import Matrix

from pyrforest import batch_factorial, batch_harmonic, remainder_forest

from .gamma_expansions import pAdicLogGammaCache
from .hgm_modpe import interpolation_polys

# ****************
# Code below is for testing purposes only

def test_batch_factorial(n, e, a, b):
    ans = batch_factorial(n, e, a, b)
    for p in prime_range(n):
        pe = p**e
        tmp = ZZ(1)
        for i in range(1, ceil(p*a/b)):
            tmp = tmp*i%pe
        if tmp != ans[p]:
            return False
    return True

def test_batch_harmonic(n, e, a, b, j):
    ans = batch_harmonic(n, e, a, b, j)
    for p in prime_range(n):
        pe = p**e
        if sum(power_mod(k, -j, pe) for k in range(1, ceil(p*a/b)))%pe != ans[p]:
            return False
    return True

def test_padic_log_gamma_expansion_at_0(n, e, t):
    cache = pAdicLogGammaCache(e)
    cache.increase_N(n)
    for p in prime_range(e+1, n):
        c, i, f = cache.expansion(0, 1, p)
        R = Zp(p, prec=e)
        g1 = R(t*p).gamma()
        g2 = c**i * R(f(t*p), e).exp()
        if g1 != g2:
            print(p, g1, g2, c, i, f)
            return False
    return True

def test_padic_log_gamma_expansion_at_offset(n, e, c, t, normalized=False):
    b = c.numerator()
    d = c.denominator()
    ans = padic_log_gamma_expansion_at_offset(n, e, c, normalized=normalized)
    for (i, p, c0, s) in ans:
        R = Zp(p, prec=e)
        if normalized:
            g1 = R(i/d+p*t).gamma().log() - R(i/d).gamma().log()
            g2 = s(R(t))
        else:
            g1 = R(i/d+p*t).gamma()
            g2 = s(R(t)).exp() * c0
        if g1 != g2:
            print(i,d,i == -b*p%d, p,g1,g2,s)
            return False
    return True

# ****************
# Code below is no longer being used, may not work correctly

def batch_pochhammer(n, e, c):
    r"""
    Amortized computation of Pochhammer symbols.

    INPUT::

     - `n`: bound on primes
     - `e`: order of the series expansion
     - `c`: a rational number

    OUTPUT::
       A dict whose value at a prime `p` is the truncated Pochhammer symbol
          (x+1)^{ceil(c*p)-1} mod (p,x)^e. We exclude primes \leq e.
    """
    # Represent x+k as a banded matrix.
    R = ZZ['k']
    y = R.gen()
    M = Matrix(R, e, e, lambda i,j,y=y: y if i==j else 1 if i==j+1 else 0)

    k = lambda p, c=c: ceil(p*c)
    m = lambda p, e=e: p**e

    ans = remainder_forest(M, m, k, kbase=1, indices=prime_range(e+1, n))
    R = ZZ['x']
    return {p: R([ans[p][i,0] for i in range(e)]) for p in prime_range(e+1, n)}

def padic_gamma_expansion_at_0(n, e):
    r"""
    Amortized computation of power series expansions of `p`-adic Gamma at 0.
    """
    ans0 = batch_pochhammer(n, e, 1)
    R = ZZ['x']
    x = R.gen()
    inter_polys = interpolation_polys(e, x)
    den = 1/factorial(e-1)
    ans = {}
    for p in prime_range(e+1, n):
        pe = p**e
        # First compute the list l[i] = Gamma(i*p).
        l = [1]
        for i in range(e-1):
            l.append(l[-1] * -ans0[p](i*p))
        # Then perform Lagrange interpolation.
        p1 = den % pe
        ans[p] = sum(l[i]*inter_polys[i]*p1 for i in range(e))
    return ans

def test_padic_gamma_expansion_at_0(n, e, t):
    ans = padic_gamma_expansion_at_0(n, e)
    for p in prime_range(e+1, n):
        R = Zp(p, prec=e)
        g1 = R(t*p).gamma()
        g2 = ans[p](R(t))        
        if g1 != g2:
            return False
    return True

def padic_gamma_expansion_at_single_offset(n, e, c, zero_exp=None):
    """
    Amortized computation of power series expansions of `p`-adic Gamma around `c`.
    
    INPUT:::
    
     - `n`: bound on primes
     - `e`: order of the series expansion
     - `c`: a rational number in (0,1). We compute a series expansion around `ceil(p*c)` for all primes `p` up to `n`, excluding primes <= e.
    """
    if not zero_exp:
        zero_exp = padic_gamma_expansion_at_0(n, e)
    if c == 0:
        return zero_exp
    ans0 = batch_pochhammer(n, e, c)

    # Compute expansions at c using the functional equation.
    d = c.denominator()
    ans = {}
    R = ZZ['x']
    x = R.gen()
    for p in prime_range(e+1, n):
       if not d%p:
           continue
       a = ceil(p*c)
       ans[p] = zero_exp[p].multiplication_trunc(ans0[p](p*x), e)
       if a%2:
           ans[p] *= -1
    return ans

def test_padic_gamma_expansion_at_offset(n, e, c, t):
    ans = padic_gamma_expansion_at_single_offset(n, e, c)
    for p in ans:
        a = ceil(p*c)
        R = Zp(p, prec=e)
        g1 = R(t*p+a).gamma()
        g2 = ans[p](R(t))
        if g1 != g2:
            return False
    return True

def padic_gamma_expansion_at_all_offsets(n, e, d, zero_exp=None):
    """
    Amortized computation of power series expansions of `p`-adic Gamma at rational arguments.
    
    INPUT:::
    
     - `n`: bound on primes
     - `e`: order of the series expansion
     - `d`: a positive integer. We compute a series expansion around c/d for start <= c/d <= end
        for all primes `p` up to `n` (excluding primes <= e or dividing `d`).
    """
    if not zero_exp:
        zero_exp = padic_gamma_expansion_at_0(n, e)
    ans0 = {c: padic_gamma_expansion_at_single_offset(n, e, c/d, zero_exp) \
        for c in range(d//2+1) if gcd(c,d) == 1}
    R = PolynomialRing(ZZ, name='x')
    x = R.gen()
    ans = {}
    pows = {p: p**e for p in prime_range(e+1,n) if d%p != 0}
    for i in range(d):
        if gcd(i,d) == 1:
            b = -i/p%d
            for p, pe in pows.items():
                # Construct the expansions around 0 < i/d <= 1.
                ans[p,i/d] = ans0[b][p](x-b/d%pe)
                if i == 0:
                    ans[p,1] = -ans[p,0]
    return ans

def test_padic_gamma_expansion_at_all_offsets(n, e, d, t):
    ans = padic_gamma_expansion_at_all_offsets(n, e, d)
    for (p, c) in ans:
        R = Zp(p, prec=e)
        g1 = R(t*p+c).gamma()
        g2 = ans[p,c](R(t))
        if g1 != g2:
            return False
    return True

def padic_log_gamma_expansion_at_all_offsets(n, e, d, zero_exp=None, normalized=False):
    """
    Amortized computation of power series expansions of log of `p`-adic Gamma at rational arguments.

    INPUT:::

     - `n`: bound on primes
     - `e`: order of the series expansion
     - `d`: a positive integer. We compute a series expansion around c/d for 0 <= c/d <= 1
        with gcd(c,d) = 1  for primes e+1 <= p < n (excluding dividing d).
    """
    if not zero_exp:
        zero_exp = padic_log_gamma_expansion_at_0(n, e)
    for b in range(d//2+1):
        if gcd(b,d) == 1:
            for (i,p,tmp) in padic_log_gamma_expansion_at_single_offset(n, e, b/d, zero_exp, normalized): #inner loop
                yield (i, p, tmp)

def test_padic_log_gamma_expansion_at_all_offsets(n, e, d, t, normalized=False):
    for (p, c, s) in padic_log_gamma_expansion_at_all_offsets(n, e, d, normalized=normalized):
        R = Zp(p, prec=e)
        g1 = R(t*p+c).gamma().log()
        if normalized:
            g1 -= R(c).gamma().log()
        g2 = s(R(t))
        if g1 != g2:
            return False
    return True


