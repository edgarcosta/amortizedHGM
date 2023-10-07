from sage.rings.fast_arith cimport prime_range
from sage.rings.integer cimport Integer
from sage.rings.rational cimport Rational
from sage.structure.element import parent
from cpython cimport array

# ******* 
# Utility functions
# *******

cpdef Integer moddiv_int(Integer a, Integer b, Integer m):
    r"""
    Compute x with |x| <= m/2 and x == a/b mod m. All of a, b, and m must be Sage integers.

    This avoids creating any elements of QQ.
    """
    cdef Integer x = a*b.inverse_mod(m)%m
    return x if x <= m>>1 else x-m

cdef moddiv(a, Integer b, Integer m):
    r"""
    Compute a/b mod m. Both b and m must be Sage integers.

    This avoids creating any elements of QQ.
    """
    return a*b.inverse_mod(m)%m

cpdef truncated_log_mod(Integer x, int e, Integer m):
    r"""
    Compute log(x) truncated modulo (x**e, m). Assumes that x is a Sage integer.
    """
    cdef Integer x1 = 1-x
    cdef Integer mult = -x1
    cdef Integer tmp = mult

    for i in range(2, e):
        mult *= x1
        tmp += moddiv_int(mult, Integer(i), m)
    return tmp

cpdef Integer truncated_exp_int(Integer x, int e):
    r"""
    Compute (e-1)!*exp(x) truncated modulo x**e. Assumes that x is a Sage integer.
    """
    cdef int i
    cdef Integer mult = Integer(e-1)
    cdef Integer tmp = x+mult

    for i in range(e-2, 0, -1):
        mult *= i
        tmp = tmp*x + mult
    return tmp

cpdef multiplicative_lift(t, Integer p, int e, x=Integer(1)):
    r"""
    Compute a polynomial whose value at x is ([t]/t)**((1-p)*x) mod p**e, where [t] denotes the
    p-adic multiplicative lift.
    """
    cdef int i
    cdef Integer pe = p**e
    cdef Integer tmp = (t%pe).powermod(p-1, pe) # Faster than power_mod(t, p-1, pe)
    cdef Integer tmp2 = truncated_log_mod(tmp, e, pe)
    tmp2 //= p

    # Exponentiate to get the desired series.
    tmp3 = Integer(1)
    tmp4 = Integer(1)
    for i in range(1, e):
        tmp4 = moddiv(tmp4*tmp2*x, Integer(i), p**(e-i))
        tmp3 += tmp4
    return tmp3

# *******
# Functions used to accelerate certain inner loops.
# *******

cdef long mbound_c_ints(long p, int start_num, int start_den, int end_num, int end_den):
    return max((end_num * (p-1)) // end_den - (start_num * (p-1)) // start_den, 1)

cpdef mbound_dict_c(indices, Rational start, Rational end):
    """
    Return a dict keyed by primes `p` in `indices` computing a range of `k`
    used in the average polynomial time computation of the hypergeometric trace formula.
    """
    cdef int i, n, start_num, start_den, end_num, end_den
    cdef array.array l

    start_num, start_den = start.as_integer_ratio()
    end_num, end_den = end.as_integer_ratio()
    n = len(indices)
    l = array.array('l', [0]) * n
    for i in range(n):
        l[i] = mbound_c_ints(indices[i], start_num, start_den, end_num, end_den)
    return dict(zip(indices, l))

cpdef dict prime_range_by_residues(a, b, dens, m, s):
    r"""
    Sort the primes from a (inclusive) to b (exclusive) into residue classes.

    Assumes s is a set of primes to be excluded. This should include all primes dividing any
    of the moduli (given in dens). We also exclude primes dividing m (without factoring m).
    """
    cdef Integer p

    prime_ranges = {}
    for d in dens:
        prime_ranges[d] = {}
        for r in range(d):
            if d.gcd(r) == 1:
                prime_ranges[d][r] = []
    for p in prime_range(a, b):
        if p not in s and m%p:
            for d in dens:
                prime_ranges[d][p % d].append(p)
    return prime_ranges

cpdef sign_flip(l, int e):
    r"""
    Given a list l of length e of the coefficients of a polynomial f(x) in descending order,
    return the list corresponding to -f(-x).
    """
    cdef int j
    return [l[j] if (e-j)%2 else -l[j] for j in range(e)]

cpdef gamma_translate(s, Integer p, harmonics, int e,
                      Integer b, Integer d, int normalized):
    # Computes an inner loop in the computation of Gamma_p(x+c).

    cdef int i, j
    cdef Integer tmp

    p_powers = [p**(i+1) for i in range(e)]

    # Note that s starts out representing the *reversed* expansion at 0.
    # We combine it with the contribution from harmonic sums.
    l = [s[j-1] + moddiv_int((1 if (e-j)%2 else -1)*harmonics[e-j][p][0,0], (e-j)*harmonics[e-j][p][0,1], p_powers[j-1]) for j in range(1,e)]
    l.append(s[e-1])

    # Recenter the log expansion.
    tmp = p*moddiv_int(-b, d, p_powers[e-2])
    for i in range(1, e):
        for j in range(i, 0, -1):
            l[j] += l[j-1]*tmp
    if normalized:
        for i in range(e-1):
            l[i] = l[i]%p_powers[i]
        l[-1] = 0 # Eliminate the constant term.
    else:
        for i in range(e):
            l[i] = l[i]%p_powers[i]

    return l

cpdef gamma_expansion_product(l, Integer p):
    # Compute a product of expansions of Gamma_p.
    # Used in an inner loop in the computation of P_{m_i} and P_{m_i+1}.

    cdef int i, j, j0, j1, e
    cdef Integer pe, p1, num, den, tmp0, inum, iden

    # Import local variables from the calling scope. These do not depend on p.
    gammas, flgl, e = l

    num = Integer(1)
    den = Integer(1)
    gammasum = [0 for i in range(e)]
    
    for (inum,iden),j in flgl.items(): # i = inum/iden
        # if e=1, then tmp1=1 and is unused
        tmp0, j0, tmp1 = gammas.expansion((inum, iden, p))
        j1 = j if j0 == 1 else -j
        if j1 > 0:
            num *= tmp0 if j1==1 else tmp0**j1
        else:
            den *= tmp0 if j1==-1 else tmp0**-j1
        if e > 1:
            for i in range(e):
                # Beware that len(tmp1) can exceed e.
                gammasum[e-1-i] += j1*tmp1[-1-i]
    
    return num, den, gammasum

cdef eval_poly_as_gen(l, x):
    r"""
    Evaluate a polynomial specified by a list of coefficients in descending order.

    This implements "Horner's rule" which long predates Horner.
    """
    ans = 0
    for i in l:
        ans = ans*x + i
    return ans

cdef Integer eval_poly_as_gen_int(l, Integer x):
    r"""
    Evaluate a polynomial specified by a list of coefficients in descending order.

    This implements "Horner's rule" which long predates Horner.
    """
    cdef Integer ans = Integer(0), i
    
    for i in l:
        ans = ans*x + i
    return ans

cpdef gammas_to_displacements(l, Integer p, t):
    # Computes an inner loop in the computation of P_{m_i} and P_{m_i+1}.
    # Assumes t is the output of gamma_expansion_product.

    cdef int i, j, j0, j1, etmp, e1, e1fac, e, efac, index
    cdef Integer r, d, p1, arg0, gammaprodnum, gammaprodden, num, den, tmp3

    num, den, gammasum0 = t
    
    # Import local variables from the calling scope. These do not depend on p.
    tmp, tmp2, r, d, e1, e1fac, e, efac, inter_polys = l
    
    ans = []

    for index in range(2):
        # Adjust the computed product to account for integer shifts.
        gammaprodnum = tmp[index][0]*num
        gammaprodden = tmp[index][1]*den

        etmp = (e1, e)[index]
        if etmp <= 0:
            ans.append(None)
        elif etmp == 1:
            ans.append(moddiv_int(gammaprodnum, gammaprodden, p))
        else:
            # Adjust the logarithmic series expansion to account for integer shifts.
            # Beware that gammasum0 may be longer than e.
            p_powers = [p**(i+1) for i in range(etmp)]
            tmp2i = tmp2[index]
            gammasum = [gammasum0[i-etmp] + moddiv_int(tmp2i[etmp-1-i][0], tmp2i[etmp-1-i][1], p_powers[i]) for i in range(etmp)]

            if index == 0:
                arg0 = Integer(0) if r==0 else p*(moddiv_int(-r, d, p) if etmp == 2 else moddiv_int(-r, d*(1-p), p_powers[-2]))
                tmp3 = eval_poly_as_gen_int(gammasum, arg0) if arg0 else gammasum[-1]
                ans.append(moddiv_int(gammaprodnum*truncated_exp_int(tmp3, e1), gammaprodden*e1fac, p_powers[-1]))
            else: # index == 1 and e > 1
                # Compute the polynomial with coefficients c_{i,h}(p) by interpolation.
                arg0 = Integer(0)
                tmp1 = 0
                for pol in inter_polys:
                    tmp3 = eval_poly_as_gen_int(gammasum, arg0)
                    tmp1 += truncated_exp_int(tmp3, e)*pol
                    arg0 += p
                ans.append(eval_poly_as_gen(
                    [moddiv_int(tmp1[i].divide_knowing_divisible_by(p**i)*gammaprodnum,
                    gammaprodden*efac, p_powers[-i-1]) for i in range(e-1,-1,-1)],
                    pol.parent().gen()))
    return ans

cpdef Integer fast_hgm_sum(tuple w, ans, Integer pe1, int s):
    # Computes a sum in the innermost loop of the trace formula.

    cdef int h1, h2
    cdef Integer tmp = Integer(0), tmp2, tmp3 = Integer(1)

    for h1 in range(s):
        tmp2 = Integer(0)
        for h2 in range(h1, s):
            tmp2 = tmp2*pe1 + Integer(ans[-1-h1,h2-h1])
        tmp += w[h1]*tmp2*tmp3
        if h1 < s-1:
            tmp3 *= pe1
    return tmp

