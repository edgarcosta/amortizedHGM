from sage.rings.fast_arith cimport prime_range
from sage.rings.integer cimport Integer
from sage.rings.rational cimport Rational
from sage.structure.element import parent
from cpython cimport array

cdef long mbound_c_ints(long p, int start_num, int start_den, int end_num, int end_den):
    return max((end_num * (p-1)) // end_den - (start_num * (p-1)) // start_den, 1)

cpdef mbound_dict_c(indices, Rational start, Rational end):
    """
    Return a dict keyed by primes `p` in `indices` computing a range of `k`
    used in the average polynomial time computation of the hypergeometric trace formula.
    """
    cdef int i, n, start_num, start_den, end_num, end_den
    cdef array.array l
    start_num = start.numer()
    start_den = start.denom()
    end_num = end.numer()
    end_den = end.denom()
    n = len(indices)
    l = array.array('l', [0]) * n
    for i in range(n):
        l[i] = mbound_c_ints(indices[i], start_num, start_den, end_num, end_den)
    return dict(zip(indices, l))

cpdef prime_range_by_residues(a, b, dens, s):
    r"""
    Sort the primes from a (inclusive) to b (exclusive) into residue classes.

    Assumes s is a set of primes to be excluded. This should include all primes dividing any
    of the moduli (given in dens).
    """
    prime_ranges = {}
    for d in dens:
        prime_ranges[d] = {}
        for r in range(d):
            if d.gcd(r) == 1:
                prime_ranges[d][r] = []
    for p in prime_range(a, b):
        if p not in s:
            for d in dens:
                prime_ranges[d][p % d].append(p)
    return prime_ranges

cpdef multiplicative_lift(t, Integer p, int e, Integer efac, x):
    r"""
    Compute a polynomial whose value at x is ([t]/t)**x mod p**e, where [t] denotes the
    p-adic multiplicative lift.

    We assume that efac == factorial(e-1).
    """
    cdef Integer pe = p**e
    cdef Integer tmp = (t%pe).powermod(p-1, pe) # Faster than power_mod(t, p-1, pe)
    cdef Integer tmp2 = moddiv_int(truncated_log_mod(tmp, e, pe), 1-p, pe)
    return moddiv(truncated_exp(tmp2*x, e), efac, pe)

cpdef Integer moddiv_int(Integer a, Integer b, Integer m):
    r"""
    Compute a/b mod m. All of a, b, and m must be Sage integers.

    This avoids creating any elements of QQ.
    """
    return a*b.inverse_mod(m)%m

cpdef moddiv(a, Integer b, Integer m):
    r"""
    Compute a/b mod m. Both b and m must be Sage integers.

    This avoids creating any elements of QQ.
    """
    return a*b.inverse_mod(m)%m

cpdef Integer recenter_mod(Integer x, Integer m):
    r"""
    Convert a residue class modulo m into a representative centered at 0.
    """
    return x if x <= m//2 else x-m

cpdef eval_poly_as_gen(l, x):
    r"""
    Evaluate a polynomial specified by a generator of coefficients in descending order.

    This implements "Horner's rule" which long predates Horner.

    Assumes l is nonempty.
    """
    ans = None
    for i in l:
        ans = ans*x + i if ans else i
    if parent(ans) is not parent(x):
        # will only happen if all entries of l are zero
        ans = x.parent()(ans)
    return ans

cpdef truncated_log_mod(Integer x, int e, Integer m):
    r"""
    Compute log(x) truncated modulo (x**e, m). Assumes that x is a Sage integer.
    """
    cdef int i
    cdef Integer x1, tmp, mult

    x1 = 1-x
    tmp = Integer(0)
    mult = Integer(-1)
    for i in range(1, e):
        mult *= x1
        tmp += moddiv_int(mult, Integer(i), m)
    return tmp

cpdef Integer truncated_exp_int(Integer x, int e):
    r"""
    Compute (e-1)!*exp(x) truncated modulo x**e. Assumes that x is a Sage integer.
    """
    cdef int i
    cdef Integer tmp, mult

    tmp = Integer(1)
    mult = Integer(1)
    for i in range(e-1, 0, -1):
        mult *= i
        tmp = tmp*x + mult
    return tmp

cpdef truncated_exp(x, int e):
    r"""
    Compute (e-1)!*exp(x) truncated modulo x**e. Does not assume that x is a Sage integer.
    """
    cdef int i
    cdef Integer mult

    tmp = 1
    mult = Integer(1)
    for i in range(e-1, 0, -1):
        mult *= i
        tmp = tmp*x + mult
    return tmp

cpdef int gamma_translate(l, Integer p, harmonics, int e,
                      Integer b, Integer d, int normalized) except -1:
    # Computes an inner loop in the computation of Gamma_p(x+c).

    cdef int i, j
    cdef Integer tmp = Integer(1)
    
    pe = [p**(i+1) for i in range(e)]

    # Combine the expansion at 0 with the contribution from harmonic sums.
    # Note that l starts out representing the *reversed* expansion at 0.
    for j in range(1, e):
         tmp = -tmp
         h = harmonics[j][p] # A 1x2 matrix representing H_{j,gamma} mod p**(e-j)
         l[-1-j] += moddiv_int(-tmp*h[0,0], j*h[0,1], pe[e-j-1])

    # Recenter the log expansion.
    tmp = p*moddiv_int(-b, d, p**(e-1))
    for i in range(1, e):
        for j in range(i, 0, -1):
            l[j] += l[j-1]*tmp
    if normalized: # Eliminate the constant term.
        l[-1] = 0
    for i in range(e-1 if normalized else e):
        l[i] = l[i]%pe[i]

cpdef gammas_to_displacements(l, Integer p):
    # Computes an inner loop in the computation of P_{m_i} and P_{m_i+1}.

    cdef int index, i, j, j0, j1, e, efac
    cdef Integer r, d, pe, p1, arg0, gammaprodnum, gammaprodden, tmp0, inum, iden

    # Import local variables from the calling scope. These do not depend on p.
    gammas, flgl, gammaprodnum, gammaprodden, tmp2, index, x, r, d, e, efac, inter_polys = l
    # Note: gammaprodnum/gammaprodden records the effect of integer shifts
    # on the constant term of the Gamma series.

    if e > 1:
        # Set up accumulator for the logarithmic series expansion,
        # seeding it with the effect of integer shifts.
        gammasum = [moddiv_int(tmp2[e-1-i][0], tmp2[e-1-i][1], p**(i+1)) for i in range(e)]

    for (inum,iden),j in flgl.items(): # i = inum/iden
        # if e=1, then tmp1=1 and is unused
        tmp0, j0, tmp1 = gammas.expansion((inum, iden, p))
        j1 = j if j0 == 1 else -j
        if j1 > 0:
            gammaprodnum *= tmp0 if j1==1 else tmp0**j1
        else:
            gammaprodden *= tmp0 if j1==-1 else tmp0**-j1
        if e > 1:
            for i in range(e):
                # If j0==-1, substitute x -> -x.
                # Beware that len(tmp1) can exceed e.
                gammasum[e-1-i] += j1*tmp1[-1-i]*(-1 if j0==-1 and i%2 else 1)
    if e == 1:
        return moddiv_int(gammaprodnum, gammaprodden, p)

    arg0 = p*moddiv_int(-r, d if e==2 else d*(1-p), p if e==2 else p**(e-1))
    if index == 0:
        return moddiv_int(gammaprodnum*truncated_exp_int(eval_poly_as_gen(gammasum, arg0), e), gammaprodden*efac, p**e)
    else: # index == 1 and e > 1
        pe = p**e
        p1 = (pe-p).divide_knowing_divisible_by(p-1) # reduces to 1/(1-p) mod pe
        tmp1 = 0
        for j in range(e):
            arg0 += p1
            tmp1 += truncated_exp_int(eval_poly_as_gen(gammasum, arg0), e)*inter_polys[j]
        return moddiv(tmp1*gammaprodnum, gammaprodden*efac**2, pe)

cpdef Integer fast_hgm_sum(tuple w, array.array mat, ans, Integer pe1, int s):
    # Computes a sum in the innermost loop of the trace formula.

    cdef int h1, h2, h3, i=0
    cdef Integer tmp = Integer(0), tmp2, tmp3

    for h3 in range(s):
        tmp2 = Integer(0)
        for h1 in range(h3, s):
            tmp2 += Integer(w[h1])*mat[i]
            i += 1
        tmp3 = Integer(0)
        for h2 in range(h3, s):
           tmp3 = tmp3*pe1 + Integer(ans[-1-h3,h2-h3])
        tmp += tmp2*tmp3
    return tmp

