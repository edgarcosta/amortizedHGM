from cpython cimport array
from sage.rings.fast_arith cimport prime_range
from sage.rings.integer cimport Integer
from sage.rings.rational cimport Rational

# ******* 
# Utility functions
# *******

cpdef list powers_list(Integer p, int e, int initial_index=1):
    r"""
    Compute [p, p**2, ..., p**e].
    """
    cdef int i
    cdef list l = [p if initial_index == 1 else 1]

    for i in range(e-initial_index):
        l.append(l[-1]*p)
    return l

cpdef Integer moddiv_int(Integer a, Integer b, Integer m):
    r"""
    Compute x with |x| <= m/2 and x == a/b mod m. All of a, b, and m must be Sage integers.

    This avoids creating any elements of QQ.
    """
    cdef Integer x = a * b.inverse_mod(m) % m
    return x if x <= m>>1 else x-m

cpdef Integer truncated_log_mod(Integer x, int e, Integer m):
    r"""
    Compute log(x) truncated modulo (x**e, m). Assumes that x is a Sage integer.
    """
    cdef int i
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
    cdef list l = powers_list(p, e)
    cdef Integer pe = l[-1]
    cdef Integer tmp = (t%pe).powermod(p-1, pe) # Faster than power_mod(t, p-1, pe)
    cdef Integer tmp2 = truncated_log_mod(tmp, e, pe).divide_knowing_divisible_by(p)
    cdef Integer tmp4 = tmp2

    # Exponentiate to get the desired series.
    tmp3 = Integer(1) + tmp2*x
    tmp5 = x
    for i in range(2, e):
        tmp4 = moddiv_int(tmp4*tmp2, Integer(i), l[-1-i])
        tmp5 *= x
        tmp3 += tmp4*tmp5
    return tmp3

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

    This implements "Horner's rule" which long predates Horner. Assumes that everything
    specified is a Sage integer.
    """
    cdef Integer ans = Integer(), i

    for i in l:
        ans = ans*x + i
    return ans

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
        if p not in s and m % p:
            for d in dens:
                prime_ranges[d][p % d].append(p)
    return prime_ranges

# *******
# Functions used to accelerate certain inner loops.
# *******

cpdef list gamma_expansion_at_0(Integer p, int e, harmonics, Integer den, mat, tmp):
    cdef int i
    cdef list ans, p_powers

    p_powers = powers_list(p, e)

    # Compute the finite difference of the expansion of log Gamma_p(py).
    tmp[0,0] = truncated_log_mod(-harmonics[1][p][0,1], e, p_powers[-1]) # = log -(p-1)!
    for i in range(1, e-1):
        h = harmonics[i][p]
        tmp[0,i] = (-p_powers[i-1] if i%2 else p_powers[i-1]) * moddiv_int(-h[0,0], 
            i*h[0,1], p_powers[e-i-1])

    # Use a matrix multiplication to invert the difference operator.
    tmp *= mat
    ans = [moddiv_int(tmp[0,i].divide_knowing_divisible_by(p_powers[i]), 
        den, p_powers[-1-i]) for i in range(e-2,-1,-1)] 
    ans.append(0)
    return ans

cpdef tuple gamma_translate(list s, Integer p, harmonics, int e, Integer b, Integer d):
    r"""
    Compute an inner loop in the computation of Gamma_p(x+c).
    """
    cdef int i, j
    cdef Integer tmp, sgn, k
    cdef list p_powers = powers_list(p, e)

    # Note that s starts out representing the *reversed* expansion at 0.
    # We combine it with the contribution from harmonic sums.
    l = s[::]
    for j in range(1, e):
        h = harmonics[e-j][p]
        l[j-1] += moddiv_int(h[0,0] if (e-j)%2 else -h[0,0], (e-j)*h[0,1], p_powers[j-1])

    # Recenter the log expansion.
    tmp = p*moddiv_int(-b, d, p_powers[e-2])
    for i in range(1, e):
        for j in range(i, 0, -1):
            l[j] = (l[j]+l[j-1]*tmp) % p_powers[j]

    # Prepare output for cache. Note that h = harmonics[1][p].
    sgn, k = d.__rdivmod__(-b*p) # Same as divmod(-b*p, d)
    sgn = Integer(-1 if sgn%2 else 1)
    return ((k, d, p), (h[0,1], sgn, l))

cdef sign_flip(l, int e):
    r"""
    Given a list l of length e of the coefficients of a polynomial f(x) in descending order,
    return the list corresponding to -f(-x).
    """
    cdef int j

    if l is None:
        return None
    return [l[j] if (e-j)%2 else -l[j] for j in range(e)]

cpdef expansion_from_cache(dict cache, Integer a, Integer b, Integer p, int e):
    cdef int j
    cdef Integer c

    if (a,b,p) in cache:
        c, j, f = cache[a, b, p]
        return (-c if j<0 else c), 1, f

    # Use the Legendre relation instead.
    c, _, f = cache[b-a, b, p]
    # substitute x -> -x (and multiply by -1)
    return c, -1, sign_flip(f, e)

cpdef gamma_expansion_product(l, Integer p, int e):
    r"""
    Compute a product of cached expansions of Gamma_p.

    Used in an inner loop in the computation of P_{m_i} and P_{m_i+1}.
    """

    cdef dict gammas_cache, flgl
    cdef int gammas_e, i, j, j0, j1
    cdef list gammasum
    cdef Integer tmp0, inum, iden, c
    cdef Integer num = Integer(1), den = num

    # Import local variables from the calling scope. These do not depend on p.
    # Note: gammasum will be updated on output.
    gammas, gammas_cache, gammas_e, flgl, gammasum = l

    if e > 1:
        for i in range(e):
            gammasum[i] = 0
    
    for (inum,iden),j in flgl.items(): # i = inum/iden
        tmp0, j0, tmp1 = gammas.expansion((inum, iden, p))
        j1 = j if j0 > 0 else -j
        if j1 > 0:
            num *= tmp0 if j1 == 1 else tmp0**j1
        else:
            den *= tmp0 if j1 == -1 else tmp0**-j1
        if e > 1:
            for i in range(e):
                # Beware that len(tmp1) can exceed e.
                gammasum[e-1-i] += j1*tmp1[-1-i]
    
    return num, den, gammasum

cpdef gammas_to_displacements(Integer p, int e1, int e, Integer num, 
    Integer den, list gammasum0, tmp, l):
    r"""
    Compute an inner loop in the computation of P_{m_i} and P_{m_i+1}.
    """

    cdef int i, etmp, e1fac, efac, index
    cdef Integer r, d, p1, arg0, prod_num, prod_den, tmp3
    cdef list ans = [], gammasum, p_powers
    cdef tuple tmp_index

    # Import local variables from the calling scope. These do not depend on p.
    if l is not None:
        tmp2, r, d, e1fac, efac, inter_polys, k1 = l
    
    for index in range(2):
        # Adjust the computed product to account for integer shifts.
        tmp_index = tmp[index]
        prod_num = tmp_index[0]*num
        prod_den = tmp_index[1]*den

        etmp = e1 if index == 0 else e
        if etmp <= 0:
            ans.append(None)
        elif etmp == 1:
            ans.append(moddiv_int(prod_num, prod_den, p))
        elif index == 0 and r == 0:
            # Abbreviated version of the general case.
            p1 = p**e1
            tmp3 = gammasum0[-1] + moddiv_int(*tmp2[0][0], p1)
            tmp3 = truncated_exp_int(tmp3, e1)
            ans.append(moddiv_int(prod_num*tmp3, prod_den*e1fac, p1))
        else:
            # Adjust the logarithmic series expansion to account for integer shifts.
            # Beware that gammasum0 may be longer than e.
            p_powers = powers_list(p, etmp, initial_index=0)
            tmp2i = tmp2[index]
            gammasum = [gammasum0[i-etmp] + moddiv_int(*tmp2i[etmp-1-i], p_powers[i+1]) for i in range(etmp)]

            if index == 0: # Forces r > 0
                arg0 = p*moddiv_int(-r, d if etmp==2 else d*(1-p), p_powers[-2])
                tmp3 = eval_poly_as_gen_int(gammasum, arg0)
                tmp3 = truncated_exp_int(tmp3, e1)
                ans.append(moddiv_int(prod_num*tmp3, prod_den*e1fac, p_powers[-1]))
            else:
                # Extract c_{i,0}(p).
                # This introduces a factor of 1/(e-1)! into the carried constant.
                prod_num *= truncated_exp_int(gammasum[-1], e)
                if e == 2: # Abbreviated version of the next step
                    tmp1 = 1 + gammasum[0]*k1
                elif e == 3: # Abbreviated version of the next step
                    tmp1 = 2*(2 + 2*gammasum[1]*k1 + (gammasum[1]**2 + 2*gammasum[0])*k1**2)
                elif e == 4: # Abbreviated version of the next step
                    tmp1 = 6*(6 + 6*gammasum[2]*k1 + (3*gammasum[2]**2 + 6*gammasum[1])*k1**2 + (gammasum[2]**3 + 6*gammasum[1]*gammasum[2] + 6*gammasum[0])*k1**3)
                else: # index == 1 and e > 4
                    gammasum[-1] = Integer()
                    # Compute the polynomial with coefficients c_{i,h}(p) by interpolation.
                    # This introduces a factor of 1/(e-1)!**2 into the carried constant.
                    tmp1 = 0*k1
                    for i in range(e):
                        tmp3 = eval_poly_as_gen_int(gammasum, i*p) if i else Integer()
                        tmp1 += truncated_exp_int(tmp3, e)*inter_polys[i]
                    # Remove formal powers of p.
                    for i in range(e):
                        tmp3 = tmp1[i].divide_knowing_divisible_by(p_powers[i])
                        gammasum[e-1-i] = tmp3 % p_powers[-i-1]
                    tmp1 = eval_poly_as_gen(gammasum, k1)
                # Return the carried constant separately.
                tmp3 = moddiv_int(prod_num, prod_den*efac, p_powers[-1])
                ans.append((tmp3, tmp1))
    return ans

cpdef Integer hgm_matmult(w, ans, Integer pe1, int s):
    r"""
    Compute a matrix multiplication in the innermost loop of the trace formula.
    """
    cdef int h1, h2
    cdef Integer tmp = Integer()

    for h2 in range(s, 1, -1):
        for h1 in range(h2):
            tmp += w[h1]*ans[-1-h1,-h2]
        tmp *= pe1
    return tmp + w[0]*ans[-1,-1]

