from sage.all import *
from amortizedHGM import AmortizingHypergeometricData
import itertools
from tempfile import NamedTemporaryFile

# utility function
def s(p, d):
    # p prime (will be a wild prime in practice)
    if gcd(d, p) == 1:
        return 1
    else: 
        return 1 + valuation(d, p) + 1/(p-1)

# utility function 
def signed_reverse_weil_polynomials(d,q,i):
        R = ZZ["T"]
        if is_odd(i):
            return [f.reverse() for f in R.weil_polynomials(d,q)]
        elif d == 0:
            return [f.reverse() for f in R.weil_polynomials(d,q)]
        else:
            tmp = R.weil_polynomials(d,q) + R.weil_polynomials(d,q,sign=-1)
            return [f.reverse() for f in tmp] 

class LAmortizingHypergeometricData(AmortizingHypergeometricData):
    """
    Class for computing Euler factors and conductor exponents of wild primes for a hypergeometric motive over Q
    Inherits from the clss AmortizingHypergeometricData from https://github.com/edgarcosta/amortizedHGM.git 
    """
    
    @cached_method
    def Hmagma(self):
        """
        Creates a Magma incarnation of self 
        """
        return magma.HypergeometricData(self.alpha_beta()) 

    # utility function
    def sigma_infinity(self, p):
        """
        INPUT: 
        * "p" -- prime
        """
        return sum([s(p, denominator(i)) for i in self.alpha()])
        
    # utility function
    def sigma_zero(self, p):
        """
        INPUT: 
        * "p" -- prime
        """
        return sum([s(p, denominator(i)) for i in self.beta()])
        
    # utility function
    def sigma(self, p, k):
        """
        INPUT: 
        * "p" -- prime 
        * "k" -- p-adic valuation of specialization parameter t
        """

        sigma_infinity = self.sigma_infinity(p)
        sigma_zero = self.sigma_zero(p)
        k_crit = sigma_infinity - sigma_zero
        k_infinity = min(k_crit, 0)
        k_zero = max(k_crit, 0)

        if k <= k_infinity:
            return sigma_infinity
        elif k >= k_infinity and k <= k_zero:
            return max(sigma_infinity, sigma_zero) - abs(k)
        else:
            return sigma_zero


    def candidate_euler_factor_conductor(self, p, t):
        """
        Returns an iterator over all tuples of the form (conductor exponent, Euler factor) that may arise as 
        the Euler factor and conductor exponent at a wild prime p 
        
        INPUT:
        * "p" -- wild prime
        * "t" -- specialization point 
        """
        
        R = ZZ["T"]
        k = valuation(t, p)
        n = self.degree() # degree of the HGM
        w = self.weight() # weight of the HGM
        sigma_k = self.sigma(p, k)
        for deg in range(0, n+1): # deg = degree(Frobenius polynomial)
            for c_p in ([sigma_k-deg] if gcd(p, k) == 1 else range(n-deg, sigma_k-deg+1)): # guess conductor exponents
                if deg == 0:
                    yield (c_p, 1)
                else:
                    for ele in IntegerVectors(deg, w+1).list():
                        if not all(ele[i]%2==0 for i in range(1, w+1, 2)):
                            continue
                        # i loops over the weight, ele[i] loops over the degree
                        candidate_polynomials = [signed_reverse_weil_polynomials(ele[i], p**i, i) for i in range(w+1)]
                        polys = itertools.product(*candidate_polynomials)

                        for euler_factor in polys:
                            yield (c_p, prod(euler_factor))
    
    def tame_conductor_euler_factor(self, t):
        """  
        Returns the conductor exponent and Euler factor at tame primes using Magma intrinsics 
        
        WARNING: Magma may return the wrong output 
        
        INPUT: 
        * "t" -- specialization point 
        """
        tame_primes = self.tame_primes(t)
        alpha_beta = self.alpha_beta()
        Hmagma = magma.HypergeometricData(self.alpha_beta()) # Magma version of self
        R.<T> = ZZ[]
        n = self.degree() # degree of HGM 
        tame_factors = {} # {p:(conductor exponent, Frobenius polynomial)}
        
        for p in tame_primes:
            p_Euler_factor = R(Hmagma.EulerFactor(1/t, p).sage())
            tame_factors[p]=(n-p_Euler_factor.degree(), p_Euler_factor)
       
        return tame_factors 
    
    def maximum_precision(self, t, prec=10):
        """
        Returns the number of Dirichlet coefficients needed in the L-series to compute the values L(s) using Magma with Precision=10 
        
        INPUT:
        * "t" -- rational number, specialization point
        * "prec" -- integer (default 10), number of decimial places precision in the computation of values L(s)
        """
        # Computes the maximum conductor exponent at p 
        wild_primes = self.wild_primes()
        wild_conductors_max = {}
        for p in wild_primes: 
            wild_conductors_max[p] = self.sigma(p, valuation(t, p))
        
        Hmagma = self.Hmagma() # Magma version of self
        
        with NamedTemporaryFile('w', delete=False) as f: 
            f.write("P<T> := PolynomialRing(Integers());\n");
            f.write("EF := [")
            comma = False
            for p,b in wild_conductors_max.items():
                if comma:
                    f.write(",")
                comma = True
                f.write("<{},{},1>".format(p,b))
            f.write("];")
            f.close()
            
            magma.load(f.name)
          
        bad_euler_factors_max = magma("EF")
        
        prec = Hmagma.LSeries(1/t, BadPrimes=bad_euler_factors_max, Identify=false, Precision=magma(prec)).LCfRequired()
        
        return 2**(ceil(log(prec.sage(),2)))
    

    def load_good_euler_factors_into_magma(self, t, N, chained=None, verbose=False):
        """
        Returns the conductor exponent and Euler factor at wild primes of self 
        
        INPUTs:
        * "t" -- rational number, specialization point 
        * "N" -- integer, the number of Dirichlet coefficients needed in the L-series
        """
        # Collect prime Frobenius traces.
        prime_traces = self.amortized_padic_H_values(t, N, chained=chained)
        if verbose:
            print("Computed prime Frobenius traces")
        
        wild_primes = self.wild_primes()
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
            mp = min(ceil(log(N,p)), n+1)
            l = prime_traces[p]*T + sum(prime_power_traces[p**f]*T**f/f for f in range(2, mp))
            l = l + O(T**mp)
            euler_factors[p] = exp(-l).polynomial()
        if verbose:
            print("Computed good Euler factors")
        # Write Euler factors to a temporary file to be read in my Magma.
        with NamedTemporaryFile('w', delete=False) as f: # for python 3.12 delete_on_closed
            f.write("P<T> := PolynomialRing(Integers());\n");
            f.write("EF := [")
            comma = False
            for p,b in euler_factors.items():
                if comma:
                    f.write(",")
                comma = True
                f.write("<{},{},Polynomial({})>".format(p,0,b.list()))
            f.write("];")
            f.close()
            if verbose:
                print("Wrote good Euler factors to file")

            # Use Magma to read the temporary file.

            magma.load(f.name)
            
            if verbose: 
                print("Loaded good Euler factors into Magma")
          
        euler_factors_magma = magma("EF")
        return euler_factors_magma
        
    
    def check_functional_equation_new(self, t, good_factors, bad_factors, prec=10, verbose=False):
        """
        Returns Magma's output of CFENew on the L-series with specified Euler factors 
        The output is close to 0 when the functional equation is satisfied.
        
        INPUTS: 
        * "t" -- rational number, specialization point 
        * "good_factors" -- Magma object of Euler factors at good primes
        * "bad_factors" -- (conductor exponent, Frobenius polynomial) at wild primes 
        * "prec" -- integer (default 10), number of decimial places precision in the computation of values L(s) 
        """
      
        Hmagma = self.Hmagma() # Magma version of self
        euler_factors_magma = good_factors 
        
        
        for p,b in bad_factors.items():
            with NamedTemporaryFile('w', delete=False) as f: # for python 3.12 delete_on_closed
                f.write("P<T> := PolynomialRing(Integers());\n");
                f.write("p_euler_factor :=")
                comma = False
                f.write("<{},{},Polynomial({})>;".format(p,b[0],b[1].list()))
                f.close()
            
                magma.load(f.name)
            euler_factors_magma = euler_factors_magma.Append(magma("p_euler_factor"))
        
        LSmagma = Hmagma.LSeries(1/t, BadPrimes=euler_factors_magma, Identify=false, Precision=magma(prec))
        cfe = LSmagma.CFENew()
        
        return cfe, LSmagma.LGetCoefficients(10)

    def wild_conductor_euler_factor(self, t, prec=10, verbose=False):
        """
        Returns the "plausible" conductor exponent and Euler factor at the wild primes of a HGM 
        
        INPUT:
        * "t" -- rational number, specialization point 
        * "prec" -- integer (default 10), number of decimial places precision in the computation of values L(s) and CFENew 
        """
        
        wild_primes = self.wild_primes()
        
        if verbose:
            print("The set of wild prime(s) is:", wild_primes)
            
        bad_conductor_euler_factors = itertools.product(*[self.candidate_euler_factor_conductor(p,t) for p in wild_primes])

        N = self.maximum_precision(t) # precision
        
        if verbose:
            print("Using %s precision in the L-series"%N)
            
        good_factors = self.load_good_euler_factors_into_magma(t, N, verbose = verbose)
        
        if verbose: 
            print("Computed %s good Euler factors"%(len(good_factors)))
        
        for i, ele in enumerate(bad_conductor_euler_factors, 1):
            candidate_bad_factors = dict((wild_primes[i],ele[i]) for i in range(len(wild_primes)))
            checkFE = self.check_functional_equation_new(t, good_factors, bad_factors=candidate_bad_factors, verbose=verbose)
            
            
            if checkFE[0] < 2**(-0.9*checkFE[0].sage().parent().precision()):
                if verbose:
                    print("%s seems to work: CFENew=%s"%(candidate_bad_factors, checkFE[0]))
                    print("Now recomputing CFNew doubling the precision")
                
                # double precision and check again
                N = self.maximum_precision(t, prec=20)
                good_factors = self.load_good_euler_factors_into_magma(t, N)
                checkFE = self.check_functional_equation_new(t, good_factors, bad_factors=candidate_bad_factors, prec=20)
                if checkFE[0] < 2**(-0.99*checkFE[0].sage().parent().precision()):
                    print("%s REALLY seems to work: CFENew=%s"%(candidate_bad_factors, checkFE[0]))
                    return candidate_bad_factors 