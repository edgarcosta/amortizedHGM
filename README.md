# amortizedHGM


Sage code supporting 
 - **Hypergeometric L-functions in average polynomial time** by Edgar Costa, Kiran Kedlaya and David Roe
 
Available at [arXiv:2005.13640](https://arxiv.org/abs/2005.13640)
 and to appear in the proceedings of the 2020 Algorithmic Number Theory Symposium
 
The code will run significantly faster if linked against the library [rforest](https://math.mit.edu/~drew/)

```
sage: from hgm import AmortizingHypergeometricData
....: H = AmortizingHypergeometricData(10**2,   cyclotomic=([4,2,2], [3,3]))
....: H.amortized_padic_H_values(1/5)
Compiling hgm_misc.pyx...
Compiling average_poly.pyx...
{11: 9,
 13: 9,
 17: 13,
 19: 13,
 23: 21,
 29: 2,
 31: 25,
 37: 4,
 41: 0,
 43: 35,
 47: 29,
 53: 39,
 59: 54,
 61: 57,
 67: 59,
 71: 62,
 73: 65,
 79: 75,
 83: 2,
 89: 83,
 97: 6}
 sage: H.amortized_padic_H_values(1/5, use_c=True) # this uses the rforest library
 {11: 9,
 13: 9,
 17: 13,
 19: 13,
 23: 21,
 29: 2,
 31: 25,
 37: 4,
 41: 0,
 43: 35,
 47: 29,
 53: 39,
 59: 54,
 61: 57,
 67: 59,
 71: 62,
 73: 65,
 79: 75,
 83: 2,
 89: 83,
 97: 6}
 ```
