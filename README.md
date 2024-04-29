# amortizedHGM


Sage code supporting
 - \[ [arXiv](https://arxiv.org/abs/2005.13640) [DOI](https://doi.org/https://doi.org/10.2140/obs.2020.4.143) \] **Hypergeometric L-functions in average polynomial time** by Edgar Costa, Kiran Kedlaya and David Roe
 - [ [arXiv](https://arxiv.org/abs/2310.06971) ] **Hypergeometric L-functions in average polynomial time, II** by Edgar Costa, Kiran Kedlaya and David Roe


The previous version of the code was not a pip package, and can be found [here](https://github.com/edgarcosta/amortizedHGM/tree/arxiv/2005.13640).

This code depends on [pyrforest](https://github.com/edgarcosta/pyrforest).

# Install

```
sage -pip install --upgrade  git+https://github.com/edgarcosta/amortizedHGM.git@main
```

If you don't have permissions to install it system wide, please add the flag ``--user`` to install it just for you.

```
sage -pip install --user --upgrade git+https://github.com/edgarcosta/amortizedHGM.git@main
```

# Example
```
sage: from amortizedHGM import AmortizingHypergeometricDatamodp # the version of the first paper
....: H = AmortizingHypergeometricDatamodp(10**2,   cyclotomic=([4,2,2], [3,3]))
....: H.amortized_padic_H_values(1/5) # this uses the rforest library
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
 sage: H.amortized_padic_H_values(1/5, use_c=False) # this code uses AccRemForest
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
sage: from amortizedHGM import AmortizingHypergeometricData # the version of the second paper
sage: H = AmortizingHypergeometricData(cyclotomic=[[3,3],[2,1,1,1]])
sage: H.weight()
 2
sage: sage: H.compare(12, 314/159, vssage=True, vsmagma=False) # timings may vary
 2^12
 Amortized Gamma: 0.09 s
 Additional precomputation: 0.04 s
 Amortized HG: 0.07 s
 Sage:      18.23 s
 ```
