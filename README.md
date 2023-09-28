# amortizedHGM


Sage code supporting
 - **Hypergeometric L-functions in average polynomial time** by Edgar Costa, Kiran Kedlaya and David Roe

Available at [arXiv:2005.13640](https://arxiv.org/abs/2005.13640)
 and appeared in the proceedings of the 2020 Algorithmic Number Theory Symposium

Note: the previous version of the code was not a pip package, and can be found [here](https://github.com/edgarcosta/amortizedHGM/tree/arxiv/2005.13640).

# Install

```
sage -pip install --upgrade  git+https://github.com/edgarcosta/amortizedHGM.git@master
```

If you don't have permissions to install it system wide, please add the flag ``--user`` to install it just for you.

```
sage -pip install --upgrade  git+https://github.com/edgarcosta/amortizedHGM.git@master
```


# Example
```
sage: from amortizedHGM import AmortizingHypergeometricDatamodp # the version of the first paper
....: H = importAmortizingHypergeometricDatamodp(10**2,   cyclotomic=([4,2,2], [3,3]))
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
 ```
