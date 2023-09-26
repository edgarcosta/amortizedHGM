
from sage.arith.misc import previous_prime
from sage.misc.lazy_attribute import lazy_attribute
from sage.misc.cachefunc import cached_method
from sage.rings.fast_arith import prime_range
from sage.rings.integer_ring import ZZ

def base_shift(n):
    """
    INPUT:

    - ``n`` -- the length of a list ``base``

    OUTPUT:

    The index i so that when base is included as the base of a binary tree,
    the bottom layer is base[:i] and the nodes on the second layer are base[i:]

    EXAMPLES:

    The numbers 1..7 are arranged along the bottom of the tree as 1..6
    at the bottom layer and then the 7 at the layer above::

        sage: base_shift(7)
        6

    If given a power of 2, all entries are on the bottom layer::

        sage: base_shift(32)
        32

    If one more than a power of 2, then only two entries on the bottom layer::

        sage: base_shift(17)
        2
    """
    return 2 * n - next_power_of_2(n)

# some utils for trees
def left_child(r):
    return r % 2 == 0


def right_child(r):
    return r % 2 == 1


def next_power_of_2(n):
    """
    Returns the smallest integer power of 2 that is at least n.

    INPUT:

    - ``n`` -- an integer

    EXAMPLES::

        sage: next_power_of_2(13)
        16
        sage: next_power_of_2(1)
        1
        sage: next_power_of_2(16)
        16
        sage: next_power_of_2(17)
        32
    """
    if n <= 1:
        return ZZ(1)
    return ZZ(1) << (1 + (ZZ(n) - 1).exact_log(2))

def build_tree(base):
    """
    INPUT:

    - ``base`` -- a list of numbers (only requirement is that they can be multiplied)

    OUTPUT:

    A list of twice the length representing the binary tree with the given nodes at the base

    EXAMPLES::

        sage: tree = build_tree(list(range(1,14)))
        sage: tree
        [None,
         6227020800,
         40320,
         154440,
         24,
         1680,
         990,
         156,
         2,
         12,
         30,
         56,
         90,
         11,
         12,
         13,
         1,
         2,
         3,
         4,
         5,
         6,
         7,
         8,
         9,
         10]
        sage: print_bottom_tree(tree, levels=5)
                                      6227020800
                      40320                           154440
              24              1680            990             156
          2       12      30      56      90      11      12      13
        1   2   3   4   5   6   7   8   9   10

    This function can also be used to compute trees with other bases::

        sage: tree = build_tree([p^3 for p in prime_range(20)])
        sage: print_bottom_tree(tree, levels=4, spaces=10)
                                           912585499096480209000
                       9261000                                 98540708249269
             216                 42875               2924207             33698267
        8         27        125       343       1331      2197      4913      6859
    """
    # We want the nodes to be in order when read left-to-right, so we need to cycle
    cut = base_shift(len(base))
    half_layer = product_layer(base[:cut])
    result = half_layer + base[cut:] + base[:cut]
    current = half_layer + base[cut:]  # now current has length a power of 2
    while len(current) > 1:
        current = product_layer(current)
        result = current + result
    return [None] + result

def product_layer(layer):
    """
    INPUT:

    - ``layer`` -- a list of even length

    OUTPUT:

    A list of half the length whose terms are the products of the consecutive terms of the input

    EXAMPLES::

        sage: layer = list(range(1,15))
        sage: product_layer(layer)
        [2, 12, 30, 56, 90, 132, 182]
    """
    return [
        layer[j] * layer[k]
        for (j, k) in zip(range(0, len(layer), 2), range(1, len(layer), 2))
    ]

def print_bottom_tree(tree, levels=2, spaces=4, print_shift=0):
    """
    This utility function is used to print trees for visualization

    INPUT:

    - ``tree`` -- a list of even length; the 0th entry is ignored.
        The 1st entry is the root, then the children of the nth node are at 2n and 2n+1
    - ``levels`` -- how many levels of the tree to print (starting at the bottom)
    - ``spaces`` -- how many spaces are allocated to each entry along the bottom of the tree.
        Will look best if this is even
    - ``print_shift`` -- used for recursion; how many spaces to add at the beginning of the bottom line.

    EXAMPLES::

        sage: tree = build_tree(list(range(1,8)))
        sage: print_bottom_tree(tree)
          2       12      30      7
        1   2   3   4   5   6
        sage: print_bottom_tree(tree, levels=3)
              24              210
          2       12      30      7
        1   2   3   4   5   6
        sage: print_bottom_tree(tree, levels=4)
                      5040
              24              210
          2       12      30      7
        1   2   3   4   5   6
    """
    if levels > 0:
        n = len(tree) // 2
        shift = base_shift(n)
        print_bottom_tree(
            tree[:-shift], levels - 1, 2 * spaces, print_shift=print_shift + spaces // 2
        )
        print(
            " " * print_shift + "".join(str(elt).ljust(spaces) for elt in tree[-shift:])
        )




class ShadowForest(object):
    def __init__(self, forest, multiplier):
        self.forest = forest
        self.multiplier = multiplier

    def gamma(self, a, p):
        return self.forest.gamma(a * self.multiplier, p)


# A class for an accumulating remainder tree
class AccRemForest(object):
    """
    This class collects the different accumulating remainder trees used for the same values of `N`, `b` and `e`.

    INPUT:

    - ``N`` -- the upper bound on the primes computed (`p < N`)

    - ``b`` -- the denominator of the value of `x` for which we can compute gamma values

    - ``e` -- the p-adic precision of the results
    """


    def __init__(self, N, cut_functions, bottom_generator, prec, primes):
        self.N = N = ZZ(previous_prime(N) + 1)
        self.prec = ZZ(prec)
        # largest factorial we might need
        self.cut_functions = cut_functions
        self.bottom_generator = bottom_generator
        self.end_node = max(cut_func(N-1) for cut_func in cut_functions.values())
        self._primes = primes
        #_filter = prime_filter

    @lazy_attribute
    def _primes(self):
        r"""
        Primes up to `N` satisfying the filter

        EXAMPLES::

            sage: ARF = AccRemForest(20, {None: lambda x: x}, range, 1, lambda p: p > 3)
            sage: ARF._primes
            [5, 7, 11, 13, 17, 19]
        """
        return [p for p in prime_range(self.N) if self.prime_filter(p)]

    @lazy_attribute
    def primes(self):
        """
        Primes up to `N` satisfying the prime filter, reordered so that they are in order when read from the base of the moduli tree

        EXAMPLES::

            sage: ARF = AccRemForest(20, {None: lambda x: x}, range, 1, lambda p: p > 3)
            sage: ARF.primes
            [17, 19, 5, 7, 11, 13]
            sage: print_bottom_tree(ARF._moduli_tree, spaces=8)
                1500625         418161601       83521           130321
            625     2401    14641   28561
            sage: [p^4 for p in ARF.primes]
            [83521, 130321, 625, 2401, 14641, 28561]
        """
        # We use as strange order so that the primes are in order when read left to right
        P = self._primes
        cut = base_shift(len(P))
        return P[cut:] + P[:cut]

    @lazy_attribute
    def _value_tree(self):
        """
        The tree of products used to compute factorials

        EXAMPLES::

            sage: ARF =AccRemForest(20, {None: lambda x: x}, range, 1, lambda p: p > 3)
            sage: print_bottom_tree(ARF._value_tree, levels=6)
                                                                          263130836933693530167218012160000000
                                          20922789888000                                                  12576278705767096320000
                          40320                           518918400                       29654190720                     424097856000
                  24              1680            11880           43680           116280          255024          491400          863040
              2       12      30      56      90      132     182     240     306     380     462     552     650     756     870     992
            1   2   3   4   5   6   7   8   9   10  11  12  13  14  15  16  17  18  19  20  21  22  23  24  25  26  27  28  29  30  31  32
            sage: factorial(32)
            263130836933693530167218012160000000
        """
        return build_tree(self.bottom_generator(self.end_node))

    def _value_tree_bottom(self):
        """
        An in-order list of the nodes of the value tree, for debugging.
        """
        V = self._value_tree
        m = len(V) // 2
        V = V[m:]
        cut = base_shift(m)
        return V[m-cut:] + V[:m-cut]

    def partial_factorial(self, a, b, M=None):
        """
        Return prod(range(a,b)) % M

        EXAMPLES::

            sage: ARF = AccRemForest(20, {None: lambda x: x}, range, 1, lambda p: p > 3)
            sage: ARF.partial_factorial(5,10)
            15120
            sage: prod(range(5,10))
            15120

        TESTS::

            sage: for a in range(1, ARF.end_node):
            ....:     for b in range(a+1, ARF.end_node+1):
            ....:         assert ARF.partial_factorial(a,b) == prod(range(a,b))
            ....:         for M in [5^2, 7^4, 11^6]:
            ....:             assert ARF.partial_factorial(a,b,M) == prod(range(a,b)) % M
        """
        if a >= b:
            return ZZ(1)
        assert a > 0 and b > a, "a = %s, b = %s" % (a,b)
        # TODO: using M and self.M for two things; confusing
        def nodes(r, s):
            if r.exact_log(2) == s.exact_log(2):
                return nodes_balanced(r, s)
            else:
                assert r.exact_log(2) == s.exact_log(2) + 1
                if left_child(r):
                    return nodes_balanced(r // 2, s)
                else:  # right child
                    # even if the last child this makes sense
                    return [r] + nodes_balanced((r + 1) // 2, s)

        def nodes_balanced(r, s):
            # Include both r and s
            # print(r, s)
            if r > s:
                N = []
            elif r == s:
                N = [r]
            elif left_child(r):
                if right_child(s):
                    N = nodes_balanced(r // 2, s // 2)
                else:
                    N = nodes_balanced(r // 2, (s - 1) // 2) + [s]
            elif right_child(s):
                N = [r] + nodes_balanced((r + 1) // 2, s // 2)
            else:
                N = [r] + nodes_balanced((r + 1) // 2, (s - 1) // 2) + [s]
            return N

        ans = 1
        cut = base_shift(self.end_node)
        # a and b are 1-indexed, but Python wants them 0-indexed
        a -= 1
        b -= 1
        if a < cut:
            aa = self.end_node + (self.end_node - cut) + a
        else:
            aa = self.end_node + (a - cut)
        #assert a + 1 == self._value_tree[aa]
        b = b - 1  # shift by one for the end of the range
        if b < cut:
            bb = self.end_node + (self.end_node - cut) + b
        else:
            bb = self.end_node + (b - cut)
        #assert b + 1 == self._value_tree[bb]
        for n in nodes(aa, bb):
            # TODO: for our asymptotic runtime estimate, this should be a product tree
            ans *= self._value_tree[n]
            if M is not None:
                ans = ans % M
        return ans

    def factorial(self, b, M=None):
        """
        Return prod(1, b) % M

        EXAMPLES::

            sage: ARF = AccRemForest(20, {None: lambda x: x}, range, 1, lambda p: p > 3)
            sage: ARF.factorial(6)
            720
            sage: ARF.factorial(6, 11) == 720 % 11
            True
        """
        # TODO: this special case is because we check a > b in partial_factorial code
        if b == 0:
            return ZZ(1)
        return self.partial_factorial(1, b + 1, M)

    @lazy_attribute
    def _moduli_tree(self):
        """
        The tree computing products of p^(2e) for sequences of primes less than N.

        Note that this tree will be smaller than the value tree.

        EXAMPLES::

            sage: ARF = AccRemForest(20, {None: lambda x: x}, range, 1, lambda p: p > 3)            sage: print_bottom_tree(ARF._moduli_tree, spaces=12, levels=4)
                                                      6830089845471557190150625
                              627503752500625                                 10884540241
                  1500625                 418161601               83521                   130321
            625         2401        14641       28561
        """
        return build_tree([p ** self.prec for p in self._primes])

    @cached_method
    def tree(self, k=None):
        r"""
        An accumulating remainder tree that computes the values
        `\Gamma(ceil(kp/b)) mod p^{2e}` for `p < N`.

        INPUT:

        - ``k`` -- a key in the ``cut_functions`` dictionary

        EXAMPLES::

            sage: N, b, e, k = 15, 3, 4, 2
            sage: ARF = AccRemForest(N, {k: lambda p: ceil(k*p/b)}, lambda x: [elt for elt in range(1, x + 1)], e, lambda p: p > b)
            sage: ARF._primes
            [5, 7, 11, 13]
            sage: print_bottom_tree([elt if elt is None else str(elt.factor()) for elt in ARF._moduli_tree], spaces=20, levels=3)
                                          5^4 * 7^4 * 11^4 * 13^4
                      5^4 * 7^4                               11^4 * 13^4
            5^4                 7^4                 11^4                13^4
            sage: print_bottom_tree(ARF.tree(k)._rem_tree, spaces=8)
                6               5040
            6       24      5040    11759
            sage: [factorial(ceil(k*p/b) - 1) % p^(2*e) for p in ARF._primes]
            [6, 24, 5040, 11759]
        """
        return AccRemTree(self, self.cut_functions[k])

    def tree_bottom(self, k=None):
        r"""
        A dictionary giving the value `\Gamma(ceil(kp/b)) mod p^{prec}` when provided the key `p`.
        """
        return self.tree(k)._rem_tree_bottom




class AccRemTree(object):
    """
    INPUT:

    - ``forest`` -- an ``AccRemForest`` object
    - ``end`` -- a function of p that gives the end of the product interval
    """
    def __init__(self, forest, end):
        self.forest = forest
        self.end = end

    @lazy_attribute
    def _rem_tree(self):
        """
        A tree where each node
        """
        F = self.forest
        P = F.primes

        def left_most_child(r):
            while r < len(P):
                r = 2 * r
            return r

        def prime_at_position(c):
            return P[c - len(P)]

        result = [None, F.factorial(self.end(prime_at_position(left_most_child(1))) - 1)]
        for i in range(2, 2 * len(P)):
            if left_child(i):
                res = result[i // 2] % F._moduli_tree[i]
                q = prime_at_position(left_most_child(i // 2))
                # print("Reducing node %s  as %s!modulo %s obtaining %s" % (i//2, self.end(q) - 1, F._moduli_tree[i], res))
                #assert self.end(q) > 100 or factorial(self.end(q) - 1) % F._moduli_tree[i] == res
            else:
                a = left_most_child(i // 2)
                b = left_most_child(i)
                p, q = prime_at_position(a), prime_at_position(b)
                M = F._moduli_tree[i]
                #print((i, i//2), (a,b), (p,q), (self.end(p), self.end(q)))
                res = (result[i // 2] * F.partial_factorial(self.end(p), self.end(q), M)) % M
                # print("Computing node %s as %s! mod %s (p=%s, q=%s), obtaining %s" % (i, self.end(q) - 1, M.factor(), p, q, res))
                #assert self.end(q) > 100 or factorial(self.end(q) - 1) % M == res
            result.append(res)
        return result

    @lazy_attribute
    def _rem_tree_bottom(self):
        P = self.forest.primes
        return {p: self._rem_tree[i] for i, p in enumerate(P, len(P))}

    @lazy_attribute
    def _p_to_position(self):
        P = self.forest.primes
        return {p: i for i, p in enumerate(P, len(P))}

    def gamma(self, p):
        """
        Returns the value of Gamma_p(ceil(kp/b)) mod p^(2e)
        """
        return self._rem_tree_bottom[p]



