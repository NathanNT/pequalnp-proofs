"""Exclude 9-planes in all opposite-character choices for the 4-by-6 pencil."""

from collections import Counter
from functools import cache
from itertools import combinations, combinations_with_replacement, permutations, product
from math import factorial, prod


P = 97
CHARACTERS = list(product(range(4), range(6)))
PAIRS = []
for a, b in CHARACTERS:
    opposite = (-a % 4, -b % 6)
    if (a, b) < opposite:
        PAIRS.append(((a, b), opposite))


def partitions(items):
    if not items:
        yield ()
        return
    first, *rest = items
    for partition in partitions(rest):
        yield ((first,),) + partition
        for i, block in enumerate(partition):
            yield partition[:i] + ((first,) + block,) + partition[i + 1:]


@cache
def distinct_character_sum(order, weights):
    if sum(weights) % order:
        return 0
    value = 0
    for partition in partitions(weights):
        if all(sum(block) % order == 0 for block in partition):
            value += prod(order * (-1)**(len(block)-1) * factorial(len(block)-1)
                          for block in partition)
    return value


def coefficients(modes, degree):
    result = []
    for indices in combinations_with_replacement(range(len(modes)), degree):
        rows = tuple(sorted(modes[i][0] for i in indices))
        cols = tuple(sorted(modes[i][1] for i in indices))
        value = distinct_character_sum(4, rows) * distinct_character_sum(6, cols)
        if value:
            divisor = prod(factorial(m) for m in Counter(indices).values())
            coefficient, remainder = divmod(value, divisor)
            assert not remainder
            result.append((indices, coefficient))
    return result


def restrict_line(terms, a, b, degree):
    result = [0]*(degree+1)
    for indices, coefficient in terms:
        term = [coefficient]
        for i in indices:
            term = [x*a[i] + y*b[i] for x, y in zip(term+[0], [0]+term)]
        result = [(x+y) % P for x, y in zip(result, term)]
    return result


def trim(poly):
    poly = list(poly)
    while poly and poly[-1] == 0:
        poly.pop()
    return poly


def coprime_projective(f, g):
    if not (f[-1] or g[-1]):
        return False
    a, b = trim(f), trim(g)
    while b:
        inv = pow(b[-1], -1, P)
        while len(a) >= len(b):
            shift = len(a)-len(b)
            factor = a[-1]*inv % P
            for i, value in enumerate(b):
                a[shift+i] = (a[shift+i]-factor*value) % P
            a = trim(a)
        a, b = b, a
    return len(a) == 1


def desk_value(matrix, k):
    return sum(prod(matrix[r][c] for r, c in zip(rows, cols))
               for rows in combinations(range(4), k)
               for cols in permutations(range(6), k)) % P


def check():
    assert len(PAIRS) == 10
    count = mixed = 0
    # 5 generates F_97^*. The two Fourier roots have orders four and six.
    z4, z6 = pow(5, 24, P), pow(5, 16, P)
    assert pow(z4, 2, P) == pow(z6, 3, P) == P-1 and z6 != P-1
    for modes in product(*PAIRS):
        cubic, quartic = (coefficients(modes, k) for k in (3, 4))
        # These two axes are available in every chart. On their span the cubic
        # and quartic are nonzero multiples of the two distinct pure powers.
        a = [int(m in ((0,2),(0,4))) for m in modes]
        b = [int(m in ((1,0),(3,0))) for m in modes]
        f = restrict_line(cubic, a, b, 3)
        g = restrict_line(quartic, a, b, 4)
        assert f[0] and not any(f[1:]) and g[4] and not any(g[:4])
        assert coprime_projective(f, g)
        # Compare both coefficient tensors against the original desk equations
        # at an independent point involving every character of the chart.
        v = list(range(1, len(modes)+1))
        matrix = [[sum(h*pow(z4, u*i, P)*pow(z6, w*j, P)
                       for h, (u, w) in zip(v, modes)) % P
                   for j in range(6)] for i in range(4)]
        assert [desk_value(matrix, k) for k in (1, 2, 3, 4)] == [
            0, 0, *(sum(c * prod(v[i] for i in indices) for indices, c in terms) % P
                    for terms in (cubic, quartic))]
        count += 1
        if max(Counter(w for _, w in modes).values()) < 4:
            mixed += 1
    print(f"{count}/1024 charts excluded; {mixed} with injective contrast and no pure row.")
    assert count == 1024


if __name__ == "__main__":
    check()
