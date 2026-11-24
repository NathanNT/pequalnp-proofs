"""Test four Fourier directions for absence of any two-dimensional level space."""

from functools import cache
from itertools import combinations, product
from math import comb

from check_fourier_quotient import PAIRS, P, coefficients


def normal_powers(relation):
    # relation is monic of degree four. Reduce 1,z,...,z^7 modulo it.
    powers = [[int(i == j) for j in range(4)] for i in range(4)]
    for _ in range(4):
        last = powers[-1]
        powers.append([((last[j-1] if j else 0)-last[3]*relation[j]) % P
                       for j in range(4)])
    return powers


def spans_algebra(cross, r, s):
    pivots = {}
    for poly in cross:
        for a, b in product(range(4), repeat=2):
            v = [0]*16
            for i, j, coeff in poly:
                for h, u in enumerate(r[a+i]):
                    if u:
                        for k, w in enumerate(s[b+j]):
                            v[4*h+k] += coeff*u*w
            v = [n % P for n in v]
            for i in range(16):
                if not v[i]:
                    continue
                if i not in pivots:
                    inv = pow(v[i], -1, P)
                    pivots[i] = [n*inv % P for n in v]
                    break
                factor = v[i]
                v = [(x-factor*y) % P for x, y in zip(v, pivots[i])]
            if len(pivots) == 16:
                return True
    return False


@cache
def excludes_plane(a, b, c, e):
    cubic = coefficients((a,b,c,e), 3)
    if not cubic or any(indices != (0,0,0) for indices,_ in cubic):
        return False
    # The cubic forces the a-coordinate to vanish. The remaining plane
    # would have an equation B=v*C+w*E since the B-axis is not quartic-zero.
    terms = coefficients((b,c,e), 4)
    relations = [[0]*5, [0]*5]
    cross = [[], [], []]
    for indices, coeff in terms:
        i, j, k = (indices.count(h) for h in range(3))
        if not k:
            relations[0][i] += coeff
        if not j:
            relations[1][i] += coeff
        for t in range(i+1):
            c_degree = j+t
            if 0 < c_degree < 4:
                cross[c_degree-1].append((t, i-t, coeff*comb(i,t)))
    if not relations[0][4] % P:
        return False
    inv = pow(relations[0][4], -1, P)
    r, s = (normal_powers([v*inv % P for v in rel]) for rel in relations)
    return spans_algebra(cross, r, s)


def check():
    count = 0
    exceptional = []
    for chart in product(*PAIRS):
        a = next(m for m in chart if m in ((0,2),(0,4)))
        order_four = [m for m in chart if m[0] % 2 and m[1] in (0,3)]
        found = any(excludes_plane(a, b, c, e)
                    for b in order_four
                    for c,e in combinations([m for m in chart if m not in (a,b)], 2))
        if found:
            count += 1
        else:
            exceptional.append(chart)
    print(f"{count}/1024 charts exclude dimension nine even after any one-direction extension.")
    print(f"{len(exceptional)} charts undetermined by this four-direction test.")
    if exceptional:
        print("First undetermined chart:", exceptional[0])
    return exceptional


if __name__ == "__main__":
    assert not check()
