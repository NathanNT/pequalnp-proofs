"""Check the independent degree-five rank certificate for the explicit sparse pair.

Run with Python 3.8 or later. All arithmetic is in F_101, with i mapped to 10.
See Research record.txt for the characteristic-zero argument.
"""

from collections import defaultdict
from itertools import permutations, product


PRIME = 101
I = 10
assert I * I % PRIME == PRIME - 1
C = -3 * (1 + I)
Y = [1, I, C, C, -I, -1, -C, -C] + [0] * 8
Z = [0, 0, C, -C, 0, 0, C, -C, 0, 0, 1, -I, 0, 0, I, -1]
B = [1 + (k // 4 == k % 4) for k in range(16)]
PERMS = [tuple(4 * i + col for i, col in enumerate(p)) for p in permutations(range(4))]


def rref(rows):
    """Return reduced nonzero rows and their pivot columns."""
    a = [[v % PRIME for v in row] for row in rows]
    pivots = []
    for j in range(len(a[0])):
        h = len(pivots)
        if h == len(a):
            break
        k = next((k for k in range(h, len(a)) if a[k][j]), None)
        if k is None:
            continue
        a[h], a[k] = a[k], a[h]
        inv = pow(a[h][j], -1, PRIME)
        a[h] = [inv * x % PRIME for x in a[h]]
        for k, row in enumerate(a):
            if k != h and row[j]:
                factor = row[j]
                a[k] = [(u - factor * v) % PRIME for u, v in zip(row, a[h])]
        pivots.append(j)
    return a[:len(pivots)], pivots


def monomials(degree, variables):
    if variables == 1:
        yield (degree,)
        return
    for i in range(degree + 1):
        for tail in monomials(degree - i, variables - 1):
            yield (i,) + tail


def direction_basis():
    normals = defaultdict(lambda: [0] * 16)
    for perm in PERMS:
        for fixed in perm:
            rest = [j for j in perm if j != fixed]
            for choices in product(range(3), repeat=3):
                value = 1
                for choice, j in zip(choices, rest):
                    value *= (B, Y, Z)[choice][j]
                normals[choices.count(1), choices.count(2)][fixed] += value
    rows, pivots = rref(normals.values())
    assert len(rows) == 8
    kernel = []
    for j in range(16):
        if j not in pivots:
            v = [0] * 16
            v[j] = 1
            for k, pivot in enumerate(pivots):
                v[pivot] = -rows[k][j] % PRIME
            kernel.append(v)
    basis = [Y, Z]
    for v in kernel:
        if len(rref(basis + [v])[1]) > len(basis):
            basis.append(v)
    assert len(basis) == 8
    return basis[2:]


def equations(representatives):
    mats = [B, Y, Z] + representatives
    coeffs = defaultdict(lambda: defaultdict(int))
    for perm in PERMS:
        for choices in product(range(len(mats)), repeat=4):
            value = 1
            for k, j in zip(choices, perm):
                value = value * mats[k][j] % PRIME
            exponent = tuple(choices.count(3 + k) for k in range(6))
            key = choices.count(1), choices.count(2), sum(exponent)
            coeffs[key][exponent] += value
    forms = []
    for key, form in coeffs.items():
        reduced = {m: a % PRIME for m, a in form.items() if a % PRIME}
        if key[2] == 0:
            assert not reduced or (key == (0, 0, 0) and list(reduced.values()) == [65])
        elif key[2] == 1:
            assert not reduced
        elif reduced:
            forms.append(reduced)
    assert sorted(sum(next(iter(f))) for f in forms) == [2] * 6 + [3] * 3 + [4]
    normal = [2, 3, 5, 7, 11, 13]
    forms.append({tuple(int(i == j) for i in range(6)): a for j, a in enumerate(normal)})
    return forms


def check_degree(forms, d):
    columns = list(monomials(d, 6))
    index = {m: j for j, m in enumerate(columns)}
    rows = []
    for form in forms:
        deg = sum(next(iter(form)))
        for extra in monomials(d - deg, 6):
            row = [0] * len(columns)
            for m, value in form.items():
                row[index[tuple(a + b for a, b in zip(m, extra))]] = value
            rows.append(row)
    rank = len(rref(rows)[1])
    print(f"Degree {d}: {len(rows)} rows, {len(columns)} monomials, rank {rank} modulo {PRIME}.")
    return rank


if __name__ == "__main__":
    forms = equations(direction_basis())
    assert check_degree(forms, 5) == 252
    print("All degree-five monomials are in the ideal after the extra hyperplane equation.")
