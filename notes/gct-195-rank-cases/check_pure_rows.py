"""Exact coefficient checks for the pure-row obstruction in L-gct-195."""

from collections import Counter
from itertools import combinations, permutations
from math import prod


ROWS = range(4)
COLS = range(6)
PROFILE = (3, 3, 3, -1)


def linear_coefficient(degree, pure_row):
    """Coefficient of Y in F_degree(A+Y), indexed by y column and f monomial."""
    coeff = Counter()
    for rows in combinations(ROWS, degree):
        if pure_row not in rows:
            continue
        weight = prod(PROFILE[i] for i in rows if i != pure_row)
        slot = rows.index(pure_row)
        for cols in permutations(COLS, degree):
            other = tuple(sorted(cols[:slot] + cols[slot + 1:]))
            coeff[cols[slot], other] += weight
    return coeff


def check_linear_coefficients():
    from math import factorial

    for row in ROWS:
        for k in range(4):
            factor = factorial(k) * sum(
                prod(PROFILE[i] for i in chosen)
                for chosen in combinations([i for i in ROWS if i != row], k)
            )
            assert factor != 0
            expected = Counter({
                (j, monomial): factor for j in COLS
                for monomial in combinations([h for h in COLS if h != j], k)
            })
            assert linear_coefficient(k + 1, row) == expected


def sixth_root_sum(exponents):
    """Sum powers of a primitive sixth root in Z[X]/(X^2-X+1)."""
    powers = ((1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1))
    terms = [powers[n % 6] for n in exponents]
    return tuple(sum(v[i] for v in terms) for i in range(2))


def check_quartic():
    # f runs over all six sixth roots. Homogeneity supplies the common scale.
    for i, j in combinations(ROWS, 2):
        other = [h for h in ROWS if h not in (i, j)]
        scalar = prod(PROFILE[h] for h in other)
        exponents = (
            2 * cols[i] + 2 * cols[j] + sum(cols[h] for h in other)
            for cols in permutations(COLS, 4)
        )
        actual = tuple(scalar * v for v in sixth_root_sum(exponents))
        assert actual == (-36 * scalar, 0) and actual != (0, 0)


def check_nontriple_witness():
    # f consists of the five fifth roots and zero. The sum of all five roots
    # vanishes, so a residue count with all five entries equal evaluates to zero.
    for k in range(1, 5):
        counts = Counter(sum(cols) % 5 for cols in permutations(range(5), k))
        assert len({counts[i] for i in range(5)}) == 1
    # Products involving the sixth (zero) entry contribute zero.
    # No two nonzero entries have quotient a primitive cube root.
    assert all(3 * (i - j) % 5 != 0 for i, j in permutations(range(5), 2))


if __name__ == "__main__":
    check_linear_coefficients()
    check_quartic()
    check_nontriple_witness()
    print("PASS: 16 symbolic mixed coefficients, 6 quartic obstructions, fifth-root witness.")
