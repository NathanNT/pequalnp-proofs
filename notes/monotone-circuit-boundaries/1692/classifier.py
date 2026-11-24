"""Verify, by exhaustive order ideals, the negative rows of the order-three desk."""
from itertools import combinations
from pathlib import Path
from collections import Counter
import json

N = 13
def mask(indices):
    return sum(1 << i for i in indices)

def subsets(s):
    sub = s
    while True:
        yield sub
        if sub == 0:
            return
        sub = (sub - 1) & s

def immediate_subsets(points, lines):
    for i in range(N):
        if points & (1 << i):
            yield points ^ (1 << i), lines
        if lines & (1 << i):
            yield points, lines ^ (1 << i)

lines = [mask((j + k) % N for k in (0, 1, 3, 9)) for j in range(N)]
pencils = [mask(j for j, line in enumerate(lines) if line & (1 << i)) for i in range(N)]
def ext(points):
    return mask(j for j, line in enumerate(lines) if not line & points)

def triples_on(blocks):
    return {mask(triple) for block in blocks for triple in
            combinations([i for i in range(N) if block & (1 << i)], 3)}

collinear = triples_on(lines)
concurrent = triples_on(pencils)
quadrangles = [x for x in range(1 << N) if x.bit_count() == 4 and
               all((x & line).bit_count() <= 2 for line in lines)]
dual_quadrangles = [y for y in range(1 << N) if y.bit_count() == 4 and
                    all((y & pencil).bit_count() <= 2 for pencil in pencils)]
neg = {(x, y) for q in quadrangles for x in subsets(q) for y in subsets(ext(q))}
outside = {(x, y) for x in range(1 << N) for y in subsets(ext(x)) if (x, y) not in neg}
minimal = sorted(s for s in outside if all(t in neg for t in immediate_subsets(*s)))
expected = {(x, 0) for x in collinear} | {(0, y) for y in concurrent | set(dual_quadrangles)}
assert set(minimal) == expected
assert (len(neg), len(outside), len(collinear), len(concurrent), len(dual_quadrangles)) == (10362, 28368, 52, 52, 234)
# Direct verification across every independent pair gives a second check.
for x in range(1 << N):
    arc = all((x & line).bit_count() <= 2 for line in lines)
    for y in subsets(ext(x)):
        admissible = arc and y.bit_count() <= 3 and all((y & p).bit_count() <= 2 for p in pencils)
        assert ((x, y) in neg) == admissible
dual_triangles = {mask(c) for c in combinations(range(N), 3)} - concurrent
assert {ext(q) for q in quadrangles} == dual_triangles
assert len(dual_triangles) == len(quadrangles) == 234
print(len(neg), "entrées négatives forcées,", len(outside), "entrées indépendantes facultatives")
print("Obstructions minimales indépendantes", dict(Counter((x.bit_count(), y.bit_count()) for x,y in minimal)))
print("Bijection entre 234 quadrangles et 234 triples de droites non concourantes")

