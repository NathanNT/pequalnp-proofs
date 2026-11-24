"""Exhaustive test of sensitivity projections. NetworkX is used only to enumerate graphs."""
from collections import Counter
from itertools import combinations
from math import prod
import networkx as nx

def masks(mask):
    sub = mask
    while True:
        yield sub
        if sub == 0:
            return
        sub = (sub-1) & mask

def check(g, counts):
    n = len(g)
    adj = [sum(1 << j for j in g[i]) for i in range(n)]
    allbits = (1 << n)-1
    def edge(x):
        return any(x >> i & 1 and adj[i] & x for i in range(n))
    independent = {x for x in range(1 << n) if not edge(x)}
    for v, nv in enumerate(adj):
        available = allbits ^ (1 << v)
        degree = nv.bit_count()
        if not degree:
            continue
        rows = [x for x in masks(available) if x in independent and edge(x | (1 << v))]
        counts['vertices'] += 1
        simple_branches = all((nv & adj[p]).bit_count() <= 1 for p in range(n) if p != v and not (nv >> p & 1))
        minimum = n
        first_missing = 0
        for s in masks(available):
            projected = {x & s for x in rows}
            for t in masks(s):
                counts['patterns'] += 1
                blocked = s
                for p in range(n):
                    if t >> p & 1:
                        blocked |= adj[p]
                feasible = t in independent and bool((t & nv) or (nv & ~blocked))
                assert feasible == (t in projected)
                if t in independent and not feasible:
                    if s.bit_count() < minimum:
                        minimum, first_missing = s.bit_count(), 0
                    if s.bit_count() == minimum:
                        first_missing += 1
        if simple_branches:
            assert minimum == degree
            counts['local_threshold'] += 1
        if nx.girth(g) >= 6:
            assert first_missing == prod(len(g[p]) for p in g[v])
            counts['product'] += 1

if __name__ == '__main__':
    counts = Counter()
    for g in nx.graph_atlas_g():
        if len(g) <= 6:
            counts['graphs'] += 1
            check(g, counts)
    print(dict(counts))
    # Cubic girth-seven McGee graph. Generate only codimension-three assignments that
    # may block sensitivity; verify the absence or existence of an explicit extension.
    g = nx.LCF_graph(24,[12,7,-7],8)
    assert nx.girth(g) == 7 and all(d == 3 for _, d in g.degree())
    for v in g:
        nv = set(g[v])
        missing = []
        for support in combinations(set(g)-{v},3):
            for k in range(4):
                for subset in combinations(support,k):
                    t=set(subset)
                    if any(g.has_edge(a,b) for a,b in combinations(t,2)):
                        continue
                    if t & nv:
                        continue
                    if any(a not in support and all(not g.has_edge(a,p) for p in t) for a in nv):
                        continue
                    missing.append((support,subset))
        assert len(missing) == 27
    print('McGee: 24 centres, 27 independent minimal-size obstructions per centre.')
