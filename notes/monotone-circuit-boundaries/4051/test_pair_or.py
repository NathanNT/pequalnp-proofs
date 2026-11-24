"""Check the OR-pair characterization by truth-table fibers, then a cubic witness."""
from itertools import combinations
from collections import Counter
import networkx as nx

def edgemask(edges):
    return tuple((1 << u) | (1 << v) for u, v in edges)

def has_edge(x, edges):
    return any(x & e == e for e in edges)

def local_test(n, edges, readers):
    neighborhoods = [0] * n
    for i in range(n):
        for e in readers:
            if e >> i & 1:
                neighborhoods[i] |= e ^ (1 << i)
    return all(has_edge(neighborhoods[v] | (e ^ (1 << v)), edges)
               for v in range(n) for e in edges if e >> v & 1)

def fibers_determine(f, observations):
    found = {}
    for y, bit in zip(observations, f):
        if y in found and found[y] != bit:
            return False
        found[y] = bit
    return True

def test_fibers():
    checked, feasible = 0, 0
    atlas = nx.graph_atlas_g()
    for n in range(6):
        pairs = edgemask(combinations(range(n), 2))
        graphs = [edgemask(g.edges()) for g in atlas if len(g) == n]
        functions = [[has_edge(x, g) for x in range(1 << n)] for g in graphs]
        views = [sum(1 << j for j, e in enumerate(pairs) if x & e)
                  for x in range(1 << n)]
        for h in range(1 << len(pairs)):
            readers = tuple(e for j, e in enumerate(pairs) if h >> j & 1)
            observations = [bits & h for bits in views]
            for g, f in zip(graphs, functions):
                answer = local_test(n, g, readers)
                assert answer == fibers_determine(f, observations)
                checked += 1
                feasible += answer
    return checked, feasible

if __name__ == '__main__':
    print('Pairs of graphs through five vertices; feasible:', test_fibers())
    g = nx.LCF_graph(24, [12,7,-7], 8)
    assert nx.girth(g) == 7 and all(d == 3 for _, d in g.degree())
    # Consecutive pairs in each block form two edges of the Hamiltonian cycle of G.
    gates = []
    for a in range(0, 24, 4):
        assert g.has_edge(a, a+1) and g.has_edge(a+2, a+3)
        gates += [(i,j) for i in (a,a+1) for j in (a+2,a+3)]
    assert len(gates) == 24 and set(Counter(p for e in gates for p in e).values()) == {2}
    assert local_test(24, edgemask(g.edges()), edgemask(gates))
    print('McGee: 24 inputs, 24 OR gates, each variable read twice. The local criterion holds.')
    # The K2,3 graph shows why excluding squares matters to the strict-degree theorem.
    example = nx.complete_bipartite_graph(2,3)
    for x in range(32):
        assert has_edge(x, edgemask(example.edges())) == bool(x & 3 and x & 28)
    print('K2,3: the two degree-three inputs each have a single raw OR reader.')
