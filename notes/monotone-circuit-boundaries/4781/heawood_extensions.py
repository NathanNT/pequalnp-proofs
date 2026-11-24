from functools import cache
import networkx as nx

edges = [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),
         (3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),
         (6,8),(6,9),(6,11)]
N = 14
hole = (1<<0) | (1<<7)
def mask(vertices):
    return sum(1<<i for i in vertices)
def contains(s, t):
    return s & t == t
def image(s, perm):
    return mask(perm[i] for i in range(N) if s & (1<<i))
required = [mask(e) for e in edges[1:]]
positive = {s for s in range(1<<N) if any(contains(s, e) for e in required)}
negative = {s for s in range(1<<N) if (s not in positive and not contains(s,hole)) or s == hole}
unknown = set(range(1<<N)) - positive - negative
residual = [2, 12, 5, 9, 6, 11, 4, 13]
residual_mask = mask(residual)
F = nx.Graph(edges)
assert nx.utils.graphs_equal(F.subgraph(residual), nx.cycle_graph(residual))
free_cycle = {s for s in range(1<<N) if s and s & ~residual_mask == 0 and
              all(not contains(s, mask(e)) for e in F.subgraph(residual).edges())}
assert {s ^ hole for s in unknown} == free_cycle
assert len(unknown) == 46
maxneg = {s for s in negative if all((s | 1<<v) not in negative for v in range(N) if not s & 1<<v)}
assert negative == {s for s in range(1<<N) if any(contains(t,s) for t in maxneg)}
# If one extremal test is deleted, this explicit monotone predicate flips it alone on the test set.
for e in required:
    assert all(any(contains(x, q) for q in required if q!=e) == (x in positive and x!=e)
               for x in set(required) | maxneg)
for t in maxneg:
    assert all((x in positive or contains(x,t)) == (x in positive or x==t)
               for x in set(required) | maxneg)

def count_upsets(elements, le):
    n=len(elements)
    below=[sum(1<<j for j in range(n) if le(elements[j], elements[i])) for i in range(n)]
    above=[sum(1<<j for j in range(n) if le(elements[i], elements[j])) for i in range(n)]
    @cache
    def count(active):
        if not active: return 1
        indices=[i for i in range(n) if active & (1<<i)]
        i=max(indices,key=lambda j: min((below[j]&active).bit_count(),(above[j]&active).bit_count()))
        return count(active & ~below[i]) + count(active & ~above[i])
    return count((1<<n)-1)

def fixed_count(perm):
    orbits=[]
    remaining=unknown.copy()
    while remaining:
        s=next(iter(remaining))
        orbit=[]
        while s in remaining:
            remaining.remove(s)
            orbit.append(s)
            s=image(s,perm)
        orbits.append(orbit)
    return count_upsets(orbits,lambda a,b:any(contains(y,x) for x in a for y in b))
total = count_upsets(sorted(unknown), lambda a,b:contains(b,a))
stabilizer = [p for p in nx.algorithms.isomorphism.GraphMatcher(F,F).isomorphisms_iter()
              if image(hole,p)==hole]
fixed=[fixed_count(p) for p in stabilizer]
assert len(stabilizer)==16 and max(fixed)==total
assert sum(fixed)%16==0
print('lignes obligatoirement vraies, fausses, libres',len(positive),len(negative),len(unknown))
print('tests irrédundants',len(required),len(maxneg))
print('séparateurs monotones',total,'classes à symétrie près',sum(fixed)//16)
print('points fixes des 16 symétries',sorted(fixed))


# Count independently by fixing the values on singleton, quadruple and triple levels.
# With these levels fixed, every permitted pair can be selected independently.
def count_by_levels():
    count = 0
    for true_vertices in range(256):
        active = [s for s in range(1,256) if not s & true_vertices and all(
            (s & ((1<<i) | (1<<((i+1)%8)))).bit_count() < 2 for i in range(8))]
        pairs, triples, quads = ([s for s in active if s.bit_count()==n] for n in [2,3,4])
        for quad_selection in range(1<<len(quads)):
            false_quads=[q for i,q in enumerate(quads) if not quad_selection & (1<<i)]
            allowed_triples=[t for t in triples if not any(contains(q,t) for q in false_quads)]
            blocked=set(triples)-set(allowed_triples)
            allowed_pairs=[p for p in pairs if not any(contains(t,p) for t in blocked | set(false_quads))]
            supersets=[mask(i for i,t in enumerate(allowed_triples) if contains(t,p)) for p in allowed_pairs]
            for true_triples in range(1<<len(allowed_triples)):
                free_pairs=sum(contains(true_triples,t) for t in supersets)
                count+=1<<free_pairs
    return count

if __name__=="__main__":
    assert count_by_levels() == total
    print("Comptage indépendant par cardinalités confirmé")

