"""Search exact minimum monotone circuits and test for a dirty lift-fixed optimum."""
from itertools import combinations
from pathlib import Path
import argparse, json, subprocess, tempfile
import networkx as nx

def instance(graph, size, require_dirty, witnesses=False):
    n=len(graph)
    edges=[(1<<a)|(1<<b) for a,b in graph.edges()]
    good=lambda x:any((x&e)==e for e in edges)
    maximal=[x for x in range(1<<n) if not good(x) and all(good(x|(1<<i)) for i in range(n) if not x>>i&1)]
    rows=edges+maximal
    vmap={}; cs=[]
    def v(*key):
        if key not in vmap:vmap[key]=len(vmap)+1
        return vmap[key]
    def disj(z,terms):
        cs.append([-z,*terms])
        cs.extend([z,-t] for t in terms)
    for j in range(size):
        m=n+j
        op=v('and',j)
        sels=[[v('src',j,b,i) for i in range(m)] for b in range(2)]
        for choices in sels:
            cs.append(choices)
            cs.extend([-a,-b] for a,b in combinations(choices,2))
        for a in range(m):
            for b in range(a+1):cs.append([-sels[0][a],-sels[1][b]])
        if j+1<size:
            cs.append([v('src',k,b,m) for k in range(j+1,size) for b in range(2)])
        for t,row in enumerate(rows):
            out,left,right=v('out',j,t),v('left',j,t),v('right',j,t)
            for b,z in enumerate([left,right]):
                for i in range(m):
                    sel=sels[b][i]
                    if i<n:cs.append([-sel,z if row>>i&1 else -z])
                    else:
                        prev=v('out',i-n,t)
                        cs.extend([[-sel,-z,prev],[-sel,z,-prev]])
            cs.extend([[-op,-out,left],[-op,-out,right],[-op,out,-left,-right],
                       [op,out,-left],[op,out,-right],[op,-out,left,right]])
        if witnesses:
            for focus,indices in [(op,range(len(edges),len(rows))),(-op,range(len(edges)))]:
                for side,other in [('left','right'),('right','left')]:
                    marks=[]
                    for t in indices:
                        mark=v('essential',j,focus,side,t)
                        cs.extend([[-mark,v(side,j,t)],[-mark,-v(other,j,t)]])
                        marks.append(mark)
                    cs.append([-focus,*marks])
        if require_dirty:
            dirty=v('dirty',j)
            disj(dirty,[v('out',j,k) for k in range(len(edges),len(rows))])
            a,b=v('badside',j,0),v('badside',j,1)
            for side,z in enumerate([a,b]):
                for i,s in enumerate(sels[side]):
                    if i<n:cs.append([-s,z])
                    else:
                        prev=v('dirty',i-n)
                        cs.extend([[-s,-z,prev],[-s,z,-prev]])
            # An OR with one clean and one dirty operand admits an implicant lift.
            cs.extend([[op,-a,b],[op,a,-b]])
            marker=v('dirtyand',j)
            cs.extend([[-marker,op],[-marker,dirty]])
        # Adjacent independent gates have a canonical lexicographic topological order.
        if j:
            pivot=v('src',j,1,n+j-1)
            for a in range(n+j-1):
                for b in range(a):
                    cs.append([pivot,-v('src',j-1,0,a),-v('src',j,0,b)])
                for c in range(a+1,n+j-1):
                    for d in range(a+1,c):
                        cs.append([pivot,-v('src',j-1,0,a),-v('src',j,0,a),
                                   -v('src',j-1,1,c),-v('src',j,1,d)])
    if require_dirty:cs.append([v('dirtyand',j) for j in range(size)])
    for t in range(len(rows)):
        cs.append([v('out',size-1,t) if t<len(edges) else -v('out',size-1,t)])
    return vmap,cs,rows

def solve(graph,s,dirty,cutoff,witnesses=False):
    var,clauses,rows=instance(graph,s,dirty,witnesses)
    cadical=Path.home()/'.elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe'
    with tempfile.TemporaryDirectory(prefix="lift-search-") as name:
        p=Path(name)/'lift.cnf'
        p.write_text(f'p cnf {len(var)} {len(clauses)}\n'+'\n'.join(' '.join(map(str,c))+' 0' for c in clauses)+'\n',encoding='ascii')
        try:proc=subprocess.run([str(cadical),'-q',str(p)],capture_output=True,timeout=cutoff)
        except subprocess.TimeoutExpired:return 'UNKNOWN',None
    if proc.returncode==20:return 'UNSAT',None
    if proc.returncode!=10:raise RuntimeError(proc.stdout[-100:]+proc.stderr[-100:])
    model={int(x) for l in proc.stdout.splitlines() if l.startswith(b'v ') for x in l[2:].split() if int(x)>0}
    n=len(graph); gates=[]
    for j in range(s):
        a,b=[next(i for i in range(n+j) if var['src',j,k,i] in model) for k in range(2)]
        gates.append(('and' if var['and',j] in model else 'or',a,b))
    negatives=[0]*s
    for r in range(1<<n):
        vals=[bool(r>>i&1) for i in range(n)]
        goal=any(vals[a] and vals[b] for a,b in graph.edges)
        for j,(op,a,b) in enumerate(gates):
            vals.append(vals[a] and vals[b] if op=='and' else vals[a] or vals[b])
            if not goal and vals[-1]:negatives[j]+=1
        assert vals[-1]==goal
    if dirty:
        flags=[True]*n+[v>0 for v in negatives]
        assert any(op=='and' and flags[n+j] for j,(op,_,_) in enumerate(gates))
        assert all(flags[a]==flags[b] for op,a,b in gates if op=='or')
    return 'SAT',gates

def run(n,cutoff):
    results=[]
    for graph in nx.graph_atlas_g():
        if len(graph)!=n or not nx.is_connected(graph) or not nx.is_bipartite(graph):continue
        if any(len(set(graph[a])&set(graph[b]))>1 for a,b in combinations(graph.nodes(),2)):continue
        edge_list=sorted([list(e) for e in graph.edges()])
        e=len(edge_list)
        cover=min(k for k in range(n+1) if any(all(a in c or b in c for a,b in graph.edges) for c in combinations(range(n),k)))
        # A star program centred at a minimum cover gives this upper bound.
        upper=e+cover-1
        row={'edges':edge_list,'order':n,'star_upper':upper,'tests':[]}
        for s in range(n-1,upper+1):
            base,w=solve(graph,s,False,cutoff)
            if base=='UNSAT':
                row['tests'].append([s,base]);continue
            result,example=solve(graph,s,True,cutoff)
            row['tests'].append([s,base,result])
            if result=='SAT':row['dirty_witness']=example
            if base=='SAT':row['first_found']=s;break
        print(edge_list,row['tests'],flush=True)
        results.append(row)
        Path(f'lift-{n}.json').write_text(json.dumps(results,indent=1),encoding='utf8')
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('order',type=int);p.add_argument('cutoff',type=int)
    a=p.parse_args();run(a.order,a.cutoff)

