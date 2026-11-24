"""Bounded resynthesis of three point stars, retaining four fixed point stars."""
from pathlib import Path
from itertools import combinations
import subprocess, tempfile, time, json
import heawood_extensions as H

cadical=Path.home()/".elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical.exe"
rows=sorted(set(H.required)|H.maxneg)
expect={r:r in H.positive for r in rows}
neighbors={p:[l for v,l in H.edges[1:] if v==p] for p in range(7)}

def background(window,variant):
    gates=[]
    def gate(op,a,b):
        gates.append((op,a,b))
        return 13+len(gates)
    terms=[]
    available=list(window)+list(range(7,14))
    for p in range(7):
        if p in window: continue
        ls=neighbors[p]
        ls=ls[variant%len(ls):]+ls[:variant%len(ls)]
        acc=ls[0]
        for l in ls[1:]:
            acc=gate('or',acc,l)
            available.append(acc)
        terms.append(gate('and',p,acc))
    result=terms[0]
    for t in terms[1:]: result=gate('or',result,t)
    return gates,result,available

def evalw(gates,r):
    w=[bool(r & 1<<i) for i in range(14)]
    for op,a,b in gates: w.append((w[a] and w[b]) if op=='and' else (w[a] or w[b]))
    return w

def attempt(window,variant,limit):
    gates,out,available=background(window,variant)
    budget=24-len(gates)-1
    tests={}
    for r in rows:
        vals=evalw(gates,r)
        if vals[out]:
            assert expect[r]
            continue
        col=tuple(vals[i] for i in available)
        assert col not in tests or tests[col]==expect[r]
        tests[col]=expect[r]
    patterns=list(tests)
    variables={}
    def var(*key):
        if key not in variables: variables[key]=1+len(variables)
        return variables[key]
    clauses=[]
    n=len(available)
    for j in range(budget):
        op=var('and',j)
        sels=[[var('src',side,j,i) for i in range(n+j)] for side in range(2)]
        clauses.extend(sels)
        for a in range(n+j):
            for b in range(a): clauses.append([-sels[0][a],-sels[1][b]])
        for t,pat in enumerate(patterns):
            v=var('v',j,t); l,r=var('left',j,t),var('right',j,t)
            for side,operand in enumerate([l,r]):
                for i,s in enumerate(sels[side]):
                    if i<n: clauses.append([-s,operand if pat[i] else -operand])
                    else:
                        u=var('v',i-n,t)
                        clauses.extend([[-s,-operand,u],[-s,operand,-u]])
            clauses.extend([[-op,-v,l],[-op,-v,r],[-op,v,-l,-r],
                            [op,v,-l],[op,v,-r],[op,-v,l,r]])
    for t,p in enumerate(patterns):
        z=var('v',budget-1,t)
        clauses.append([z if tests[p] else -z])
    with tempfile.TemporaryDirectory(prefix='heawood-window-') as folder:
        cnf=Path(folder)/'window.cnf'
        cnf.write_text(f'p cnf {len(variables)} {len(clauses)}\n'+
                       '\n'.join(' '.join(map(str,c))+' 0' for c in clauses)+'\n',encoding='ascii')
        try:
            run=subprocess.run([str(cadical),'-q',str(cnf)],capture_output=True,timeout=limit)
        except subprocess.TimeoutExpired: return 'TIMEOUT',budget,len(tests)
    if run.returncode==20: return 'UNSAT',budget,len(tests)
    if run.returncode!=10: raise RuntimeError(run.stdout[-200:]+run.stderr[-200:])
    model={int(x) for l in run.stdout.splitlines() if l.startswith(b'v ') for x in l[2:].split() if int(x)>0}
    used=available.copy()
    for j in range(budget):
        a,b=[next(used[i] for i in range(n+j) if var('src',side,j,i) in model) for side in range(2)]
        gates.append(('and' if var('and',j) in model else 'or',a,b))
        used.append(13+len(gates))
    gates.append(('or',out,used[-1]))
    assert len(gates)==24
    for r in range(1<<14):
        value=evalw(gates,r)[-1]
        assert (r not in H.positive or value) and (r not in H.negative or not value)
    Path('heawood24-witness.json').write_text(json.dumps(gates),encoding='utf8')
    return 'SAT',budget,len(tests)

if __name__=='__main__':
    reps=[]
    side_group=[p for p in H.stabilizer if p[0]==0]
    for win in combinations(range(7),3):
        if win==min(tuple(sorted(p[i] for i in win)) for p in side_group): reps.append(win)
    print('représentants',len(reps),flush=True)
    for win in reps:
        status,budget,rows_tested=attempt(win,0,18)
        print(win,status,budget,rows_tested,flush=True)
        if status=='SAT': break

