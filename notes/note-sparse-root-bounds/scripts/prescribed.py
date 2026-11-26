"""
Prescribed-roots search.  A signomial with n+1 exponents is determined up to scale by n prescribed simple positive
roots; its coefficients then alternate in sign.  We look for (exponents, roots) such that this coefficient vector has the
required algebraic structure (three cubes of binomials, or f*g+1 with trinomials).  A zero of the residuals inside a
sign-feasible chamber is a genuine example attaining Descartes' bound.

usage: prescribed.py cubes|fg  seed  ntrials
"""
import sys, math, itertools, random
import numpy as np
from flint import arb_mat, arb, ctx
from scipy.optimize import least_squares
ctx.prec = 200

def coeffs(E, T):
    """coefficient vector (as floats of logs and signs) of sum_j c_j exp(E_j t) vanishing at all t in T; len(E)=len(T)+1.
       normalised c_last = 1.  returns list of arb"""
    n=len(T)
    A=arb_mat(n,n,[ (arb(E[j])*arb(T[r])).exp() for r in range(n) for j in range(n)])
    b=arb_mat(n,1,[ -(arb(E[n])*arb(T[r])).exp() for r in range(n)])
    x=A.solve(b)
    return [x[j,0] for j in range(n)]+[arb(1)]

def logabs(v):
    return float(abs(v).log().mid())
def sgn(v):
    return 1 if v>0 else (-1 if v<0 else 0)

# ---------- three cubes of binomials ----------
def cubes_setup(p):
    # p: a0,d0,a1,d1,a2,d2 (6) then gaps (10) of roots (t1=0); normalisation: a0=0 fixed -> p has 5 exponent params
    d0=math.exp(p[0]); a1=p[1]; d1=math.exp(p[2]); a2=p[3]; d2=math.exp(p[4])
    blocks=[[3*0+j*d0 for j in range(4)],[3*a1+j*d1 for j in range(4)],[3*a2+j*d2 for j in range(4)]]
    gaps=[math.exp(g) for g in p[5:15]]
    T=[0.0]
    for g in gaps: T.append(T[-1]+g)
    return blocks,T
def cubes_res(p):
    blocks,T=cubes_setup(p)
    flat=[(e,i,j) for i,b in enumerate(blocks) for j,e in enumerate(b)]
    flat.sort()
    E=[e for e,_,_ in flat]
    if min(np.diff(E))<1e-9: return np.full(6,1e3)
    try:
        c=coeffs(E,T)
    except Exception:
        return np.full(6,1e3)
    h={ (i,j):c[k] for k,(e,i,j) in enumerate(flat)}
    r=[]
    for i in range(3):
        l=[logabs(h[(i,j)]) for j in range(4)]
        r.append(2*l[1]-l[0]-l[2]-math.log(3)); r.append(2*l[2]-l[1]-l[3]-math.log(3))
    return np.array(r)
def cubes_feasible(p):
    blocks,T=cubes_setup(p)
    flat=[(e,i,j) for i,b in enumerate(blocks) for j,e in enumerate(b)]; flat.sort()
    rank={(i,j):k for k,(e,i,j) in enumerate(flat)}
    return all((rank[(i,0)]-rank[(i,2)])%2==0 and (rank[(i,1)]-rank[(i,3)])%2==0 for i in range(3))

# ---------- f*g + 1, trinomials ----------
def fg_setup(p):
    m=math.exp(p[0]); x1=math.exp(p[1]); x2=math.exp(p[2]); y1=math.exp(p[3]); y2=math.exp(p[4])
    al=[0,x1,x1+x2]; be=[m,m+y1,m+y1+y2]
    gaps=[math.exp(g) for g in p[5:12]]      # 9 roots: t1=0, t9 = t1+... (8 gaps) ; scale fixed by first gap = 1
    T=[0.0,1.0]
    for g in gaps: T.append(T[-1]+g)
    return al,be,T
def fg_res(p):
    al,be,T=fg_setup(p)
    flat=[(0.0,-1,-1)]+[(al[i]+be[j],i,j) for i in range(3) for j in range(3)]
    flat.sort()
    E=[e for e,_,_ in flat]
    if min(np.diff(E))<1e-9: return np.full(4,1e3)
    try: c=coeffs(E,T)
    except Exception: return np.full(4,1e3)
    L={(i,j):logabs(c[k]) for k,(e,i,j) in enumerate(flat)}
    return np.array([L[(0,0)]+L[(k,l)]-L[(0,l)]-L[(k,0)] for k in (1,2) for l in (1,2)])
def fg_feasible(p):
    al,be,T=fg_setup(p)
    flat=[(0.0,-1,-1)]+[(al[i]+be[j],i,j) for i in range(3) for j in range(3)]; flat.sort()
    rank={(i,j):k for k,(e,i,j) in enumerate(flat)}
    return all((rank[(0,0)]+rank[(k,l)]-rank[(0,l)]-rank[(k,0)])%2==0 for k in (1,2) for l in (1,2))

if __name__=='__main__':
    mode=sys.argv[1]; seed=int(sys.argv[2]); nt=int(sys.argv[3])
    rng=np.random.default_rng(seed)
    best=None; hits=0
    for trial in range(nt):
        if mode=='cubes':
            p0=np.concatenate([rng.normal(0,1,1),rng.normal(0,1.5,1),rng.normal(0,1,1),rng.normal(0,1.5,1),rng.normal(0,1,1),rng.normal(-1,0.7,10)])
            res,feas=cubes_res,cubes_feasible
        else:
            p0=np.concatenate([rng.normal(-1,1.5,1),rng.normal(0,1.2,4),rng.normal(0,0.7,7)])
            res,feas=fg_res,fg_feasible
        if not feas(p0): continue
        try:
            r=least_squares(res,p0,xtol=1e-13,ftol=1e-13,gtol=1e-13,max_nfev=300,diff_step=1e-6)
        except Exception as e:
            continue
        ok=feas(r.x)
        if best is None or (ok and r.cost<best[0]): best=(r.cost,r.x.copy(),ok)
        if ok and r.cost<1e-16:
            hits+=1
            print('HIT',mode,'seed',seed,'trial',trial,'cost',r.cost,'p',repr(list(map(float,r.x))),flush=True)
            if hits>=3: break
        elif trial%20==0:
            print('trial',trial,'cost %.3e'%r.cost,'feasible' if ok else 'left chamber','best %.3e'%(best[0] if best else -1),flush=True)
    print('done',mode,'seed',seed,'hits',hits,'best cost',None if best is None else best[0],flush=True)
