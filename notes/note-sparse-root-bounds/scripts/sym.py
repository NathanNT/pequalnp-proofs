"""
Anti-reciprocal ansatz (t = log x, centred exponents):
   F(t) = sum_pairs [u_p(t)^3 - u_p(-t)^3] + sum_self 8 c_s^3 sinh(mu_s t)^3,     u_p(t) = A e^{alpha t} + B e^{beta t}
F is odd; with k = 2*npairs + nself cubes the Descartes bound 4k-1 is attained iff F has 2k-1 positive zeros.
F = sum_m C_m sinh(E_m t) over the 2k "slot" exponents; 2k-1 prescribed positive roots determine C up to scale.
Structure conditions (sign-exact):  pair slots y_j = 3 alpha + j (beta-alpha), h_j = C(y_j)/2:  h1^2=3 h0 h2, h2^2=3 h1 h3;
                                      self slots 3mu, mu:  C(mu) = -3 C(3mu).
usage: sym.py npairs nself seed tlimit [maxhits]
"""
import os, time
os.environ.setdefault('OPENBLAS_NUM_THREADS','1'); os.environ.setdefault('OMP_NUM_THREADS','1')
import sys, math, numpy as np
from flint import arb_mat, arb, ctx
from scipy.optimize import least_squares
def setup(p,npr,ns):
    pairs=[(p[2*i],p[2*i+1]) for i in range(npr)]
    mus=[math.exp(v) for v in p[2*npr:2*npr+ns]]
    k=2*npr+ns
    T=[]; t=0.0
    for g in p[2*npr+ns:2*npr+ns+2*k-1]:
        t+=math.exp(g); T.append(t)
    return pairs,mus,T
def slots(pairs,mus):
    sl=[]
    for i,(al,be) in enumerate(pairs):
        for j in range(4): sl.append((3*al+j*(be-al),('p',i,j)))
    for i,mu in enumerate(mus):
        sl.append((3*mu,('s',i,0))); sl.append((mu,('s',i,1)))
    return sl
def solve(p,npr,ns,prec=192):
    pairs,mus,T=setup(p,npr,ns)
    sl=slots(pairs,mus); n=len(sl)
    ab=sorted(abs(e) for e,_ in sl)
    if ab[0]<1e-7 or min(np.diff(ab))<1e-7: return None
    while True:
        ctx.prec=prec
        rows=[[ (arb(e)*arb(t)).sinh() for e,_ in sl] for t in T]
        A=arb_mat(n-1,n-1,[rows[r][c] for r in range(n-1) for c in range(n-1)])
        b=arb_mat(n-1,1,[-rows[r][n-1] for r in range(n-1)])
        try:
            x=A.solve(b); C=[x[q,0] for q in range(n-1)]+[arb(1)]
            if all(abs(v.rad())<=abs(v.mid())*arb(1e-20) for v in C): break
        except Exception: pass
        prec*=2
        if prec>1600: return None
    return {key:C[q] for q,(e,key) in enumerate(sl)},pairs,mus,T
def res(p,npr,ns):
    out=solve(p,npr,ns)
    if out is None: return np.full(2*npr+ns,1.0)
    C=out[0]; r=[]
    for i in range(npr):
        h0,h1,h2,h3=[C[('p',i,j)] for j in range(4)]
        r.append(float(((h1*h1-3*h0*h2)/(h1*h1+3*abs(h0*h2))).mid()))
        r.append(float(((h2*h2-3*h1*h3)/(h2*h2+3*abs(h1*h3))).mid()))
    for i in range(ns):
        c3,c1=C[('s',i,0)],C[('s',i,1)]
        r.append(float(((c1+3*c3)/(abs(c1)+3*abs(c3))).mid()))
    return np.array(r)
def cbrt(v): return math.copysign(abs(v)**(1/3),v)
def extract(p,npr,ns):
    C,pairs,mus,T=solve(p,npr,ns,384)
    P=[]
    for i,(al,be) in enumerate(pairs):
        h0=float(C[('p',i,0)].mid())/2; h3=float(C[('p',i,3)].mid())/2
        P.append((cbrt(h0),al,cbrt(h3),be))
    Sf=[(cbrt(float(C[('s',i,0)].mid())/2),mu) for i,mu in enumerate(mus)]
    return P,Sf,T
def actual_changes(p,npr,ns):
    P,Sf,T=extract(p,npr,ns); ctx.prec=384
    def F(t):
        t=arb(t); s=arb(0)
        for A,al,B,be in P:
            s+=(arb(A)*(arb(al)*t).exp()+arb(B)*(arb(be)*t).exp())**3-(arb(A)*(-arb(al)*t).exp()+arb(B)*(-arb(be)*t).exp())**3
        for c,mu in Sf: s+=8*arb(c)**3*((arb(mu)*t).sinh())**3
        return s
    pts=[T[0]/2]+[(T[q]+T[q+1])/2 for q in range(len(T)-1)]+[T[-1]+0.5*(T[-1]-T[-2] if len(T)>1 else T[-1])]
    sg=[1 if F(t)>0 else -1 for t in pts]
    return sum(1 for q in range(len(sg)-1) if sg[q]*sg[q+1]<0)
if __name__=='__main__':
    npr=int(sys.argv[1]); ns=int(sys.argv[2]); seed=int(sys.argv[3]); tlimit=float(sys.argv[4]); maxhits=int(sys.argv[5]) if len(sys.argv)>5 else 3
    k=2*npr+ns; rng=np.random.default_rng(seed); nh=0; best=1e9; t0=time.time(); start=0; cnt={}
    while time.time()-t0<tlimit:
        start+=1
        p0=np.concatenate([rng.normal(0,2.0,2*npr),rng.normal(0,0.7,ns),rng.normal(-1.2,0.7,2*k-1)])
        try: r=least_squares(lambda p: res(p,npr,ns),p0,xtol=1e-14,ftol=1e-14,gtol=1e-14,max_nfev=300,diff_step=1e-6)
        except Exception as e: continue
        best=min(best,r.cost)
        if r.cost<1e-18:
            try: ch=actual_changes(r.x,npr,ns)
            except Exception as e: ch=-1
            cnt[ch]=cnt.get(ch,0)+1
            if ch>=2*k-1:
                nh+=1; print('HIT k',k,'config',npr,ns,'seed',seed,'start',start,'cost %.2e'%r.cost,'p=',repr([float(v) for v in r.x]),flush=True)
                if nh>=maxhits: break
    print('done k',k,'config',(npr,ns),'seed',seed,'starts',start,'hits',nh,'best %.2e'%best,'converged-by-sign-changes',dict(sorted(cnt.items())),flush=True)
