"""
f*g+1 with trinomials f,g (real exponents), prescribed 9 roots, in a divided-difference basis that stays well
conditioned when exponents of f or of g merge (confluent limit).
  f = sum_i u_i phi_i,  g = sum_k v_k psi_k,   phi/psi = Newton divided-difference basis of exp(e t) on the exponents.
  F = sum_{i,k} M_ik phi_i psi_k + 1 ;  M determined by the 9 roots ;  need rank(M) = 1.
"""
import sys, math, numpy as np
from flint import arb, arb_mat, ctx
from scipy.optimize import least_squares
ctx.prec=400
def ddbasis(E,t):
    # Newton divided differences of e -> exp(e t) at nodes E[0..2] (arb); returns [f[E0], f[E0,E1], f[E0,E1,E2]]
    f=[(e*t).exp() for e in E]
    d01=(f[1]-f[0])/(E[1]-E[0]); d12=(f[2]-f[1])/(E[2]-E[1])
    d012=(d12-d01)/(E[2]-E[0])
    return [f[0],d01,d012]
def setup(p):
    m,x1,x2,y1,y2=[max(float(v),1e-60) for v in p[:5]]
    al=[arb(0),arb(x1),arb(x1)+arb(x2)]; be=[arb(m),arb(m)+arb(y1),arb(m)+arb(y1)+arb(y2)]
    T=[0.0,1.0]
    for g in p[5:12]: T.append(T[-1]+math.exp(g))
    return al,be,T
def Mmat(p):
    al,be,T=setup(p)
    rows=[]
    for t in T:
        t=arb(t); ph=ddbasis(al,t); ps=ddbasis(be,t)
        rows.append([ph[i]*ps[k] for i in range(3) for k in range(3)])
    A=arb_mat(9,9,[x for r in rows for x in r]); b=arb_mat(9,1,[arb(-1)]*9)
    x=A.solve(b)
    return [[x[3*i+k,0] for k in range(3)] for i in range(3)], al,be,T
def res(p):
    try: M,al,be,T=Mmat(p)
    except Exception: return np.full(9,1e3)
    nrm=sum(M[i][k]*M[i][k] for i in range(3) for k in range(3))
    r=[]
    for (i,j) in ((0,1),(0,2),(1,2)):
        for (k,l) in ((0,1),(0,2),(1,2)):
            r.append(float(((M[i][k]*M[j][l]-M[i][l]*M[j][k])/nrm).mid()))
    return np.array(r)
def actual_count(p,verbose=False):
    M,al,be,T=Mmat(p)
    # best rank one approx via the largest row/column
    Mf=np.array([[float(M[i][k].mid()) for k in range(3)] for i in range(3)])
    i0,k0=np.unravel_index(np.argmax(abs(Mf)),Mf.shape)
    u=[M[i][k0]/M[i0][k0] for i in range(3)]; v=[M[i0][k] for k in range(3)]
    def F(t):
        t=arb(t); ph=ddbasis(al,t); ps=ddbasis(be,t)
        return sum(u[i]*ph[i] for i in range(3))*sum(v[k]*ps[k] for k in range(3))+1
    pts=[T[0]-0.5*(T[1]-T[0])]+[(T[k]+T[k+1])/2 for k in range(len(T)-1)]+[T[-1]+0.5*(T[-1]-T[-2])]
    sg=[1 if F(t)>0 else -1 for t in pts]
    return sum(1 for k in range(len(sg)-1) if sg[k]*sg[k+1]<0)
if __name__=='__main__':
    seed=int(sys.argv[1]); nt=int(sys.argv[2]); conf=sys.argv[3] if len(sys.argv)>3 else 'free'
    rng=np.random.default_rng(seed); nh=0; best=1e9
    lo=np.array([1e-6,0,0,0,0]+[-6]*7); hi=np.array([50,50,50,50,50]+[3]*7)
    for trial in range(nt):
        ex=np.exp(rng.normal(0,1.2,5)); ex[0]=math.exp(rng.normal(-1,1.5))
        if conf=='gconf': ex[3]=ex[4]=1e-9
        if conf=='fconf': ex[1]=ex[2]=1e-9
        p0=np.concatenate([ex,rng.normal(-0.5,0.7,7)])
        p0=np.clip(p0,lo+1e-12,hi-1e-12)
        try: r=least_squares(res,p0,bounds=(lo,hi),xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=300,diff_step=1e-7)
        except Exception as e: continue
        best=min(best,r.cost)
        if r.cost<1e-20:
            cnt=actual_count(r.x)
            print('CAND seed',seed,'trial',trial,'cost %.2e'%r.cost,'actual sign changes',cnt,'p=',repr([float(v) for v in r.x]),flush=True)
            if cnt>=9:
                nh+=1
                if nh>=3: break
        elif trial%25==0: print('trial',trial,'cost %.2e best %.2e'%(r.cost,best),flush=True)
    print('done',seed,'hits',nh,'best',best,flush=True)
