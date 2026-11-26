"""
Turn a numerical hit of sym.py into an exact candidate: integer centred exponents (common denominator D) and
rational coefficients, re-solving the structure equations with the exponents frozen.
usage: rationalize.py logfile hitindex
"""
import os, re, sys, math, json
os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
import numpy as np
from fractions import Fraction as Fr
from flint import arb, ctx
from scipy.optimize import least_squares
import sym
def parse(logfile):
    hits=[]
    for line in open(logfile):
        m=re.match(r'HIT k (\d+) config (\d+) (\d+) .*p= (\[.*\])',line)
        if m: hits.append((int(m.group(2)),int(m.group(3)),eval(m.group(4))))
    return hits
def Fval(P,Sf,t,prec=600):
    ctx.prec=prec; t=arb(t); s=arb(0); tot=arb(0)
    for A,al,B,be in P:
        for sgn in (1,-1):
            u=arb(A)*(sgn*arb(al)*t).exp()+arb(B)*(sgn*arb(be)*t).exp()
            s+=sgn*u**3
            tot+=(abs(arb(A))*(sgn*arb(al)*t).exp()+abs(arb(B))*(sgn*arb(be)*t).exp())**3
    for c,mu in Sf:
        s+=arb(c)**3*((arb(mu)*t).exp()-(-arb(mu)*t).exp())**3
        tot+=abs(arb(c))**3*((arb(mu)*t).exp()+(-arb(mu)*t).exp())**3
    return s,tot
def try_D(npr,ns,p,D,verbose=False):
    k=2*npr+ns
    pairs,mus,T=sym.setup(p,npr,ns)
    allexp=[abs(v) for pr in pairs for v in pr]+mus
    scale=max(allexp)
    # integer centred exponents
    ip=[(round(al/scale*D),round(be/scale*D)) for al,be in pairs]; im=[round(mu/scale*D) for mu in mus]
    if any(a==b for a,b in ip) or any(m==0 for m in im): return None
    sl=[abs(3*a+j*(b-a)) for a,b in ip for j in range(4)]+[3*m for m in im]+[m for m in im]
    if 0 in sl or len(set(sl))<len(sl): return None
    # frozen exponents (in units where t' = t*scale/D ... use exponent = integer, roots rescaled)
    T2=[t*scale/D for t in T]
    fixed=[v for pr in ip for v in pr]+[math.log(m) for m in im]
    g0=[math.log(T2[0])]+[math.log(T2[i+1]-T2[i]) for i in range(len(T2)-1)]
    def r(g): return sym.res(np.concatenate([fixed,g]),npr,ns)
    try: sol=least_squares(r,np.array(g0),xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=400,diff_step=1e-7)
    except Exception as e: return None
    if sol.cost>1e-20: return None
    pfull=np.concatenate([fixed,sol.x])
    P,Sf,Tn=sym.extract(pfull,npr,ns)
    if sym.actual_changes(pfull,npr,ns)<2*k-1: return None
    return dict(D=D,ip=ip,im=im,P=P,Sf=Sf,T=Tn,cost=sol.cost)
def round_coeffs(res,digits):
    P,Sf=res['P'],res['Sf']
    allc=[abs(A) for A,_,B,_ in P]+[abs(B) for A,_,B,_ in P]+[abs(c) for c,_ in Sf]
    big=max(allc)
    def rd(v):
        v=v/big
        if v==0: return Fr(0)
        e=math.floor(math.log10(abs(v)))
        q=Fr(10)**(e-digits+1)
        return Fr(round(Fr(v)/q))*q
    P2=[(rd(A),a,rd(B),b) for (A,_,B,_),(a,b) in zip(P,res['ip'])]
    S2=[(rd(c),m) for (c,_),m in zip(Sf,res['im'])]
    return P2,S2
def changes(P2,S2,T):
    pts=[T[0]/2]+[(T[q]+T[q+1])/2 for q in range(len(T)-1)]+[T[-1]+0.5*(T[-1]-T[-2])]
    Pf=[(float(A),a,float(B),b) for A,a,B,b in P2]; Sf=[(float(c),m) for c,m in S2]
    vals=[Fval([(Fr(A),a,Fr(B),b) for A,a,B,b in P2] if False else Pf,Sf,t) for t in pts]
    sg=[1 if v[0]>0 else -1 for v in vals]
    marg=min(float((abs(v[0])/v[1]).mid()) for v in vals)
    return sum(1 for q in range(len(sg)-1) if sg[q]*sg[q+1]<0),marg,pts
if __name__=='__main__':
    hits=parse(sys.argv[1]); idx=int(sys.argv[2]); npr,ns,p=hits[idx]; k=2*npr+ns
    pairs,mus,T=sym.setup(p,npr,ns)
    print('hit',idx,'config',(npr,ns),'pairs',[(round(a,4),round(b,4)) for a,b in pairs],'mus',[round(m,4) for m in mus],'roots',[round(t,4) for t in T])
    for D in (8,12,16,24,32,48,64,96,128,192,256,384,512,768,1024,2048,4096,8192,16384):
        res=try_D(npr,ns,p,D)
        if res is None: continue
        out=None
        for digits in (2,3,4,5,6,8,10,12):
            P2,S2=round_coeffs(res,digits)
            ch,marg,pts=changes(P2,S2,res['T'])
            if ch>=2*k-1:
                out=(digits,P2,S2,marg,pts); break
        if out:
            digits,P2,S2,marg,pts=out
            print('D',D,'OK: coefficient digits',digits,'margin(min |F|/sum|terms|) %.2e'%marg)
            print('  pairs (A, alpha, B, beta):',[(str(A),a,str(B),b) for A,a,B,b in P2])
            print('  self (c, mu):',[(str(c),m) for c,m in S2])
            print('  roots t:',[round(t,6) for t in res['T']])
            json.dump(dict(k=k,npr=npr,ns=ns,D=D,pairs=[(str(A),a,str(B),b) for A,a,B,b in P2],selfs=[(str(c),m) for c,m in S2],roots=res['T'],pts=pts),open('cand_k%d_%s_%d_D%d.json'%(k,os.path.basename(sys.argv[1]).split('.')[0],idx,D),'w'))
            if len(sys.argv)>3: continue
            break
        else: print('D',D,'exponents OK but coefficient rounding failed')
