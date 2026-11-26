"""
EXACT certification (integer/rational arithmetic only) that a candidate sum of k cubes of binomials has >= 4k-1
distinct positive roots: evaluate the polynomial at 4k rational points and check that the signs alternate.
usage: exact_check.py cand.json [decimals]
"""
import sys, json, math
from fractions import Fraction as Fr
def build(c):
    """returns list of binomials [(coef, exp), (coef, exp)] with nonnegative integer exponents"""
    cent=[abs(v) for A,a,B,b in c['pairs'] for v in (a,b)]+[m for _,m in c['selfs']]
    h=max(cent)
    gs=[]
    for A,a,B,b in c['pairs']:
        A=Fr(A); B=Fr(B)
        gs.append([(A,h+a),(B,h+b)]); gs.append([(-A,h-a),(-B,h-b)])
    for cc,m in c['selfs']:
        cc=Fr(cc); gs.append([(cc,h+m),(-cc,h-m)])
    return gs,h
def expand(gs):
    terms={}
    for (A,a),(B,b) in gs:
        for j,cf in enumerate((1,3,3,1)):
            e=(3-j)*a+j*b; terms[e]=terms.get(e,Fr(0))+cf*A**(3-j)*B**j
    return dict(sorted(terms.items()))
def sign_at(terms,x):
    # x = Fraction p/q ; sign of sum c_e x^e  = sign of sum c_e p^e q^(deg-e)
    p,q=x.numerator,x.denominator; deg=max(terms)
    den=1
    for v in terms.values(): den=den*v.denominator//math.gcd(den,v.denominator)
    s=0
    for e,v in terms.items(): s+=int(v*den)*p**e*q**(deg-e)
    return (s>0)-(s<0)
if __name__=='__main__':
    c=json.load(open(sys.argv[1])); dec=int(sys.argv[2]) if len(sys.argv)>2 else 7
    gs,h=build(c); terms=expand(gs); k=c['k']
    print('k =',k,' binomials (coef, exponent):')
    for g in gs: print('   ',[(str(a),e) for a,e in g])
    print('expanded: %d monomials, degree %d'%(len(terms),max(terms)))
    signs=[(v>0)-(v<0) for v in terms.values()]
    print('Descartes sign changes of coefficient sequence:',sum(1 for i in range(len(signs)-1) if signs[i]*signs[i+1]<0))
    # sample points: exp(t) for t in pts (and reciprocals), rounded to `dec` decimals
    up=[Fr(round(math.exp(t)*10**dec),10**dec) for t in c['pts']]
    pts=sorted([1/x for x in up]+up)
    sg=[sign_at(terms,x) for x in pts]
    ch=sum(1 for i in range(len(sg)-1) if sg[i]*sg[i+1]<0)
    print('sample points (increasing):',[str(x) if x.denominator==10**dec or True else float(x) for x in pts][:3],'...')
    print('exact signs:',sg)
    print('EXACT sign changes at %d rational points: %d  => at least %d distinct positive roots (Descartes bound %d)'%(len(pts),ch,ch,4*k-1))
    json.dump(dict(binomials=[[(str(a),e) for a,e in g] for g in gs],points=[str(x) for x in pts],signs=sg),open(sys.argv[1].replace('.json','_exact.json'),'w'))
