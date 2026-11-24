"""Exact cyclic and asymmetric permanent-plane certificates. Requires SymPy 1.14."""
from itertools import combinations, permutations
from math import factorial
from sympy import Matrix, Poly, QQ, Rational, Symbol, expand, factor, groebner, ones, prod, rem, symbols

a,b,c,d,e,f,p,q,r,w = symbols("a b c d e f p q r w")
abc, deF, fixed_vars = (a,b,c), (d,e,f), (p,q,r)
indices = tuple(range(4))


def eigenmatrix(a,b,c,first,second):
    return Matrix([[a,b*second,b*first,c], [b*second,a*first,b,c*first],
                   [b*first,b,a*second,c*second], [c,c*first,c*second,0]])


def fixed_matrix(p,q,r):
    return Matrix([[p,q,q,r],[q,p,q,r],[q,q,p,r],[r,r,r,-3*p-6*q-6*r]])


def permanent(M):
    return sum(prod(M[i,pi[i]] for i in indices) for pi in permutations(indices))


def coefficient(*matrices):
    # Select distinct rows in each term of the permanent; the other entries are ones.
    numerator = sum(prod(M[i,pi[i]] for M,i in zip(matrices,rows))
                    for pi in permutations(indices)
                    for rows in permutations(indices,len(matrices)))
    divisor = prod(factorial(matrices.count(M)) for j,M in enumerate(matrices)
                   if M not in matrices[:j])
    return factor(rem(expand(numerator),w*w+w+1,w)/divisor)


def forms():
    P = eigenmatrix(a,b,c,w,-1-w)
    N = eigenmatrix(d,e,f,-1-w,w)
    F = fixed_matrix(p,q,r)
    U = coefficient(P,P,P)
    V = coefficient(N,N,N)
    assert expand(U.xreplace(dict(zip(abc,deF)))-V) == 0
    assert expand(U-(a**3+6*a*a*c+3*a*b*b-6*a*b*c+3*a*c*c+2*b**3+6*b*c*c)) == 0
    return dict(U=U,V=V,Q=coefficient(P,N),R=coefficient(P,P,N,N),
                QF=coefficient(F,F),CF=coefficient(F,F,F),PF=coefficient(F,F,F,F),
                S=coefficient(P,P,P,F),Sminus=coefficient(N,N,N,F),
                Cmix=coefficient(P,N,F),Dmix=coefficient(P,N,F,F))


def charts(coords):
    for i,var in enumerate(coords):
        yield {**dict.fromkeys(coords[:i],0),var:1}


def basis(eqs,variables):
    if not variables:
        return [1] if any(x != 0 for x in eqs) else []
    return list(groebner(eqs,*variables,domain=QQ,order="grevlex"))


def check_pure_components(F):
    for coords,eqs in ((fixed_vars,[F[k] for k in ("QF","CF","PF")]),
                       (abc,[F["U"].diff(v) for v in abc])):
        for chart in charts(coords):
            variables=[k for k in coords if k not in chart]
            assert basis([v.subs(chart) for v in eqs],variables)==[1]


def minors2(M):
    return [M.extract(i,j).det() for i in combinations(range(3),2)
            for j in combinations(range(3),2)]


def check_mixed_planes(F):
    # Each point in these projective charts parametrizes a pair of eigenlines.
    eqs=[F["Q"]/12,F["R"]/3,F["U"],F["V"]]
    MA=Matrix([F[k] for k in ("Q","U","R")]).jacobian(abc)
    MB=Matrix([F[k] for k in ("Q","V","R")]).jacobian(deF)
    MH=Matrix([F[k] for k in ("Cmix","S","Sminus")]).jacobian(fixed_vars)
    for i,left in enumerate(charts(abc)):
        for j,right in enumerate(charts(deF)):
            chart=left|right
            variables=[v for v in abc+deF if v not in chart]
            eq=[v.subs(chart) for v in eqs]
            if i!=j:
                assert basis(eq,variables)==[1]
                continue
            for M in (MA,MB):
                assert basis(eq+minors2(M.subs(chart)),variables)==[1]
            if i==0:
                G=groebner(eq,*variables,order="grevlex",domain=QQ).fglm("lex")
                assert len(G.polys)==4
                # A monic triangular basis solves b,c,e in terms of f.
                for poly,var in zip(G.polys[:3],(b,c,e)):
                    assert (poly.as_expr()-var).free_symbols <= {f}
                univariate=Poly(G.polys[-1].as_expr(),f,domain=QQ)
                assert univariate.degree()==30 and univariate.gcd(univariate.diff()).degree()==0
                assert basis(eq+[MH.subs(chart).det()],variables)==[1]
                assert basis(eq+[b-e,c-f],variables)==[1]
                assert basis(eq+[1-b+c,1-e+f],variables)==[1]
            elif i==1:
                G=groebner(eq,*variables,domain=QQ,order="lex")
                assert list(G)==[c+f,f**2+Rational(1,3)]
            else:
                assert eq==[0,0,0,0]


def check_mixed_direction(F):
    # The conic of fixed components, projected from a rational point.
    O=(-11,3,-1)
    QF=F["QF"]
    assert QF.subs(dict(zip(fixed_vars,O)))==0
    assert Matrix([QF.diff(v) for v in fixed_vars]).jacobian(fixed_vars).det()!=0
    h=Symbol("h")
    for left in list(charts(abc))[:2]:
        for Y in ((0,1,h),(0,0,1)):
            qy=QF.subs(dict(zip(fixed_vars,Y)))
            oy=QF.subs(dict(zip(fixed_vars,[o+y for o,y in zip(O,Y)])))-qy
            coords=[expand(qy*o-oy*y) for o,y in zip(O,Y)]
            chart=left|dict(zip(fixed_vars,coords))
            variables=[v for v in (b,c) if v not in left]+([h] if h in Y else [])
            def put(v):
                return Poly(v.subs(chart,simultaneous=True),*variables,domain=QQ)
            def cross(u,v):
                return [u[(i+1)%3]*v[(i+2)%3]-u[(i+2)%3]*v[(i+1)%3] for i in range(3)]
            def contract(form,vector):
                return sum(put(coeff)*prod(val**i for val,i in zip(vector,powers))
                           for powers,coeff in Poly(form,*deF).terms())
            def new_basis(equations):
                return basis([v.as_expr() for v in equations],variables)
            M=[[put(F[k].diff(v)) for v in deF] for k in ("Q","Cmix","Dmix")]
            det=sum(s*t for s,t in zip(cross(M[0],M[1]),M[2]))
            G=new_basis([put(F["U"]),put(F["S"]),det])
            for j,k in combinations(range(3),2):
                if G==[1]:
                    break
                v=cross(M[j],M[k])
                G=new_basis([Poly(t,*variables,domain=QQ) for t in G]+[contract(F["R"],v)])
                if G==[1]:
                    break
                mixed=put(F["PF"])*contract(F["V"],v)-put(F["CF"])*contract(F["Sminus"],v)
                G=new_basis([Poly(t,*variables,domain=QQ) for t in G]+[mixed])
            assert G==[1]
    star={a:0,b:0,c:1}
    assert expand(F["Q"].subs(star)-12*(-d+e))==0
    assert expand(F["R"].subs(star).subs(e,d)-18*d*d)==0
    assert F["V"].subs({d:0,e:0})==0 and F["Sminus"].subs({d:0,e:0})==0


def check_asymmetric_line():
    M=Matrix([[0,-1,-1,0],[-1,0,2,-1],[-1,2,0,1],[0,-1,1,0]])
    N=Matrix([[0,-3,3,2],[-3,0,0,-1],[3,0,0,-1],[2,-1,-1,0]])
    A=M+2*N
    x,t=symbols("x t")
    z=symbols("z:10")
    pairs=list(combinations_with_diagonal())
    D=Matrix(4,4,lambda i,j:z[pairs.index(tuple(sorted((i,j))))])
    P=Poly(permanent(ones(4)+x*A+t*D)-24,x,t)
    eq=[P.coeff_monomial(x**k*t) for k in range(4)]+[z[1]]
    reduced,_=Matrix([[v.coeff(k) for k in z] for v in eq]).rref()
    assert reduced[:,:5] == Matrix.eye(5)
    sub={z[i]:-sum(reduced[i,j]*z[j] for j in range(5,10)) for i in range(5)}
    equations=[v.subs(sub) for mon,v in P.terms() if mon[1]>=2]
    for ix,chart in enumerate(charts(z[5:])):
        G=basis([k.subs(chart) for k in equations],list(z[6+ix:]))
        if ix==0:
            assert set(G)=={z[9]**2,z[6]+5*z[9]/3+Rational(1,3),z[7]-z[9],
                            z[8]+8*z[9]/3-Rational(2,3)}
        else:
            assert G==[1]
    assert Poly(permanent(ones(4)+x*M+t*N),x,t).as_expr()==24
    assert sorted(abs(A[i,j]) for i in range(4) for j in range(i+1,4))==[1,2,3,4,5,7]


def combinations_with_diagonal():
    return ((i,j) for i in indices for j in range(i,4))


if __name__=="__main__":
    F=forms()
    check_pure_components(F)
    check_mixed_planes(F)
    print("33 cyclically invariant level planes; all 30 in the main chart are first-order maximal.")
    check_mixed_direction(F)
    print("No level three-space can contain a projective eigenline of the three-cycle.")
    check_asymmetric_line()
    print("The indicated asymmetric rational line lies in exactly one level plane.")
