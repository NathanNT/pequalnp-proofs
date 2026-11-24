"""Verify a nonsymmetric-under-permutations family of symmetric level lines."""
from itertools import combinations_with_replacement, permutations
from sympy import GF, Matrix, Poly, QQ, expand, groebner, ones, prod, symbols
from sympy.polys.matrices import DomainMatrix


def permanent(M):
    return sum(prod(M[i,j] for i,j in enumerate(pi)) for pi in permutations(range(4)))


def matrix(u,v,z,k):
    return Matrix([[u,0,1,0],[0,v,k,0],[1,k,z,0],[0,0,0,0]])


def verify():
    z,s,t=symbols("z s t")
    minpoly=Poly(z**6+18*z**5+93*z**4+72*z**3-265*z**2-42*z+135,z,domain=QQ)
    assert minpoly.is_irreducible
    v=(4*z**5+78*z**4+489*z**3+948*z**2-373*z-1536)/147
    A=matrix(-6-v-z,v,z,2)
    polynomial=Poly(permanent(ones(4)+s*A)-24,s)
    assert all(Poly(k,z,domain=QQ).rem(minpoly).is_zero for k in polynomial.coeffs())
    assert minpoly.eval(25)%31==0
    for i in range(4):
        for j in range(4):
            val=A[i,j].subs(z,25)
            n,d=val.as_numer_denom()
            A[i,j]=int(n)*pow(int(d),-1,31)%31
    assert A==matrix(15,16,25,2)
    pairs=list(combinations_with_replacement(range(4),2))
    V=symbols("v:10")
    B=Matrix(4,4,lambda i,j: V[pairs.index(tuple(sorted((i,j))))])
    P=Poly(permanent(ones(4)+s*A+t*B)-24,s,t)
    # Adding a multiple of A to B sets its first diagonal entry to zero.
    linear=[P.coeff_monomial(s**k*t) for k in range(4)]+[V[0]]
    mat=Matrix([[form.coeff(v) for v in V] for form in linear])
    reduced,pivots=DomainMatrix.from_Matrix(mat).convert_to(GF(31)).rref()
    reduced=reduced.to_Matrix()
    assert pivots==(0,1,2,3)
    free=list(V[4:])
    substitution={V[j]:-sum(reduced[i,k]*V[k] for k in range(4,10))
                  for i,j in enumerate(pivots)}
    equations=[Poly(val.subs(substitution),*free,modulus=31).as_expr()
               for mon,val in P.terms() if mon[1]>=2]
    for i,pivot in enumerate(free):
        chart=dict.fromkeys(free[:i],0)|{pivot:1}
        eq=[val.subs(chart) for val in equations]
        tail=free[i+1:]
        if tail:
            assert list(groebner(eq,*tail,order="grevlex",modulus=31))==[1]
        else:
            assert any(int(val)%31 for val in eq)
    # At k=2 the six points form the entire fiber of the two-equation
    # family. This also verifies the stated positive-dimensional extension.
    D,F=symbols("D F")
    u=-6-D-F
    ray=Poly(permanent(ones(4)+s*matrix(u,D,F,2))-24,s)
    G=groebner([ray.nth(2),ray.nth(3)],D,F,domain=QQ,order="lex")
    assert G[0]==expand(D-v.subs(z,F))
    assert G[1]==minpoly.as_expr().subs(z,F)
    print("Verified all six complex level lines and exclusion of every level plane through them.")


if __name__=="__main__":
    verify()
