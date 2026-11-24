"""Exact polynomial checks for the sparse hook and transposition obstructions."""
from itertools import combinations, permutations

from sympy import Matrix, Poly, QQ, expand, factor, groebner, ones, prod, symbols


def permanent(matrix):
    return sum(prod(matrix[i, j] for i, j in enumerate(sigma))
               for sigma in permutations(range(matrix.rows)))


def check_repeated_rows():
    k, u, v, m, h, l = symbols("k u v m h l")
    repeated = Matrix([[k,k,u,v], [k,k,u,v], [u,u,m,h], [v,v,h,l]])
    formula = 2*(k**2*(m*l+h**2) + 2*k*u**2*l + 4*k*u*v*h
                 + 2*k*v**2*m + 2*u**2*v**2)
    assert expand(permanent(repeated) - formula) == 0

    s, t, b, c, e, f, n = symbols("s t b c e f n")
    # The report treats k constant directly. Here k is a free coordinate.
    coordinates = {k:1+s, u:1+b*s, v:1+c*s, m:1+t,
                   h:1+e*s+n*t, l:1+f*s-n**2*t}
    equations = Poly(formula.subs(coordinates)-24, s, t).coeffs()
    basis = groebner(equations+[n**2-2*n-1],b,c,e,f,n,domain=QQ,order="grevlex")
    assert list(basis) == [1]


def check_sparse_hook():
    a,b,c,d,e,f,g,h,i,j,x,t = symbols("a b c d e f g h i j x t")
    direction = Matrix([[a,b,c,d],[b,e,f,g],[c,f,h,i],[d,g,i,j]])
    hook = Matrix([[0,1,-1,0],[1,0,0,0],[-1,0,0,0],[0,0,0,0]])
    poly = Poly(permanent(ones(4)+x*hook+t*direction)-24,t,x)
    expected = [6*(a+2*b+2*c+2*d+e+2*f+2*g+h+2*i+j),
                4*(-e-g+h+i),e-2*f+h]
    for power, form in enumerate(expected):
        assert expand(poly.coeff_monomial(t*x**power)-form) == 0
    # The last two linear equations imply these substitutions.
    substitution = {e:-g+h+i, f:(-g+2*h+i)/2}
    assert expand(poly.coeff_monomial(t**2*x**2).subs(substitution)-(g-i)**2) == 0


def check_plane_charts(forms, parameters):
    # Each chart is an RREF cell of Gr(2,4). Each homogeneous form of
    # degree d is identically zero on the plane iff it vanishes at (1,h)
    # for h = 0,...,d.
    u,v = symbols("U V")
    for pivots in combinations(range(4),2):
        variables = iter(symbols("z:4"))
        active = []
        coordinates = {}
        for index, param in enumerate(parameters):
            if index in pivots:
                coordinates[param] = (u,v)[pivots.index(index)]
                continue
            row = [0,0]
            for j, pivot in enumerate(pivots):
                if pivot < index:
                    row[j] = next(variables)
                    active.append(row[j])
            coordinates[param] = row[0]*u+row[1]*v
        equations = []
        excluded = False
        for degree, form in forms:
            for h in range(degree+1):
                values = {s:y.subs({u:1,v:h}) for s,y in coordinates.items()}
                equations.append(form.subs(values,simultaneous=True).expand())
            if active:
                excluded = list(groebner(equations,*active,order="grevlex",domain=QQ)) == [1]
            else:
                excluded = any(value != 0 for value in equations)
            if excluded:
                break
        assert excluded, pivots


def check_transposition():
    a,b,c,d,e,f,g,x,t = symbols("a b c d e f g x t")
    anti = Matrix([[a,0,b,c],[0,-a,-b,-c],[b,-b,0,0],[c,-c,0,0]])
    line = Poly(permanent(ones(4)+x*anti)-24,x)
    assert expand(line.nth(2)+2*a**2+8*a*(b+c)+8*b*c) == 0
    assert expand(line.nth(4)-4*b**2*c**2) == 0
    special = anti.subs({a:-4,b:1,c:0})
    fixed = Matrix([[a,b,c,d],[b,a,c,d],[c,c,e,f],[d,d,f,g]])
    poly = Poly(permanent(ones(4)+x*special+t*fixed)-24,t,x)
    linear = [poly.coeff_monomial(t*x**j) for j in range(4)]
    substitution = {a:-5*c-5*d+15*e/4+7*f/2-g/4,
                    b:3*c+3*d-17*e/4-9*f/2-g/4}
    assert all(expand(form.subs(substitution)) == 0 for form in linear)
    assert Matrix([[form.diff(v) for v in (a,b)] for form in linear]).rank() == 2
    assert expand(poly.coeff_monomial(t**2*x**2).subs(substitution)
                  - 16*(d-f)*(f-g)) == 0
    for extra, parameters in [({d:f},(c,e,f,g)),({g:f},(c,d,e,f))]:
        forms = [(degree,factor(poly.coeff_monomial(t**degree).subs(substitution).subs(extra)))
                 for degree in (2,3,4)]
        check_plane_charts(forms,parameters)


if __name__ == "__main__":
    check_repeated_rows()
    check_sparse_hook()
    check_transposition()
    print("Verified repeated rows, the sparse hook, and all 12 mixed-eigenspace charts.")
