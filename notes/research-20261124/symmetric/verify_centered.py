"""Check the zero-row-sum obstruction over the rational numbers, using SymPy."""
from itertools import permutations
from sympy import Matrix, Poly, QQ, eye, expand, groebner, ones, prod, symbols

def permanent(matrix):
    return sum(prod(matrix[i,j] for i,j in enumerate(sigma))
               for sigma in permutations(range(matrix.rows)))

a,b,c,d,e,f,t = symbols('a b c d e f t')
B = Matrix([[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]])
A = Matrix([[a,d,e],[d,b,f],[e,f,c]])
assert B.T * B == 4 * eye(3)
assert B.T * ones(4,1) == 0 * ones(3,1)
T = B*A*B.T
# Working in QQ[a,b,c,d,e,f][t] keeps the coefficient identities exact.
R = QQ.poly_ring(a,b,c,d,e,f)
P = Poly(permanent(ones(4)+t*T), t, domain=R)
assert P.nth(0) == 24 and P.nth(1) == 0
assert expand(P.nth(2) - 16*(A*A).trace()) == 0
assert expand(P.nth(3) - 64*permanent(A)) == 0

# Each of the eight possible signs on the three off-diagonal coordinates
# affects only their product. Both values of that product are covered by
# adjoining w with w^2 + 2 = 0.
x,y,z,p,q,r,w = symbols('x y z p q r w')
X = Matrix([x,y,z])
K = Matrix([[0,p,q],[-p,0,r],[-q,-r,0]])
Y = K*X
a,b,c = X+Y
F,E,D = X-Y
twice_cubic = 2*a*b*c-a*F**2-b*E**2-c*D**2+w*D*E*F
equations = Poly(twice_cubic,x,y,z).coeffs()
assert len(equations) == 10
basis = groebner([w**2+2, *equations],p,q,r,w,order='grevlex',domain=QQ)
assert list(basis) == [1]
print("Verified the quadratic and cubic coefficients, and the unit ideal in every chart.")
