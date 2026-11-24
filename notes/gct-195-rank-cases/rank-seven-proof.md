# The rank-seven case for L-gct-195

Let F_k(M) be the sum of the k-by-k subpermanents of a complex 4-by-6 matrix for k=1,2,3,4. Suppose all four vanish on the linear space L. Define D by (row 1 + 3 row 4, row 2 + 3 row 4, row 3 + 3 row 4). The argument below proves that dim ker(D|L)=2 implies dim D(L)≤6, and hence rank seven forces nullity at most one. The coefficient computation and its interface with Lean are described below.

## Normalizing the kernel

Write r=(3,3,3,-1), and fix a primitive cube root w. The fixed-profile theorem gives nullity at most two. At equality the kernel amplitudes consist of two independently scalable vectors supported on disjoint triples of columns. The first permanent equation applied to either supported vector says its three entries sum to zero, since the row sum of r is 8. Their squares sum to zero by the fixed-profile theorem. For such a nonzero triple (a,b,c), c=−a−b gives a²+ab+b²=0. Therefore a is nonzero and b/a is w or w². After swapping the last two columns if necessary, each triple is proportional to (1,w,w²). Relabel the columns to put the two triples in order. Relabeling preserves every subpermanent sum and both dimensions. The two kernel matrices are now A=r times f and B=r times g, with f=(1,w,w²,0,0,0) and g=(0,0,0,1,w,w²).

## The fifteen quotient coordinates

Use the row basis r, e₄, c=(1,w,w²,0), d=(1,w²,w,0), and the column basis given by the three Fourier modes on each triple separately, in phase order 0,1,2. Number their rank-one products from 0 through 23 in row-major order. The row basis is independent since r has a nonzero constant first-three component and e₄ is independent of it. The column blocks are invertible three-point Fourier matrices.

For x in L, expand F_k(x+sA+tB). Every coefficient vanishes. The terms linear in x give seven independent linear equations. Their joint kernel consists of A,B and the following independent columns T_i, listed in the above 24-element basis (E_j denotes basis vector j).

- T₀=−E₂+4E₈, T₁=−E₀+E₃−4E₆+4E₉, T₂=−E₅+4E₁₁.
- T_i=E_(i+9) for i=3,...,14.

Independence follows from their disjoint nonempty supports and those of A=E₁ and B=E₄. The exact certificate checks that all seventeen are annihilated. The Lean proof completes these directions to a 24-vector basis. It verifies a right inverse with denominator 108 and computes seven independent gradient equations that force all seven complementary coefficients to vanish. Thus the list spans the entire tangent space. Because A and B belong to L, subtracting their components puts every coset in a unique space W in these fifteen coordinates. Consequently dim W=dim D(L).

## Bounding W

In the following equations subscripts are coordinate indices starting at zero. In F₄(x+sA+tB), the coefficients of s², st, t², divided by 162, are respectively

    x₄x₁₂ + x₆x₁₀
    −108x₀x₂ + x₅x₁₄ + x₈x₁₁
    x₃x₁₃ + x₇x₉.

All three vanish. The sum of the first two is the dot product of the vectors

    p=(x₄,x₆,x₀,x₅,x₈),     q=(x₁₂,x₁₀,−108x₂,x₁₄,x₁₁).

On the linear space (p,q)(W), that dot product vanishes identically, so the image has dimension at most five. For example, polarization shows that the q-image of ker p annihilates p(W), and rank–nullity gives the bound.

On the common kernel p=q=0 put (h,u,y,z,v)=(x₁,x₃,x₇,x₉,x₁₃). The constant coefficient of F₂, the t coefficient of F₃, the t² coefficient of F₄, and F₃ itself give

    18h²+uz=0,    yv=0,    uv+yz=0,
    u³+y³+z³+v³−36huz=0.

The linear functional u+2y+2z+3v is injective on this slice. To check its kernel, yv=0 and uv+yz=0 leave three cases. If y=u=0 or v=z=0, then h=0, and the linear and cubic equations force the other two coordinates to vanish. If y=v=0, then u=−2z and h=±z/3. The cubic becomes 17z³=0 or −31z³=0. Thus the slice has dimension at most one. Adding dimensions gives dim W≤6.

## Coefficient verification and scope

For rank-one directions with row vectors R_j and column vectors C_j, the coefficient of the associated monomial in F_k is the product of the ordered injective row sum and ordered injective column sum, divided by the factorial of each mode multiplicity. This follows by assigning the k slots to distinct rows and columns. Permuting indistinguishable slots counts precisely the same term. Multilinearity allows a T_i given as a sum of rank-one directions as well. FourierTable.lean evaluates these sums in the Eisenstein integers and checks every coefficient used in the dimension proof, including the zero coefficients. ChartTable.lean verifies the inverse coordinate matrix and the gradient equations over the same ring.

The separate statement file retains the original four matrix hypotheses verbatim. The project checker accepted PEqualNP.Gct.RankSeven195 and rechecked 2,265 project constants. The development includes column relabeling, polarization of the original sums, the inverse change of coordinates, the tangent equations, and the final rank–nullity argument.

In a nine-dimensional putative counterexample, the two surviving possibilities for this row profile are rank eight with nullity one and rank nine with nullity zero. These cases do not supply the two independent triple directions used to deduce the displayed equations.
