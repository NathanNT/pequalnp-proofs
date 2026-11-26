"""
Completion of mult_search.py for the exponent triples it leaves undecided: those in which all three pairs of blocks
share a slot exponent ("triangles").  Same question: can a nonzero G = sum_{i} (A_i x^{a_i} + B_i x^{b_i})^3 with these
exponents and real coefficients have a root of multiplicity >= 8 at x = 1 ?

Method (pivot with one coincidence).  Take a pivot block P, a genuine binomial normalised to (A_P, B_P) = (1, z), z != 0,
such that the other two blocks J, K share EXACTLY one slot exponent e* (slot jJ of J, slot jK of K).  Let E' be the 7
distinct exponents of J and K and a_e the aggregated coefficient of J and K at e.  The moment equations n = 0..6 give
        a_e(z) = - sum_j C(3,j) z^j  l_e(y_{P,j})            (l_e = Lagrange basis on E'),
and the equation n = 7 is the cubic
        C(z) = sum_j C(3,j) W(y_{P,j}) z^j = 0,              W(y) = prod_{e in E'} (y - e).
For each real root z* != 0 of C (isolated exactly, then enclosed in a ball), the slot values of J and K are known
except for the split tau / (a_{e*} - tau) at the shared exponent.  The cone equations
        h1^2 = 3 h0 h2,  h2^2 = 3 h1 h3,  h1 h2 = 9 h0 h3
for J and for K are then checked in rigorous ball arithmetic: the triple is REFUTED for this pivot and root if every
candidate value of tau makes some equation provably nonzero.  Anything that cannot be refuted is reported as FLAG.

Coverage.  In a triangle with at least 9 distinct exponents, at least two of the three blocks are valid pivots
(the other two blocks share exactly one exponent), and a solution has at least two genuine blocks; so some valid
pivot is genuine in any solution.  Hence "all valid pivots refuted" proves there is no solution.

usage: mult_triangles.py S nproc procindex
"""
import sys
from fractions import Fraction as Fr
import sympy as sp
from flint import arb, ctx
from mult_search import slots, classify, triples, BIN

ctx.prec = 400
Z = sp.symbols('z')


def nz(v):
    """ball provably nonzero"""
    return not v.contains(0)


def cone_ok_possible(h):
    """False if the quadruple of balls provably violates the cone equations"""
    h0, h1, h2, h3 = h
    return not (nz(h1 * h1 - 3 * h0 * h2) or nz(h2 * h2 - 3 * h1 * h3) or nz(h1 * h2 - 9 * h0 * h3))


def tau_candidates(h, j):
    """h: list of 4 balls with h[j] unknown.  Returns (status, candidates):
       status 'none'  : the tau-free cone equation is provably violated;
       status 'list'  : finitely many candidate balls for h[j] (each must still be checked);
       status 'free'  : cannot pin tau down rigorously (degenerate) -> caller must flag."""
    h = list(h)
    if j == 0:
        h1, h2, h3 = h[1], h[2], h[3]
        if nz(h2 * h2 - 3 * h1 * h3): return 'none', []
        if nz(h2): return 'list', [h1 * h1 / (3 * h2)]
        if nz(h3): return 'list', [h1 * h2 / (9 * h3)]
        return 'free', []
    if j == 3:
        h0, h1, h2 = h[0], h[1], h[2]
        if nz(h1 * h1 - 3 * h0 * h2): return 'none', []
        if nz(h1): return 'list', [h2 * h2 / (3 * h1)]
        if nz(h0): return 'list', [h1 * h2 / (9 * h0)]
        return 'free', []
    if j == 1:
        h0, h2, h3 = h[0], h[2], h[3]
        if nz(h2 * h2 * h2 - 27 * h0 * h3 * h3): return 'none', []
        if nz(h3): return 'list', [h2 * h2 / (3 * h3)]
        if nz(h2): return 'list', [9 * h0 * h3 / h2]
        return 'free', []
    if j == 2:
        h0, h1, h3 = h[0], h[1], h[3]
        if nz(h1 * h1 * h1 - 27 * h0 * h0 * h3): return 'none', []
        if nz(h0): return 'list', [h1 * h1 / (3 * h0)]
        if nz(h1): return 'list', [9 * h0 * h3 / h1]
        return 'free', []


def real_roots_balls(coeffs):
    """rigorous enclosures of the real roots of the rational polynomial sum coeffs[i] z^i (zero root dropped)"""
    p = sp.Poly(list(reversed(coeffs)), Z, domain='QQ')
    if p.is_zero:
        return None
    out = []
    for fac, _ in p.factor_list()[1]:
        if fac.degree() == 0:
            continue
        if fac.degree() == 1:
            r = -fac.all_coeffs()[1] / fac.all_coeffs()[0]
            if r != 0:
                out.append(arb(int(r.p)) / arb(int(r.q)))
            continue
        for (lo, hi), _m in fac.intervals(eps=sp.Rational(1, 10 ** 80)):
            lo = sp.Rational(lo); hi = sp.Rational(hi)
            a = arb(int(lo.p)) / arb(int(lo.q)); b = arb(int(hi.p)) / arb(int(hi.q))
            out.append(a.union(b))
    return out


def pivot_test(sl, P):
    """returns 'refuted', 'flag: ...' or None if P is not a valid pivot"""
    J, K = [i for i in range(3) if i != P]
    shared = set(sl[J]) & set(sl[K])
    if len(shared) != 1:
        return None
    estar = next(iter(shared)); jJ = sl[J].index(estar); jK = sl[K].index(estar)
    Ep = sorted(set(sl[J]) | set(sl[K]))
    assert len(Ep) == 7
    yP = sl[P]
    # cubic C(z)
    def W(y):
        v = Fr(1)
        for e in Ep: v *= (y - e)
        return v
    C = [BIN[j] * W(yP[j]) for j in range(4)]
    roots = real_roots_balls(C)
    if roots is None:
        return 'flag: C identically zero'
    if not roots:
        return 'refuted'
    # aggregated values a_e(z) = - sum_j BIN[j] z^j l_e(yP[j])  (exact rational coefficients)
    coef = {}
    for e in Ep:
        den = Fr(1)
        for f in Ep:
            if f != e: den *= (e - f)
        cs = []
        for j in range(4):
            v = Fr(1)
            for f in Ep:
                if f != e: v *= (yP[j] - f)
            cs.append(-BIN[j] * v / den)
        coef[e] = cs
    def aval(e, z):
        s = arb(0)
        for j in range(4):
            c = coef[e][j]
            s += (arb(c.numerator) / arb(c.denominator)) * z ** j
        return s
    for z in roots:
        hJ = [aval(y, z) for y in sl[J]]; hK = [aval(y, z) for y in sl[K]]
        total = hJ[jJ]                       # aggregated value at e*
        stJ, candJ = tau_candidates(hJ, jJ)
        if stJ == 'none':
            continue
        stK, candK = tau_candidates(hK, jK)
        if stK == 'none':
            continue
        if stJ == 'list':
            cands = candJ
        elif stK == 'list':
            cands = [total - t for t in candK]
        else:
            return 'flag: split not determined at z=%s' % z
        alive = False
        for tau in cands:
            a = list(hJ); a[jJ] = tau
            b = list(hK); b[jK] = total - tau
            if cone_ok_possible(a) and cone_ok_possible(b):
                alive = True
        if alive:
            return 'flag: not refuted at z=%s' % z
    return 'refuted'


def triangle_test(tr):
    sl = [slots(a, b) for a, b in tr]
    coll, distinct = classify(sl)
    assert len(coll) == 3 and distinct >= 9
    res = [pivot_test(sl, P) for P in range(3)]
    valid = [r for r in res if r is not None]
    if len(valid) < 2:
        return 'flag: fewer than two valid pivots %s' % res
    bad = [r for r in valid if r != 'refuted']
    return 'refuted' if not bad else '; '.join(bad)


if __name__ == '__main__':
    S = int(sys.argv[1]); nproc = int(sys.argv[2]); idx = int(sys.argv[3])
    n = 0; flags = 0
    for tr in triples(S, nproc, idx):
        sl = [slots(a, b) for a, b in tr]
        coll, distinct = classify(sl)
        if distinct < 9 or len(coll) != 3:
            continue
        n += 1
        r = triangle_test(tr)
        if r != 'refuted':
            flags += 1
            print('FLAG', tr, r, flush=True)
    print('DONE triangles S', S, 'part', idx, 'of', nproc, 'triangles', n, 'refuted', n - flags, 'flagged', flags, flush=True)
