"""
Exact search: can a nonzero sum of three cubes of real binomials with INTEGER exponents have a positive root of
multiplicity >= 8 ?   (Known: 7 is attained [maxkieff, Discussion #21999]; 9 is an upper bound [L-gct-234].)

Setting.  G = sum_{i=0}^{2} (A_i x^{a_i} + B_i x^{b_i})^3, a_i < b_i integers, A_i, B_i real.  Rescaling x moves any
positive root to x = 1, so only the root x = 1 is considered.  Slots of block i: y_{i,j} = 3 a_i + j (b_i - a_i),
j = 0..3, with slot values h_{i,j} = C(3,j) A_i^{3-j} B_i^j.   (x-1)^8 | G  <=>  sum_{i,j} h_{i,j} y_{i,j}^n = 0, n = 0..7.

Pivot method.  Let block P be a genuine binomial, normalised A_P = 1, B_P = z != 0.  If the 8 slots of the other two
blocks J, K are pairwise distinct, the 8 moment equations determine their slot values:
        h_s(z) = - sum_{j=0}^{3} C(3,j) z^j L_s(y_{P,j}),     L_s = Lagrange basis polynomial on the 8 slots of J, K.
A real quadruple (h0,h1,h2,h3) is of the form (A^3, 3A^2B, 3AB^2, B^3) with A, B real iff
        h1^2 = 3 h0 h2,  h2^2 = 3 h1 h3,  h1 h2 = 9 h0 h3.
So a solution with pivot P exists iff six explicit integer polynomials of degree <= 6 in z have a common real root
z != 0.  A nonzero G with a root of multiplicity >= 8 has at least 9 monomials, hence at least two genuine blocks.

Scope.  Exponent triples with min exponent 0, max exponent <= S, pairwise distinct supports and at least 9 distinct
slot exponents.  If at most two pairs of blocks share a slot exponent, the pivots tried below (and, for two sharing
pairs, the 'two cubes plus one monomial' test) cover every solution.  Triples in which all three pairs of blocks
share a slot exponent are counted and reported as "out of scope".

usage: mult_search.py S nproc procindex        (prints one summary line; hits are printed as they are found)
       mult_search.py selftest
"""
import sys, itertools, math
from fractions import Fraction as Fr

P61 = (1 << 61) - 1
BIN = (1, 3, 3, 1)


def slots(a, b):
    d = b - a
    return (3 * a, 3 * a + d, 3 * a + 2 * d, 3 * a + 3 * d)


def polmul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        if x:
            for j, y in enumerate(q):
                r[i + j] += x * y
    return r


def cone_polys(yP, yJ, yK, num=int):
    """six polynomials in z (integer coefficient lists, low degree first) for pivot slots yP and other slots yJ, yK.
    Works for any number type supporting exact arithmetic (int exponents) or mpmath numbers (num=None)."""
    S = list(yJ) + list(yK)
    H = []
    dens = []
    for s in S:
        den = 1
        for e in S:
            if e != s:
                den = den * (s - e)
        co = []
        for j in range(4):
            v = 1
            for e in S:
                if e != s:
                    v = v * (yP[j] - e)
            co.append(-BIN[j] * v)
        H.append(co)
        dens.append(den)
    polys = []
    for blk in (0, 4):
        H0, H1, H2, H3 = H[blk:blk + 4]
        d0, d1, d2, d3 = dens[blk:blk + 4]
        # h_i = H_i / d_i
        a = polmul(H1, H1); b = polmul(H0, H2)
        polys.append([a[i] * d0 * d2 - 3 * b[i] * d1 * d1 for i in range(7)])
        a = polmul(H2, H2); b = polmul(H1, H3)
        polys.append([a[i] * d1 * d3 - 3 * b[i] * d2 * d2 for i in range(7)])
        a = polmul(H1, H2); b = polmul(H0, H3)
        polys.append([a[i] * d0 * d3 - 9 * b[i] * d1 * d2 for i in range(7)])
    return polys


def trim(p):
    while p and p[-1] == 0:
        p = p[:-1]
    return p


def gcd_mod(p, q, m=P61):
    p = trim([x % m for x in p]); q = trim([x % m for x in q])
    while q:
        inv = pow(q[-1], -1, m)
        while len(p) >= len(q):
            c = p[-1] * inv % m
            sh = len(p) - len(q)
            p = trim([(p[i] - c * q[i - sh]) % m if i >= sh else p[i] for i in range(len(p) - 1)])
            if not p:
                break
        p, q = q, p
    return p            # gcd (not normalised); [] means both were zero


def exact_common_real_root(polys):
    """exact: do the rational polynomials have a common real root z != 0 ?  returns (bool, description)"""
    import sympy as sp
    z = sp.symbols('z')
    g = None
    for p in polys:
        e = sp.Poly(list(reversed(p)), z, domain='ZZ') if any(p) else None
        if e is None:
            continue
        g = e if g is None else sp.gcd(g, e)
    if g is None:
        return True, 'all six polynomials vanish identically'
    # remove the factor z
    while g.eval(0) == 0 and g.degree() > 0:
        g = sp.Poly(sp.quo(g.as_expr(), z), z)
    if g.degree() <= 0:
        return False, 'gcd constant'
    roots = sp.Poly(g.as_expr(), z).real_roots()
    if roots:
        return True, 'gcd %s, real roots %s' % (g.as_expr(), [sp.N(r, 12) for r in roots])
    return False, 'gcd %s has no real root' % g.as_expr()


def classify(sl):
    """number of block pairs sharing a slot exponent, and number of distinct slot exponents"""
    sets = [set(s) for s in sl]
    pairs = [(0, 1), (0, 2), (1, 2)]
    coll = [pr for pr in pairs if sets[pr[0]] & sets[pr[1]]]
    distinct = len(sets[0] | sets[1] | sets[2])
    return coll, distinct


def monomial_case(slU, slV, e):
    """G = g_U^3 + g_V^3 + c x^e with 9 distinct exponents: the coefficient vector with an 8-fold root at 1 is unique up
    to scale, c_y = 1/Q'(y); exact test of the cone equations on the two genuine blocks."""
    E = list(slU) + list(slV) + [e]
    if len(set(E)) < 9:
        return False
    def w(y):
        v = Fr(1)
        for f in E:
            if f != y:
                v *= (y - f)
        return 1 / v
    for blk in (slU, slV):
        h0, h1, h2, h3 = [w(y) for y in blk]
        if not (h1 * h1 == 3 * h0 * h2 and h2 * h2 == 3 * h1 * h3 and h1 * h2 == 9 * h0 * h3):
            return False
    return True


def pivot_hits(sl, P):
    J, K = [i for i in range(3) if i != P]
    polys = cone_polys(sl[P], sl[J], sl[K])
    nz = [trim(list(p)) for p in polys if any(p)]
    if len(nz) >= 2:
        # Modular filter.  If the integer polynomials F1, F2 had a common root, their primitive gcd d in Z[z] would
        # have degree >= 1 and its leading coefficient would divide those of F1 and F2.  So if the prime does not
        # divide the leading coefficient of F1 (or of F2), d keeps its degree modulo the prime and the gcd modulo the
        # prime is non-constant.  Hence: leading coefficient preserved and gcd modulo the prime constant => no common
        # root.  Otherwise fall through to the exact computation.
        lead_ok = (nz[0][-1] % P61 != 0) or (nz[1][-1] % P61 != 0)
        if lead_ok:
            g = gcd_mod(nz[0], nz[1])
            if len(g) <= 1:
                return []
    ok, desc = exact_common_real_root(polys)
    return [(P, desc)] if ok else []


def test_triple(tr):
    """returns (kind, hits): kind = 'few' (< 9 distinct exponents), 'out' (all three pairs of blocks share an exponent),
    or 'in' (fully decided)"""
    sl = [slots(a, b) for a, b in tr]
    coll, distinct = classify(sl)
    if distinct < 9:
        return 'few', []
    if len(coll) == 3:
        return 'out', []
    hits = []
    if len(coll) == 0:
        for P in (0, 1):
            hits += pivot_hits(sl, P)
    elif len(coll) == 1:
        for P in coll[0]:
            hits += pivot_hits(sl, P)
    else:
        # two colliding pairs share a common block M; the other two blocks U, V do not collide with each other
        M = [i for i in range(3) if all(i in pr for pr in coll)][0]
        U, V = [i for i in range(3) if i != M]
        hits += pivot_hits(sl, M)                      # solutions in which M is a genuine binomial
        for e in (sl[M][0], sl[M][3]):                # solutions in which M is a single monomial
            if monomial_case(sl[U], sl[V], e):
                hits.append((M, 'monomial block at exponent %d' % e))
    return 'in', hits


def triples(S, nproc, idx):
    pairs = [(a, b) for a in range(S + 1) for b in range(a + 1, S + 1)]
    n = len(pairs)
    for i in range(n):
        if i % nproc != idx:
            continue
        for j in range(i + 1, n):
            mj = min(pairs[i][0], pairs[j][0])
            for k in range(j + 1, n):
                if mj != 0 and pairs[k][0] != 0:
                    continue
                yield (pairs[i], pairs[j], pairs[k])


def selftest():
    import mpmath as mp
    mp.mp.dps = 40
    # (1) linear algebra: the computed slot values satisfy the 8 moment equations exactly
    tr = ((0, 5), (2, 9), (1, 5)); sl = [slots(a, b) for a, b in tr]; zz = Fr(-3, 7)
    assert len(set(sl[1]) | set(sl[2])) == 8
    S = list(sl[1]) + list(sl[2])
    hs = []
    for s in S:
        den = Fr(1)
        for e in S:
            if e != s: den *= (s - e)
        v = Fr(0)
        for j in range(4):
            w = Fr(1)
            for e in S:
                if e != s: w *= (sl[0][j] - e)
            v += -BIN[j] * zz ** j * w
        hs.append(v / den)
    for n in range(8):
        tot = sum(BIN[j] * zz ** j * Fr(sl[0][j]) ** n for j in range(4)) + sum(h * Fr(s) ** n for h, s in zip(hs, S))
        assert tot == 0, n
    print('selftest 1 (moment equations hold exactly): ok')
    # (2) degenerate true positive: J has the same support as P reversed -> g_J = -g_P, g_K = 0 solves for every z
    yP = slots(0, 5); yJ = tuple(reversed(yP)); yK = slots(1, 4)
    # use distinct slots for the solver: J = P is not allowed (collision with pivot is fine, J,K must be distinct)
    polys = cone_polys(yP, yJ, yK)
    assert all(not any(p) for p in polys), polys
    print('selftest 2 (identically solvable degenerate case detected): ok')
    # (3) real-exponent positive controls from the common-root family of Discussion #21999 (maxkieff):
    #     centres L = (q, -p, 0), squared widths (8p^2+5pq+5q^2, 5p^2+5pq+8q^2, 8p^2+11pq+8q^2), weights w_i D_i^3 ~ (p, q, -p-q).
    #     Then the order at 1 is >= 8 (exactly 9 iff p = q up to symmetry), and z = -1 must be a common root of the six polynomials.
    for p_, q_, expect in ((mp.mpf(1), mp.mpf(2), 8), (mp.mpf(1), mp.mpf(1), 9)):
        Ls = [q_, -p_, mp.mpf(0)]
        vs = [8 * p_ ** 2 + 5 * p_ * q_ + 5 * q_ ** 2, 5 * p_ ** 2 + 5 * p_ * q_ + 8 * q_ ** 2, 8 * p_ ** 2 + 11 * p_ * q_ + 8 * q_ ** 2]
        Ds = [mp.sqrt(v) for v in vs]
        sl_ = [[3 * (L - D) / 2 + j * D for j in range(4)] for L, D in zip(Ls, Ds)]
        w = [p_ / Ds[0] ** 3, q_ / Ds[1] ** 3, -(p_ + q_) / Ds[2] ** 3]
        order = None
        for n in range(0, 12):
            tot = sum(w[i] * sum(BIN[j] * (-1) ** j * sl_[i][j] ** n for j in range(4)) for i in range(3))
            sc = sum(abs(w[i]) * sum(BIN[j] * abs(sl_[i][j]) ** n for j in range(4)) for i in range(3))
            if abs(tot) > mp.mpf(10) ** (-25) * (sc + 1):
                order = n; break
        assert order == expect, (order, expect)
        polys = cone_polys(sl_[0], sl_[1], sl_[2])
        vals = [abs(sum(c * (-1) ** i for i, c in enumerate(pp))) / (sum(abs(c) for c in pp) + 1) for pp in polys]
        assert max(vals) < mp.mpf(10) ** (-25), vals
        print('selftest 3 (real exponents, p=%s q=%s): order of vanishing %d as expected; z = -1 is a common root of the six polynomials: ok' % (p_, q_, order))


if __name__ == '__main__':
    if sys.argv[1] == 'selftest':
        selftest(); sys.exit(0)
    S = int(sys.argv[1]); nproc = int(sys.argv[2]); idx = int(sys.argv[3])
    cnt = {'few': 0, 'out': 0, 'in': 0}; nh = 0
    for tr in triples(S, nproc, idx):
        kind, hits = test_triple(tr)
        cnt[kind] += 1
        for P, desc in hits:
            nh += 1
            print('HIT', tr, 'pivot', P, desc, flush=True)
    print('DONE S', S, 'part', idx, 'of', nproc, 'in-scope', cnt['in'], 'out-of-scope(all three pairs of blocks share an exponent)', cnt['out'],
          'fewer-than-9-exponents', cnt['few'], 'hits', nh, flush=True)
