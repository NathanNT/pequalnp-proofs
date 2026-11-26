"""
Generate a self-contained Lean 4 (Mathlib) file certifying that an explicit sum of k cubes of binomials has at least
4k-1 distinct positive roots, in the fixed-point interval-arithmetic format of the PEqualNP rows L-gct-251/253/261.

usage: gen_lean.py cand.json decimals scale_digits Namespace theoremName out.lean [template.lean]
"""
import os, sys, json, math
from fractions import Fraction as Fr
from exact_check import build, expand, sign_at

# default template: the row file L_gct_251.lean of the repository this note lives in
DEFAULT_TEMPLATE = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'lean', 'PEqualNP',
                                'Outside', 'L_gct_251.lean')


def boxMul(s, a, b):
    return (a[0] * b[0] // s, a[1] * b[1] // s + 1)


def powerBox(s, base, k, n):
    if k == 0:
        return (s, s)
    u = powerBox(s, base, k - 1, n // 2)
    v = boxMul(s, u, u)
    return v if n % 2 == 0 else boxMul(s, v, (base, base))


def weightedBox(s, b, ts):
    lo = hi = 0
    for c, e in ts:
        z = powerBox(s, b, 52, e)
        lo += c * z[0]
        hi += c * z[1]
    return (lo, hi)


def lit(v):
    v = Fr(v)
    if v.denominator == 1:
        return str(v.numerator) if v >= 0 else '(%d)' % v.numerator
    return '(%d / %d)' % (v.numerator, v.denominator)


def main():
    cand, dec, M, NS, THM, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5], sys.argv[6]
    template = sys.argv[7] if len(sys.argv) > 7 else DEFAULT_TEMPLATE
    c = json.load(open(cand))
    k = c['k']
    gs, h = build(c)
    terms = expand(gs)
    # decimal sample points: exp(+-t) rounded to `dec` decimals
    ups = [round(math.exp(t) * 10 ** dec) for t in c['pts']]
    downs = [round(math.exp(-t) * 10 ** dec) for t in c['pts']]
    ints = sorted(set(ups + downs))
    assert len(ints) == 4 * k
    pts = [Fr(v, 10 ** dec) for v in ints]
    sg = [sign_at(terms, x) for x in pts]
    assert all(sg[i] * sg[i + 1] < 0 for i in range(len(sg) - 1)), sg
    phase = 0 if sg[0] > 0 else 1
    count = 4 * k - 1
    scale = 10 ** M
    bases = [v * 10 ** (M - dec) for v in ints]
    den = 1
    for v in terms.values():
        den = den * v.denominator // math.gcd(den, v.denominator)
    pos = [(int(v * den), e) for e, v in terms.items() if v > 0]
    neg = [(int(-v * den), e) for e, v in terms.items() if v < 0]
    # emulate the Lean interval check exactly
    for i, b in enumerate(bases):
        p = weightedBox(scale, b, pos)
        n = weightedBox(scale, b, neg)
        ok = (n[1] < p[0]) if (i + phase) % 2 == 0 else (p[1] < n[0])
        assert ok, ('interval check fails at point', i, 'increase scale digits')
    print('emulated interval check passes at all', len(bases), 'points; den has', len(str(den)), 'digits; phase', phase)

    src = open(template, encoding='utf-8').read().split('\n')
    i0 = next(i for i, l in enumerate(src) if l.startswith('open Polynomial'))
    i1 = next(i for i, l in enumerate(src) if l.startswith('noncomputable def list0'))
    generic = [l for l in src[i0:i1] if not l.startswith('-- ')]
    L = []
    L += ['import Mathlib.Topology.Algebra.Polynomial',
          'import Mathlib.Order.Interval.Set.Monotone',
          'import Mathlib.Tactic.Linarith',
          '',
          '/-!',
          '# A sum of %d cubes of real binomials with %d distinct positive roots' % (k, count),
          '',
          "Descartes' rule of signs allows at most %d positive roots for such a sum (it has at most %d monomials)," % (count, 4 * k),
          'so the example below is optimal.  The sign of the polynomial is certified at %d rational points' % (4 * k),
          'by outward-rounded fixed-point interval arithmetic evaluated in the kernel (`decide +kernel`).',
          '',
          'Provenance.  The example (exponents, coefficients, sample points) was found by a numerical search and',
          'certified for the note "Positive roots of sums of cubes of binomials" (see the README next to this file).',
          'The generic part of this file (`covers`, `boxMul`, `powerBox`, `weightedBox`, `sign_from_boxes`,',
          '`rootsOfCrossings`, `sparse`, and the final assembly) is taken unchanged from the PEqualNP row L-gct-251',
          '(k-sandhu), which follows the fixed-point method of L-gct-261 (hedanbaomi); both are in',
          'open-goat/pequalnp-proofs under Apache-2.0.  This file imports Mathlib only.',
          '-/',
          '',
          'namespace %s' % NS,
          '']
    L += generic
    for i, g in enumerate(gs):
        L.append('noncomputable def list%d : List (ℕ × ℝ) := [(%d, %s),' % (i, g[0][1], lit(g[0][0])))
        L.append('    (%d, %s)]' % (g[1][1], lit(g[1][0])))
        L.append('')
        L.append('noncomputable def part%d : Polynomial ℝ := sparse list%d' % (i, i))
        L.append('')
    L.append('noncomputable def gs : Fin %d → Polynomial ℝ := ![%s]' % (k, ', '.join('part%d' % i for i in range(k))))
    L.append('')
    L.append('noncomputable def P : Polynomial ℝ :=')
    L.append('  (Finset.univ : Finset (Fin %d)).sum fun i => C (1 : ℝ) * gs i ^ 3' % k)
    L.append('')
    L.append('lemma gs_card (i : Fin %d) : (gs i).support.card ≤ 2 := by' % k)
    L.append('  fin_cases i')
    for i in range(k):
        L.append('  · exact (sparse_card list%d).trans (by decide)' % i)
    L.append('')
    L.append('def count : ℕ := %d' % count)
    L.append('def phase : ℕ := %d' % phase)
    L.append('def scale : ℕ := %d' % scale)
    L.append('def den : ℕ := %d' % den)
    L.append('def samples : List ℕ := [%s]' % ', '.join(str(b) for b in bases))
    L.append('def base (i : ℕ) : ℕ := samples.getD i 0')
    L.append('')
    L.append('def posTerms : List (ℕ × ℕ) := [%s]' % ',\n    '.join('(%d, %d)' % t for t in pos))
    L.append('def negTerms : List (ℕ × ℕ) := [%s]' % ',\n    '.join('(%d, %d)' % t for t in neg))
    L.append('')
    parts = ', '.join('part%d' % i for i in range(k))
    lists = ', '.join('list%d' % i for i in range(k))
    L.append('set_option maxRecDepth 8192 in')
    L.append('set_option maxHeartbeats 4000000 in')
    L.append('lemma eval_eq (x : ℝ) : (den : ℝ) * P.eval x =')
    L.append('    weightedEval x posTerms - weightedEval x negTerms := by')
    L.append('  simp only [P, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.cons_zero, Fin.cons_succ, Matrix.cons_val_zero, '
             'Matrix.cons_val_succ, gs, map_one, one_mul, %s, %s, sparse, eval_mul, eval_add,' % (parts, lists))
    L.append('    eval_pow, eval_zero, eval_one, eval_monomial, den, posTerms, negTerms, weightedEval,')
    L.append('    Nat.cast_ofNat, ← pow_add]')
    L.append('  ring')
    j0 = next(i for i, l in enumerate(src) if l.startswith('noncomputable def point'))
    j1 = next(i for i, l in enumerate(src) if l.startswith('end PEqualNP.Outside.L_gct_251'))
    L += src[j0:j1]
    L.append('end %s' % NS)
    L.append('')
    stmt = ('(∀ (s : Fin %d → ℝ) (g : Fin %d → Polynomial ℝ), (∀ i, s i = 1 ∨ s i = -1) → '
            '(∀ i, (g i).support.card ≤ 2) → ((((Finset.univ : Finset (Fin %d)).sum fun i => '
            'Polynomial.C (s i) * g i ^ 3)).roots.toFinset.filter (fun x : ℝ => 0 < x)).card ≤ %d)') % (k, k, k, count - 1)
    L.append('/-- There is a sum of %d cubes of real polynomials with at most two terms each that has at least %d' % (k, count))
    L.append('distinct positive roots: the bound "at most %d" fails. -/' % (count - 1))
    L.append('theorem %s :' % THM)
    L.append('    ¬ %s := by' % stmt)
    L.append('  intro h')
    L.append('  open %s in' % NS)
    L.append('  exact by')
    L.append('    have limit := h (fun _ => 1) gs (fun _ => Or.inl rfl) gs_card')
    L.append('    change (P.roots.toFinset.filter (fun x : ℝ => 0 < x)).card ≤ %d at limit' % (count - 1))
    L.append('    have lower := roots_lower')
    L.append('    norm_num [count] at lower')
    L.append('    omega')
    L.append('')
    L.append('#print axioms %s' % THM)
    open(out, 'w', encoding='utf-8', newline='\n').write('\n'.join(L) + '\n')
    json.dump(dict(k=k, binomials=[[(str(a), e) for a, e in g] for g in gs], points=[str(x) for x in pts],
                   signs=sg, count=count, scale_digits=M, decimals=dec),
              open(out.replace('.lean', '.json'), 'w'), indent=1)
    print('wrote', out)


if __name__ == '__main__':
    main()
