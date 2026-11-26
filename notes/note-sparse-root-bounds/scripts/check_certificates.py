"""
Exact verification of the sign patterns of the two examples of the note (Theorem 6 and Example 8).

Each file data/*_certificate.json contains
  "binomials": the binomials g_i as lists [[coefficient, exponent], [coefficient, exponent]] (rational coefficients),
  "points":    the rational sample points, in increasing order (the points used in the Lean files; the sixteen
               points of Theorem 6 are also printed in the note),
  "signs":     the sign of P = sum_i g_i^3 at each point.

The script evaluates P at every point in exact rational arithmetic, directly from the binomials, and checks that the
points increase strictly, that the signs are the stored ones and that they alternate.  It also expands P and reports
the number of monomials, so that the rule of signs gives the matching upper bound.

Standard library only.   usage: python check_certificates.py [certificate.json ...]
"""
import glob, json, os, sys
from fractions import Fraction as Fr


def check(path):
    c = json.load(open(path))
    gs = [[(Fr(co), int(e)) for co, e in g] for g in c['binomials']]
    pts = [Fr(p) for p in c['points']]
    assert all(pts[i] < pts[i + 1] for i in range(len(pts) - 1)), 'points not increasing'
    assert pts[0] > 0
    signs = []
    for x in pts:
        v = sum(sum(co * x ** e for co, e in g) ** 3 for g in gs)
        assert v != 0
        signs.append(1 if v > 0 else -1)
    assert signs == c['signs'], 'signs differ from the stored ones'
    assert all(signs[i] * signs[i + 1] < 0 for i in range(len(signs) - 1)), 'signs do not alternate'
    terms = {}
    for (a, ea), (b, eb) in gs:
        for j, cf in enumerate((1, 3, 3, 1)):
            e = (3 - j) * ea + j * eb
            terms[e] = terms.get(e, Fr(0)) + cf * a ** (3 - j) * b ** j
    terms = {e: v for e, v in terms.items() if v != 0}
    coeff_signs = [1 if terms[e] > 0 else -1 for e in sorted(terms)]
    variations = sum(1 for i in range(len(coeff_signs) - 1) if coeff_signs[i] != coeff_signs[i + 1])
    k = len(gs)
    print('%s: %d cubes of binomials, degree %d, %d monomials, %d sign variations of the coefficients;'
          % (os.path.basename(path), k, max(terms), len(terms), variations))
    print('    P alternates at the %d stored points, first sign %+d: at least %d positive roots, at most %d.'
          % (len(pts), signs[0], len(pts) - 1, variations))
    assert len(pts) - 1 == variations == 4 * k - 1
    return True


if __name__ == '__main__':
    here = os.path.dirname(os.path.abspath(__file__))
    files = sys.argv[1:] or sorted(glob.glob(os.path.join(here, '..', 'data', '*_certificate.json')))
    for f in files:
        check(f)
    print('all certificates verified')
