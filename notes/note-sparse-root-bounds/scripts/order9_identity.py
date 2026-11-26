"""
Proposition 11 of the note: a sum of three cubes of two-term signomials with real exponents and a root of order 9.

    Phi(s) = 3*sqrt(3)*cosh(s)*sinh(sqrt(2)*s)^3 - 2*sqrt(2)*sinh(sqrt(3)*s)^3 = (4*sqrt(6)/315) s^9 + O(s^11).

(1) Taylor expansion by computer algebra.
(2) The same through the closed form of the Taylor coefficients used in the printed proof.
(3) The twelve exponents of the signomial form are pairwise distinct.

Requires sympy.   usage: python order9_identity.py
"""
import sympy as sp

s = sp.symbols('s')
r2, r3 = sp.sqrt(2), sp.sqrt(3)
Phi = 3 * r3 * sp.cosh(s) * sp.sinh(r2 * s)**3 - 2 * r2 * sp.sinh(r3 * s)**3
ser = sp.series(Phi, s, 0, 12).removeO()
print('(1) Phi(s) =', sp.simplify(ser), '+ O(s^13)')

print('(2) Taylor coefficient of s^(2m+1)/(2m+1)! from the closed form:')
for m in range(0, 6):
    n = 2 * m + 1
    c = sp.Rational(3, 8) * r3 * ((3 * r2 + 1)**n + (3 * r2 - 1)**n - 3 * (r2 + 1)**n - 3 * (r2 - 1)**n) \
        - (r2 / 2) * ((3 * r3)**n - 3 * r3**n)
    c = sp.simplify(sp.expand(c))
    print('    m = %d (order %d): %s   -> coefficient of s^%d: %s' % (m, n, c, n, sp.simplify(c / sp.factorial(n))))

third = sp.Rational(1, 3)
exps = [3 * (third + r2) - 2 * j * r2 for j in range(4)] + [3 * (-third + r2) - 2 * j * r2 for j in range(4)] \
     + [3 * r3 - 2 * j * r3 for j in range(4)]
vals = sorted(float(e) for e in exps)
print('(3) exponents:', [sp.nsimplify(e) for e in exps])
print('    pairwise distinct:', all(vals[i + 1] - vals[i] > 1e-9 for i in range(len(vals) - 1)))
