"""
Proposition 12 of the note (the family with a common root).

G(x) = sum_{i=0}^{2} w_i (x^{a_i} - x^{b_i})^3,  L_i = a_i + b_i,  D_i = b_i - a_i,  omega_i = w_i D_i^3.
Euler moments  mu_n = sum_i (omega_i / D_i^3) sum_j C(3,j) (-1)^j (3 a_i + j D_i)^n ;  the order of G at x = 1 is the
least n with mu_n != 0.

Family (weights and quadratic forms: maxkieff, Discussion #21999 of open-goat/pequalnp-proofs):
    L = (q, -p, 0),  omega = (p, q, -p-q),
    D_0^2 = 8p^2+5pq+5q^2,  D_1^2 = 5p^2+5pq+8q^2,  D_2^2 = 8p^2+11pq+8q^2.
This script verifies symbolically that mu_n = 0 for n <= 7 and prints mu_8 and mu_9 in factored form.

Requires sympy.   usage: python common_root_family.py
"""
import sympy as sp

p, q, D = sp.symbols('p q D')
BIN = (1, 3, 3, 1)
L = [q, -p, sp.Integer(0)]
v = [8 * p**2 + 5 * p * q + 5 * q**2, 5 * p**2 + 5 * p * q + 8 * q**2, 8 * p**2 + 11 * p * q + 8 * q**2]
omega = [p, q, -(p + q)]


def block_moment(Li, vi, n):
    """sum_j C(3,j)(-1)^j (3(L-D)/2 + j D)^n / D^3, as a polynomial in L and D^2 = v"""
    e = sum(BIN[j] * (-1)**j * (sp.Rational(3, 2) * (Li - D) + j * D)**n for j in range(4))
    e = sp.Poly(sp.expand(sp.cancel(e / D**3)), D)
    assert all(k % 2 == 0 for (k,), _ in e.terms()), 'odd power of D'
    return sum(c * vi**(k // 2) for (k,), c in e.terms())


for i in range(3):
    disc = sp.Poly(v[i].subs(q, 1), p).discriminant()
    print('quadratic form %d: discriminant %s (negative: positive definite)' % (i, disc))

for n in range(0, 10):
    mu = sp.factor(sp.expand(sum(omega[i] * block_moment(L[i], v[i], n) for i in range(3))))
    print('mu_%d =' % n, mu)

quartic = 6 * p**4 + 5 * p**3 * q - 10 * p**2 * q**2 + 5 * p * q**3 + 6 * q**4
print('quartic factor of mu_9 at q = p :', sp.expand(quartic.subs(q, p)))
print('quartic factor of mu_9 at p = -2q:', sp.expand(quartic.subs(p, -2 * q)))
print('quartic factor of mu_9 at q = -2p:', sp.expand(quartic.subs(q, -2 * p)))
