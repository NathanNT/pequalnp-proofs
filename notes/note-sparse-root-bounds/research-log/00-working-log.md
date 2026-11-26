# Working log

Date: 2026-11-26. State of `open-goat/pequalnp-proofs` examined: commit
`ff9577c31478c84118afce361cbf5c332499ab24` (main). The work recorded here was done by an AI system
(Claude Fable 5.2, Anthropic); see the disclosure of the note.

## 1. State of the project at the start

- Eighteen statements of the family `L-gct-234`, `L-gct-241` to `L-gct-273` were checked upstream; the pairs
  `L-gct-236/237` and `L-gct-238/239` (order of a root for cubes of trinomials and 4-nomials) were open and are not
  treated in the note.
- The project had one paper, on a different subject, and no write-up of these statements.
- Discussion #21999 (maxkieff, with a reply by silentoplayz) treats the order of a root for three cubes.
- The repository accepts Lean proofs of posted statements; the note is therefore not proposed as a pull request.
- The project's records do not mention the real tau-conjecture; the connection is made by the note.

## 2. Lean verification

All files were compiled with Lean 4.36.0 against the pinned Mathlib (commit
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`), the eighteen repository files after deleting the line
`import PEqualNP.Defs` where present, each followed by `#print axioms`. Result in every case:
`propext`, `Classical.choice`, `Quot.sound`.

- Repository files: `L_gct_234` (about 140 s), `241` (73 s), `267` (279 s), the fifteen others (7 to 19 s each).
- Files of the note: `FourCubes15` (67 s), `FiveCubes19` (8 s), `RealExponentMoments` (9 s after building
  `L_gct_234` as a module).

## 3. What the files exhibit beyond their statements

| name | family | statement | exhibited in the file | rule of signs |
|---|---|---|---|---|
| 241 | 3 cubes of binomials | > 9 | 11 | 11 |
| 251 | 4 cubes of binomials | > 13 | 14 | 15 |
| 253 | 5 cubes of binomials | > 17 | 19 | 19 |
| 255 | 6 cubes of binomials | > 21 | 23 | 23 |
| 243, 245, 247, 249 | 3 cubes of 3-, 4-, 5-, 6-nomials | > 14, 21, 26, 33 | 15, 23, 27, 35 | 29, 59, 104, 167 |
| 257, 259 | 3 cubes of binomials, trinomials, real roots | > 19, > 29 | 22, 30 | 23, 59 |
| 261, 263, 265 | f g + 1, t = 3, 4, 5, positive roots | > 7, 10, 11 | 8, 11, 12 | 9, 16, 25 |
| 267, 269, 271 | f g + 1, t = 3, 4, 5, real roots | > 7, 12, 14 | 8, 13, 15 | 19, 33, 51 |
| 273 | p q - r s, 4-nomials | > 22 | 23 | 31 |

## 4. Results added by the note

1. Four cubes of binomials with 15 positive roots: found by a numerical search (section 6), made exact, verified in
   exact rational arithmetic (`scripts/check_certificates.py`) and in Lean (`lean/FourCubes15.lean`).
2. A second example for five cubes with 19 roots and exponents at most 384 (`lean/FiveCubes19.lean`).
3. Gluing lemma and N(k) = 4k - 1 for k >= 3 (proofs in the note).
4. Order of a root of three cubes:
   - moments 8 and 9 of the common-root family of Discussion #21999 (`scripts/common_root_family.py`);
   - the identity 3 sqrt3 cosh(s) sinh^3(sqrt2 s) - 2 sqrt2 sinh^3(sqrt3 s) = (4 sqrt6/315) s^9 + O(s^11)
     (`scripts/order9_identity.py`);
   - the bound 9 for real exponents (from the second review; `lean/RealExponentMoments.lean`);
   - exact computation for integer exponents in [0, 32]: no root of order 8 or more. 4,179,296 exponent triples:
     3,787 with fewer than nine exponents; 2,145,738, 1,673,517 and 294,861 with zero, one and two linked pairs,
     treated by `scripts/mult_search.py`; 61,393 with three linked pairs, treated by `scripts/mult_triangles.py`.
     No solution, no undecided case. The first complete run used a modular filter without the test on the leading
     coefficient; the run was repeated with the test, with the same result, and the archived output
     (`data/search_logs/`) is that of the repeated run.

## 5. Searches without result

- `f g + 1` with trinomials and nine positive roots: the searches (`scripts/prescribed.py`, `scripts/fg_dd.py`)
  converged only to degenerate configurations in which the exponents of one factor merge; the polynomials
  reconstructed from them have at most seven changes of sign at the sample points. No conclusion.
- Four cubes with one reflected pair and two self-reflected binomials: no example with 15 roots in about 3400 starts.
- Sums of three cubes with real exponents and a root of order 9, by least squares from random starts: only
  degenerate configurations. The example of order 9 was found through the common-root family instead.

## 6. Method of the search for examples

A signomial with n + 1 exponents is determined up to a factor by n simple positive roots. The unknowns are the
exponents of the binomials and the roots; the equations say that the four coefficients of each cube have the form
(A^3, 3A^2B, 3AB^2, B^3). The search was restricted to polynomials P with x^(3N) P(1/x) = -P(x), built from pairs
g(x), -x^N g(1/x) and binomials c (x^(N/2+m) - x^(N/2-m)), which halves the number of unknown roots
(`scripts/sym.py`). Numerical solutions were made exact by `scripts/rationalize.py`.

## 7. Software

- Lean 4.36.0, Mathlib at the commit above.
- Python 3.14.7, sympy 1.14.0, mpmath 1.3.0, scipy 1.18.1, numpy 2.5.5, python-flint 0.9.0.
- pdfTeX 1.40.25 (TeX Live 2023).
- Reviews: GPT-6 Astra (`gpt-6-astra`) on version 1 and GPT-6.2 Astra (`gpt-6.2-astra`) on version 2, both at
  reasoning effort xhigh, run non-interactively with the Codex engine. See `reviews/`.
