# Positive roots of sums of cubes of binomials

A research note proposed to the PEqualNP project for evaluation. It is not an official publication of the project and
it has not been peer reviewed. It was prepared by an AI system (Claude Fable 5.2, Anthropic) and reviewed by AI systems
acting as referees (OpenAI GPT-6 Astra for version 1, GPT-6.2 Astra for version 2). A review by an AI system is not
academic peer review. No human mathematician has checked the text.

- Paper: [`paper/sparse-root-bounds.pdf`](paper/sparse-root-bounds.pdf), LaTeX source [`paper/sparse-root-bounds.tex`](paper/sparse-root-bounds.tex)
- Related discussion, whose results on multiplicity the note uses and credits:
  <https://github.com/open-goat/pequalnp-proofs/discussions/21999> (maxkieff, silentoplayz)

## Content

1. An account of eighteen Lean-checked statements of `open-goat/pequalnp-proofs` (`L-gct-234`, and `L-gct-241` to
   `L-gct-273`, odd numbers), submitted by Aargau, BastianMIllan, blarneys, gcq, hedanbaomi, junyeopYim, k-sandhu,
   SemyonOsadchii and XXXLUMI. All eighteen files were recompiled against Mathlib alone.
2. A sum of four cubes of real binomials with 15 distinct positive roots, the bound given by Descartes' rule; the
   lower bound is checked in Lean. The file of `L-gct-251` has 14.
3. Proved in the note, not formalized: a gluing lemma, and with it N(k) = 4k - 1 for every k >= 3, where N(k) is the
   largest number of distinct positive roots of a nonzero sum of k cubes of real binomials. N(1) = 1 and N(2) = 3.
4. On the order of a root of a sum of three cubes: the bound 9 of `L-gct-234` (Aargau) also holds for real
   exponents, and an identity shows that 9 is attained there; two further moments of maxkieff's common-root family;
   an exact computation showing that no example with integer exponents in [0, 32] has a positive root of order 8 or
   more.

The note says nothing about the truth of the real tau-conjecture, and it claims no priority.

## Layout

| path | content |
|---|---|
| `paper/` | LaTeX source and PDF |
| `lean/FourCubes15.lean` | at least 15 positive roots for an explicit sum of four cubes of binomials (imports Mathlib only) |
| `lean/FiveCubes19.lean` | a second example for five cubes with small exponents, at least 19 roots |
| `lean/RealExponentMoments.lean` | the moment step of `L-gct-234` with real exponents (imports that file) |
| `data/*_certificate.json` | the two examples with their rational sample points and the signs (the sixteen points of Theorem 6 are also printed in the note) |
| `data/*_candidate.json`, `data/search_hits_raw.txt` | output of the numerical search for examples |
| `data/search_logs/` | complete output of the computation behind Proposition 13 |
| `scripts/check_certificates.py` | exact evaluation of both polynomials at the rational points stored in their certificates |
| `scripts/order9_identity.py`, `scripts/common_root_family.py` | computer-algebra checks of Propositions 11 and 12 |
| `scripts/mult_search.py`, `scripts/mult_triangles.py` | the computation behind Proposition 13 |
| `scripts/sym.py`, `scripts/rationalize.py`, `scripts/gen_lean.py`, `scripts/exact_check.py` | search for examples, rounding to exact data, generator of the two Lean files |
| `scripts/prescribed.py`, `scripts/fg_dd.py` | earlier searches, including the inconclusive search for 9 roots of `f g + 1` |
| `scripts/recheck_rows.sh` | recompiles all the Lean files and checks the axioms |
| `research-log/` | working log with software versions |
| `reviews/` | record of the two reviews and the replies |

## Reproducing

Lean, from the root of the repository, after the project's setup has fetched the prebuilt Mathlib:

```
bash notes/note-sparse-root-bounds/scripts/recheck_rows.sh
```

The script exits with status 0 only if all twenty-one files compile and each final theorem depends on exactly
`propext`, `Classical.choice`, `Quot.sound`.

Python 3.10 or later, from `notes/note-sparse-root-bounds/scripts/`. The first command needs only the standard
library; the others need `sympy mpmath scipy numpy python-flint`.

```
python check_certificates.py        # Theorem 6 and Example 8: exact signs at the certificate points
python order9_identity.py           # Proposition 11
python common_root_family.py        # Proposition 12
python mult_search.py selftest
for i in 0 1 2 3 4 5; do python mult_search.py 32 6 $i; done      # each part must end with "hits 0"
for i in 0 1 2 3 4 5; do python mult_triangles.py 32 6 $i; done   # each part must end with "flagged 0"
```

Each part of the two last commands takes about fifteen minutes; the output of the complete runs is in
`data/search_logs/`. The generator `gen_lean.py` reproduces the two Lean files and the certificates from the
candidate files:

```
python gen_lean.py ../data/four_cubes_candidate.json 7 120 SparseRootBounds.FourCubes \
       SparseRootBounds.four_binomial_cubes_fifteen_positive_roots FourCubes15.lean
python gen_lean.py ../data/five_cubes_candidate.json 6 200 SparseRootBounds.FiveCubes \
       SparseRootBounds.five_binomial_cubes_nineteen_positive_roots FiveCubes19.lean
```

The searches for examples (`sym.py`) are randomized; the exact checks and the Lean files do not depend on them.

## Licence and reuse

The Lean files reuse code of `open-goat/pequalnp-proofs`, Apache-2.0: the interval arithmetic and the counting
argument of the files of `L-gct-251` (k-sandhu) and `L-gct-261` (hedanbaomi), and the lemmas of the file of
`L-gct-234` (Aargau). The content of this directory is offered under the same licence.
