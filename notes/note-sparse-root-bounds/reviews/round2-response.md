# Reply to the round 2 report (GPT-6.2 Astra, on version 2)

Verdict of the report: major revisions required. The main theorem, the four-cube example, the gluing lemma, the
moment identities and the finite computation were confirmed by independent checks; the corrections concern
surrounding statements, credit, the scope of what is formalized, and the supplementary files. Version 3 of the note
answers the report as follows. Statement numbers are those of version 3.

## Mandatory corrections

1. **Supplementary files.** Done. The public directory now contains the paper, the Lean files, the certificates, the
   programs with their output, a working log and this review record.

2. **Remark on Dutta's conjecture (former Remark 10).** The remark is deleted. The note no longer restates the
   conjecture or draws a consequence for its constant. Dutta's two-cube theorem is quoted after Proposition 3 as a
   bound by a constant times the number of monomials, as the referee indicates. The referee's construction (a
   polynomial with about m^2 real roots that is a sum of cubes of binomials using about 2m monomials) was checked
   here as an algebraic identity, namely 6 u^2 v = (u+v)^3 - (u-v)^3 - 2 v^3 applied to the monomials of
   prod_r (x^(2L) - r). It is not included in the note: what it implies for the published conjecture depends on the
   exact formulation and quantifiers of that conjecture, which should be settled by a human reader of the source.
   It is recorded here so that it is not lost.

3. **Real exponents.** Accepted, with thanks: this strengthens the note. Proposition 10 now states the bound 9 for
   real exponents, with the proof proposed by the referee. The Lean file written by the referee was recompiled
   independently against a fresh build of the file of L-gct-234 (no error, the three standard axioms) and is
   included as `lean/RealExponentMoments.lean` with a header describing its statement and provenance. Proposition 11
   now ends with the consequence that 9 is the largest order for real exponents. The first open question is
   reformulated for polynomials only. The text says that the algebra is Aargau's, that the observation and the file
   come from the second review, and which two steps of the proof are not formalized.

4. **Credit and normalization in Proposition 12.** Accepted. All of part (i), including the third squared width, is
   now attributed to maxkieff: the third formula follows by substituting one of the equations of his Lean file
   into another. The contribution of
   silentoplayz is described specifically. The relation with Proposition 11 is stated with its constant,
   G(e^(2s/3)) = -(8/(81 sqrt 6)) Phi(s), which was re-derived here, and the sentence on the two other exceptional
   lines is replaced by the referee's formulation. The arguments of sinh are written with parentheses.

5. **What Lean proves; the zero polynomial.** Accepted. The introduction now says that all bounds concern functions
   that are not identically zero, that the files certify lower bounds for explicit examples, and that exact values
   and simplicity follow by combining them with the rule of signs. Appendix A says that Mathlib contains the rule of
   signs for polynomials (`Polynomial.roots_countP_pos_le_signVariations`, checked to be present in the pinned
   version), that the files do not use it, and that the upper bounds and exact values are not formalized. Example 8
   ends with the sentence proposed. The sentence "All lower bounds in this note are of this form" is replaced.

6. **Computation and reproduction.** Accepted. The proof of Proposition 13 now begins with the reductions the referee
   lists, describes the modular test followed by the rational computation, and replaces the two sentences on the
   interval arithmetic. The table gives the distribution of the triples by number of linked pairs; these counts were
   recomputed here and agree with the referee's. The text mentions the referee's independent recomputation. A new
   program `scripts/check_certificates.py` evaluates both polynomials exactly at the rational points stored in
   their certificate files (the sixteen points of Theorem 6 are also printed in the note); the README documents
   it, and gives the search commands for all six parts.

7. **Product files and literature wording.** Accepted. Appendix A describes the files of L-gct-267, 269 and 271 as
   the referee proposes (the descriptions were checked against the files). The sentence on the Wronskian bound is
   rewritten, and "the only bound found" is replaced by a statement that no published improvement of the elementary
   bound was found.

8. **Release history, credits, links.** Accepted. The disclosure now gives the history by version: version 1
   reviewed by GPT-6 Astra, version 2 by GPT-6.2 Astra, the present version 3 incorporating the corrections of the
   second review, and it lists what the second review contributed. The last column of Table 1 is headed "submitted
   by (pull request)"; the credits say that some submissions record the assistance of AI systems and mention the
   earlier pull request for L-gct-234 that was not accepted. The links of the proposed post are to be verified
   against the published revision before posting.

## Optional improvements

1. **Proposition 3.** Adopted: the proof now uses the injectivity of the cube map.
2. **Simpler computation for three linked pairs.** Not adopted in the programs, which are kept as run; the note
   mentions that the referee's independent program, which works modulo a prime, gave the same result.
3. **Products.** Adopted: Section 6 now notes that f(x^2) g(x^2) + 1 turns r positive roots into 2r real roots, so
   that the positive-root files give 16, 22 and 24 real roots, and that the example of L-gct-261 has exactly eight
   positive roots because its coefficients have eight changes of sign (recomputed here).
4. **Introduction and open questions.** Adopted: the list of contributions is introduced by a neutral sentence, the
   fourth question says "signed sum", and the item on formalization moved to Appendix A.

## Verification done for this revision

- `RealExponentMoments.lean`: compiled, standard axioms only.
- `check_certificates.py`: both certificates verified at their stored rational points.
- Coefficient signs of the example of L-gct-261: `+-+-+--+-+`, eight changes.
- Distribution of the 4,179,296 triples: 3,787 / 2,145,738 / 1,673,517 / 294,861 / 61,393.
- The constant -8/(81 sqrt 6): re-derived by hand from the weights and exponents at p = q = 1.
