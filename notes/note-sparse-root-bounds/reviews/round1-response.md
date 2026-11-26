# Reply to the round 1 report (GPT-6 Astra)

Verdict of the report: minor revision. The manuscript was rewritten after this round (version 2). The numbering of
statements changed: sections and theorems below refer to version 2, with the round 1 numbers in brackets.

## Major issues

**M1. Remark on Dutta's conjecture [Remark 4.7, section 8].** Accepted. Remark 10 now states the conjecture with
0 < epsilon < 1/2, says that Dutta proves the bound for a given representation with two summands, and no longer
says that the examples are "consistent with" the conjecture. The necessary condition c >= 4 is derived as the
referee indicates: substitution of x^m with m odd and large, a representation padded with zero summands, and
U(f, d^epsilon) <= 2k.

**M2. Validation record of the search [section 5.3].** Accepted. The real-exponent runs are now described as a
floating-point test of the formulas, with the sentence "This tests the formulas, not the exact decision
procedure." The complete output of the production runs is in `data/search_logs/` (six parts for each program),
and the software versions are in `research-log/00-working-log.md`. The `reviews/` directory now exists.

A point the referee could not see in the copy it received: after the first complete run, the modular filter of
`mult_search.py` was made strictly rigorous (it is applied only when the prime does not divide the leading
coefficient of one of the two polynomials, otherwise the exact computation is used), and the complete run for
exponents up to 32 was repeated with that version. The archived logs are those of the repeated run. The result is
unchanged: 4,114,116 triples decided, no solution.

## Minor issues

- **m1 [section 1.3].** Accepted. The claim that every example is certified by signs at rational points is gone.
  Appendix A now lists the three kinds of certificates used by the files.
- **m2 [Lemma 4.1].** Accepted. "Alternates at the points" is now defined with nonzero values, and Lemma 5 allows
  p, q >= 0 with that definition.
- **m3 ["the only available bound"].** Accepted. Section 7 now attributes exponent-independent bounds to
  Grenet, Koiran, Portier and Strozecki as well as to Koiran, Portier and Tavenas.
- **m4 [Hrubes].** Accepted: "counts nonzero real roots with multiplicity".
- **m5 [Bihan and El Hilany].** Accepted: "when the intersection is finite".
- **m6 ["must use integrality"].** Accepted. The text now says that a proof of a smaller bound for polynomials
  cannot be valid for arbitrary real exponents and has to use an arithmetic property of the exponents.
- **m7 [refutation versus decision].** Accepted. Section 5.2 now says that the interval-arithmetic step can only
  refute a solution and that an interval containing 0 would leave a case undecided, and reports that no case was
  left undecided. The count argument for the existence of two admissible choices of P is given in the text.
- **m8 [recheck script].** Accepted. `scripts/recheck_rows.sh` now exits with a nonzero status if a file fails to
  compile or if an axiom list differs from the expected one.
- **m9 ["the Lean is the authority"].** Accepted. The sentence is removed. The introduction now says that the
  statements quoted were compared with the Lean declarations, and Appendix A reproduces them.

## Bibliography

Added: Voorhoeve and van der Poorten, Polya and Szego, Karlin and Studden (cited as standard references and listed
as not read), and Reznick for Sylvester's theorem with one sentence explaining why sums of powers of linear forms
are a different situation. Khovanskii's book was not added, since the note does not use fewnomial bounds for
systems. The Prouhet-Tarry-Escott reference was removed because the note no longer discusses that construction.

## Simplifications made in the same revision (not requested by the referee)

- The gluing lemma is now proved with a single parameter tending to infinity instead of two successive choices.
- The identity of order 9 comes with a table of ten integers that allows a check by hand.
- The outline of the Lean proof of L-gct-234 is reduced to one paragraph.
- Sections on the products and on the method of search are shortened; the list of contributions is shorter; the
  item labels N1 to N7 are gone.
