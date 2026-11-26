# Round 2, confirmation pass: GPT-6.2 Astra on version 3

Same referee and session as round 2. The report is reproduced verbatim except for one section and two
cross-references to it, which concern the supplementary files and not the mathematics. The reply is in
`round2-confirmation-response.md`.

---

# Version 3 confirmation report

**Minor revisions required**

To the author of *Positive roots of sums of cubes of binomials*,

The real-exponent result is correct. Proposition 10 proves the upper bound nine, Proposition 11 attains it, and the new Lean file checks the algebraic implication claimed for it. The finite computation in Proposition 13 also stands. The remaining corrections concern the wording of a real-root count, the scope and credit of earlier work, and the release materials. The proposed Discussion still points to an unavailable branch. I made no changes to the submitted files.

## A. Disposition of the eight Review 2 corrections

| No. | Status | Finding |
|---|---|---|
| 1. Supplementary files | **Resolved for the documented public package** | The project-state survey, both literature reports and the review prompts are absent. `research-log/` contains the rewritten log. `reviews/` contains the five files described in the reply. |
| 2. Dutta | **Resolved** | Former Remark 10 is gone. The paragraph after Proposition 3 gives the correct bound in terms of the support union, and §7 does not restate the conjecture. The counterexample is absent from the manuscript. It survives in **both** the archived Round 2 report and the reply. [Dutta, Theorem 10](https://logic.pdmi.ras.ru/csr2021/sites/logic.pdmi.ras.ru.csr2021/files/Pranjal-Dutta/index.pdf) |
| 3. Real-exponent bound | **Resolved** | Proposition 10, the last sentence of Proposition 11 and the first question in §8 correctly distinguish the exact real-exponent maximum from the open polynomial question. One sentence after the proof describes an implication backwards. |
| 4. Proposition 12 and contributor credit | **Partly resolved** | The normalization, exceptional lines, parentheses and main attribution are correct. The introduction overstates silentoplayz’s result, and the script header still credits maxkieff with only the first two squared widths. |
| 5. Scope of Lean verification | **Partly resolved** | The nonzero convention, Table 1 caption, Example 8 and Mathlib reference are correct. The introduction and Appendix A still make blanket statements contradicted by `L-gct-234`, which proves an upper bound. |
| 6. Computation and reproduction | **Partly resolved** | The reductions, linked-pair table, modular test, interval step and six-part commands are in place. The new checker evaluates the correct points. The remaining error is documentary: only the four-cube sample points are printed in the manuscript. |
| 7. Product files and literature | **Resolved** | Appendix A correctly describes the eight explicit roots in row 267, twelve crossings plus zero in row 269, and fifteen half-integer intervals in row 271. The revised Wronskian comparison and qualified multiplicity literature statement in §7 address the review. The newly added \(x^2\) sentence in §6 needs a separate correction. |
| 8. Release history, credits and links | **Partly resolved** | The disclosure assigns the two reviews to the correct versions. Table 1 identifies PR submitters, and the credits distinguish the earlier unmerged row-234 submission. I checked the eighteen merged PR records and the unmerged one. The six release links remain unavailable. |

## B. Mathematical and computational checks

**Propositions 10 and 11.** Moving a positive root \(r\) to \(1\) replaces \(A_i,B_i\) by \(A_ir^{a_i},B_ir^{b_i}\). The substitution \(x=e^u\) preserves the order there. Expanding one cube and multiplying by \(e^{-3tu}\) gives exactly the four frequencies printed in \(T_n(t)\), with coefficients \(A_i^3,3A_i^2B_i,3A_iB_i^2,B_i^3\). If \(c_iA_iB_i(a_i-b_i)=0\), that summand has at most one term, including the possibility of complete cancellation. The whole sum then has at most \(1+4+4=9\) terms and order at most eight.

For the genuine inputs, Lean proves precisely
\[
(\forall n<10,\ \forall t,\ T_n(t)=0)
\quad\Longrightarrow\quad
(\exists t_0,\ \forall n,\ T_n(t_0)=0).
\]
The two paper steps suffice. Multiplication by a nonvanishing exponential preserves order, and the Vandermonde matrix on the distinct shifted frequencies forces every aggregated coefficient to vanish. I freshly built `PEqualNP.Outside.L_gct_234` and compiled `RealExponentMoments.lean` with Lean 4.36.0. The proof body matches the Review 2 file. The main theorem printed exactly `propext`, `Classical.choice` and `Quot.sound`.

I independently recovered \(4\sqrt6/315\) as the first nonzero Taylor coefficient of \(\Phi\), in degree nine. At \(p=q=1\), the coefficients of the two hyperbolic terms in \(G(e^{2s/3})\) are \(-16/18^{3/2}\) and \(16/27^{3/2}\). Dividing by their respective coefficients in \(\Phi\) gives \(-8/(81\sqrt6)\) in both cases. The normalization in Proposition 12 and the exact maximum in Proposition 11 follow.

**Propositions 3 and 13.** The new proof of Proposition 3 works: real cube injectivity gives the same zero set as \(g_1+g_2\), and the displayed example gives \((x-1)(x-2)(x-3)\). In Proposition 13, translating exponents preserves positive-root order, the nine-term requirement forces two genuine inputs, and the pivot cases cover the remaining triples. The modular rejection has the required leading-coefficient safeguard. The interval code rejects a split only when a necessary equation provably fails. I reran the independent finite-field checker. In table order the counts were **3,787; 2,145,738; 1,673,517; 294,861; 61,393**, with **zero unresolved triples**. I also ran the supplied self-tests, moment scripts and exact certificate checker. All 16 and 20 rational sample points match the respective Lean lists.

**Section 6.** I expanded row 261 from its coefficients. In increasing degree the signs are `+-+-+--+-+`, with eight changes. The eight certified crossings therefore exhaust the positive roots, all simple. For the \(x^2\) substitution, the \(2r\) **nonzero** real roots are exact if the original has exactly \(r\) positive roots. Zero can give one more. For example, \(f=x^2-x-1,\ g=1\) gives \(fg+1=x(x-1)\), and the substituted polynomial has three distinct real roots.

This was a confirmation pass. I did not recompile the other unchanged Lean files or repeat the randomized discovery searches.

## C. Audit of the supplementary files

[Omitted here: a section about the content of the supplementary files, without mathematical content.]

## D. Proposed GitHub Discussion

The draft explains the purpose and method, distinguishes the models’ contributions, expressly identifies the reviews as AI-assisted, and makes all five requests of the desk. Its tone is modest. I found no em dashes or unsupported priority claim. I recommend retaining the title and making these exact changes:

1. **Line 5, final sentence.** “In Discussion #21999, maxkieff gave the order-seven example, the common-root bound and the descent modulo five. Silentoplayz gave an obstruction for certain exponent patterns when the multiplicity is one less than the number of occupied powers.” Retain the discussion link. [Upstream discussion and reply](https://github.com/open-goat/pequalnp-proofs/discussions/21999)
2. **Line 10.** Replace “the exact maximum 4k - 1” with “the exact maximum of \(4k-1\) **distinct positive roots for a nonzero sum of \(k\) binomial cubes**.”
3. **Line 11.** “For a nonzero sum of three cubes of two-term signomials with real exponents, the largest order of a positive root is nine. The upper bound extends Aargau’s polynomial proof, and an explicit example attains it. The note also computes two further moments of maxkieff’s common-root family. For polynomial binomials the maximum is between seven and nine. An exhaustive computation gives an upper bound of seven when all input exponents lie in \([0,32]\).”
4. **Line 15.** Replace “wrote the Lean file for that step” with “wrote the Lean file proving the implication between the shifted moment equations.”
5. **Lines 19–24.** Replace the branch reference in all six links with the approved public commit and verify each destination. I confirmed that the fork exists, the proposed Git ref returns **404**, and the note directory is absent from the default branch. Publication of the Discussion should await working links.

## E. Remaining mandatory corrections

Line numbers below refer to `paper/sparse-root-bounds.tex` unless another file is named.

| Location | Severity | Reason and replacement |
|---|---|---|
| §6, lines 588–590 | Minor | The substitution can also produce the root zero. Use **“If \(fg+1\) has \(r\) distinct positive roots, then \(f(x^2)g(x^2)+1\) has at least \(2r\) distinct real roots, with the same sparsity per factor. The three positive-root files therefore give real-root lower bounds of 16, 22 and 24.”** |
| Introduction, lines 120–123; §5.2, lines 447–449; `scripts/common_root_family.py:8` | Minor | Use **“Silentoplayz excludes order 11 with 12 occupied powers, and order 10 with 11 occupied powers, when three consecutive slots of one cube are unshared and no other occupied power lies between them.”** The reply’s one-dimensional argument does not cover order 10 with 12 occupied powers. For Proposition 12 use **“For distinct centres, the moment equations determine the weights up to a common factor. Part (i), including all three squared widths, is maxkieff’s calculation. The third displayed formula follows by substituting his value of \(B\) into his equation for \(V\).”** Give the same credit in the script header and the author reply. [Earlier Lean calculation](https://github.com/maxkieff/pequalnp-proofs/blob/27acb67dbe/lean/PEqualNP/Research/SparseCubeBoundary.lean#L75-L86) |
| Abstract, lines 52–55; introduction, lines 112–114; Appendix A, lines 706–709; after Proposition 10, lines 391–394 | Minor | Specify **“positive root”** in the abstract’s multiplicity claim. For the verification summary use **“Row 234 proves a polynomial multiplicity upper bound. The root-count files certify lower bounds for explicit examples. When a witness attains the Descartes bound, the bound also gives exactness and simplicity. The general root-count theorem additionally uses gluing.”** After Proposition 10 use **“The two steps proved on paper are the passage from order at least ten to the ten shifted moment equations, and the Vandermonde deduction from cancellation at one shift.”** |
| Appendix A, lines 729–731; `README.md:36,39,63`; `scripts/check_certificates.py:2,6`; `reviews/round2-response.md:47,76` | Minor | Example 8 prints the polynomial. Its points are in the certificate and Lean file. Use **“The checker evaluates both polynomials at the rational points stored in their certificates. The sixteen points for Theorem 6 are also printed in the manuscript.”** |
| `reviews/README.md:23–25` | Minor | Make the independent coverage unambiguous. Use **“Round 1 independently checked the nontriangle cases and reran the supplied triangle program. Round 2 independently checked all 4,179,296 triples, including the triangles.”** |
| `discussion-post.md:5,10–11,15,19–24` and release contents | Minor wording; **posting blocker** for links | Apply the replacements in D and verify the six links against the approved release. |

These corrections require no change to the mathematical proofs or certificates. The polynomial multiplicity maximum remains between seven and nine. The exact value nine established in version 3 is for real exponents.
