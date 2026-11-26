# Round 2 report: GPT-6.2 Astra on version 2

Model: OpenAI GPT-6.2 Astra (`gpt-6.2-astra`), reasoning effort xhigh, run non-interactively with the Codex
engine in a copy of the submission, with access to Lean, Python and the web. The report is reproduced
verbatim except for the omissions marked in square brackets, which concern the supplementary files and not
the mathematics, and the address of the hosting repository in section 6. The reply is in
`round2-response.md`.

---

## 1. Editorial verdict

**Major revisions required**

To the author of *Positive roots of sums of cubes of binomials*,

The main theorem stands. The four-cube example has exactly fifteen simple positive roots, the revised gluing proof works, and the finite multiplicity exclusion survives an independent computation over all 4,179,296 exponent triples. These results justify submitting a corrected note to the research desk for evaluation.

Three findings change the editorial decision. The uniform inequality attributed to Dutta in Remark 10 admits an elementary counterexample. The real-exponent multiplicity question listed in Section 8 can be answered using Aargau’s existing proof. [One further finding, about the supplementary files and without mathematical content, is omitted here.] The proposed fork branch also returned 404. **Hold the Discussion for correction and link verification.**

## 2. What I verified myself

**Manuscript and formal sources.** I read the TeX, extracted the PDF text and properties, and inspected renderings of all thirteen pages. I compared the eighteen row files with the upstream Git blobs at the cited commit. All eighteen matched after line-ending normalization. I checked the final declarations, the internal root counts, all eighteen merged pull requests, and their commit records. The numbers and submitting accounts in Table 1 agree with those records. I also read the relevant parts of Discussion #21999 and the earlier common-root Lean proof linked there. [Pinned upstream repository](https://github.com/open-goat/pequalnp-proofs/tree/ff9577c31478c84118afce361cbf5c332499ab24) · [Discussion #21999](https://github.com/open-goat/pequalnp-proofs/discussions/21999)

**Lean.** I compiled all eighteen upstream files and both accompanying files with Lean 4.36.0 and Mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. I removed `import PEqualNP.Defs` in scratch copies where present. All twenty compilations succeeded. Every final theorem printed exactly `propext`, `Classical.choice`, and `Quot.sound`. I also regenerated both new Lean sources and their JSON certificates from the candidate data and the row-251 template. They matched the supplied files.

**Root counts.** I independently evaluated the six algebraic sample points in Theorem 4 with rigorous ball arithmetic. All four numerical columns round as printed. The first two totals, where cancellation matters most, are approximately \(1.0772677650\times10^{-5}\) and \(-2.0133710119\times10^{-4}\). The six signs are \(+,-,+,-,+,-\). The reciprocal identity gives the other six signs.

| Witness | Independent check | Conclusion |
|---|---|---|
| XXXLUMI’s three cubes | Twelve distinct exponents, reciprocal symmetry, eleven sign changes | Eleven simple positive roots |
| Theorem 6, four cubes | Degree 4608, sixteen terms, direct rational evaluation at every printed point, signs starting negative | Fifteen simple positive roots |
| Example 8, five cubes | Degree 1152, twenty terms, direct rational evaluation at every certificate point, signs starting positive | Nineteen simple positive roots |
| k-sandhu’s row 251 | Fourteen certified crossings and fourteen changes in the expanded coefficient signs | This particular witness has exactly fourteen positive roots |
| hedanbaomi’s row 261 | Nine alternating sample values and eight changes in the expanded coefficient signs | This particular \(fg+1\) has exactly eight simple positive roots |
| BastianMIllan’s row 267 | Exact factorization after multiplication by 50176 | The roots are \(\pm1,\pm4,\pm7,\pm8\) |

**Gluing and extremality.** The revised definition of alternation handles a one-point list correctly. In Lemma 5, the perturbation tends to zero at every fixed \(x_i\), while
\[
\lambda^{-d-1}R_\lambda(\lambda y_j)\longrightarrow \sigma y_j^{3n}Q(y_j)\ne0.
\]
The two lists eventually separate, including when \(p=0\) or \(q=0\). Multiplication by \(x^{3n}\) preserves the required cube representation. The induction from \(3,4,5\) and the real-root construction \(x^3P(x^2)\) both follow. The earlier bases \(3,5,6\) alone do give every \(k\ge3\) except \(4,7\).

**Multiplicity.** I recovered the coefficient 2925 of \((x-1)^7\) in maxkieff’s example. I independently obtained both moment factorizations in Proposition 12 and all ten integers in Proposition 11. The difference in the ninth derivatives is \(4608\sqrt6\), giving \(4\sqrt6/315\) after division by \(9!\). The order-nine signomial has twelve distinct exponents. I also tested the real-exponent extension of Aargau’s argument described in mandatory correction 3.

**Exhaustive computation.** I inspected both supplied search programs, checked the twelve archived run summaries, ran the self-tests, and wrote a separate finite-field checker. It used the prime 32749 and did not use the submitted rational-gcd or ball-arithmetic routines. My counts were:

| Configuration | Triples |
|---|---:|
| Fewer than nine distinct exponents | 3,787 |
| No linked pairs | 2,145,738 |
| One linked pair | 1,673,517 |
| Two linked pairs | 294,861 |
| Three linked pairs, at least nine distinct exponents | 61,393 |
| **Total** | **4,179,296** |

There were **zero unresolved triples**. In particular, the independent check covered all 61,393 triples for which the submitted program isolates roots and tests a coefficient split. This establishes Proposition 13 at its stated finite range to the usual standard of an exhaustive computer calculation.

**Literature and limits of my checks.** I consulted primary sources for Koiran’s conjecture and permanent implication, the exponent-independent bounds, the historical \(fg+1\) question, Dutta’s support-union definition, Hrubeš’s multiplicity qualification, and the comparisons with sparse intersection theory. The Koiran–Portier–Tavenas bound quoted in Section 7 evaluates to about \(8.0570\times10^{12}\). I did not independently derive Aargau’s two large polynomial certificates by hand, repeat the randomized discovery runs, read the Hungarian Hajós original or the three classical books/articles identified as unread, or establish historical priority. I verified Dutta’s conference formulation against the author’s text and the journal bibliographic record. I did not verify the full 2026 journal formulation. [Koiran](https://arxiv.org/pdf/1004.4960) · [Koiran, Portier and Tavenas](https://arxiv.org/pdf/1205.1015) · [Dutta, §4 and Theorem 10](https://logic.pdmi.ras.ru/csr2021/sites/logic.pdmi.ras.ru/csr2021/files/Pranjal-Dutta/index.pdf) · [Journal record](https://link.springer.com/article/10.1007/s00224-026-10294-7) · [Hrubeš](https://users.math.cas.cz/~hrubes/PDFs/RealTau.pdf)


## 3. Mandatory corrections

1. [Omitted here: a passage about the content of the supplementary files, without mathematical content. The requested changes were made.]

2. **Major · Correct Remark 10 and its interpretation in Section 7.** `paper/sparse-root-bounds.tex`, lines 177–179, 341–349 and 559–562. Dutta’s Theorem 10 gives a bound of **order** the support-union size for two cubes. A coefficient-one bound is false. For instance, \(g_1=x^4-5x^2,\ g_2=4\) use three distinct monomials, and \(g_1^3+g_2^3\) has four real roots. More importantly, the uniform conjectural inequality as formulated in the note fails for every constant \(c\). The deduction \(c\ge4\) is a valid conditional implication, but the remark leaves a materially misleading impression about the existence of such a constant. The conference text places the quantifiers on the constants after the polynomial. The uniform interpretation used in the manuscript is the one addressed by the following counterexample. [Dutta, Definition 4, Conjecture 2 and Theorem 10](https://logic.pdmi.ras.ru/csr2021/sites/logic.pdmi.ras.ru/csr2021/files/Pranjal-Dutta/index.pdf)

   **Counterexample.** Fix \(m\ge2\) and a positive integer \(L\). Set
   \[
   F(x)=\prod_{r=1}^{m^2-1}(x^{2L}-r),\qquad d=2L(m^2-1).
   \]
   It has at least \(m^2-1\) distinct positive roots. Every monomial in \(F\) has the form \(x^{2L(mi+j)}\) with \(0\le i,j<m\). Set \(u_i=x^{Lmi}\) and \(v_j=x^{2Lj}\). Then \(x^{2L(mi+j)}=u_i^2v_j\), and
   \[
   6u_i^2v_j=(u_i+v_j)^3-(u_i-v_j)^3-2v_j^3.
   \]
   Thus \(F\) is a weighted sum of at most \(3m^2\) binomial or monomial cubes whose inputs use at most \(2m\) distinct monomials altogether. Given any fixed \(\epsilon>0\), choose \(L\) with \(\lfloor d^\epsilon\rfloor\ge3m^2\). Then \(U(F,\lfloor d^\epsilon\rfloor)\le2m\), whereas \(m^2-1>2cm\) for sufficiently large \(m\).

   I recommend deleting Remark 10 and using the following in Section 7: **“Dutta’s Theorem 10 bounds the number of distinct real roots of a nonzero sum of two weighted cubes by a constant times the number of distinct monomials in their inputs. Proposition 3 gives the exact positive-root maximum for binomial inputs.”** The counterexample above is a finding of this review. Any separate claim concerning the published conjecture should identify the precise version and quantifiers and receive human mathematical scrutiny. Koiran’s polynomial-in-\(kmt\) conjecture is unaffected.

3. **Major · Correct the status of the real-exponent upper bound.** TeX lines 363–371 and Section 8, item 1. The final declaration of `L_gct_234` concerns polynomials. Its algebraic proof nevertheless gives the upper bound nine for real exponents. There is no need to list this as an open mathematical question.

   **Replacement proof.** Move the root to \(x=1\) and write \(x=e^t\). An input becomes \(A e^{at}+B e^{bt}\), with \(a,b\in\mathbb R\). If one input has fewer than two terms, the sum has at most nine terms, and the Vandermonde bound gives order at most eight. Otherwise take \(AB(a-b)\ne0\) for each input. The \(n\)-th derivative of one cube at zero is
   \[
   T_n(A,B,a,b)=A^3(3a)^n+3A^2B(2a+b)^n+3AB^2(a+2b)^n+B^3(3b)^n.
   \]
   If the first ten derivatives of the sum vanish, the same holds after multiplication by \(e^{-3ht}\) for every real \(h\). These are precisely the first ten moment equations with \(a,b\) replaced by \(a-h,b-h\).

   Apply Aargau’s real-parameter reductions to these equations. If all three inputs vanish at zero, `threeVanish_mixture` and `vanishingSequence_four` give cancellation of the moments in every order. Exactly two vanishing inputs are impossible by the zeroth equation. With exactly one, the reduction gives the contradiction `oneVanish_excludes`. If all three are nonzero, put \(\alpha=A/(A+B)\) for each input. Its normalized moments depend on its mean \(\alpha a+(1-\alpha)b\), its variance parameter \(\alpha(1-\alpha)(a-b)^2\), and \(a+b\) minus twice its mean. The zeroth and first equations force the three means either to agree or to be pairwise distinct. In the first case `equalMean_mixture` makes the normalized moment sequences identical, and their weighted sum vanishes in every order. In the second case `Chart.distinct_mean_excludes` gives a contradiction. These algebraic lemmas have real parameters. Finally, vanishing of every moment at one shift forces every combined exponential coefficient to be zero, by the Vandermonde matrix on the distinct shifted exponents. This contradicts a nonzero signomial. Proposition 11 therefore attains the exact real-exponent maximum, nine. [Aargau’s pinned proof](https://github.com/open-goat/pequalnp-proofs/blob/ff9577c31478c84118afce361cbf5c332499ab24/lean/PEqualNP/Outside/L_gct_234.lean)

   I checked the transfer in a scratch Lean file with **real-valued exponents**. The theorem that ten vanishing shifted moments imply cancellation in all orders compiled with the same three standard axioms. The identification with analytic order in the preceding paragraph is an ordinary mathematical argument. Credit the algebraic proof to Aargau and identify this extension as a deduction checked in Review 2. The remaining polynomial question is **“Can a nonzero sum of three cubes of real polynomial binomials have a positive root of order eight or nine?”**

4. **Major · Correct the credit and normalization of Proposition 12.** TeX lines 422–424, 446–448 and Credits. The claim that the formula for \(D_2^2\) is new is untenable. In maxkieff’s `lattice_obstruction`, the displayed steps `e` and `f` give \(V=B+3p^2+6pq\) and \(B=5p^2+5pq+8q^2\). Substitution is exactly the manuscript’s third squared width. Use **“Part (i), including the third squared width after substitution, is maxkieff’s calculation. Here we evaluate the next two moments and identify the orders of vanishing for real exponents.”** Keep the order-seven example, common-root bound and descent with maxkieff. Credit silentoplayz specifically for the obstruction involving three consecutive unshared exponents. [Earlier Lean calculation](https://github.com/maxkieff/pequalnp-proofs/blob/27acb67dbe/lean/PEqualNP/Research/SparseCubeBoundary.lean#L78-L95) · [Discussion and reply](https://github.com/open-goat/pequalnp-proofs/discussions/21999)

   There is also a missing factor in the identification with Proposition 11. Write \(\Phi\) for its hyperbolic expression. The exact relation at \(p=q=1\) is
   \[
   G(e^{2s/3})=-\frac{8}{81\sqrt6}\,\Phi(s).
   \]
   The other exceptional lines require more than a permutation. For example, at \(q=-2p\) the centres are \((-2p,-p,0)\). Translating them by \(p\), then permuting, gives \((-p,0,p)\) in sorted order. A common centre translation contributes a nonvanishing exponential factor. Replace lines 446–448 with **“After a common translation of the centres, rescaling the variable, permuting the summands and multiplying by a nonzero constant, the three exceptional lines give the same order-nine example.”** Then give the displayed factor. In Proposition 11 itself write \(\sinh((\lambda+1)s)\) throughout, so that the argument of \(\sinh\) is unambiguous.

5. **Minor · State precisely what Lean proves and exclude the zero polynomial.** Abstract, Table 1 caption, TeX lines 159–161, 231–232, 313–326, 521, 539–540 and 603. The files certify witness lower bounds. Exactness and simplicity in this note also use the upper bound. “Descartes’ rule … is not formalized” is inaccurate without qualification. The pinned Mathlib contains `Polynomial.roots_countP_pos_le_signVariations`. The signomial extension and the application yielding the displayed equalities are distinguishable from that library theorem. Also, \(f=1,g=-1\) makes \(fg+1\) identically zero, and \(pq=rs\) causes the same problem for the other product family. [Mathlib’s polynomial rule of signs](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Algebra/Polynomial/RuleOfSigns.lean)

   Use **“Throughout, bounds on numbers or orders of roots concern nonzero functions. Table 1 counts distinct roots, except in row 234, which bounds the order of one root. The Lean files certify the stated lower bounds. Combining them with the rule of signs gives exactness and simplicity for the extremal witnesses.”** End Example 8 with **“The accompanying Lean file proves the lower bound nineteen.”** Replace “All lower bounds in this note are of this form” with **“We use alternation to prove the positive-root counts in Sections 3 and 4.”**

6. **Minor · Make the computational proof and reproduction instructions agree.** Proposition 13, TeX lines 472–517, `scripts/exact_check.py`, and README under “Reproducing.” The finite theorem is correct. Two reductions are missing from the prose, and the advertised sign-check command evaluates different points from the printed certificate. All eight below-one points for four cubes and all ten for five cubes differ. For example, the command uses \(10000000/10233687\) where Theorem 6 prints \(9771649/10000000\). Both signs are correct.

   Add to the proof: **“Subtract the smallest input exponent \(b\) from all input exponents. This divides the sum by \(x^{3b}\) and preserves its order at a positive root. At least two inputs must be genuine binomials, since one cube and two monomials have at most six terms. A remaining monomial can be entered in a two-exponent pair by giving its unused term coefficient zero. Repeated pairs leave at most eight distinct cube exponents and can be discarded.”** In the nontriangle case say that the program first uses a degree-preserving modular gcd test and falls back to a rational gcd with real-root testing. In the triangle case replace the last two sentences at lines 505–508 with **“The program rejects a candidate when a necessary equation has an interval enclosure excluding zero. It flags a candidate if it cannot determine a sufficient split or refute every surviving split. No candidate was flagged.”** One enclosure containing zero does not prevent a different equation from refuting the candidate.

   Make the documented verification command read the stored `points` and `binomials`, evaluate \(\sum_i g_i(x)^3\) as a rational number at each point, and assert strict ordering and the stored alternating signs. Alternatively, document the generator invocation that reproduces the exact printed points. I verified that `gen_lean.py` regenerates both certificates. Label the existing `exact_check.py` command as an additional reciprocal-point check. The README should also run both multiplicity scripts for **all** partition indices \(0,\ldots,5\), rather than showing only commands for index zero.

7. **Minor · Correct the descriptions of the product proofs and the literature bounds.** Appendix A, lines 645–650, and Section 7, lines 555–570. Row 269 uses rational endpoints including \(1/6\) and \(1/4\), together with the exact root zero. Row 271 uses half-integers. Replace the description with **“Row 267 verifies eight explicit integer roots. Row 269 combines twelve crossings between rational sample points with the root zero. Row 271 uses fifteen crossings between consecutive half-integers.”**

   “For a fixed power they are weaker than expansion” also needs a narrower scope. It conflicts with the immediately following observation for sufficiently large fixed \(r\). Use **“For three cubed binomials, the general Wronskian bound is much larger than the expansion bound of eleven. Since it is independent of \(r\) for three fixed binomial inputs, it eventually improves on the expansion bound \(3r+2\) as \(r\) increases.”** Replace “the only bound found” for multiplicities by **“We found no published upper bound for this polynomial family improving the elementary bound eleven.”** The comparison with Bihan and El Hilany correctly includes their finite-intersection hypothesis. [Wronskian bound, Theorem 12](https://arxiv.org/pdf/1205.1015) · [Bihan and El Hilany](https://arxiv.org/abs/1506.03309)

8. **Major · Correct the release history, public credits and links.** Disclosure, Appendix A lines 667–670, README, research logs, and `discussion-post.md` lines 17–26. Version 2 was revised after round 1. It cannot already have incorporated the findings in this report. The supplied `reviews/` contains only the round-1 prompt, report and reply. Round 1 used its own nontriangle checker and the author’s triangle program. The proposed post merges the two reviewers’ actions and says their corrections were made.

   For this version use **“Claude Fable 5.2 prepared the note and revised it after a mathematical and editorial review by GPT-6 Astra. GPT-6.2 Astra independently examined version 2. These were AI-assisted reviews. No human mathematical review is recorded.”** Date any later author reply against the version it actually covers. Identify Table 1’s last column as **“credited PR submitter”**. PR 13524 records Claude Fable 5.2 as a co-author of that upstream contribution, and PR 16079 explicitly records Codex assistance. The earlier unmerged submission for row 234 can be acknowledged as an independent attempt while keeping the checked row credited to Aargau. Remove “our bound 9” from any public version of `literature-A-upper-bounds.md`, line 33. [PR 13524 commit](https://github.com/open-goat/pequalnp-proofs/commit/031b81019c62f0dc8de94251f0a735dc12d7ba0b) · [PR 16079](https://github.com/open-goat/pequalnp-proofs/pull/16079) · [Earlier row-234 submission](https://github.com/open-goat/pequalnp-proofs/pull/23279) · [Accepted row-234 submission](https://github.com/open-goat/pequalnp-proofs/pull/23576)

   GitHub’s API returned **“No commit found for the ref `paper/sparse-root-bounds`.”** Every proposed deliverable link depends on that ref. Section 6 below gives the posting copy using the intended paths. Verify the PDF, source, Lean files, certificates and README at the approved public revision before posting. An unavailable review archive should not be advertised.

## 4. Optional improvements

1. **Minor · Shorten Proposition 3, lines 166–179.** A factorization is unnecessary. A complete proof is: **“A nonzero binomial has at most one positive root, and \((x-1)^3\) attains one. Since the real cube map is injective, \(g_1(x)^3+g_2(x)^3=0\) exactly when \(g_1(x)+g_2(x)=0\). For a nonzero sum of cubes the latter polynomial is nonzero and has at most four terms, hence at most three positive roots. Taking \(g_1=x^3-6x^2\) and \(g_2=11x-6\) attains the three roots \(1,2,3\).”** Retain Dutta’s citation with the corrected support-union statement.

2. **Minor · Simplify the triangle computation in Proposition 13.** For this range one can dispense with root isolation and coefficient splitting. Impose the cubic moment equation for the pivot and one necessary equation on the three known coefficients of each other cube. For a missing coefficient in position \(0,1,2,3\), respectively, use
   \[
   h_2^2=3h_1h_3,\qquad h_2^3=27h_0h_3^2,\qquad
   h_1^3=27h_0^2h_3,\qquad h_1^2=3h_0h_2.
   \]
   These follow directly from \(h_j=\binom3j A^{3-j}B^j\). Substitute the seven-node interpolation polynomials, remove only powers of the pivot variable \(z\) known to divide over \(\mathbb Q\), and take a gcd modulo 32749. The interpolation denominators are units because distinct nodes lie between 0 and 96. A constant modular gcd excludes a common nonzero characteristic-zero root when at least one input polynomial retains its degree. I guarded the degree using the extremal possible powers in the products before subtraction. This test refuted every required triangle pivot in my run. The submitted interval proof can remain. This gives a shorter independently verified alternative if you wish to replace it.

3. **Minor · Give the product rows a mathematical connection, Section 6.** The positive and real columns otherwise read like unrelated records. Add **“If \(fg+1\) has \(r\) distinct positive roots, then \(f(x^2)g(x^2)+1\) has at least \(2r\) distinct real roots with the same sparsity per factor. Thus the three positive-root files also give real-root lower bounds of 16, 22 and 24. Table 1 records what each individual real-root file certifies.”** Likewise, the eight-crossing example in row 261 has coefficient signs \(+,-,+,-,+,-,-,+,-,+\) in increasing degree. Its eight sign variations explain in one sentence why the eight located roots exhaust its positive roots.

4. **Minor · Tighten the introduction and open questions.** TeX lines 119–130, 581–603 and 687–696 repeat the contributions and novelty qualifications. Keep the result list near the beginning and use Credits for provenance. Replace “The following is not in the repository or in that discussion” with **“Beyond the eighteen accepted files at the cited commit, this note gives the following constructions and deductions.”** In Section 8 specify **signed** sums if even powers are intended. For unsigned even powers, every real zero must be a common zero of all nonzero inputs, so binomial inputs have at most one positive common zero. Move the item about future Lean work out of the list of mathematical questions.

## 5. Assessment by requirement

**1. Correctness and rigor.** The main root-count theorem, its real-root corollary, the order-nine example, the moment identities and the finite computation are sound. The necessary substantive revisions concern the support-union inequality, the status of the real-exponent maximum, the normalization after Proposition 12 and the scope of formal verification. The stated connection to Koiran’s conjecture is appropriately limited to a structured family with fixed product length.

**2. Human readability.** A mathematician can reconstruct the main extremal argument from the text. The one-parameter gluing proof and the integer table for Proposition 11 are particularly clear. The weakest passages omit short explanations exactly where a reader needs them, notably the support normalization, the meaning of a failed interval test and the distinction between an upper bound and a certificate of crossings. I found no prose em dashes or en dashes in the manuscript source or proposed post. The TeX double hyphens are bibliographic conventions.

**3. Simplicity and economy.** Retain the rewritten gluing proof. The injectivity argument above shortens Proposition 3, and the four split-free identities offer a simpler exact computation. The paper gains more from explaining how Aargau’s moment argument applies than from reproducing its large certificates. The open-questions list and Credits can both be shortened after those changes.

**4.** [Omitted here: a passage about the content of the supplementary files, without mathematical content. The requested changes were made.]

**5. Attribution and originality.** The eighteen accepted rows are genuine and correctly associated with their submitting accounts. The four-cube witness adds something the row-251 example does not achieve. The compact five-cube witness is a second example achieving a previously certified count. The gluing deduction is worth presenting. The third width formula is already implicit in maxkieff’s displayed algebra, and the real-exponent upper bound draws its substance from Aargau. I found no basis for a stronger priority claim. The reference edge-function paper concerns different mathematics, and the desk is better placed to identify work in preparation. [Project reference publication](https://pequalnp.com/papers/note-1) · [Research board](https://pequalnp.com/board)

**6. GitHub Discussion.** The draft asks the right questions of the desk. It is longer than necessary, omits the significance of the second five-cube certificate, blurs the review histories, and advertises unavailable links. Its claim that a literature search “found nothing” should be removed. The project describes official papers as accounts of checked map statements. The unformalized general theorem therefore belongs explicitly in the desk’s assessment of publication fit. [Project editorial process](https://pequalnp.com/papers/how)

## 6. Recommended GitHub Discussion

**Title**

Positive roots of sums of cubes of binomials: a research note for desk evaluation

**Message**

This note brings together eighteen PEqualNP statements on roots of sparse polynomials and the multiplicity results in Discussion #21999. It compares the Lean declarations with their proofs and gives a conventional mathematical account of the examples, including cases where a file certifies more roots than its posted statement requires. Table 1 identifies the contributor and pull request for each accepted file. [Multiplicity discussion](https://github.com/open-goat/pequalnp-proofs/discussions/21999)

The main addition is a sum of four binomial cubes with fifteen distinct positive roots. The new Lean file certifies fifteen crossings, using the interval arithmetic developed by hedanbaomi and adapted by k-sandhu. Descartes’ rule gives the matching upper bound. An elementary gluing argument combines this example with XXXLUMI’s three-cube example and junyeopYim’s five-cube example. It gives the exact maximum \(4k-1\) for every \(k\ge3\). The gluing argument and general theorem are proved on paper. A second Lean file gives a smaller-degree example attaining the already known count of nineteen for five cubes.

The note also calculates two further moments of maxkieff’s common-root family, gives a real-exponent example of order nine, and supplies an exhaustive computation excluding order eight or higher for nonzero polynomial sums with input exponents from 0 to 32. The unrestricted integer-exponent multiplicity remains between seven and nine.

Claude Fable 5.2 carried out the mathematical analysis and literature review, reconstructed the proofs, prepared the manuscript and verification files, and revised the text. GPT-6 Astra reviewed the first version. GPT-6.2 Astra independently reviewed the revised mathematics and exposition, checked the Lean files and computations, and recommended corrections. These were AI-assisted reviews. The note is submitted for human evaluation.

[Manuscript PDF](<address of the hosting repository>/notes/note-sparse-root-bounds/paper/sparse-root-bounds.pdf) · [LaTeX source](<address of the hosting repository>/notes/note-sparse-root-bounds/paper/sparse-root-bounds.tex) · [Lean files](<address of the hosting repository>/notes/note-sparse-root-bounds/lean) · [Certificates and search output](<address of the hosting repository>/notes/note-sparse-root-bounds/data) · [Reproduction instructions](<address of the hosting repository>/notes/note-sparse-root-bounds/README.md)

Could the desk assess the correctness, relevance and originality of the note, and say whether it overlaps an editorial project already under way? Comments on attribution, necessary corrections, and any additional formalization or investigation would be welcome. If the corrected note meets the project’s publication standards, please consider it for inclusion among the project’s papers.

## 7. Remaining scientific concerns and limitations

The integer-exponent multiplicity maximum remains \(7\), \(8\) or \(9\). The finite exclusion does not distinguish these possibilities at larger exponent span. The maximum for \(fg+1\) with trinomial inputs also remains unresolved by the submitted work. The search for fifteen-root witnesses establishes the example supplied, without addressing minimum degree or coefficient size.

The support-union counterexample and the real-exponent upper-bound deduction arose during this review. Any public version incorporating them should identify that provenance and give a human reader enough detail to check them. Neither result establishes a complexity-class separation. The desk’s judgment on overlap, human mathematical review and publication fit remains outstanding.

I did not edit any submission file or publish anything. The independent checks used the permitted scratch directory. Automatic approval review blocked its cleanup, so the scratch files remain separate from the 61-file submission.
