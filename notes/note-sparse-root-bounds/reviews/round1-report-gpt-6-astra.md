## Summary of the submission

The manuscript surveys eighteen Lean proofs concerning roots of structured sparse polynomials.  
Its principal new contribution is a four-binomial-cube polynomial attaining fifteen positive roots.  
An elementary gluing argument then establishes the sharp maximum \(4k-1\) for every \(k\ge3\).  
The maximum over all real roots, \(8k-1\), follows immediately by substitution.  
The multiplicity section explains an existing bound of nine and develops an existing common-root family.  
It gives a real-exponent example of multiplicity nine and a computational exclusion of multiplicities at least eight for input exponents in \([0,32]\).  
The main mathematics survived my checks; several statements about prior work and verification require correction.

## Verdict

**MINOR REVISION**

The principal theorem, explicit examples, and finite multiplicity exclusion survived substantial independent verification.  
The required changes concern localized logical qualifications, inaccurate literature statements, and the presentation of computational evidence.

## Checks I performed myself

- **Proposition 2.3.** Re-derived the factorization argument. The real zero sets of \(g_1^3+g_2^3\) and \(g_1+g_2\) coincide. The proposed example attains three positive roots. The conclusions \(N(1)=1\), \(N(2)=3\) are correct.

- **Theorem 3.1.** Independently expanded the three cubes and verified
  \[
  x^{38406}P(1/x)=-P(x).
  \]
  I re-derived the reduction \(P(u)=A(q)u^6+B(q)u^3+C(q)\), \(q=u^{256}\). For all six specified rational \(q\)-values, I constructed rational enclosures of \(q^{1/256}\), verified their defining inequalities exactly, and evaluated rational bounds for \(P\). The signs are precisely \(+,-,+,-,+,-\). Reciprocity, the intermediate value theorem, and Descartes establish exactly eleven simple positive roots.

- **Lemma 4.1.** Checked the quantifiers, preservation of the sum-of-cubes structure, separation of the sample points, and both domination inequalities. The interval prescribed for \(\delta\) is nonempty under the stated choice of \(n\). The argument works whenever the sample values are nonzero. There is a minor zero-sign-change edge case discussed below.

- **Theorem 4.2 and Example 4.4.** Using independently written code and exact rational arithmetic, I evaluated the polynomials directly from their binomials:
  
  | Example | Expanded terms | Degree | Independently verified signs |
  |---|---:|---:|---|
  | Four cubes | 16 | 4608 | All 16 sample values alternate, beginning negative |
  | Five cubes | 20 | 1152 | All 20 sample values alternate, beginning positive |

  Both reciprocal identities also hold exactly. Descartes then gives exactly fifteen and nineteen positive roots, respectively, all simple.

- **Theorem 4.5 and Corollary 4.6.** Checked the induction, including the need for the three base cases \(k=3,4,5\). The construction \(x^3P(x^2)\) gives exactly the asserted \(8k-1\) distinct real roots. The root at zero need not be simple, and the corollary does not claim otherwise.

- **Propositions 5.2 and 5.3.** Independently derived the moments by expanding the finite binomial sums. The vanishing through \(\mu_7\), the displayed factorizations of \(\mu_8,\mu_9\), and the exceptional parameter lines are correct. Independently obtained
  \[
  \Phi(s)=\frac{4\sqrt6}{315}s^9+\frac{\sqrt6}{105}s^{11}+O(s^{12}),
  \]
  confirming exact order nine. I also factored the credited order-seven polynomial and recovered its leading Taylor coefficient \(2925\).

- **The two new Lean files.** Both compiled successfully with Lean 4.36.0 and the supplied Mathlib environment. Their printed dependencies are exactly `propext`, `Classical.choice`, and `Quot.sound`. I found no `sorry`, additional axiom, or weakening that defeats the advertised lower bounds. Their final theorems negate universal bounds of fourteen and eighteen; internal counting lemmas establish the explicit examples. Exactness and simplicity additionally require the paper’s Descartes argument.

- **Existing Lean work and credit.** Checked the final statements and relevant counting declarations in all eighteen local row files against the tables. The numerical entries match. I checked the listed pull-request authors against the public records. I also verified that the generic proof infrastructure in the new files is copied from row 251 as disclosed. The attribution of the multiplicity constructions and common-root family agrees with [Discussion #21999](https://github.com/open-goat/pequalnp-proofs/discussions/21999).

- **Row 234.** Compiled `rows/L_gct_234.lean` successfully and compared its principal reductions and declarations with §5.1. The outline is substantially faithful: moment vanishing, the small-input reduction, vanishing/nonvanishing cases, and the two algebraic certificates are represented correctly. I did not manually rederive the enormous certificates.

- **N7: coverage and computation.** Audited both search programs. I independently checked the cubic-cone equations, Lagrange reconstruction, normalization, repeated-support exclusion, monomial cases, modular gcd justification, and the triangle splitting argument. Independent enumeration recovered:
  \[
  4\,179\,296=3\,787+4\,114\,116+61\,393.
  \]
  An independently written modular implementation excluded all **4,114,116** nontriangle cases, with no unresolved cases. Its treatment of removable powers of \(z\) used exact coefficient bounds and modular reconstruction, not an unverified assumption about reduction modulo a prime. A complete rerun of the authors’ triangle program returned:
  ```
  triangles 61393 refuted 61393 flagged 0
  ```
  I also ran the authors’ main search at \(S=12\), its self-tests, and a sample at \(S=32\).

  **Thus N7 is established at its stated finite range, subject to the ordinary trust assumptions of these computational tools.** I found no omitted overlap, monomial, or zero-input case invalidating it.

- **Limits of this review.** I did **not** recompile the other seventeen existing row files, independently reproduce every old sign certificate, rerun the entire original main search at \(S=32\), or write an independent replacement for the triangle interval arithmetic. I did not compare the rendered PDF against the source. Literature checking used primary sources where accessible; it was not an exhaustive historical priority investigation.

## Major issues

I found no major defect invalidating the principal extremal theorem or N7. The following are substantive corrections to surrounding claims.

**M1. Remark 4.7 and §8 overstate what the cited two-cube theorem establishes.**

Read literally against the preceding definition of \(U\), “the conjecture is proved … for two cubes” is too strong. Dutta’s Theorem 10 bounds roots by the support union of a **two-summand representation**. Minimizing over such representations gives a bound in terms of \(U(f,2)\). It does not automatically give a bound in terms of \(U(f,d^\epsilon)\), which may be smaller. The source states the former result explicitly. [Dutta, author’s version, Theorem 10](https://logic.pdmi.ras.ru/csr2021/sites/logic.pdmi.ras.ru.csr2021/files/Pranjal-Dutta/index.pdf)

Replace this with “the two-summand analogue is proved,” or state the actual inequality. Also specify \(0<\epsilon<1/2\).

The necessary condition \(c\ge4\) is correct: use **odd** substitutions \(x\mapsto x^m\), choose the degree large enough to allow \(k\) summands, and pad with zero summands. However, \(U(f,d^\epsilon)\le2k\) supplies no lower bound on the minimizing \(U\). It therefore does not verify the conjectured inequality for this family. Replace the claimed inference of “consistency” with the precise necessary-condition statement.

**M2. Section 5.3 and the supplementary material overstate parts of the validation record.**

The real-exponent positive controls in `mult_search.py:selftest` use 40-digit floating-point arithmetic and a \(10^{-25}\) tolerance. They check residuals in the moment and cone formulas. They do **not** run the exact gcd/root-decision pipeline on those examples. Consequently, the wording that the program “recovers” a common root and thereby demonstrates solution detection is stronger than the actual test.

This does not invalidate the exact production search, which I audited and substantially reproduced. It does matter in a paper whose distinction between numerical exploration and proof is central.

Describe these controls as numerical consistency tests. Archive the complete production summaries, commands, software versions, and unresolved-case counts. The supplied `data/` does not contain those full N7 transcripts. The advertised `reviews/` directory is also absent from the supplied submission; include it or correct the assertions that its contents are available.

## Minor issues

**m1. §1.3 falsely gives one universal description of the certificates.**  
Not every example is certified by alternating signs at rational positive points. Row 241 uses algebraic points \(q^{1/256}\), enclosed rationally; row 267 uses exact root identities. Statements about all real roots also require more than the stated positive-point pattern. Describe the actual certificate types.

**m2. Lemma 4.1 has an unhandled boundary case.**  
Under §1.3, “zero sign changes” imposes no nonvanishing condition. Thus \(P=0\), or a chosen sample point with \(P(x_0)=0\), is allowed, whereas the proof asserts \(a>0\). Require nonzero sample values, restrict the lemma to positive \(p,q\), or handle zero cases separately. The induction uses positive \(p,q\), so its validity is unaffected.

**m3. §8: “the only available bound” is false.**  
Grenet–Koiran–Portier–Strozecki already give bounds independent of the powering exponents for the relevant model. The KPT bound is an available bound, not the only one. The deduction that sufficiently large powers cannot attain \(3d+2\) remains valid. [GKPS, introduction](https://arxiv.org/pdf/1107.1434)

**m4. §8 omits “nonzero” in the multiplicity version of the real \(\tau\)-conjecture.**  
Hrubeš’s statement counts multiplicities of **nonzero roots**. Without that qualification, \(x^D\) is an immediate counterexample. [Hrubeš, abstract and §2](https://theoryofcomputing.org/articles/v009a010/v009a010.pdf)

**m5. §8 omits the finite-intersection hypothesis in the Bihan–El Hilany statement.**  
A trinomial curve can contain the line. Their bound applies when the intersection is finite, equivalently when the restricted polynomial is not identically zero. Add this qualification. [Bihan–El Hilany](https://arxiv.org/pdf/1506.03309)

**m6. §5.2’s “must use integrality” needs a precise interpretation.**  
The example proves that a stronger polynomial bound cannot follow from an argument valid for arbitrary real exponents. It does not prescribe the syntax or method of every possible proof. Rational exponents can also be reduced to integer exponents by clearing denominators and shifting. “Must exploit an arithmetic restriction absent for arbitrary real exponents” is more accurate.

**m7. §5.3 should distinguish a refutation procedure from an unconditional decision procedure.**  
The triangle routine can return `FLAG`; fixed-precision interval arithmetic is not guaranteed to decide every future instance. For \(S=32\), zero flags makes the exclusion conclusive. State this explicitly. Add a short inclusion–exclusion justification for the assertion that at least two triangle pivots are valid.

**m8. The rechecking script does not propagate failures reliably.**  
`recheck_rows.sh` records `FAILED` but continues and can exit successfully after a failed compilation. It also prints, rather than validates, the axiom list. Make its exit status reflect compilation failures and unexpected dependencies.

**m9. The abstract’s “Lean is the authority” sentence is not a substitute for statement agreement.**  
The author remains responsible for ensuring that the mathematical claims match the checked declarations. The present main lower bounds do match; the wording should not suggest that discrepancies in the prose would be acceptable.

## Originality and significance

**N1 and N4 are the principal contributions.** I found no primary source establishing the exact four-cube example or the all-\(k\) sharpness theorem. They are plausibly new, but my search does not certify priority.

The distinction from classical Chebyshev-system theory is real. For distinct real exponents, the exponential functions have nonvanishing Wronskians, giving the familiar ambient zero bound. That theory does not automatically put an extremal coefficient vector on the nonlinear cones imposed by cubing binomials. Thus “this is just the Chebyshev-system theorem” would be an inadequate dismissal.

**N3 is elementary.** It is a finite-point domination construction, closely related to familiar scale-separation arguments. It deserves a proof and can be useful, but should not be advertised as a deep new technique.

**N5 is an immediate corollary**, not a separate substantial advance.

**N6 is a modest but useful observation.** The family and its arithmetic obstruction belong to maxkieff. Evaluating two further moments and specializing to an exceptional line are short algebraic consequences. The explicit order-nine identity usefully demonstrates why arbitrary-real-exponent arguments cannot settle the stronger integer-exponent claim.

**N7 is meaningful finite evidence**, stronger than the previously reported search for orders ten and eleven. It neither proves \(M=7\) nor supplies an argument controlling exponents above 32.

The credit boundaries are generally fair. The eleven-root example, nineteen-root attainment, order-seven construction, common-root classification, and order-nine upper bound are not appropriated as new results. N2 is correctly described as a smaller alternative example.

The complexity framing is appropriately restrained. Fixed cubes of binomials already admit a linear bound by expansion. Sharpness of that bound does not advance a circuit lower bound or resolve any \(P\) versus \(NP\) question. The appropriate contribution is a short extremal/fewnomial note with computational certificates.

## Bibliography

The bibliography is substantially real and relevant; it is not a collection of fabricated references. Its mathematical qualifications nevertheless need attention.

- **Koiran 2011:** The real \(\tau\)-conjecture and the stated constant-free permanent consequence are represented appropriately. [Primary paper](https://arxiv.org/pdf/1004.4960)
- **Koiran–Portier–Tavenas 2015:** Theorem 12 supports the displayed application. Substitution gives approximately \(8.057\times10^{12}\), as claimed. The exclusivity claim is wrong; see m3. [Primary paper](https://arxiv.org/pdf/1205.1015)
- **Dutta 2021:** The support-union definition and conjectural framework are relevant, subject to M1. The cited 2026 journal publication exists; I checked its metadata, not its complete text. [Journal record](https://link.springer.com/article/10.1007/s00224-026-10294-7)
- **Dutta–Saxena–Thierauf:** The broad connection between sparse sums of powers, hardness, and identity testing is accurately described. [ITCS paper](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITCS.2021.23)
- **GKPS and Jindal et al.:** The attribution of the \(fg+1\) question to Chattopadhyay is supported. Jindal et al. support the stated historical absence of subquadratic bounds and superlinear examples; a 2020 paper alone cannot certify the state of knowledge in November 2026. [GKPS](https://arxiv.org/pdf/1107.1434), [Jindal et al.](https://arxiv.org/pdf/1911.02540)
- **Hrubeš and Koiran–Skomra:** Relevant and accurately connected to multiplicity questions once the exclusion of zero is made explicit. [Hrubeš](https://theoryofcomputing.org/articles/v009a010/v009a010.pdf), [Koiran–Skomra](https://arxiv.org/pdf/1904.00702)
- **Lenstra and Hajós:** Lenstra’s Proposition 3.2 supports the sparse multiplicity bound and credits Hajós. I did not inspect the Hungarian original; the manuscript’s disclosure of indirect citation is appropriate. [Lenstra](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1999a/art.pdf)
- **Albouy–Fu:** Correctly relevant to real exponents and sharpness with free coefficients. [Primary paper](https://arxiv.org/pdf/1307.6842)
- **Bihan–El Hilany:** Correct sharp value, but the finite-intersection condition is essential; see m5. [Primary paper](https://arxiv.org/pdf/1506.03309)
- **Bihan–Dickenstein–Forsgård:** The comparison is legitimate as motivation. Their setting has free coefficients; the constrained cube family is not a counterexample to their questions. [Primary paper](https://arxiv.org/pdf/2402.08410)

The missing classical context should be addressed selectively. Add precise references to Pólya–Szegő and Voorhoeve–van der Poorten, which the text currently names without proper bibliographic entries; KPT explicitly explains their relationship to the Wronskian method. A standard Chebyshev-system reference such as Karlin–Studden would also help.

Sylvester’s results on sums of powers of linear forms merit a brief distinction, rather than an unsupported suggestion that they settle the present problem: varying binomial exponents create a different family. [Reznick’s account, §3](https://arxiv.org/html/1007.5485v1) Khovanskii’s *Fewnomials* supplies broader context, not the missing sharp construction.

I did not read the original Sylvester, Hajós, or Voorhoeve–van der Poorten texts in full, nor exhaust the classical literature. No stronger priority conclusion is warranted.

## Required changes before the manuscript can be recommended

- [ ] Correct the Dutta claim, specify \(0<\epsilon<1/2\), and make the \(c\ge4\) deduction precise.
- [ ] Repair the zero-sign-change edge case in Lemma 4.1.
- [ ] Replace the universal rational-point certificate claim with an accurate account.
- [ ] Identify the real-exponent self-tests as numerical residual checks.
- [ ] Archive complete N7 run summaries, dependency versions, and zero-unresolved-case results.
- [ ] Explain that the triangle routine may return unresolved flags and why none remain here.
- [ ] Correct the KPT exclusivity claim, the Hrubeš nonzero-root qualification, and the finite-intersection qualification.
- [ ] Make the compilation script fail on failed checks or unexpected axioms.
- [ ] Supply the advertised review archive or remove the unavailable-artifact claims.
- [ ] Add focused classical references while retaining the present restraint about priority and complexity-theoretic significance.