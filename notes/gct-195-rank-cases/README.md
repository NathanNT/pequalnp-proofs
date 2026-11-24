# L-gct-195 at contrast ranks seven and eight

The statements start with the four subpermanent sums in the desk's L-gct-195. The seven and eight refer to the dimension of the image of the row contrast map. For a matrix with rows R₁ through R₄, the image coordinates are R₁+3R₄, R₂+3R₄, and R₃+3R₄.

## Rank seven

[RankSeven195.txt](RankSeven195.txt) is the independently elaborated checker statement. Rank seven implies kernel dimension at most one, so the full space has dimension at most eight. [The Lean theorem](PEqualNP/Gct/RankSeven195.lean) and [the mathematical proof](rank-seven-proof.md) include the two-triple equality case, Fourier change of coordinates, polarized permanent equations, and rank–nullity.

## Rank eight

Fix a primitive cube root w, set f=(1,w,w²,0,0,0), and let A have rows (3f,3f,3f,−f). Let H consist of the matrices

    t A + (z, w z, w² z, y),

where parentheses list rows and y and z range independently over six columns. This ambient space has dimension thirteen. The fourth row gives six independent directions, the Fourier row pattern gives six more, and the sum of the first three rows detects t.

Let L be any level space containing A. Set B=L∩H. The [cubic theorem](PEqualNP/Gct/CubicRankEightCase.lean) gives dim B≤6. If L/B has dimension at most two, the theorem gives dim L≤8 and, at contrast rank eight, zero kernel. Equivalently, every nine-dimensional counterexample containing this particular A would need at least three independent matrix directions outside H. The checker statement permits any suitable B. [Exact statement](CubicRankEightCase.txt)

To see the role of the cubic, subtract t A. The third subpermanent sum of (z,wz,w²z,y) is the ordered sum of zᵢzⱼzₖ over distinct columns. The terms involving y cancel because 1+w+w²=0. With s the sum of the zᵢ, the surviving sum is

    2 Σᵢ(zᵢ−s/2)³ + s³.

The seven linear coordinates (s,z₁−s/2,…,z₆−s/2) recover z. Polarizing their weighted sum of cubes bounds the dimension of the z image by three. In the kernel of this projection only the last row remains. Its mixed equations with A force y₁=y₂=y₃=0 and y₄+y₅+y₆=0, leaving at most two dimensions. The single A direction gives the sixth. [Cubic dimension argument](PEqualNP/Gct/CubicSix.lean) · [Mixed equations](PEqualNP/Gct/OneModeCubic.lean) · [Dimension count](PEqualNP/Gct/OneModeBound.lean)

The unrestricted rank-eight case and the full L-gct-195 upper bound remain open in this work.

## Pure rows and a quotient witness

For any nonzero contrast-kernel matrix (3f,3f,3f,−f) in L, at most one pure-row subspace has dimension at least two. The vector f is arbitrary. [Proof and argument](pure-rows.md) · [Checker output](pure-rows-checker.log).

Let M record three row sums and five column sums, and let P be any subspace of L. If dim(L/P) + dim M(P) > 8, there exists a matrix in L outside P with every row and column sum zero whose entrywise conjugate lies outside L. Taking P = 0 applies this test to any nine-dimensional candidate, including spaces with injective contrast. [Exact statement](QuotientWitness195.txt) · [Lean proof](PEqualNP/Gct/QuotientWitness195.lean) · [Checker output](quotient-checker.log).

The two Fourier scripts separately test 1,024 ten-dimensional character spaces W. The extension calculation establishes dim(L ∩ W) ≤ 7 for these spaces, hence dim L ≤ 8 when at most one further direction is added to W. The programs check finite certificates. Run `python check_fourier_quotient.py` and `python check_fourier_extensions.py` from this directory. The unrestricted dimension bound remains open.

## Verification

The proof environment uses Lean 4.36.0 and the checker from project revision `26285e089fbda7ce3c86eea27cf728023a31de65`. From PowerShell, pass the existing configured project’s lean directory to the script. The pinned Mathlib, the project definitions, L065, the FermatFromKneser helper, and the checklemma executable must already be built. The script compiles the supplied sources into a local .build directory.

    .\verify.ps1 -LeanRoot 'path\to\pequalnp-proofs\lean'

[Rank-seven checker output](checker.log) · [Rank-eight checker output](cubic-checker.log)

## Novelty audit

The public source comparison on 24 November 2026 covered 9,407 PR heads and 10,458 distinct Lean file versions. Twenty-six versions across six paths matched the 4-by-6 matrix and dimension patterns. The related L-gct-206 construction uses a Fourier column and proves a lower bound. The search also covered 14 repository discussions, including available comments, and 232 GCT history records. The two previous submissions indexed under L-gct-195 were a skeleton and a reduction by pure-row dimension. Neither provides these contrast-rank conclusions. These searches cover public work visible at the time.

[Earlier skeleton](https://github.com/open-goat/pequalnp-proofs/pull/2842) · [Earlier reduction](https://github.com/open-goat/pequalnp-proofs/pull/8388/files) · [Seven-dimensional witness](https://github.com/open-goat/pequalnp-proofs/pull/76) · [Project discussions](https://github.com/open-goat/pequalnp-proofs/discussions)
