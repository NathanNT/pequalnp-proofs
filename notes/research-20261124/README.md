# Checked results on permanent level spaces and quinary planes

This branch collects three independent investigations. The pinned Lean version is 4.36.0. Each statement below has a local project checker verdict. The two permanent existence questions remain open.

| Module | Checked result | Kernel constants |
| --- | --- | ---: |
| QuinaryPlane | A two-dimensional quinary code with vanishing quadratic and quartic coordinate sums has length at least ten. Equality consists of two signed repetition blocks of length five. | 1674 |
| HookMaximality | The symmetric hook through the all-ones matrix is maximal under inclusion. | 1650 |
| CyclicPlane | An explicit symmetric plane with cyclic symmetry is a constant-permanent plane and is maximal under inclusion. | 1657 |
| KleinPermanent | At the matrix with diagonal 2 and other entries 1, a level space invariant under the four specified simultaneous translations has dimension at most three. | 1687 |
| RowPair | Under the stated injective row-pair projections, a six-dimensional space with nonvanishing translated permanent fixes four entries on a permutation. | 1656 |
| RowPairDirection | Every six-dimensional candidate at the modified base has a nonzero direction supported on at most two rows and one supported on at most two columns. | 1851 |
| SparseCoexistence | An explicit independent pair with those supports spans a constant-permanent plane. | 1702 |
| SparseExtension | The explicit pair extends to a level space of dimension three. | 1714 |
| SparsePairSharp | Every extension containing that same pair has dimension at most three, and the bound is attained. | 1766 |

The Lean sources are in `lean/PEqualNP/Outside` and `lean/PEqualNP/Research`. Each research folder here holds its exact checker statements. Two support modules supply matrix certificates and lemmas for the sharp bound. The independent Python certificates accompany the symmetric and modified-base cases. The wider classification of cyclic planes and the separate asymmetric-family calculations have algebraic certificates. Only the explicit cyclic plane in the table has a Lean verdict for that part of the investigation.

From the repository's `lean` directory, a reproduction for the sharp pair uses the project's pinned dependencies:

```sh
lake build PEqualNP.Research.SparsePairSharp checklemma
lake env .lake/build/bin/checklemma PEqualNP.Research.SparsePairSharp ../notes/research-20261124/modified/statements/SparsePairSharp.txt check
```

The quinary theorem is public for mathematical review in [upstream discussion 8671](https://github.com/open-goat/pequalnp-proofs/discussions/8671). The two permanent studies concern [the symmetric level-space question](https://pequalnp.com/lemma#L-gct-231) and [the modified-base question](https://pequalnp.com/lemma#L-gct-229). A three-dimensional example at the modified base leaves the six-dimensional question open.

Two earlier investigations retain their own review history on this fork: [weighted incidence and its projective-plane application](https://github.com/NathanNT/pequalnp-proofs/pull/1) and [quartic equality and stability over the complex numbers](https://github.com/NathanNT/pequalnp-proofs/pull/2).
