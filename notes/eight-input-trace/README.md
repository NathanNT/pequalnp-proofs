# Two derivations of the eight-input trace bound

L-meta-4628 rules out computing the specified edge function by a signed trace with at most eleven paid indices. Restricting a leaf reduces the problem to sirusdv's seven-input certificate. The project checker accepted the resulting proof locally against the desk statement and rechecked 2,349 constants. [Seven-input certificate](https://github.com/open-goat/pequalnp-proofs/pull/6399).

The earlier lemma `low255` by dsgallups already implies the same bound. The accompanying transport maps vertices 0 through 7 to [4,0,1,6,7,3,5,2], tracks free copies and complements, and charges each paid operation to an index. The checker accepted the identical target statement and rechecked 2,378 constants. The earlier contribution has priority. [Official verdict on #8718](https://github.com/open-goat/pequalnp-proofs/pull/8718#issuecomment-7142528417).

To reproduce both checks, fetch the public head of #8718, for example with `git fetch https://github.com/open-goat/pequalnp-proofs.git refs/pull/8718/head`. In this directory run `python verify.py <checkout>/lean <Lean-4.36.0-toolchain> <repository-containing-the-8718-blob>`. The script checks the exact dependency blob and builds the three modules in a temporary directory.
