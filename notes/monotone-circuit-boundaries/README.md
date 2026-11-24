# Boundary tests for monotone graph circuits

## Heawood with one exceptional edge

In L-meta-4781 the exceptional edge is (0,7). A separator must accept an input containing any other edge, reject every independent set and reject the exceptional pair itself. Its 46 undetermined truth-table entries correspond to the nonempty independent sets of the residual cycle (2,12,5,9,6,11,4,13,2).

Two Lean theorems identify these separators with the monotone functions on eight bits that reject zero and accept every input containing a cycle edge, and classify their minimum coordinate supports. A determining set needs at least four coordinates. At equality it is an alternating vertex class and the function is the OR of those four coordinates. The exhaustive Python count gives 14,514,289 separators in 919,855 orbits under the stabilizer of the distinguished edge.

Monotonicity reduces verification of a candidate circuit to 58 rows: the 20 required edge pairs, the 37 maximal independent sets and the exceptional pair. The 24-gate SAT run reached its 180-second cutoff. All nine fixed-window runs reached their 18-second cutoffs. The 25-gate lower bound remains open here.

## Minimum circuits and direct input readers

For L-meta-3754, deleting a gate and redirecting its uses gives a necessary condition for minimum size. No earlier wire covers all edge-pair rows where the gate is true while introducing no new true rows on maximal independent sets. This holds for any finite simple graph in the binary monotone model. On the path a–b–c–d, form the AND of (a OR c) and (b OR d), and then AND the result with (b OR c). The first AND accepts the independent pair {a,d}. This five-gate circuit is lift-fixed and passes every earlier-wire test. The same edge function has a four-gate implementation. The example separates the necessary condition from global minimality. The small-graph solver results, including timeouts, are in [3754](3754/).

For L-meta-4051, three checked lemmas treat sensitivity under restrictions, direct input readers and exact recovery from a layer of pairwise ORs. The scripts include a McGee graph example in which every input has two OR readers and a decoder exists. The size of the decoder remains unrestricted.

For L-meta-1692 the exhaustive order-three plane calculation gives 10,362 forced negative rows and 28,368 individually optional nonincident rows. A collinear triple already gives a separator differing from incidence. The 64-gate bound remains open here.

## Reproduce

With the pinned Mathlib and project checker built, run `python verify.py <checkout>/lean <Lean-4.36.0-toolchain>` from this directory. It checks six separate statements. The gate-deletion argument imports the upstream L-meta-2668 module, included at blob `0722c4a5b8473d5ef035bba21f5c4786febb54c5`. [Upstream dependency](https://github.com/open-goat/pequalnp-proofs/blob/aeef32c907d2bd344ab16172b8baadd5081b0582/lean/PEqualNP/Outside/L_meta_2668.lean).

Graph experiments use Python 3 and NetworkX. The order-three classifier uses the Python standard library. The SAT scripts target the CaDiCaL binary shipped with Lean 4.36.0 on Windows.
