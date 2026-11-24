import Mathlib

namespace PEqualNP.Research.HeawoodSupportAux

def edges : List (BitVec 8) := [3,6,12,24,48,96,192,129]
def hasEdge (x : BitVec 8) := edges.any fun m => x &&& m == m

theorem ownEdge : ∀ e ∈ edges, hasEdge e = true := by decide +kernel

theorem covers : ∀ k : BitVec 8, (∀ e ∈ edges, e &&& k ≠ 0) →
    4 ≤ k.cpop.toNat ∧ (k.cpop.toNat ≤ 4 → k = 85 ∨ k = 170) := by decide +kernel

theorem addOutside : ∀ k : BitVec 8, k = 85 ∨ k = 170 →
    ∀ x : BitVec 8, x &&& k ≠ 0 → hasEdge (x ||| ~~~k) = true := by decide +kernel

theorem sameMask : ∀ k : BitVec 8, k = 85 ∨ k = 170 →
    ∀ x : BitVec 8, (x ||| ~~~k) &&& k = x &&& k := by decide +kernel

end PEqualNP.Research.HeawoodSupportAux

open PEqualNP.Research.HeawoodSupportAux

theorem PEqualNP.Research.HeawoodSupport :
let cycleEdge : BitVec 8 → Bool := fun x =>
  [3,6,12,24,48,96,192,129].any fun m : BitVec 8 => x &&& m == m
∀ (q : BitVec 8 → Bool), q 0 = false → (∀ y, cycleEdge y = true → q y = true) →
  ∀ k : BitVec 8, (∀ y, q (y &&& k) = q y) →
  4 ≤ k.cpop.toNat ∧ (k.cpop.toNat ≤ 4 →
    (k = 85 ∨ k = 170) ∧ ∀ y, q y = decide (y &&& k ≠ 0)) := by
  intro cycleEdge q hz sound k factor
  have hit (e : BitVec 8) (he : e ∈ edges) : e &&& k ≠ 0 := by
    intro h
    have yes := sound e (ownEdge e he)
    have eq := factor e
    rw [h,hz,yes] at eq
    contradiction
  obtain ⟨lb,shape⟩ := covers k hit
  refine ⟨lb,fun le => ⟨shape le,fun x => ?_⟩⟩
  by_cases empty : x &&& k = 0
  · rw [← factor x, empty, hz]
    decide
  · have yes := sound (x ||| ~~~k) (addOutside k (shape le) x empty)
    have same := factor (x ||| ~~~k)
    rw [sameMask k (shape le) x, factor x, yes] at same
    exact same.trans (decide_eq_true empty).symm

#print axioms PEqualNP.Research.HeawoodSupport

