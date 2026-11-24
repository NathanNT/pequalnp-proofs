import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.L_meta_3306 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Finset ℕ), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ x6 < x2.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x9 : ℕ) (x10 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).inputs = [x9, x10] ∧ (x9 ∈ x3 ∧ x10 ∈ x4 ∨ x9 ∈ x4 ∧ x10 ∈ x3)) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x7 ∧ x7.size = x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.circuitFun x1 x2 ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op) ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8 = PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8) ∧ ∀ x8 < x7.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x11 : ℕ) (x12 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).inputs = [x11, x12] ∧ x11 ∈ x4 ∧ x12 ∈ x3 := by
  classical
  intro n C A B initial cross
  let oriented (g : Gate) := ∃ a b, g.inputs = [a,b] ∧ a ∈ B ∧ b ∈ A
  let reorder (g : Gate) : Gate :=
    if g.op = GateOp.and ∧ ¬ oriented g then { g with inputs := g.inputs.reverse } else g
  let D : Circuit := ⟨C.gates.map reorder, C.output⟩
  have ops (g : Gate) : (reorder g).op = g.op := by
    unfold reorder
    split <;> rfl
  have len (g : Gate) : (reorder g).inputs.length = g.inputs.length := by
    unfold reorder
    split <;> simp
  have mem (g : Gate) (k : ℕ) : k ∈ (reorder g).inputs ↔ k ∈ g.inputs := by
    unfold reorder
    split <;> simp
  have atGate (j : ℕ) : gateAt D j = reorder (gateAt C j) := by
    simp only [gateAt, D, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases C.gates[j]? <;> simp [reorder]
  have same (g : Gate) (f : ℕ → Bool) :
      (reorder g).op.eval ((reorder g).inputs.map f) = g.op.eval (g.inputs.map f) := by
    unfold reorder
    split
    · rename_i h
      simp [h.1, GateOp.eval, List.map_reverse]
    · rfl
  let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have run (gs : List Gate) (w : List Bool) : (gs.map reorder).foldl step w = gs.foldl step w := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons]
      rw [ih]
      exact congrArg (gs.foldl step) (congrArg (fun b => w ++ [b]) (same g _))
  refine ⟨D, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
    simpa only [ops] using initial.1 h hh
  · intro j hj k hk
    apply initial.2.1 j (by simpa [D] using hj) k
    exact (mem _ _).mp (atGate j ▸ hk)
  · intro g hg
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
    exact (len h).trans (initial.2.2 h hh)
  · simp [D, Circuit.size]
  · funext x
    exact congrArg (fun w : List Bool => w.getD C.output false) (run C.gates (List.ofFn x))
  · intro j
    rw [atGate, ops]
  · intro j hj
    simp [atGate, reorder, hj]
  · intro j hj hOp
    rw [atGate, ops] at hOp
    obtain ⟨a,b,hab,hs⟩ := cross j (by simpa [D] using hj) hOp
    rw [atGate]
    by_cases ho : oriented (gateAt C j)
    · rw [show reorder (gateAt C j) = gateAt C j by simp [reorder, ho]]
      exact ho
    · have hba : a ∈ A ∧ b ∈ B := hs.resolve_right (fun h => ho ⟨a,b,hab,h⟩)
      exact ⟨b,a,by simp [reorder, hOp, ho, hab],hba.2,hba.1⟩
