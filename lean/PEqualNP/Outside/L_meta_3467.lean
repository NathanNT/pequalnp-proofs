import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection

namespace PEqualNP.Outside.L_meta_3467

theorem eval_input (C : Circuit) (x : List Bool) (h : C.output < x.length) :
    C.eval x = x.getD C.output false := by
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have keep (gs : List Gate) (w : List Bool) (hw : C.output < w.length) :
      (gs.foldl step w).getD C.output false = w.getD C.output false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
      simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hw]
  exact keep C.gates x h

end PEqualNP.Outside.L_meta_3467

open PEqualNP.Outside.L_meta_3467 in
theorem PEqualNP.Outside.L_meta_3467 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro q n S C hq _ _ _ _ hout _ reject
  classical
  exfalso
  by_cases h : C.output < n
  · have bad := reject Finset.univ ∅ (by simp) (by simp [IsFalseInput])
    have bound : C.output < (incidenceInput (Finset.univ : Finset (Fin n)) (∅ : Finset (Fin n))).length := by
      simpa [incidenceInput] using hout
    rw [eval_input C _ bound] at bad
    simp [incidenceInput, List.getD_eq_getElem?_getD] at bad
    rw [List.getElem?_append_left (by simpa using h : C.output < (List.replicate n true).length)] at bad
    simp [h] at bad
  · let j : Fin n := ⟨C.output - n, by omega⟩
    have bad := reject ∅ {j} (by simp; omega) (by simp [IsFalseInput])
    have bound : C.output < (incidenceInput (∅ : Finset (Fin n)) {j}).length := by
      simpa [incidenceInput] using hout
    rw [eval_input C _ bound] at bad
    have hj : C.output - n < n := j.isLt
    have hright : (List.ofFn (fun i : Fin n => decide (i ∈ (∅ : Finset (Fin n))))).length ≤ C.output := by
      simp; omega
    simp only [incidenceInput, List.getD_eq_getElem?_getD, List.getElem?_append_right hright,
      List.length_ofFn, List.getElem?_ofFn, hj, dite_true, Option.getD_some] at bad
    simp [j] at bad
