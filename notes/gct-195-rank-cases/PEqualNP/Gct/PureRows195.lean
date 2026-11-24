import PEqualNP.Gct.PureCriterion

theorem PEqualNP.Gct.PureRows195 :
∀ L : Submodule ℂ (Fin 4 × Fin 6 → ℂ), (∀ t ∈ L, (∑ i : Fin 4, ∑ j, t (i, j)) = 0 ∧ (∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a, j) * t (b, l) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, if a < b ∧ b < c then t (a, j) * t (b, l) * t (c, m) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, ∑ n, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else t (0, j) * t (1, l) * t (2, m) * t (3, n)) = 0) →
(∃ f : Fin 6 → ℂ, f ≠ 0 ∧ (fun p : Fin 4 × Fin 6 =>
  (if p.1=3 then (-1 : ℂ) else 3) * f p.2) ∈ L) →
let U (i : Fin 4) := L.comap
  ({ toFun := fun (y : Fin 6 → ℂ) (p : Fin 4 × Fin 6) => if p.1=i then y p.2 else 0
     map_add' := by intro a b; funext p; by_cases h : p.1=i <;> simp [h]
     map_smul' := by intro a b; funext p; by_cases h : p.1=i <;> simp [h] } :
    (Fin 6 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 6 → ℂ))
∀ i j : Fin 4, i ≠ j → Module.finrank ℂ (U i) ≤ 1 ∨ Module.finrank ℂ (U j) ≤ 1 := by
  intro L lev ⟨f,hn,hf⟩ U i j ij
  by_contra! two
  exact PEqualNP.Gct.PureRows.criterion L lev f hf hn i j ij two.1 two.2
