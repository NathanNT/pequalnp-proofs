import PEqualNP.Gct.QuotientWitness

theorem PEqualNP.Gct.QuotientWitness195 :
∀ L : Submodule ℂ (Fin 4 × Fin 6 → ℂ), (∀ t ∈ L, (∑ i : Fin 4, ∑ j, t (i, j)) = 0 ∧ (∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a, j) * t (b, l) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, if a < b ∧ b < c then t (a, j) * t (b, l) * t (c, m) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, ∑ n, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else t (0, j) * t (1, l) * t (2, m) * t (3, n)) = 0) →
let m : L →ₗ[ℂ] ((Fin 3 → ℂ) × (Fin 5 → ℂ)) :=
  { toFun := fun x => (fun i => ∑ j, x.val (i.castSucc,j), fun j => ∑ i, x.val (i,j.castSucc))
    map_add' := by intro x y; ext <;> simp [Finset.sum_add_distrib]
    map_smul' := by intro r x; ext <;> simp [Finset.mul_sum] }
∀ P : Submodule ℂ L, 8 < Module.finrank ℂ (L ⧸ P) + Module.finrank ℂ (P.map m) →
∃ x : L, x∉P ∧ (∀ i, ∑ j,x.val (i,j)=0) ∧ (∀ j, ∑ i,x.val (i,j)=0) ∧
    (fun p => star (x.val p))∉L := by
  intro L lev m P dim
  exact PEqualNP.Gct.PureQuotient.quotientWitness L lev P dim
