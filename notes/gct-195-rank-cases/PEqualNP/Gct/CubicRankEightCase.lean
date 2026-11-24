import PEqualNP.Gct.OneModeBound

theorem PEqualNP.Gct.CubicRankEightCase :
∀ L : Submodule ℂ (Fin 4 × Fin 6 → ℂ), (∀ t ∈ L, (∑ i : Fin 4, ∑ j, t (i, j)) = 0 ∧ (∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a, j) * t (b, l) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, if a < b ∧ b < c then t (a, j) * t (b, l) * t (c, m) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, ∑ n, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else t (0, j) * t (1, l) * t (2, m) * t (3, n)) = 0) → ∀ w : ℂ, w^2+w+1=0 →
let A : Fin 4 × Fin 6 → ℂ := fun p =>
  (if p.1=3 then -1 else 3)*(![1,w,w^2,0,0,0] p.2)
∀ B : Submodule ℂ (Fin 4 × Fin 6 → ℂ), B≤L → A∈B →
(∀ m∈B, ∃ (t : ℂ) (y z : Fin 6 → ℂ), m=t • A +
  (fun p => if p.1=3 then y p.2 else (![1,w,w^2,0] p.1)*z p.2)) →
let D : L →ₗ[ℂ] (Fin 3 × Fin 6 → ℂ) :=
  { toFun := fun m p => m.val (p.1.castSucc,p.2) + 3*m.val (3,p.2)
    map_add' := by intro x y; ext p; simp; ring
    map_smul' := by intro c x; ext p; simp; ring }
Module.finrank ℂ B ≤ 6 ∧
(Module.finrank ℂ (L ⧸ B.comap L.subtype) ≤ 2 →
  Module.finrank ℂ L ≤ 8 ∧ (Module.finrank ℂ (LinearMap.range D) = 8 →
    Module.finrank ℂ (LinearMap.ker D) = 0)) := by
  intro L h w hw A B hBL hA hshape D
  have hb := PEqualNP.Gct.OneMode.blockBound hw B (fun m hm => h m (hBL hm)) hA hshape
  refine ⟨hb,?_⟩
  intro hq
  have d := (B.comap L.subtype).finrank_quotient_add_finrank
  have b := (Submodule.comapSubtypeEquivOfLe hBL).finrank_eq
  change Module.finrank ℂ (B.comap L.subtype) = Module.finrank ℂ B at b
  have l : Module.finrank ℂ L ≤ 8 := by
    rw [← d]
    exact Nat.add_le_add hq (b.trans_le hb)
  exact ⟨l,fun hr => by have r := D.finrank_range_add_finrank_ker; omega⟩

