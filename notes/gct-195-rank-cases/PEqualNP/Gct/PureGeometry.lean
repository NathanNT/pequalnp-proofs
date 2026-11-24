import PEqualNP.Gct.RankSeven195
import Mathlib.LinearAlgebra.Matrix.Dual
namespace PEqualNP.Gct.PureGeometry
open Module
abbrev R := Fin 6 → ℂ

noncomputable def blend {n : ℕ} (w : Fin n → R) : (Fin n → ℂ) →ₗ[ℂ] R :=
  ∑ k, (LinearMap.proj (R:=ℂ) (φ:=fun _ : Fin n => ℂ) k).smulRight (w k)

theorem blend_dot {n : ℕ} (w : Fin n → R) (c : Fin n → ℂ) (y : R) :
    (blend w c) ⬝ᵥ y = ∑ k, c k * (w k ⬝ᵥ y) := by
  simp only [blend,LinearMap.sum_apply,LinearMap.smulRight_apply,LinearMap.proj_apply,
    sum_dotProduct,smul_dotProduct,smul_eq_mul]

theorem threeImpossible (U V : Submodule ℂ R) (hu : 2≤finrank ℂ U) (hv : 2≤finrank ℂ V)
    (cross : ∀ x∈V, ∀ y∈U, x ⬝ᵥ y=0) (w : Fin 3 → R)
    (wu : ∀ k, ∀ x∈U, w k ⬝ᵥ x=0) (wv : ∀ k, ∀ x∈V, w k ⬝ᵥ x=0)
    (reg : ∀ c : Fin 3 → ℂ, (∀ k, (blend w c) ⬝ᵥ w k=0) → c=0) : False := by
  let h : ((Fin 3 → ℂ) × V) →ₗ[ℂ] R :=
    (blend w).comp (LinearMap.fst ℂ _ _) + V.subtype.comp (LinearMap.snd ℂ _ _)
  let E := dotProductEquiv ℂ (Fin 6)
  let m := (E.toLinearMap.comp h).codRestrict U.dualAnnihilator (by
    intro v; rw [Submodule.mem_dualAnnihilator]; intro y hy
    change (blend w v.1 + v.2.val) ⬝ᵥ y=0
    simp [add_dotProduct,blend_dot,wu _ y hy,cross _ v.2.property y hy])
  have inj : Function.Injective m := by
    apply LinearMap.ker_eq_bot.mp; apply le_antisymm _ bot_le
    intro v hv0
    have eqn : blend w v.1 + v.2.val=0 := E.injective (show E (h v)=E 0 by
      rw [map_zero]; exact congrArg Subtype.val (show m v=0 from hv0))
    have hc : v.1=0 := reg _ (by
      intro k
      have e := congrArg (fun t : R => t ⬝ᵥ w k) eqn
      rw [add_dotProduct, dotProduct_comm v.2.val, wv _ _ v.2.property,add_zero] at e
      simpa using e)
    rw [hc,map_zero,zero_add] at eqn
    exact Prod.ext hc (Subtype.ext eqn)
  have d := m.finrank_le_finrank_of_injective inj
  have b := Subspace.finrank_add_finrank_dualAnnihilator_eq U
  simp [Module.finrank_prod,Module.finrank_pi,Fintype.card_fin] at d b
  omega

theorem fourSpan (w : Fin 4 → R) (indep : Function.Injective (blend w))
    (U : Submodule ℂ R) (hu : 2≤finrank ℂ U)
    (huv : ∀ k, ∀ x∈U, w k ⬝ᵥ x=0) (y : R) (hy : ∀ k, w k ⬝ᵥ y=0) : y∈U := by
  let M : R →ₗ[ℂ] (Fin 4 → ℂ) := LinearMap.pi fun i => dotProductEquiv ℂ (Fin 6) (w i)
  let K := LinearMap.ker M
  have uk : U≤K := by intro x hx; funext k; exact huv k _ hx
  let E := dotProductEquiv ℂ (Fin 6)
  let b := (E.toLinearMap.comp (blend w)).codRestrict K.dualAnnihilator (by
    intro c; rw [Submodule.mem_dualAnnihilator]; intro x hx
    change (blend w c) ⬝ᵥ x=0
    have e (i : Fin 4) : w i ⬝ᵥ x=0 := congrFun (show M x=0 from hx) i
    simp [blend_dot,e])
  have bi : Function.Injective b := fun _ _ h => indep (E.injective (congrArg Subtype.val h))
  have d := b.finrank_le_finrank_of_injective bi
  have dim := Subspace.finrank_add_finrank_dualAnnihilator_eq K
  simp [Module.finrank_pi,Fintype.card_fin] at d dim
  have eqn : U=K := Submodule.eq_of_le_of_finrank_le uk (by omega)
  rw [eqn]; exact (show M y=0 by funext k; exact hy k)
end PEqualNP.Gct.PureGeometry
