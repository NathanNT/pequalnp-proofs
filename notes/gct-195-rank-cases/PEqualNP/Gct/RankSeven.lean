import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace PEqualNP.Gct.RankSeven
open Module
private lemma slice_zero (h u y z v : ℂ)
    (e₀ : 18*h^2 + u*z = 0) (e₁ : y*v = 0) (e₂ : u*v + y*z = 0)
    (e₃ : u^3+y^3+z^3+v^3-36*h*u*z=0) (ell : u+2*y+2*z+3*v=0) :
    h=0 ∧ u=0 ∧ y=0 ∧ z=0 ∧ v=0 := by
  rcases mul_eq_zero.mp e₁ with hy|hv
  · subst y
    have uv : u*v=0 := by linear_combination e₂
    rcases mul_eq_zero.mp uv with hu|hv
    · subst u
      have hh : h^2=0 := by linear_combination e₀/18
      have hz : z= -(3/2)*v := by linear_combination ell/2
      rw [hz] at e₃
      have h3 : v^3=0 := by linear_combination (-8/19)*e₃
      simp_all
    · subst v
      have hu : u= -2*z := by linear_combination ell
      subst u
      have factor : (3*h-z)*(3*h+z)=0 := by linear_combination e₀/2
      rcases mul_eq_zero.mp factor with hp|hp
      · have hh : h=z/3 := by linear_combination hp/3
        rw [hh] at e₃
        have h3 : z^3=0 := by linear_combination e₃/17
        simp_all
      · have hh : h= -z/3 := by linear_combination hp/3
        rw [hh] at e₃
        have h3 : z^3=0 := by linear_combination -e₃/31
        simp_all
  · subst v
    have yz : y*z=0 := by linear_combination e₂
    rcases mul_eq_zero.mp yz with hy|hz
    · subst y
      have hu : u= -2*z := by linear_combination ell
      subst u
      have factor : (3*h-z)*(3*h+z)=0 := by linear_combination e₀/2
      rcases mul_eq_zero.mp factor with hp|hp
      · have hh : h=z/3 := by linear_combination hp/3
        rw [hh] at e₃
        have h3 : z^3=0 := by linear_combination e₃/17
        simp_all
      · have hh : h= -z/3 := by linear_combination hp/3
        rw [hh] at e₃
        have h3 : z^3=0 := by linear_combination -e₃/31
        simp_all
    · subst z
      have hh : h^2=0 := by linear_combination e₀/18
      have hu : u= -2*y := by linear_combination ell
      rw [hu] at e₃
      have h3 : y^3=0 := by linear_combination -e₃/7
      simp_all

theorem normalFormBound {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (p : V →ₗ[ℂ] (Fin 5 → ℂ)) (q : V →ₗ[ℂ] Module.Dual ℂ (Fin 5 → ℂ))
    (h u y z v : V →ₗ[ℂ] ℂ) (pairing : ∀ x, q x (p x) = 0)
    (slice : ∀ x, p x = 0 → q x = 0 →
      18*(h x)^2 + u x*z x = 0 ∧ y x*v x=0 ∧ u x*v x+y x*z x=0 ∧
      (u x)^3+(y x)^3+(z x)^3+(v x)^3-36*h x*u x*z x=0)
    (coords : ∀ x, p x=0 → q x=0 → h x=0 → u x=0 → y x=0 → z x=0 → v x=0 → x=0) :
    finrank ℂ V ≤ 6 := by
  let K := LinearMap.ker p
  let S := LinearMap.range p
  have ann (x : K) : q x.val ∈ S.dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    rintro _ ⟨b,rfl⟩
    have hx : p x.val=0 := x.property
    have e := pairing (x.val+b)
    simpa [map_add,hx,pairing] using e
  let a := ((q.domRestrict K).codRestrict S.dualAnnihilator ann)
  let f := u + (2:ℂ) • y + (2:ℂ) • z + (3:ℂ) • v
  let emb := a.prod (f.domRestrict K)
  have inj : Function.Injective emb := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro x hx
    change emb x=0 at hx
    have ax := congrArg Prod.fst hx
    have fx := congrArg Prod.snd hx
    have qx : q x.val=0 := congrArg Subtype.val ax
    have px : p x.val=0 := x.property
    have el : u x.val+2*y x.val+2*z x.val+3*v x.val=0 := by simpa [emb,f,smul_eq_mul] using fx
    obtain ⟨e0,e1,e2,e3⟩ := slice x.val px qx
    obtain ⟨hh,hu,hy,hz,hv⟩ := slice_zero _ _ _ _ _ e0 e1 e2 e3 el
    exact Subtype.ext (coords x.val px qx hh hu hy hz hv)
  have bound := emb.finrank_le_finrank_of_injective inj
  have dim := Subspace.finrank_add_finrank_dualAnnihilator_eq S
  have tot := p.finrank_range_add_finrank_ker
  simp only [Module.finrank_prod, Module.finrank_self] at bound
  simp only [Module.finrank_pi, Fintype.card_fin] at dim
  change finrank ℂ K ≤ finrank ℂ S.dualAnnihilator + 1 at bound
  change finrank ℂ S + finrank ℂ K = finrank ℂ V at tot
  omega
end PEqualNP.Gct.RankSeven
