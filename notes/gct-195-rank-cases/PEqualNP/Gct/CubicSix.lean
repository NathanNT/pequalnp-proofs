import Mathlib
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace PEqualNP.Gct.CubicSix
open Module Finset

private theorem half {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : V →ₗ[ℂ] (Fin n → ℂ)) (hi : Function.Injective f)
    (c : Fin n → ℂ) (hc : ∀ i, c i≠0) (cube : ∀ x, (∑ i, c i*(f x i)^3)=0) :
    2*finrank ℂ V ≤ n := by
  classical
  let g (i : Fin n) := (LinearMap.proj (R:=ℂ) (φ:=fun _ : Fin n => ℂ) i).comp f
  let I := {i : Fin n // g i≠0}
  obtain ⟨t,ht⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (fun i : I => LinearMap.ker (g i.val)) (fun i h => i.property (LinearMap.ker_eq_top.mp h))
  have generic (i : Fin n) (h : g i≠0) : f t i≠0 := ht ⟨i,h⟩
  have polar (a b d : V) : (∑ i, c i*f a i*f b i*f d i)=0 := by
    have e : (6:ℂ)*(∑ i, c i*f a i*f b i*f d i) =
        (∑ i, c i*(f (a+b+d) i)^3) - (∑ i, c i*(f (a+b) i)^3) -
        (∑ i, c i*(f (a+d) i)^3) - (∑ i, c i*(f (b+d) i)^3) +
        (∑ i, c i*(f a i)^3) + (∑ i, c i*(f b i)^3) + (∑ i, c i*(f d i)^3) := by
      rw [Finset.mul_sum]
      repeat rw [← Finset.sum_sub_distrib]
      repeat rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp [map_add]; ring
    simp only [cube,sub_zero,add_zero] at e
    exact (mul_eq_zero.mp e).resolve_left (by norm_num)
  let h : V →ₗ[ℂ] (Fin n → ℂ) := LinearMap.pi (fun i => (c i*f t i) • g i)
  have hin : Function.Injective h := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro x hx
    apply hi
    rw [map_zero]
    funext i
    have h0 := congrFun (show h x=0 from hx) i
    change c i*f t i*f x i=0 at h0
    by_cases hg : g i=0
    · exact congrArg (fun l : V →ₗ[ℂ] ℂ => l x) hg
    · exact (mul_eq_zero.mp h0).resolve_left (mul_ne_zero (hc i) (generic i hg))
  let E := dotProductEquiv ℂ (Fin n)
  let dual := E.toLinearMap.comp h
  have ann (x : V) : dual x ∈ (LinearMap.range f).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    rintro _ ⟨y,rfl⟩
    exact polar t x y
  let into := dual.codRestrict (LinearMap.range f).dualAnnihilator ann
  have inj : Function.Injective into := by
    intro x y hxy
    exact hin (E.injective (congrArg Subtype.val hxy))
  have le := into.finrank_le_finrank_of_injective inj
  have dim := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.range f)
  rw [LinearMap.finrank_range_of_inj hi] at dim
  simp only [Module.finrank_pi,Fintype.card_fin] at dim
  omega

def ordered3 (z : Fin 6 → ℂ) : ℂ := ∑ j,∑ l,∑ n,
    if j=l ∨ j=n ∨ l=n then 0 else z j*z l*z n
theorem dimension (W : Submodule ℂ (Fin 6 → ℂ)) (iso : ∀ x∈W, ordered3 x=0) :
    finrank ℂ W≤3 := by
  let sum : W →ₗ[ℂ] ℂ := ∑ j : Fin 6, (LinearMap.proj (R:=ℂ) (φ:=fun _ : Fin 6 => ℂ) j).domRestrict W
  let f : W →ₗ[ℂ] (Fin 7 → ℂ) := LinearMap.pi (Fin.cons sum
    (fun i => (LinearMap.proj (R:=ℂ) (φ:=fun _ : Fin 6 => ℂ) i).domRestrict W - (1/2:ℂ) • sum))
  let c : Fin 7 → ℂ := Fin.cons 1 (fun _ => 2)
  have inj : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro x hx
    have hz := congrFun (show f x=0 from hx) 0
    change sum x=0 at hz
    apply Subtype.ext
    funext i
    have h := congrFun (show f x=0 from hx) i.succ
    change x.val i - (1/2:ℂ)*(sum x)=0 at h
    simpa [hz] using h
  have eqn (x : W) : (∑ i, c i*(f x i)^3)=ordered3 x.val := by
    rw [Fin.sum_univ_succ]
    simp [f,c,sum,ordered3,Fin.sum_univ_succ,LinearMap.sum_apply] <;> ring
  have bound := half f inj c (fun i => by refine Fin.cases ?_ (fun _ => ?_) i <;> norm_num [c]) (fun x => (eqn x).trans (iso _ x.property))
  omega
end PEqualNP.Gct.CubicSix
