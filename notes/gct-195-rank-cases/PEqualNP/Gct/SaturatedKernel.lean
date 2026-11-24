import PEqualNP.Gct.ProfileFourSix
import PEqualNP.Gct.PermanentPencil
import PEqualNP.Gct.KernelTriples

namespace PEqualNP.Gct.RankSeven
open Module PermanentPencil

noncomputable def profile : (Fin 6 → ℂ) →ₗ[ℂ] (Pos → ℂ) where
  toFun x p := (if p.1=3 then -1 else 3)*x p.2
  map_add' := by intro x y; funext p; simp [mul_add]
  map_smul' := by intro c x; funext p; simp; ring

/-- At saturation both kernel generators are supported on independent Fourier triples. -/
theorem kernelNormalForm (w : ℂ) (hw : w^2+w+1=0) (L : Submodule ℂ (Pos → ℂ))
    (levelL : ∀ m ∈ L, level m) (hd : finrank ℂ (L.comap profile)=2) :
    ∃ (e : Fin 2 × Fin 3 ≃ Fin 6) (v : Fin 2 → Fin 3 → ℂ),
      (∀ b, v b 0=1 ∧ ((v b 1=w ∧ v b 2=w^2) ∨ (v b 1=w^2 ∧ v b 2=w))) ∧
      ∀ amplitudes : Fin 2 → ℂ, ∃ x, profile x ∈ L ∧
        ∀ b i, x (e (b,i))=amplitudes b*v b i := by
  classical
  let X := L.comap profile
  have lv (x : Fin 6 → ℂ) (hx : x∈X) := levelL (profile x) hx
  obtain ⟨_,caseEq⟩ := PEqualNP.Gct.ProfileFourSix X (by
    intro x hx
    exact ⟨(lv x hx).1,(lv x hx).2.1,(lv x hx).2.2.2⟩)
  obtain ⟨e₀,v₀,hv₀,sp₀⟩ := caseEq hd
  have hcast : finrank ℂ X = 2 := hd
  let castB := finCongr hcast
  let e : Fin 2 × Fin 3 ≃ Fin 6 := (Equiv.prodCongr castB.symm (Equiv.refl _)).trans e₀
  let v := fun b : Fin 2 => v₀ (castB.symm b)
  have gen (a : Fin 2 → ℂ) : ∃ x ∈ X, ∀ b i, x (e (b,i))=a b*v b i := by
    let z := fun b i => a (castB b)*v₀ b i
    obtain ⟨x,hx,hz⟩ := (sp₀ z).mpr ⟨fun b => a (castB b),by intros; rfl⟩
    refine ⟨x,hx,fun b i => ?_⟩
    simpa [e,z,v] using hz (castB.symm b) i
  have sum0 (x : Fin 6 → ℂ) (hx : x∈X) : ∑ j,x j=0 := by
    have H := (lv x hx).1
    simp only [first,profile,LinearMap.coe_mk,AddHom.coe_mk,Fin.sum_univ_four] at H
    norm_num at H
    simp only [← Finset.mul_sum] at H
    linear_combination H/8
  have per (b : Fin 2) : v b 0 ≠ 0 ∧ ((v b 1=w*v b 0 ∧ v b 2=w^2*v b 0) ∨
      (v b 1=w^2*v b 0 ∧ v b 2=w*v b 0)) := by
    have h := hv₀ (castB.symm b)
    apply fourierTriple hw h.1 _ h.2.1
    obtain ⟨x,hx,hxi⟩ := gen (fun j => if b=j then 1 else 0)
    have hxsum := (e.sum_comp x).trans (sum0 x hx)
    simpa [Fintype.sum_prod_type,hxi] using hxsum
  refine ⟨e,fun b i => v b i/v b 0,?_,?_⟩
  · intro b
    obtain ⟨hn,k⟩ := per b
    constructor
    · exact div_self hn
    rcases k with ⟨h₁,h₂⟩|⟨h₁,h₂⟩
    · exact Or.inl ⟨by simp [h₁,hn],by simp [h₂,hn]⟩
    · exact Or.inr ⟨by simp [h₁,hn],by simp [h₂,hn]⟩
  · intro a
    obtain ⟨x,hx,h⟩ := gen (fun b => a b/v b 0)
    exact ⟨x,hx,fun b i => (h b i).trans (by ring)⟩
end PEqualNP.Gct.RankSeven
