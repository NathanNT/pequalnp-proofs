import Mathlib.Tactic
open Finset
namespace PEqualNP.Gct.RankSeven

theorem fourierTriple {w : ℂ} (hw : w^2+w+1=0) {v : Fin 3 → ℂ} (hn : v≠0)
    (hs : ∑ i, v i=0) (hq : ∑ i, v i^2=0) :
    v 0≠0 ∧ ((v 1=w*v 0 ∧ v 2=w^2*v 0) ∨ (v 1=w^2*v 0 ∧ v 2=w*v 0)) := by
  simp only [Fin.sum_univ_three] at hs hq
  have he : v 2= -v 0-v 1 := by linear_combination hs
  rw [he] at hq
  have hprod : (v 1-w*v 0)*(v 1-w^2*v 0)=0 := by
    linear_combination hq/2 + ((w-1)*(v 0)^2-v 0*v 1)*hw
  obtain h|h := mul_eq_zero.mp hprod <;> have hv := sub_eq_zero.mp h
  · have ht : v 2=w^2*v 0 := by linear_combination hs - hv - v 0*hw
    refine ⟨?_,Or.inl ⟨hv,ht⟩⟩
    intro h0
    apply hn
    funext i
    fin_cases i <;> simp_all
  · have ht : v 2=w*v 0 := by linear_combination hs - hv - v 0*hw
    refine ⟨?_,Or.inr ⟨hv,ht⟩⟩
    intro h0
    apply hn
    funext i
    fin_cases i <;> simp_all
end PEqualNP.Gct.RankSeven
