import PEqualNP.Gct.PureGeometry
namespace PEqualNP.Gct.PureGeometry
open Finset
private theorem vanishPoly (s : Finset (Fin 6)) (f : R) (a : R)
    (h : ∀ k ≤ s.card, ∑ j, a j * f j^k=0) :
    ∑ j, a j * ∏ t ∈ s, (f j-f t)=0 := by
  classical
  induction s using Finset.induction_on generalizing a with
  | empty => simpa using h 0 (by simp)
  | @insert t s ht ih =>
    have b := ih (fun j => a j*(f j-f t)) (by
      intro k hk
      have h1 := h (k+1) (by simpa [ht] using hk)
      have h0 := h k (by simp [ht]; omega)
      calc
        _ = ∑ j, (a j*f j^(k+1) - f t*(a j*f j^k)) := by
          apply sum_congr rfl; intros; ring
        _ = 0 := by rw [sum_sub_distrib,← mul_sum,h0,h1]; ring)
    simpa [prod_insert ht,mul_assoc] using b

theorem momentSix (f : R) (hf : f≠0)
    (h : ∀ k : Fin 5, ∑ j, f j^(k.val+1)=0) : ∑ j, f j^6≠0 := by
  classical
  intro h6; apply hf; funext i
  by_contra hn
  change f i ≠ 0 at hn
  let s := univ.filter fun j => f j≠f i
  have hi : i∉s := by simp [s]
  have card : s.card<6 := by
    have := card_lt_card ((show s ⊂ univ from Finset.ssubset_univ_iff.mpr (by intro he; exact hi (he.symm ▸ mem_univ i))))
    simpa using this
  have z := vanishPoly s f f (by
    intro k hk
    simp_rw [← pow_succ'] 
    by_cases hk' : k<5
    · exact h ⟨k,hk'⟩
    · have : k=5 := by omega
      subst k; exact h6)
  let v := f i * ∏ t∈s, (f i-f t)
  have hv : v≠0 := mul_ne_zero hn (prod_ne_zero_iff.mpr (by
    intro t ht; exact sub_ne_zero.mpr (Ne.symm (mem_filter.mp ht).2)))
  have e (j : Fin 6) : f j * ∏ t∈s, (f j-f t) = if f j=f i then v else 0 := by
    split_ifs with he
    · rw [he]
    · have hj : j∈s := mem_filter.mpr ⟨mem_univ _,he⟩
      rw [prod_eq_zero hj (by simp),mul_zero]
  simp_rw [e] at z
  rw [← sum_filter] at z
  simp only [sum_const,nsmul_eq_mul,mul_eq_zero,Nat.cast_eq_zero,Finset.card_eq_zero] at z
  have ne : (univ.filter fun j => f j=f i).Nonempty := ⟨i,by simp⟩
  exact z.elim ne.ne_empty hv
end PEqualNP.Gct.PureGeometry
