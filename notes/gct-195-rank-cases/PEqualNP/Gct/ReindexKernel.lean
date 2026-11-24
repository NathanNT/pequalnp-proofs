import PEqualNP.Gct.SaturatedKernel
import PEqualNP.Gct.DeskWords

namespace PEqualNP.Gct.RankSeven
open Module PermanentPencil FourierTable DeskPolar

noncomputable def reindex (e : Equiv.Perm (Fin 6)) : (Pos → ℂ) ≃ₗ[ℂ] (Pos → ℂ) where
  toFun m p := m (p.1,e p.2)
  invFun m p := m (p.1,e.symm p.2)
  left_inv m := by funext p; simp
  right_inv m := by funext p; simp
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
private lemma reSum2 (e : Equiv.Perm (Fin 6)) (f : Fin 6 → Fin 6 → ℂ) :
    ∑ j, ∑ l, f (e j) (e l) = ∑ j, ∑ l, f j l := by
  calc
    _ = ∑ j, ∑ l, f (e j) l := by
      apply Finset.sum_congr rfl; intro j _; exact Equiv.sum_comp e (f (e j))
    _ = _ := Equiv.sum_comp e (fun j => ∑ l, f j l)
private lemma reSum3 (e : Equiv.Perm (Fin 6)) (f : Fin 6 → Fin 6 → Fin 6 → ℂ) :
    ∑ j, ∑ l, ∑ n, f (e j) (e l) (e n) = ∑ j, ∑ l, ∑ n, f j l n := by
  calc
    _ = ∑ j, ∑ l, ∑ n, f (e j) l n := by
      apply Finset.sum_congr rfl; intro j _; exact reSum2 e (f (e j))
    _ = _ := Equiv.sum_comp e (fun j => ∑ l, ∑ n, f j l n)
private lemma reSum4 (e : Equiv.Perm (Fin 6)) (f : Fin 6 → Fin 6 → Fin 6 → Fin 6 → ℂ) :
    ∑ j, ∑ l, ∑ n, ∑ o, f (e j) (e l) (e n) (e o) = ∑ j, ∑ l, ∑ n, ∑ o, f j l n o := by
  calc
    _ = ∑ j, ∑ l, ∑ n, ∑ o, f (e j) l n o := by
      apply Finset.sum_congr rfl; intro j _; exact reSum3 e (f (e j))
    _ = _ := Equiv.sum_comp e (fun j => ∑ l, ∑ n, ∑ o, f j l n o)
theorem reLevel (e : Equiv.Perm (Fin 6)) (m : Pos → ℂ) (h : level m) : level (reindex e m) := by
  obtain ⟨h1,h2,h3,h4⟩ := h
  refine ⟨?_,?_,?_,?_⟩
  · change (∑ i : Fin 4, ∑ j : Fin 6, m (i,e j))=0
    apply Eq.trans _ h1
    apply Finset.sum_congr rfl; intro i _; exact Equiv.sum_comp e (fun j => m (i,j))
  · let f (j l : Fin 6) := if j=l then 0 else ∑ a : Fin 4, ∑ b : Fin 4,
      if a<b then m (a,j)*m (b,l) else 0
    simpa [second,reindex,f] using (reSum2 e f).trans h2
  · let f (j l n : Fin 6) := if j=l ∨ j=n ∨ l=n then 0 else
      ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, if a<b ∧ b<c then m (a,j)*m (b,l)*m (c,n) else 0
    simpa [third,reindex,f] using (reSum3 e f).trans h3
  · let f (j l n o : Fin 6) := if j=l ∨ j=n ∨ j=o ∨ l=n ∨ l=o ∨ n=o then 0 else
      m (0,j)*m (1,l)*m (2,n)*m (3,o)
    simpa [fourth,reindex,f] using (reSum4 e f).trans h4

theorem normalize (w : ℂ) (hw : w^2+w+1=0) (L : Submodule ℂ (Pos → ℂ))
    (lev : ∀ m∈L, level m) (dim : finrank ℂ (L.comap profile)=2) :
    ∃ M : Submodule ℂ (Pos → ℂ), finrank ℂ L=finrank ℂ M ∧ (∀ m∈M,level m) ∧
      restrict (atom w 15) ∈ M ∧ restrict (atom w 16) ∈ M := by
  classical
  obtain ⟨e,v,orient,amp⟩ := kernelNormalForm w hw L lev dim
  let τ (b : Fin 2) : Equiv.Perm (Fin 3) :=
    if v b 1=w ∧ v b 2=w^2 then Equiv.refl _ else Equiv.swap 1 2
  have phase (b : Fin 2) (i : Fin 3) : v b (τ b i) = ![1,w,w^2] i := by
    obtain ⟨h₀,hs⟩ := orient b
    by_cases h : v b 1=w ∧ v b 2=w^2
    · fin_cases i <;> simp [τ,h,h₀,h.1,h.2,Matrix.cons_val]
    · obtain ⟨h₁,h₂⟩ := hs.resolve_left h
      have swap : τ b = Equiv.swap 1 2 := if_neg h
      rw [swap]
      fin_cases i <;> simp [h₀,h₁,h₂,Equiv.swap_apply_def,Matrix.cons_val]
  let split : Fin 2 × Fin 3 ≃ Fin 6 := finProdFinEquiv
  let p := (split.symm.trans (Equiv.prodCongrRight τ)).trans e
  let R := reindex p
  let M := L.map R.toLinearMap
  refine ⟨M,(R.submoduleMap L).finrank_eq,?_,?_,?_⟩
  · rintro _ ⟨m,hm,rfl⟩
    exact reLevel p m (lev m hm)
  · obtain ⟨x,hx,hxv⟩ := amp (fun b => if b=0 then 1 else 0)
    refine ⟨profile x,hx,?_⟩
    funext ij
    rcases ij with ⟨r,j⟩
    let bi := split.symm j
    have hcol : x (p j) = (if bi.1=0 then 1 else 0)*(![1,w,w^2] bi.2) := by
      exact (hxv bi.1 (τ bi.1 bi.2)).trans (by rw [phase])
    change (if r=3 then (-1:ℂ) else 3)*x (p j)=atom w 15 r.val j.val
    rw [hcol]
    fin_cases r <;> fin_cases j <;>
      norm_num [bi,split,finProdFinEquiv,Fin.divNat,Fin.modNat,atom,row,col,val,wave,c,Matrix.cons_val] <;>
      first | linear_combination hw | linear_combination 3*hw | linear_combination -hw | ring
  · obtain ⟨x,hx,hxv⟩ := amp (fun b => if b=1 then 1 else 0)
    refine ⟨profile x,hx,?_⟩
    funext ij
    rcases ij with ⟨r,j⟩
    let bi := split.symm j
    have hcol : x (p j) = (if bi.1=1 then 1 else 0)*(![1,w,w^2] bi.2) := by
      exact (hxv bi.1 (τ bi.1 bi.2)).trans (by rw [phase])
    change (if r=3 then (-1:ℂ) else 3)*x (p j)=atom w 16 r.val j.val
    rw [hcol]
    fin_cases r <;> fin_cases j <;>
      norm_num [bi,split,finProdFinEquiv,Fin.divNat,Fin.modNat,atom,row,col,val,wave,c,Matrix.cons_val] <;>
      first | linear_combination hw | linear_combination 3*hw | linear_combination -hw | ring
end PEqualNP.Gct.RankSeven
