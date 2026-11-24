import PEqualNP.Gct.ChartTable
import PEqualNP.Gct.DeskWords
namespace PEqualNP.Gct.FourierTable
open Finset
noncomputable def extAtom (w : ℂ) (i : Nat) : Mat := fun r j => val w (extRow i r)*val w (extCol i j)
noncomputable def chart (w : ℂ) (z : Fin 24 → ℂ) : Mat := fun r j => ∑ i, z i*extAtom w i r j
private lemma val_plus (w : ℂ) (a b : E) : val w (plus a b)=val w a+val w b := by
  simp [plus,val]; ring
private lemma val_times {w : ℂ} (hw : w^2+w+1=0) (a b : E) :
    val w (times a b)=val w a*val w b := by
  push_cast [times,val]
  linear_combination -(a.2:ℂ)*(b.2:ℂ)*hw
private lemma val_fold (w : ℂ) (xs : List E) (t : E) :
    val w (xs.foldl plus t)= val w t+(xs.map (val w)).sum := by
  induction xs generalizing t with
  | nil => simp
  | cons a xs ih => simp [ih,val_plus,add_assoc]
private lemma map_scale {α : Type*} (l : List α) (a : ℂ) (f : α → ℂ) :
    (l.map (fun i => a*f i)).sum = a*(l.map f).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih,mul_add]
private lemma inj_cons {w : ℂ} (hw : w^2+w+1=0) (f : Nat → Nat → E) (i : Nat) (is l : List Nat) :
    val w (injectSum f (i::is) l)=(l.map (fun j => val w (f i j)*val w (injectSum f is (l.erase j)))).sum := by
  simp [injectSum,val_fold,List.map_map,Function.comp_def,val_times hw]
private lemma extSeparable {w : ℂ} (hw : w^2+w+1=0) (is rs cs : List Nat) :
    rect (is.map (extAtom w)) rs cs = val w (injectSum extRow is rs) * val w (injectSum extCol is cs) := by
  induction is generalizing rs cs with
  | nil => simp [rect,injectSum]
  | cons i is ih =>
    simp only [List.map_cons,rect,ih,extAtom,inj_cons hw]
    have h (r : Nat) : (cs.map (fun j => val w (extRow i r) * val w (extCol i j) *
        (val w (injectSum extRow is (rs.erase r)) * val w (injectSum extCol is (cs.erase j))))).sum =
        (val w (extRow i r) * val w (injectSum extRow is (rs.erase r))) *
        (cs.map (fun j => val w (extCol i j)*val w (injectSum extCol is (cs.erase j)))).sum := by
      rw [← map_scale]
      congr 1
      apply List.map_congr_left
      intro j _
      ring
    simp_rw [h]
    rw [mul_comm,← map_scale]
    congr 1
    apply List.map_congr_left
    intro r _
    ring

theorem extAtomContraction {w : ℂ} (hw : w^2+w+1=0) (is : List Nat) :
    rect (is.map (extAtom w)) (List.range 4) (List.range 6)= val w (grad is) := by
  rw [extSeparable hw,grad,val_times hw]


private lemma rangeFin (f : Nat → ℂ) : ((List.range 24).map f).sum = ∑ i : Fin 24, f i.val := by
  have eqn (n : Nat) : ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j := by
    induction n with
    | zero => simp
    | succ n ih => simp [List.range_succ,List.sum_append,Finset.sum_range_succ,ih]
  rw [eqn,Fin.sum_univ_eq_sum_range]
private lemma inverse_entry (i j : Fin 24) : entrySum i j=c (if i.val=j.val then den else 0) := by
  have h : ((List.range 24).all (fun k => entrySum i k == c (if i.val=k then den else 0)))=true := by
    fin_cases i
    · exact inverseRow0
    · exact inverseRow1
    · exact inverseRow2
    · exact inverseRow3
    · exact inverseRow4
    · exact inverseRow5
    · exact inverseRow6
    · exact inverseRow7
    · exact inverseRow8
    · exact inverseRow9
    · exact inverseRow10
    · exact inverseRow11
    · exact inverseRow12
    · exact inverseRow13
    · exact inverseRow14
    · exact inverseRow15
    · exact inverseRow16
    · exact inverseRow17
    · exact inverseRow18
    · exact inverseRow19
    · exact inverseRow20
    · exact inverseRow21
    · exact inverseRow22
    · exact inverseRow23
  exact eq_of_beq (List.all_eq_true.mp h j.val (List.mem_range.mpr j.isLt))
private lemma sum_inv {w : ℂ} (hw : w^2+w+1=0) (i j : Fin 24) :
    (∑ k : Fin 24, val w (entry i k)*val w (invEntry k j))=if i=j then 108 else 0 := by
  have h := congrArg (val w) (inverse_entry i j)
  simp only [entrySum,val_fold,List.map_map,Function.comp_def,val_times hw,val_c,Int.cast_zero,zero_add] at h
  rw [rangeFin] at h
  split_ifs at h ⊢ <;> simp_all [den,Fin.ext_iff]
theorem chart_surj {w : ℂ} (hw : w^2+w+1=0) (m : PermanentPencil.Pos → ℂ) :
    ∃ z : Fin 24 → ℂ, DeskPolar.restrict (chart w z)=m := by
  let v (j : Fin 24) := m ((finProdFinEquiv : Fin 4 × Fin 6 ≃ Fin 24).symm j)
  let z (k : Fin 24) := ∑ j : Fin 24, val w (invEntry k j)*v j / 108
  have ident (i : Fin 24) : (∑ k : Fin 24, z k * val w (entry i k))=v i := by
    simp only [z,Finset.sum_mul]
    rw [Finset.sum_comm]
    calc
      _ = ∑ j : Fin 24, (∑ k : Fin 24, val w (entry i k)*val w (invEntry k j)) * (v j/108) := by
        apply Finset.sum_congr rfl; intro j _
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro k _; ring
      _ = _ := by simp [sum_inv hw,ite_mul]; ring
  refine ⟨z,?_⟩
  funext p
  obtain ⟨i,rfl⟩ := (finProdFinEquiv : Fin 4 × Fin 6 ≃ Fin 24).symm.surjective p
  simpa [DeskPolar.restrict,chart,extAtom,v,entry,val_times hw,finProdFinEquiv] using ident i

private lemma interchange24 {α : Type*} (l : List α) (f : α → Fin 24 → ℂ) :
    (l.map (fun a => ∑ i, f a i)).sum = ∑ i, (l.map (fun a => f a i)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih,Finset.sum_add_distrib]
theorem firstSlot24 {w : ℂ} (hw : w^2+w+1=0) (z : Fin 24 → ℂ) (seeds : List Nat) :
    mixed (chart w z :: seeds.map (extAtom w)) = ∑ i : Fin 24, z i*val w (grad (i.val::seeds)) := by
  unfold mixed
  calc
    _ = ∑ i : Fin 24, z i * rect (extAtom w i::seeds.map (extAtom w)) (List.range 4) (List.range 6) := by
      simp only [rect,chart,Finset.sum_mul]
      simp_rw [interchange24]
      apply Finset.sum_congr rfl; intro i _
      rw [← map_scale]; congr 1; apply List.map_congr_left; intro r _
      rw [← map_scale]; congr 1; apply List.map_congr_left; intro j _; ring
    _ = _ := by
      apply Finset.sum_congr rfl; intro i _
      rw [← extAtomContraction hw (i.val::seeds)]; rfl
end PEqualNP.Gct.FourierTable
