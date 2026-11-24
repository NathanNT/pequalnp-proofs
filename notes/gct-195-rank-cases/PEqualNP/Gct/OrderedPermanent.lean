import PEqualNP.Gct.SaturatedTensorBound

namespace PEqualNP.Gct.FourierTable
open Finset

abbrev Mat := Nat → Nat → ℂ
noncomputable def atom (w : ℂ) (i : Nat) : Mat := fun r j => val w (row i r)*val w (col i j)
noncomputable def combo (w : ℂ) (x : Fin 15 → ℂ) : Mat :=
  fun r j => ∑ i : Fin 15, x i * atom w i r j

/-- The ordered mixed rectangular permanent. Each chosen row and column is removed. -/
noncomputable def rect : List Mat → List Nat → List Nat → ℂ
  | [], _, _ => 1
  | m::ms, rs, cs => (rs.map (fun r => (cs.map (fun j => m r j *
      rect ms (rs.erase r) (cs.erase j))).sum)).sum

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
private lemma separable {w : ℂ} (hw : w^2+w+1=0) (is rs cs : List Nat) :
    rect (is.map (atom w)) rs cs = val w (injectSum row is rs) * val w (injectSum col is cs) := by
  induction is generalizing rs cs with
  | nil => simp [rect,injectSum]
  | cons i is ih =>
    simp only [List.map_cons,rect,ih,atom,inj_cons hw]
    have h (r : Nat) : (cs.map (fun j => val w (row i r) * val w (col i j) *
        (val w (injectSum row is (rs.erase r)) * val w (injectSum col is (cs.erase j))))).sum =
        (val w (row i r) * val w (injectSum row is (rs.erase r))) *
        (cs.map (fun j => val w (col i j)*val w (injectSum col is (cs.erase j)))).sum := by
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

theorem atomContraction {w : ℂ} (hw : w^2+w+1=0) (is : List Nat) :
    rect (is.map (atom w)) (List.range 4) (List.range 6)= val w (contraction is) := by
  rw [separable hw,contraction,val_times hw]

private lemma interchange {α : Type*} (l : List α) (f : α → Fin 15 → ℂ) :
    (l.map (fun a => ∑ i, f a i)).sum = ∑ i, (l.map (fun a => f a i)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih,Finset.sum_add_distrib]

theorem expandSlot (w : ℂ) (x : Fin 15 → ℂ) (before after : List Mat) (rs cs : List Nat) :
    rect (before ++ (combo w x :: after)) rs cs =
      integrate x (fun i => rect (before ++ (atom w i :: after)) rs cs) := by
  induction before generalizing rs cs with
  | nil =>
    simp only [List.nil_append,rect,combo,integrate,Finset.sum_mul]
    simp_rw [interchange]
    apply Finset.sum_congr rfl
    intro i _
    rw [← map_scale]
    congr 1
    apply List.map_congr_left
    intro r _
    rw [← map_scale]
    congr 1
    apply List.map_congr_left
    intro j _
    ring
  | cons b bs ih =>
    simp only [List.cons_append,rect,ih,integrate,Finset.mul_sum]
    simp_rw [interchange]
    apply Finset.sum_congr rfl
    intro i _
    rw [← map_scale]
    congr 1
    apply List.map_congr_left
    intro r _
    rw [← map_scale]
    congr 1
    apply List.map_congr_left
    intro j _
    ring
end PEqualNP.Gct.FourierTable
