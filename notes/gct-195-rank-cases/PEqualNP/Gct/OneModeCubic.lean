import PEqualNP.Gct.DeskOrder
import PEqualNP.Gct.CubicSix
namespace PEqualNP.Gct.OneMode
open Module FourierTable DeskPolar PermanentPencil
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


def phase (w : ℂ) : Fin 4 → ℂ := ![1,w,w^2,0]
def block (w : ℂ) (y z : Fin 6 → ℂ) (p : Pos) :=
  if p.1=3 then y p.2 else phase w p.1*z p.2
theorem cubicConstraint {w : ℂ} (hw : w^2+w+1=0) (y z : Fin 6 → ℂ)
    (h : level (block w y z)) : CubicSix.ordered3 z=0 := by
  have rows (j l n : Fin 6) : (∑ a : Fin 4, ∑ b : Fin 4, ∑ c' : Fin 4,
      if a<b ∧ b<c' then block w y z (a,j)*block w y z (b,l)*block w y z (c',n) else 0)
      = z j*z l*z n := by
    norm_num [Fin.sum_univ_four,block,phase,Matrix.cons_val]
    linear_combination ((w-1)*z j*z l*z n + w*z j*z l*y n)*hw
  have hc := h.2.2.1
  simpa only [third,rows,CubicSix.ordered3] using hc

def lastRow (y : Fin 6 → ℂ) : Mat := fun r j => if r=3 then y (Fin.ofNat 6 j) else 0
def residual (k j : Nat) := times (injectSum row (List.replicate k 15) [0,1,2])
    (injectSum col (List.replicate k 15) ((List.range 6).erase j))
noncomputable def mixedLast (w : ℂ) (y : Fin 6 → ℂ) (k : Nat) :=
  mixed (lastRow y::List.replicate k (atom w 15))
private lemma expansion {w : ℂ} (hw : w^2+w+1=0) (y : Fin 6 → ℂ) (k : Nat) :
    mixedLast w y k = ∑ j : Fin 6, y j*val w (residual k j.val) := by
  let cs := List.range 6
  have term (r : Nat) : (cs.map (fun j => lastRow y r j*
        rect (List.replicate k (atom w 15)) ((List.range 4).erase r) (cs.erase j))).sum =
      if r=3 then (cs.map (fun j => y (Fin.ofNat 6 j)*val w (residual k j))).sum else 0 := by
    by_cases hr : r=3
    · subst r
      simp only [lastRow,if_true]
      congr 1; apply List.map_congr_left; intro j _
      rw [← List.map_replicate (f:=atom w) (a:=15),separable hw,residual,val_times hw]; rfl
    · simp [lastRow,hr]
  unfold mixedLast mixed
  simp only [rect]
  change ((List.range 4).map (fun r => (cs.map (fun j => lastRow y r j *
    rect (List.replicate k (atom w 15)) ((List.range 4).erase r) (cs.erase j))).sum)).sum=_
  simp_rw [term]
  rw [show List.range 4=[0,1,2,3] from rfl,show cs=[0,1,2,3,4,5] from rfl]
  simp [Fin.sum_univ_succ] <;> first | rfl | exact Or.inl rfl

def residualTable (k : Nat) : List E := match k with
  | 0 => [c 1,c 1,c 1,c 1,c 1,c 1]
  | 1 => [c (-9),(0,-9),(9,9),c 0,c 0,c 0]
  | 2 => [c 108,(-108,-108),(0,108),c 0,c 0,c 0]
  | _ => [c 0,c 0,c 0,c 972,c 972,c 972]
private lemma residual_ok (k : Fin 4) (j : Fin 6) :
    residual k.val j.val = (residualTable k.val)[j.val]! := by
  have tab : (List.range 4).all (fun i => (List.range 6).all
    (fun t => residual i t == (residualTable i)[t]!)) = true := by decide
  exact eq_of_beq (List.all_eq_true.mp (List.all_eq_true.mp tab k.val (List.mem_range.mpr k.isLt)) j.val (List.mem_range.mpr j.isLt))
theorem lastConstraint {w : ℂ} (hw : w^2+w+1=0) (y : Fin 6 → ℂ)
    (test : ∀ k : Fin 4, mixedLast w y k.val=0) :
    y 0=0 ∧ y 1=0 ∧ y 2=0 ∧ y 3+y 4+y 5=0 := by
  have h (k : Fin 4) := (expansion hw y k.val).symm.trans (test k)
  simp only [residual_ok] at h
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  norm_num [Fin.sum_univ_succ,residualTable,val,c] at h0 h1 h2 h3
  have surd : 1+2*w≠0 := by
    intro eq; have he : w= -1/2 := by linear_combination eq/2
    rw [he] at hw; norm_num at hw
  have p : (1+2*w)*(y 1-y 2)=0 := by linear_combination -h1/9-h2/108
  have eq12 := sub_eq_zero.mp ((mul_eq_zero.mp p).resolve_left surd)
  rw [eq12] at h1 h0
  have e0 : y 0=y 2 := by linear_combination -h1/9
  have e3 : y 3+y 4+y 5=0 := by linear_combination h3/972
  rw [e0] at h0
  have e2 : y 2=0 := by linear_combination (h0-e3)/3
  exact ⟨e0.trans e2,eq12.trans e2,e2,e3⟩
end PEqualNP.Gct.OneMode

