import PEqualNP.Gct.RankSeven195
import Mathlib.LinearAlgebra.Matrix.Dual

namespace PEqualNP.Gct.PureRows
open Module FourierTable DeskPolar PermanentPencil
abbrev Row := Fin 6 → ℂ
abbrev Fn := Nat → ℂ

noncomputable def inj : List Fn → List Nat → ℂ
  | [], _ => 1
  | g :: gs, l => total l (fun j => g j * inj gs (l.erase j))

private lemma totalCong {l : List Nat} {a b : Fn} (h : ∀ j ∈ l, a j=b j) :
    total l a=total l b := congrArg List.sum (List.map_congr_left h)

private lemma eraseSum (l : List Nat) (f : Fn) {j : Nat} (h : j ∈ l) :
    total (l.erase j) f=total l f-f j := by
  have e := ((List.perm_cons_erase h).map f).sum_eq
  simp [total] at *
  linear_combination -e

private lemma tsumAdd (l : List Nat) (f g : Fn) :
    total l (fun j => f j + g j)=total l f+total l g := by
  induction l with
  | nil => simp [total]
  | cons j l ih =>
    change (f j+g j)+total l _=(f j+total l f)+(g j+total l g)
    rw [ih]; ring

private lemma tsumSub (l : List Nat) (f g : Fn) :
    total l (fun j => f j - g j)=total l f-total l g := by
  induction l with
  | nil => simp [total]
  | cons j l ih =>
    change (f j-g j)+total l _=(f j+total l f)-(g j+total l g)
    rw [ih]; ring

noncomputable def tensor (u : Fn × Fn) : Mat := fun r j => u.1 r * u.2 j

theorem separate (us : List (Fn × Fn)) (rs cs : List Nat) :
    rect (us.map tensor) rs cs = inj (us.map Prod.fst) rs * inj (us.map Prod.snd) cs := by
  induction us generalizing rs cs with
  | nil => simp [rect,inj]
  | cons u us ih =>
    simp only [List.map_cons,rect,ih,inj,tensor]
    change total rs (fun r => total cs (fun j => _)) = _ * _
    trans total rs (fun r => (u.1 r * inj (us.map Prod.fst) (rs.erase r)) *
      total cs (fun j => u.2 j * inj (us.map Prod.snd) (cs.erase j)))
    · apply totalCong
      intro r _
      rw [← total_scale]; apply totalCong; intros; ring
    · rw [mul_comm,← total_scale]; apply totalCong; intros; ring

theorem formula1 (l : List Nat) (a : Fn) :
    inj [a] l = (1) * (total l (fun j => a j)) := by
  change total l (fun j => a j * inj [] (l.erase j)) = _
  trans total l (fun j => ((1) * (a j)))
  · apply totalCong
    intro j hj
    simp [inj]
  · simp only [tsumAdd,total_scale]

theorem formula2 (l : List Nat) (a b : Fn) :
    inj [a,b] l = (1 * (total l (fun j => b j))) * (total l (fun j => a j)) +
      (-1) * (total l (fun j => a j * b j)) := by
  change total l (fun j => a j * inj [b] (l.erase j)) = _
  trans total l (fun j => ((1 * (total l (fun j => b j))) * (a j)) + ((-1) * (a j * b j)))
  · apply totalCong
    intro j hj
    rw [formula1]
    simp only [eraseSum l _ hj]
    ring
  · simp only [tsumAdd,total_scale]

theorem formula3 (l : List Nat) (a b c : Fn) :
    inj [a,b,c] l = (1 * (total l (fun j => b j)) * (total l (fun j => c j))) * (total l (fun j => a j)) +
      (-1 * (total l (fun j => c j))) * (total l (fun j => a j * b j)) +
      (-1 * (total l (fun j => b j))) * (total l (fun j => a j * c j)) +
      (-1 * (total l (fun j => b j * c j))) * (total l (fun j => a j)) +
      (2) * (total l (fun j => a j * b j * c j)) := by
  change total l (fun j => a j * inj [b,c] (l.erase j)) = _
  trans total l (fun j => ((1 * (total l (fun j => b j)) * (total l (fun j => c j))) * (a j)) + ((-1 * (total l (fun j => c j))) * (a j * b j)) + ((-1 * (total l (fun j => b j))) * (a j * c j)) + ((-1 * (total l (fun j => b j * c j))) * (a j)) + ((2) * (a j * b j * c j)))
  · apply totalCong
    intro j hj
    rw [formula2]
    simp only [eraseSum l _ hj]
    ring
  · simp only [tsumAdd,total_scale]

theorem formula4 (l : List Nat) (a b c d : Fn) :
    inj [a,b,c,d] l = (1 * (total l (fun j => b j)) * (total l (fun j => c j)) * (total l (fun j => d j))) * (total l (fun j => a j)) +
      (-1 * (total l (fun j => c j)) * (total l (fun j => d j))) * (total l (fun j => a j * b j)) +
      (-1 * (total l (fun j => b j)) * (total l (fun j => d j))) * (total l (fun j => a j * c j)) +
      (-1 * (total l (fun j => b j)) * (total l (fun j => c j))) * (total l (fun j => a j * d j)) +
      (-1 * (total l (fun j => b j * c j)) * (total l (fun j => d j))) * (total l (fun j => a j)) +
      (2 * (total l (fun j => d j))) * (total l (fun j => a j * b j * c j)) +
      (1 * (total l (fun j => b j * c j))) * (total l (fun j => a j * d j)) +
      (-1 * (total l (fun j => c j)) * (total l (fun j => b j * d j))) * (total l (fun j => a j)) +
      (1 * (total l (fun j => b j * d j))) * (total l (fun j => a j * c j)) +
      (2 * (total l (fun j => c j))) * (total l (fun j => a j * b j * d j)) +
      (-1 * (total l (fun j => b j)) * (total l (fun j => c j * d j))) * (total l (fun j => a j)) +
      (1 * (total l (fun j => c j * d j))) * (total l (fun j => a j * b j)) +
      (2 * (total l (fun j => b j))) * (total l (fun j => a j * c j * d j)) +
      (2 * (total l (fun j => b j * c j * d j))) * (total l (fun j => a j)) +
      (-6) * (total l (fun j => a j * b j * c j * d j)) := by
  change total l (fun j => a j * inj [b,c,d] (l.erase j)) = _
  trans total l (fun j => ((1 * (total l (fun j => b j)) * (total l (fun j => c j)) * (total l (fun j => d j))) * (a j)) + ((-1 * (total l (fun j => c j)) * (total l (fun j => d j))) * (a j * b j)) + ((-1 * (total l (fun j => b j)) * (total l (fun j => d j))) * (a j * c j)) + ((-1 * (total l (fun j => b j)) * (total l (fun j => c j))) * (a j * d j)) + ((-1 * (total l (fun j => b j * c j)) * (total l (fun j => d j))) * (a j)) + ((2 * (total l (fun j => d j))) * (a j * b j * c j)) + ((1 * (total l (fun j => b j * c j))) * (a j * d j)) + ((-1 * (total l (fun j => c j)) * (total l (fun j => b j * d j))) * (a j)) + ((1 * (total l (fun j => b j * d j))) * (a j * c j)) + ((2 * (total l (fun j => c j))) * (a j * b j * d j)) + ((-1 * (total l (fun j => b j)) * (total l (fun j => c j * d j))) * (a j)) + ((1 * (total l (fun j => c j * d j))) * (a j * b j)) + ((2 * (total l (fun j => b j))) * (a j * c j * d j)) + ((2 * (total l (fun j => b j * c j * d j))) * (a j)) + ((-6) * (a j * b j * c j * d j)))
  · apply totalCong
    intro j hj
    rw [formula3]
    simp only [eraseSum l _ hj]
    ring
  · simp only [tsumAdd,total_scale]

end PEqualNP.Gct.PureRows
