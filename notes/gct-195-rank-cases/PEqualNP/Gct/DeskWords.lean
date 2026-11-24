import PEqualNP.Gct.SaturatedMatrixBound
import PEqualNP.Gct.PermanentPencil
import Mathlib.Data.List.FinRange

namespace PEqualNP.Gct.DeskPolar
open PEqualNP.Gct.FourierTable PEqualNP.Gct.PermanentPencil
abbrev Word := List (Nat × Nat)
def words : Nat → List Nat → List Nat → List Word
  | 0, _, _ => [[]]
  | n+1, rs, cs => rs.flatMap fun r => cs.flatMap fun j =>
      (words n (rs.erase r) (cs.erase j)).map ((r,j) :: ·)
noncomputable def weight : List Mat → Word → ℂ
  | m::ms, (r,j)::ij => m r j*weight ms ij
  | _, _ => 1
noncomputable def total {α : Type*} (l : List α) (f : α → ℂ) := (l.map f).sum
lemma total_flat {α β : Type*} (xs : List α) (g : α → List β) (f : β → ℂ) :
    total (xs.flatMap g) f = total xs (fun a => total (g a) f) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simpa [total,List.flatMap_cons,List.sum_append] using congrArg (total (g a) f + ·) ih
lemma total_scale {α : Type*} (xs : List α) (c : ℂ) (f : α → ℂ) :
    total xs (fun a => c*f a)=c*total xs f := by
  induction xs with
  | nil => simp [total]
  | cons a xs ih => simpa [total,mul_add] using congrArg (c*f a + ·) ih
lemma total_consmap {α β : Type*} (xs : List α) (g : α → β) (f : β → ℂ) :
    total (xs.map g) f = total xs (fun a => f (g a)) := by simp [total,List.map_map,Function.comp_def]
lemma rect_words (ms : List Mat) (rs cs : List Nat) :
    rect ms rs cs = total (words ms.length rs cs) (weight ms) := by
  induction ms generalizing rs cs with
  | nil => simp [rect,words,total,weight]
  | cons m ms ih =>
    simp only [rect,List.length_cons,words,total_flat,total_consmap,weight,ih,total_scale]
    rfl

def each (n : Nat) {α : Type*} (f : Fin n → List α) := (List.finRange n).flatMap f
def desk : Nat → List Word
  | 1 => each 4 fun i => each 6 fun j => [[(i.val,j.val)]]
  | 2 => each 6 fun j => each 6 fun l => if j=l then [] else
      each 4 fun a => each 4 fun b => if a<b then [[(a.val,j.val),(b.val,l.val)]] else []
  | 3 => each 6 fun j => each 6 fun l => each 6 fun n => if j=l ∨ j=n ∨ l=n then [] else
      each 4 fun a => each 4 fun b => each 4 fun c => if a<b ∧ b<c then
        [[(a.val,j.val),(b.val,l.val),(c.val,n.val)]] else []
  | 4 => each 6 fun j => each 6 fun l => each 6 fun n => each 6 fun o =>
      if j=l ∨ j=n ∨ j=o ∨ l=n ∨ l=o ∨ n=o then [] else
      [[(0,j.val),(1,l.val),(2,n.val),(3,o.val)]]
  | _ => []

lemma overFin {n : Nat} (f : Fin n → ℂ) : total (List.finRange n) f = ∑ i, f i := by
  induction n with
  | zero => simp [total]
  | succ n ih =>
    rw [List.finRange_succ,Fin.sum_univ_succ]
    simp [total,List.map_map,Function.comp_def] at ih ⊢
    exact ih _
lemma total_each {α : Type*} (n : Nat) (g : Fin n → List α) (f : α → ℂ) :
    total (each n g) f = ∑ i, total (g i) f := by rw [each,total_flat,overFin]
def restrict (m : Mat) : Pos → ℂ := fun ij => m ij.1.val ij.2.val
lemma desk_diag (m : Mat) (hm : level (restrict m)) :
    ∀ k ∈ ([1,2,3,4] : List Nat), total (desk k) (weight (List.replicate k m))=0 := by
  have e (p : Prop) [Decidable p] (u v : List Word) (f : Word → ℂ) :
        total (if p then u else v) f = if p then total u f else total v f := by split <;> rfl
  rcases hm with ⟨h1,h2,h3,h4⟩
  intro k hk
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl
  all_goals simp only [desk,total_each,e]
  all_goals simp only [List.replicate_succ,List.replicate_zero,weight,
    total,List.map_nil,List.map_cons,List.sum_cons,List.sum_nil,mul_one,add_zero]
  · exact h1
  · exact h2
  · simpa [third,restrict,mul_assoc] using h3
  · simpa [fourth,restrict,mul_assoc] using h4

end PEqualNP.Gct.DeskPolar
