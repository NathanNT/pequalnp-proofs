import PEqualNP.Gct.DeskWords
set_option maxRecDepth 100000
namespace PEqualNP.Gct.DeskPolar
open PEqualNP.Gct.FourierTable PEqualNP.Gct.PermanentPencil
def permutationsOf : Word → List Word
  | [a] => [[a]] 
  | [a,b] => [[a,b],[b,a]] 
  | [a,b,c] => [[a,b,c],[a,c,b],[b,a,c],[b,c,a],[c,a,b],[c,b,a]] 
  | [a,b,c,d] => [[a,b,c,d],[a,b,d,c],[a,c,b,d],[a,c,d,b],[a,d,b,c],[a,d,c,b],[b,a,c,d],[b,a,d,c],[b,c,a,d],[b,c,d,a],[b,d,a,c],[b,d,c,a],[c,a,b,d],[c,a,d,b],[c,b,a,d],[c,b,d,a],[c,d,a,b],[c,d,b,a],[d,a,b,c],[d,a,c,b],[d,b,a,c],[d,b,c,a],[d,c,a,b],[d,c,b,a]] 
  | _ => []

lemma total_congr {α : Type*} {f g : α → ℂ} (xs : List α) (h : ∀ i ∈ xs, f i=g i) :
    total xs f=total xs g := congrArg List.sum (List.map_congr_left h)
lemma total_add {α : Type*} (xs : List α) (f g : α → ℂ) :
    total xs (fun i => f i+g i)=total xs f+total xs g := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih => simp only [total,List.map_cons,List.sum_cons] at ih ⊢; rw [ih]; ring
lemma total_sub {α : Type*} (xs : List α) (f g : α → ℂ) :
    total xs (fun i => f i-g i)=total xs f-total xs g := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih => simp only [total,List.map_cons,List.sum_cons] at ih ⊢; rw [ih]; ring

private lemma polar1 (x : Mat) (ij : Word) (hl : ij.length=1) :
    total (permutationsOf ij) (weight [x]) = weight (List.replicate 1 (x)) ij := by
  rcases ij with _|⟨⟨r0,c0⟩,ij⟩; · simp at hl
  cases ij with
  | cons _ _ => simp at hl
  | nil => simp [permutationsOf,total,weight,Pi.add_apply] <;> ring
theorem conditional1 (perm1 : (words 1 (List.range 4) (List.range 6)).Perm ((desk 1).flatMap permutationsOf)) (S : Submodule ℂ Mat) (lev : ∀ m∈S, level (restrict m)) {x : Mat} (hx : x∈S) :
    mixed [x]=0 := by
  unfold mixed
  rw [rect_words]
  change total (words 1 (List.range 4) (List.range 6)) (weight [x])=0
  have hp := (perm1.map (weight [x])).sum_eq
  change total _ _ = total _ _ at hp
  rw [hp,total_flat]
  have eqn := total_congr (desk 1) (fun ij hij => polar1 x ij
    (eq_of_beq (List.all_eq_true.mp (show ((desk 1).all (fun ij => ij.length == 1))=true from by decide) ij hij)))
  rw [eqn]
  have e0 := desk_diag (x) (lev _ hx) 1 (by decide)
  simp only [e0]
private lemma polar2 (x y : Mat) (ij : Word) (hl : ij.length=2) :
    total (permutationsOf ij) (weight [x,y]) = weight (List.replicate 2 (x+y)) ij - weight (List.replicate 2 (y)) ij - weight (List.replicate 2 (x)) ij := by
  rcases ij with _|⟨⟨r0,c0⟩,ij⟩; · simp at hl
  rcases ij with _|⟨⟨r1,c1⟩,ij⟩; · simp at hl
  cases ij with
  | cons _ _ => simp at hl
  | nil => simp [permutationsOf,total,weight,Pi.add_apply] <;> ring
theorem conditional2 (perm2 : (words 2 (List.range 4) (List.range 6)).Perm ((desk 2).flatMap permutationsOf)) (S : Submodule ℂ Mat) (lev : ∀ m∈S, level (restrict m)) {x y : Mat} (hx : x∈S) (hy : y∈S) :
    mixed [x,y]=0 := by
  unfold mixed
  rw [rect_words]
  change total (words 2 (List.range 4) (List.range 6)) (weight [x,y])=0
  have hp := (perm2.map (weight [x,y])).sum_eq
  change total _ _ = total _ _ at hp
  rw [hp,total_flat]
  have eqn := total_congr (desk 2) (fun ij hij => polar2 x y ij
    (eq_of_beq (List.all_eq_true.mp (show ((desk 2).all (fun ij => ij.length == 2))=true from by decide) ij hij)))
  rw [eqn]
  simp only [total_add,total_sub]
  have e0 := desk_diag (x+y) (lev _ (S.add_mem hx hy)) 2 (by decide)
  have e1 := desk_diag (y) (lev _ hy) 2 (by decide)
  have e2 := desk_diag (x) (lev _ hx) 2 (by decide)
  simp only [e0,e1,e2,add_zero,sub_zero]
private lemma polar3 (x y z : Mat) (ij : Word) (hl : ij.length=3) :
    total (permutationsOf ij) (weight [x,y,z]) = weight (List.replicate 3 (x+y+z)) ij - weight (List.replicate 3 (y+z)) ij - weight (List.replicate 3 (x+z)) ij - weight (List.replicate 3 (x+y)) ij + weight (List.replicate 3 (z)) ij + weight (List.replicate 3 (y)) ij + weight (List.replicate 3 (x)) ij := by
  rcases ij with _|⟨⟨r0,c0⟩,ij⟩; · simp at hl
  rcases ij with _|⟨⟨r1,c1⟩,ij⟩; · simp at hl
  rcases ij with _|⟨⟨r2,c2⟩,ij⟩; · simp at hl
  cases ij with
  | cons _ _ => simp at hl
  | nil => simp [permutationsOf,total,weight,Pi.add_apply] <;> ring
theorem conditional3 (perm3 : (words 3 (List.range 4) (List.range 6)).Perm ((desk 3).flatMap permutationsOf)) (S : Submodule ℂ Mat) (lev : ∀ m∈S, level (restrict m)) {x y z : Mat} (hx : x∈S) (hy : y∈S) (hz : z∈S) :
    mixed [x,y,z]=0 := by
  unfold mixed
  rw [rect_words]
  change total (words 3 (List.range 4) (List.range 6)) (weight [x,y,z])=0
  have hp := (perm3.map (weight [x,y,z])).sum_eq
  change total _ _ = total _ _ at hp
  rw [hp,total_flat]
  have eqn := total_congr (desk 3) (fun ij hij => polar3 x y z ij
    (eq_of_beq (List.all_eq_true.mp (show ((desk 3).all (fun ij => ij.length == 3))=true from by decide) ij hij)))
  rw [eqn]
  simp only [total_add,total_sub]
  have e0 := desk_diag (x+y+z) (lev _ (S.add_mem (S.add_mem hx hy) hz)) 3 (by decide)
  have e1 := desk_diag (y+z) (lev _ (S.add_mem hy hz)) 3 (by decide)
  have e2 := desk_diag (x+z) (lev _ (S.add_mem hx hz)) 3 (by decide)
  have e3 := desk_diag (x+y) (lev _ (S.add_mem hx hy)) 3 (by decide)
  have e4 := desk_diag (z) (lev _ hz) 3 (by decide)
  have e5 := desk_diag (y) (lev _ hy) 3 (by decide)
  have e6 := desk_diag (x) (lev _ hx) 3 (by decide)
  simp only [e0,e1,e2,e3,e4,e5,e6,add_zero,sub_zero]
private lemma polar4 (x y z u : Mat) (ij : Word) (hl : ij.length=4) :
    total (permutationsOf ij) (weight [x,y,z,u]) = weight (List.replicate 4 (x+y+z+u)) ij - weight (List.replicate 4 (y+z+u)) ij - weight (List.replicate 4 (x+z+u)) ij - weight (List.replicate 4 (x+y+u)) ij - weight (List.replicate 4 (x+y+z)) ij + weight (List.replicate 4 (z+u)) ij + weight (List.replicate 4 (y+u)) ij + weight (List.replicate 4 (x+u)) ij + weight (List.replicate 4 (y+z)) ij + weight (List.replicate 4 (x+z)) ij + weight (List.replicate 4 (x+y)) ij - weight (List.replicate 4 (u)) ij - weight (List.replicate 4 (z)) ij - weight (List.replicate 4 (y)) ij - weight (List.replicate 4 (x)) ij := by
  rcases ij with _|⟨⟨r0,c0⟩,ij⟩; · simp at hl
  rcases ij with _|⟨⟨r1,c1⟩,ij⟩; · simp at hl
  rcases ij with _|⟨⟨r2,c2⟩,ij⟩; · simp at hl
  rcases ij with _|⟨⟨r3,c3⟩,ij⟩; · simp at hl
  cases ij with
  | cons _ _ => simp at hl
  | nil => simp [permutationsOf,total,weight,Pi.add_apply] <;> ring
theorem conditional4 (perm4 : (words 4 (List.range 4) (List.range 6)).Perm ((desk 4).flatMap permutationsOf)) (S : Submodule ℂ Mat) (lev : ∀ m∈S, level (restrict m)) {x y z u : Mat} (hx : x∈S) (hy : y∈S) (hz : z∈S) (hu : u∈S) :
    mixed [x,y,z,u]=0 := by
  unfold mixed
  rw [rect_words]
  change total (words 4 (List.range 4) (List.range 6)) (weight [x,y,z,u])=0
  have hp := (perm4.map (weight [x,y,z,u])).sum_eq
  change total _ _ = total _ _ at hp
  rw [hp,total_flat]
  have eqn := total_congr (desk 4) (fun ij hij => polar4 x y z u ij
    (eq_of_beq (List.all_eq_true.mp (show ((desk 4).all (fun ij => ij.length == 4))=true from by decide) ij hij)))
  rw [eqn]
  simp only [total_add,total_sub]
  have e0 := desk_diag (x+y+z+u) (lev _ (S.add_mem (S.add_mem (S.add_mem hx hy) hz) hu)) 4 (by decide)
  have e1 := desk_diag (y+z+u) (lev _ (S.add_mem (S.add_mem hy hz) hu)) 4 (by decide)
  have e2 := desk_diag (x+z+u) (lev _ (S.add_mem (S.add_mem hx hz) hu)) 4 (by decide)
  have e3 := desk_diag (x+y+u) (lev _ (S.add_mem (S.add_mem hx hy) hu)) 4 (by decide)
  have e4 := desk_diag (x+y+z) (lev _ (S.add_mem (S.add_mem hx hy) hz)) 4 (by decide)
  have e5 := desk_diag (z+u) (lev _ (S.add_mem hz hu)) 4 (by decide)
  have e6 := desk_diag (y+u) (lev _ (S.add_mem hy hu)) 4 (by decide)
  have e7 := desk_diag (x+u) (lev _ (S.add_mem hx hu)) 4 (by decide)
  have e8 := desk_diag (y+z) (lev _ (S.add_mem hy hz)) 4 (by decide)
  have e9 := desk_diag (x+z) (lev _ (S.add_mem hx hz)) 4 (by decide)
  have e10 := desk_diag (x+y) (lev _ (S.add_mem hx hy)) 4 (by decide)
  have e11 := desk_diag (u) (lev _ hu) 4 (by decide)
  have e12 := desk_diag (z) (lev _ hz) 4 (by decide)
  have e13 := desk_diag (y) (lev _ hy) 4 (by decide)
  have e14 := desk_diag (x) (lev _ hx) 4 (by decide)
  simp only [e0,e1,e2,e3,e4,e5,e6,e7,e8,e9,e10,e11,e12,e13,e14,add_zero,sub_zero]
end PEqualNP.Gct.DeskPolar
