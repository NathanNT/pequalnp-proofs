import Mathlib
import PEqualNP.Research.SparseExtension

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

namespace PEqualNP.Research.SparsePairBound
open PEqualNP.Research.SparseCoexistence
open PEqualNP.Research.KleinPermanent (base perm4 coeffs top_zero)
abbrev V := Fin 13 → ℂ

noncomputable def fixed (x y z : ℂ) : M := Matrix.of ![
    ![((44 * x) + (44 * y)),((-59 * x) + (-44 * y) + (-33 * z)),(44 * z),(44 * z)],
    ![((-59 * x) + (-44 * y) + (-33 * z)),((44 * x) + (44 * y)),(44 * z),(44 * z)],
    ![((-11 * z) + (-5 * x)),((-11 * z) + (-5 * x)),((-44 * y) + (44 * x)),((-59 * x) + (-33 * z) + (44 * y))],
    ![((-11 * z) + (-5 * x)),((-11 * z) + (-5 * x)),((-59 * x) + (-33 * z) + (44 * y)),((-44 * y) + (44 * x))]]

noncomputable def slice (x y z r f : ℂ) : M := fixed x y z + r • (Matrix.of ![
    ![493,(-468 + (-155 * Complex.I)),0,0],
    ![(468 + (155 * Complex.I)),-493,0,0],
    ![0,0,493,(468 + (155 * Complex.I))],
    ![0,0,(-468 + (-155 * Complex.I)),-493]]) + f • (Matrix.of ![
    ![0,0,37,-37],
    ![0,0,-37,37],
    ![(1 + (-6 * Complex.I)),(-1 + (6 * Complex.I)),0,0],
    ![(-1 + (6 * Complex.I)),(1 + (-6 * Complex.I)),0,0]])

noncomputable def pack (v : V) : M := slice (v 0) (v 1) (v 2) (v 3) (v 4) + (Matrix.of ![
    ![(v 5),(v 6),(v 7),(v 8)],
    ![0,0,(v 9),0],
    ![(v 10),(v 11),(v 12),0],
    ![0,0,0,0]])

noncomputable def packed : V →ₗ[ℂ] M where
  toFun := pack
  map_add' v w := by ext i j; fin_cases i <;> fin_cases j <;> simp [pack,slice,fixed,Matrix.cons_val_succ] <;> ring
  map_smul' c v := by ext i j; fin_cases i <;> fin_cases j <;> simp [pack,slice,fixed,Matrix.cons_val_succ] <;> ring

noncomputable def deriv (A X : M) : ℂ :=
  ∑ p : Equiv.Perm (Fin 4), (
    X (p 0) 0*A (p 1) 1*A (p 2) 2*A (p 3) 3 +
    A (p 0) 0*X (p 1) 1*A (p 2) 2*A (p 3) 3 +
    A (p 0) 0*A (p 1) 1*X (p 2) 2*A (p 3) 3 +
    A (p 0) 0*A (p 1) 1*A (p 2) 2*X (p 3) 3)

lemma deriv_interp (A X : M) : 12*deriv A X = 8*((A+(1 : ℂ) • X).permanent-(A+(-1 : ℂ) • X).permanent)
       - ((A+(2 : ℂ) • X).permanent-(A+(-2 : ℂ) • X).permanent) := by
  simp only [deriv,Matrix.permanent,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  simp [Fin.prod_univ_four,Matrix.add_apply]
  ring

lemma deriv_zero (A X : M) (h : ∀ t : ℂ, (A+t • X).permanent=65) : deriv A X=0 := by
  have idn := deriv_interp A X
  simp only [h] at idn
  linear_combination idn/12

lemma deriv_explicit (A X : M) : deriv A X =
    X 0 0*(A 1 1*A 2 2*A 3 3 + A 1 1*A 2 3*A 3 2 + A 1 2*A 2 1*A 3 3 + A 1 2*A 2 3*A 3 1 + A 1 3*A 2 1*A 3 2 + A 1 3*A 2 2*A 3 1) +
    X 0 1*(A 1 0*A 2 2*A 3 3 + A 1 0*A 2 3*A 3 2 + A 1 2*A 2 0*A 3 3 + A 1 2*A 2 3*A 3 0 + A 1 3*A 2 0*A 3 2 + A 1 3*A 2 2*A 3 0) +
    X 0 2*(A 1 0*A 2 1*A 3 3 + A 1 0*A 2 3*A 3 1 + A 1 1*A 2 0*A 3 3 + A 1 1*A 2 3*A 3 0 + A 1 3*A 2 0*A 3 1 + A 1 3*A 2 1*A 3 0) +
    X 0 3*(A 1 0*A 2 1*A 3 2 + A 1 0*A 2 2*A 3 1 + A 1 1*A 2 0*A 3 2 + A 1 1*A 2 2*A 3 0 + A 1 2*A 2 0*A 3 1 + A 1 2*A 2 1*A 3 0) +
    X 1 0*(A 0 1*A 2 2*A 3 3 + A 0 1*A 2 3*A 3 2 + A 0 2*A 2 1*A 3 3 + A 0 2*A 2 3*A 3 1 + A 0 3*A 2 1*A 3 2 + A 0 3*A 2 2*A 3 1) +
    X 1 1*(A 0 0*A 2 2*A 3 3 + A 0 0*A 2 3*A 3 2 + A 0 2*A 2 0*A 3 3 + A 0 2*A 2 3*A 3 0 + A 0 3*A 2 0*A 3 2 + A 0 3*A 2 2*A 3 0) +
    X 1 2*(A 0 0*A 2 1*A 3 3 + A 0 0*A 2 3*A 3 1 + A 0 1*A 2 0*A 3 3 + A 0 1*A 2 3*A 3 0 + A 0 3*A 2 0*A 3 1 + A 0 3*A 2 1*A 3 0) +
    X 1 3*(A 0 0*A 2 1*A 3 2 + A 0 0*A 2 2*A 3 1 + A 0 1*A 2 0*A 3 2 + A 0 1*A 2 2*A 3 0 + A 0 2*A 2 0*A 3 1 + A 0 2*A 2 1*A 3 0) +
    X 2 0*(A 0 1*A 1 2*A 3 3 + A 0 1*A 1 3*A 3 2 + A 0 2*A 1 1*A 3 3 + A 0 2*A 1 3*A 3 1 + A 0 3*A 1 1*A 3 2 + A 0 3*A 1 2*A 3 1) +
    X 2 1*(A 0 0*A 1 2*A 3 3 + A 0 0*A 1 3*A 3 2 + A 0 2*A 1 0*A 3 3 + A 0 2*A 1 3*A 3 0 + A 0 3*A 1 0*A 3 2 + A 0 3*A 1 2*A 3 0) +
    X 2 2*(A 0 0*A 1 1*A 3 3 + A 0 0*A 1 3*A 3 1 + A 0 1*A 1 0*A 3 3 + A 0 1*A 1 3*A 3 0 + A 0 3*A 1 0*A 3 1 + A 0 3*A 1 1*A 3 0) +
    X 2 3*(A 0 0*A 1 1*A 3 2 + A 0 0*A 1 2*A 3 1 + A 0 1*A 1 0*A 3 2 + A 0 1*A 1 2*A 3 0 + A 0 2*A 1 0*A 3 1 + A 0 2*A 1 1*A 3 0) +
    X 3 0*(A 0 1*A 1 2*A 2 3 + A 0 1*A 1 3*A 2 2 + A 0 2*A 1 1*A 2 3 + A 0 2*A 1 3*A 2 1 + A 0 3*A 1 1*A 2 2 + A 0 3*A 1 2*A 2 1) +
    X 3 1*(A 0 0*A 1 2*A 2 3 + A 0 0*A 1 3*A 2 2 + A 0 2*A 1 0*A 2 3 + A 0 2*A 1 3*A 2 0 + A 0 3*A 1 0*A 2 2 + A 0 3*A 1 2*A 2 0) +
    X 3 2*(A 0 0*A 1 1*A 2 3 + A 0 0*A 1 3*A 2 1 + A 0 1*A 1 0*A 2 3 + A 0 1*A 1 3*A 2 0 + A 0 3*A 1 0*A 2 1 + A 0 3*A 1 1*A 2 0) +
    X 3 3*(A 0 0*A 1 1*A 2 2 + A 0 0*A 1 2*A 2 1 + A 0 1*A 1 0*A 2 2 + A 0 1*A 1 2*A 2 0 + A 0 2*A 1 0*A 2 1 + A 0 2*A 1 1*A 2 0) := by
  have he := deriv_interp A X
  simp only [perm4,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul] at he
  linear_combination he/12

lemma sample0 (v : V) : deriv (base+(0 : ℂ) • Y+(0 : ℂ) • Z) (pack v) =
    (16)*v 5 + (11)*v 6 + (11)*v 7 + (11)*v 8 + (11)*v 9 + (11)*v 10 + (11)*v 11 + (16)*v 12 := by
  rw [deriv_explicit]
  simp only [pack,slice,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  norm_num [fixed,base,Y,Z,c,Matrix.cons_val_succ]
  ring_nf
  all_goals norm_num [Complex.I_sq,pow_succ] <;> ring

lemma sample1 (v : V) : deriv (base+(1 : ℂ) • Y+(0 : ℂ) • Z) (pack v) =
    ((29 + (18 * Complex.I)))*v 5 + ((29 + (13 * Complex.I)))*v 6 + ((14 + (3 * Complex.I)))*v 7 + ((14 + (3 * Complex.I)))*v 8 + ((8 + (-3 * Complex.I)))*v 9 + ((-1 + (-24 * Complex.I)))*v 10 + ((23 + (-12 * Complex.I)))*v 11 + ((16 + (12 * Complex.I)))*v 12 := by
  rw [deriv_explicit]
  simp only [pack,slice,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  norm_num [fixed,base,Y,Z,c,Matrix.cons_val_succ]
  ring_nf
  all_goals norm_num [Complex.I_sq,pow_succ] <;> ring

lemma sample2 (v : V) : deriv (base+(-1 : ℂ) • Y+(0 : ℂ) • Z) (pack v) =
    ((3 + (-18 * Complex.I)))*v 5 + ((-7 + (-13 * Complex.I)))*v 6 + ((8 + (-3 * Complex.I)))*v 7 + ((8 + (-3 * Complex.I)))*v 8 + ((14 + (3 * Complex.I)))*v 9 + ((23 + (-12 * Complex.I)))*v 10 + ((-1 + (-24 * Complex.I)))*v 11 + ((16 + (12 * Complex.I)))*v 12 := by
  rw [deriv_explicit]
  simp only [pack,slice,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  norm_num [fixed,base,Y,Z,c,Matrix.cons_val_succ]
  ring_nf
  all_goals norm_num [Complex.I_sq,pow_succ] <;> ring

lemma sample3 (v : V) : deriv (base+(0 : ℂ) • Y+(1 : ℂ) • Z) (pack v) =
    ((16 + (12 * Complex.I)))*v 5 + ((11 + (12 * Complex.I)))*v 6 + ((14 + (3 * Complex.I)))*v 7 + ((8 + (-3 * Complex.I)))*v 8 + ((14 + (3 * Complex.I)))*v 9 + ((-1 + (-24 * Complex.I)))*v 10 + ((-1 + (-24 * Complex.I)))*v 11 + ((29 + (18 * Complex.I)))*v 12 := by
  rw [deriv_explicit]
  simp only [pack,slice,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  norm_num [fixed,base,Y,Z,c,Matrix.cons_val_succ]
  ring_nf
  all_goals norm_num [Complex.I_sq,pow_succ] <;> ring

lemma sample4 (v : V) : deriv (base+(0 : ℂ) • Y+(-1 : ℂ) • Z) (pack v) =
    ((16 + (12 * Complex.I)))*v 5 + ((11 + (12 * Complex.I)))*v 6 + ((8 + (-3 * Complex.I)))*v 7 + ((14 + (3 * Complex.I)))*v 8 + ((8 + (-3 * Complex.I)))*v 9 + ((23 + (-12 * Complex.I)))*v 10 + ((23 + (-12 * Complex.I)))*v 11 + ((3 + (-18 * Complex.I)))*v 12 := by
  rw [deriv_explicit]
  simp only [pack,slice,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  norm_num [fixed,base,Y,Z,c,Matrix.cons_val_succ]
  ring_nf
  all_goals norm_num [Complex.I_sq,pow_succ] <;> ring

lemma sample5 (v : V) : deriv (base+(1 : ℂ) • Y+(1 : ℂ) • Z) (pack v) =
    ((29 + (30 * Complex.I)))*v 5 + ((29 + (25 * Complex.I)))*v 6 + ((17 + (8 * Complex.I)))*v 7 + ((11 + (-2 * Complex.I)))*v 8 + ((11 + (-2 * Complex.I)))*v 9 + ((-13 + (-62 * Complex.I)))*v 10 + ((-1 + (-34 * Complex.I)))*v 11 + ((29 + (30 * Complex.I)))*v 12 := by
  rw [deriv_explicit]
  simp only [pack,slice,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  norm_num [fixed,base,Y,Z,c,Matrix.cons_val_succ]
  ring_nf
  all_goals norm_num [Complex.I_sq,pow_succ] <;> ring

lemma sample6 (v : V) : deriv (base+(-1 : ℂ) • Y+(1 : ℂ) • Z) (pack v) =
    ((3 + (-6 * Complex.I)))*v 5 + ((-7 + (-1 * Complex.I)))*v 6 + ((11 + (-2 * Complex.I)))*v 7 + ((5 + (-4 * Complex.I)))*v 8 + ((17 + (8 * Complex.I)))*v 9 + ((-1 + (-34 * Complex.I)))*v 10 + ((-13 + (-62 * Complex.I)))*v 11 + ((29 + (30 * Complex.I)))*v 12 := by
  rw [deriv_explicit]
  simp only [pack,slice,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  norm_num [fixed,base,Y,Z,c,Matrix.cons_val_succ]
  ring_nf
  all_goals norm_num [Complex.I_sq,pow_succ] <;> ring

lemma sample7 (v : V) : deriv (base+(1 : ℂ) • Y+(-1 : ℂ) • Z) (pack v) =
    ((29 + (30 * Complex.I)))*v 5 + ((29 + (25 * Complex.I)))*v 6 + ((11 + (-2 * Complex.I)))*v 7 + ((17 + (8 * Complex.I)))*v 8 + ((5 + (-4 * Complex.I)))*v 9 + ((-1 + (-34 * Complex.I)))*v 10 + ((59 + (-14 * Complex.I)))*v 11 + ((3 + (-6 * Complex.I)))*v 12 := by
  rw [deriv_explicit]
  simp only [pack,slice,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  norm_num [fixed,base,Y,Z,c,Matrix.cons_val_succ]
  ring_nf
  all_goals norm_num [Complex.I_sq,pow_succ] <;> ring

lemma eliminate_extra (L : Submodule ℂ M) (hY : Y ∈ L) (hZ : Z ∈ L)
    (lev : ∀ X ∈ L, (base+X).permanent=65) (v : V) (hv : pack v ∈ L) :
    ∀ k : Fin 8, v ⟨k.val+5,by omega⟩=0 := by
  have allp (s t : ℂ) : deriv (base+s • Y+t • Z) (pack v)=0 := by
    apply deriv_zero
    intro u
    rw [add_assoc,add_assoc]
    exact lev _ (L.add_mem (L.smul_mem s hY) (L.add_mem (L.smul_mem t hZ) (L.smul_mem u hv)))
  have h0 := allp 0 0
  rw [sample0] at h0
  have h1 := allp 1 0
  rw [sample1] at h1
  have h2 := allp (-1 : ℂ) 0
  rw [sample2] at h2
  have h3 := allp 0 1
  rw [sample3] at h3
  have h4 := allp 0 (-1 : ℂ)
  rw [sample4] at h4
  have h5 := allp 1 1
  rw [sample5] at h5
  have h6 := allp (-1 : ℂ) 1
  rw [sample6] at h6
  have h7 := allp 1 (-1 : ℂ)
  rw [sample7] at h7
  intro k
  fin_cases k
  · change v 5=0
    linear_combination (norm := (ring_nf <;> norm_num [Complex.I_sq,pow_succ] <;> ring)) (((-2753/3900) + ((-577/1300) * Complex.I)))*h0 + (((61/1950) + ((6751/15600) * Complex.I)))*h1 + (((197/390) + ((479/3120) * Complex.I)))*h2 + (((413/975) + ((5921/15600) * Complex.I)))*h3 + (((22/195) + ((77/624) * Complex.I)))*h4 + (((-12/325) + ((-109/325) * Complex.I)))*h5 + (((-921/2600) + ((-161/1300) * Complex.I)))*h6 + (((99/2600) + ((-44/325) * Complex.I)))*h7
  · change v 6=0
    linear_combination (norm := (ring_nf <;> norm_num [Complex.I_sq,pow_succ] <;> ring)) (((4531/7800) + ((5087/7800) * Complex.I)))*h0 + (((487/15600) + ((-3863/7800) * Complex.I)))*h1 + (((-1381/3120) + ((-337/1560) * Complex.I)))*h2 + (((-2329/7800) + ((-8521/15600) * Complex.I)))*h3 + (((-22/195) + ((-103/624) * Complex.I)))*h4 + (((-133/5200) + ((2069/5200) * Complex.I)))*h5 + (((1517/5200) + ((969/5200) * Complex.I)))*h6 + (((-99/2600) + ((44/325) * Complex.I)))*h7
  · change v 7=0
    linear_combination (norm := (ring_nf <;> norm_num [Complex.I_sq,pow_succ] <;> ring)) (((341/3120) + ((-161/1040) * Complex.I)))*h0 + (((389/2080) + ((22/195) * Complex.I)))*h1 + (((-265/1248) + ((-5/156) * Complex.I)))*h2 + (((-227/1560) + ((679/6240) * Complex.I)))*h3 + (((25/208) + ((-35/1248) * Complex.I)))*h4 + (((-83/2080) + ((-261/2080) * Complex.I)))*h5 + (((1111/6240) + ((347/6240) * Complex.I)))*h6 + (((-241/1560) + ((161/3120) * Complex.I)))*h7
  · change v 8=0
    linear_combination (norm := (ring_nf <;> norm_num [Complex.I_sq,pow_succ] <;> ring)) (((349/4680) + ((1151/9360) * Complex.I)))*h0 + (((137/2340) + ((-1219/9360) * Complex.I)))*h1 + (((-23/468) + ((-125/1872) * Complex.I)))*h2 + (((-43/1040) + ((419/6240) * Complex.I)))*h3 + (((5/312) + ((-61/1248) * Complex.I)))*h4 + (((-83/2080) + ((2/65) * Complex.I)))*h5 + (((67/2080) + ((-9/520) * Complex.I)))*h6 + (((-9/1040) + ((2/65) * Complex.I)))*h7
  · change v 9=0
    linear_combination (norm := (ring_nf <;> norm_num [Complex.I_sq,pow_succ] <;> ring)) (((89/144) + ((-13/36) * Complex.I)))*h0 + (((-131/288) + ((11/144) * Complex.I)))*h1 + (((-47/288) + ((41/144) * Complex.I)))*h2 + (((-19/48) + ((1/12) * Complex.I)))*h3 + (((-3/16) + ((1/16) * Complex.I)))*h4 + (((7/24) + ((5/96) * Complex.I)))*h5 + (((7/48) + ((-17/96) * Complex.I)))*h6 + (((7/48) + ((-1/48) * Complex.I)))*h7
  · change v 10=0
    linear_combination (norm := (ring_nf <;> norm_num [Complex.I_sq,pow_succ] <;> ring)) (((-1/12) + ((1/12) * Complex.I)))*h0 + (((1/16) + ((-1/16) * Complex.I)))*h1 + (((1/48) + ((-1/48) * Complex.I)))*h2 + (((1/16) + ((-1/16) * Complex.I)))*h3 + (((1/48) + ((-1/48) * Complex.I)))*h4 + (((-1/24) + ((1/24) * Complex.I)))*h5 + (((-1/48) + ((1/48) * Complex.I)))*h6 + (((-1/48) + ((1/48) * Complex.I)))*h7
  · change v 11=0
    linear_combination (norm := (ring_nf <;> norm_num [Complex.I_sq,pow_succ] <;> ring)) (((-1/48) + ((1/48) * Complex.I)))*h1 + (((1/48) + ((-1/48) * Complex.I)))*h2 + (((1/48) + ((-1/48) * Complex.I)))*h3 + (((-1/48) + ((1/48) * Complex.I)))*h4 + (((-1/48) + ((1/48) * Complex.I)))*h6 + (((1/48) + ((-1/48) * Complex.I)))*h7
  · change v 12=0
    linear_combination (norm := (ring_nf <;> norm_num [Complex.I_sq,pow_succ] <;> ring)) (((-1/8) + ((5/24) * Complex.I)))*h0 + (((1/16) + ((-5/48) * Complex.I)))*h1 + (((1/16) + ((-5/48) * Complex.I)))*h2 + (((1/8) + ((-1/8) * Complex.I)))*h3 + (((-1/16) + ((1/16) * Complex.I)))*h5 + (((-1/16) + ((1/16) * Complex.I)))*h6


noncomputable def quad (A X : M) : ℂ := ∑ p : Equiv.Perm (Fin 4), (
X (p 0) 0*X (p 1) 1*A (p 2) 2*A (p 3) 3 +
  X (p 0) 0*A (p 1) 1*X (p 2) 2*A (p 3) 3 +
  X (p 0) 0*A (p 1) 1*A (p 2) 2*X (p 3) 3 +
  A (p 0) 0*X (p 1) 1*X (p 2) 2*A (p 3) 3 +
  A (p 0) 0*X (p 1) 1*A (p 2) 2*X (p 3) 3 +
  A (p 0) 0*A (p 1) 1*X (p 2) 2*X (p 3) 3)

lemma quad_eq (A X : M) : 2*quad A X =
    (A+X).permanent+(A-X).permanent-2*A.permanent-2*X.permanent := by
  simp only [quad,Matrix.permanent,Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  simp [Fin.prod_univ_four,Matrix.add_apply,Matrix.sub_apply]
  ring

lemma quad_zero (L : Submodule ℂ M) (lev : ∀ X ∈ L, (base+X).permanent=65)
    (A X : M) (hA : A ∈ L) (hX : X ∈ L) : quad A X=0 := by
  have e := quad_eq A X
  rw [top_zero L lev _ (L.add_mem hA hX),top_zero L lev _ (L.sub_mem hA hX),
    top_zero L lev A hA,top_zero L lev X hX] at e
  linear_combination e/2

lemma quad_explicit (A X : M) : quad A X =
    X 0 0*X 1 1*(A 2 2*A 3 3+A 2 3*A 3 2) +
    X 0 0*X 1 2*(A 2 1*A 3 3+A 2 3*A 3 1) +
    X 0 0*X 1 3*(A 2 1*A 3 2+A 2 2*A 3 1) +
    X 0 1*X 1 0*(A 2 2*A 3 3+A 2 3*A 3 2) +
    X 0 1*X 1 2*(A 2 0*A 3 3+A 2 3*A 3 0) +
    X 0 1*X 1 3*(A 2 0*A 3 2+A 2 2*A 3 0) +
    X 0 2*X 1 0*(A 2 1*A 3 3+A 2 3*A 3 1) +
    X 0 2*X 1 1*(A 2 0*A 3 3+A 2 3*A 3 0) +
    X 0 2*X 1 3*(A 2 0*A 3 1+A 2 1*A 3 0) +
    X 0 3*X 1 0*(A 2 1*A 3 2+A 2 2*A 3 1) +
    X 0 3*X 1 1*(A 2 0*A 3 2+A 2 2*A 3 0) +
    X 0 3*X 1 2*(A 2 0*A 3 1+A 2 1*A 3 0) +
    X 0 0*X 2 1*(A 1 2*A 3 3+A 1 3*A 3 2) +
    X 0 0*X 2 2*(A 1 1*A 3 3+A 1 3*A 3 1) +
    X 0 0*X 2 3*(A 1 1*A 3 2+A 1 2*A 3 1) +
    X 0 1*X 2 0*(A 1 2*A 3 3+A 1 3*A 3 2) +
    X 0 1*X 2 2*(A 1 0*A 3 3+A 1 3*A 3 0) +
    X 0 1*X 2 3*(A 1 0*A 3 2+A 1 2*A 3 0) +
    X 0 2*X 2 0*(A 1 1*A 3 3+A 1 3*A 3 1) +
    X 0 2*X 2 1*(A 1 0*A 3 3+A 1 3*A 3 0) +
    X 0 2*X 2 3*(A 1 0*A 3 1+A 1 1*A 3 0) +
    X 0 3*X 2 0*(A 1 1*A 3 2+A 1 2*A 3 1) +
    X 0 3*X 2 1*(A 1 0*A 3 2+A 1 2*A 3 0) +
    X 0 3*X 2 2*(A 1 0*A 3 1+A 1 1*A 3 0) +
    X 0 0*X 3 1*(A 1 2*A 2 3+A 1 3*A 2 2) +
    X 0 0*X 3 2*(A 1 1*A 2 3+A 1 3*A 2 1) +
    X 0 0*X 3 3*(A 1 1*A 2 2+A 1 2*A 2 1) +
    X 0 1*X 3 0*(A 1 2*A 2 3+A 1 3*A 2 2) +
    X 0 1*X 3 2*(A 1 0*A 2 3+A 1 3*A 2 0) +
    X 0 1*X 3 3*(A 1 0*A 2 2+A 1 2*A 2 0) +
    X 0 2*X 3 0*(A 1 1*A 2 3+A 1 3*A 2 1) +
    X 0 2*X 3 1*(A 1 0*A 2 3+A 1 3*A 2 0) +
    X 0 2*X 3 3*(A 1 0*A 2 1+A 1 1*A 2 0) +
    X 0 3*X 3 0*(A 1 1*A 2 2+A 1 2*A 2 1) +
    X 0 3*X 3 1*(A 1 0*A 2 2+A 1 2*A 2 0) +
    X 0 3*X 3 2*(A 1 0*A 2 1+A 1 1*A 2 0) +
    X 1 0*X 2 1*(A 0 2*A 3 3+A 0 3*A 3 2) +
    X 1 0*X 2 2*(A 0 1*A 3 3+A 0 3*A 3 1) +
    X 1 0*X 2 3*(A 0 1*A 3 2+A 0 2*A 3 1) +
    X 1 1*X 2 0*(A 0 2*A 3 3+A 0 3*A 3 2) +
    X 1 1*X 2 2*(A 0 0*A 3 3+A 0 3*A 3 0) +
    X 1 1*X 2 3*(A 0 0*A 3 2+A 0 2*A 3 0) +
    X 1 2*X 2 0*(A 0 1*A 3 3+A 0 3*A 3 1) +
    X 1 2*X 2 1*(A 0 0*A 3 3+A 0 3*A 3 0) +
    X 1 2*X 2 3*(A 0 0*A 3 1+A 0 1*A 3 0) +
    X 1 3*X 2 0*(A 0 1*A 3 2+A 0 2*A 3 1) +
    X 1 3*X 2 1*(A 0 0*A 3 2+A 0 2*A 3 0) +
    X 1 3*X 2 2*(A 0 0*A 3 1+A 0 1*A 3 0) +
    X 1 0*X 3 1*(A 0 2*A 2 3+A 0 3*A 2 2) +
    X 1 0*X 3 2*(A 0 1*A 2 3+A 0 3*A 2 1) +
    X 1 0*X 3 3*(A 0 1*A 2 2+A 0 2*A 2 1) +
    X 1 1*X 3 0*(A 0 2*A 2 3+A 0 3*A 2 2) +
    X 1 1*X 3 2*(A 0 0*A 2 3+A 0 3*A 2 0) +
    X 1 1*X 3 3*(A 0 0*A 2 2+A 0 2*A 2 0) +
    X 1 2*X 3 0*(A 0 1*A 2 3+A 0 3*A 2 1) +
    X 1 2*X 3 1*(A 0 0*A 2 3+A 0 3*A 2 0) +
    X 1 2*X 3 3*(A 0 0*A 2 1+A 0 1*A 2 0) +
    X 1 3*X 3 0*(A 0 1*A 2 2+A 0 2*A 2 1) +
    X 1 3*X 3 1*(A 0 0*A 2 2+A 0 2*A 2 0) +
    X 1 3*X 3 2*(A 0 0*A 2 1+A 0 1*A 2 0) +
    X 2 0*X 3 1*(A 0 2*A 1 3+A 0 3*A 1 2) +
    X 2 0*X 3 2*(A 0 1*A 1 3+A 0 3*A 1 1) +
    X 2 0*X 3 3*(A 0 1*A 1 2+A 0 2*A 1 1) +
    X 2 1*X 3 0*(A 0 2*A 1 3+A 0 3*A 1 2) +
    X 2 1*X 3 2*(A 0 0*A 1 3+A 0 3*A 1 0) +
    X 2 1*X 3 3*(A 0 0*A 1 2+A 0 2*A 1 0) +
    X 2 2*X 3 0*(A 0 1*A 1 3+A 0 3*A 1 1) +
    X 2 2*X 3 1*(A 0 0*A 1 3+A 0 3*A 1 0) +
    X 2 2*X 3 3*(A 0 0*A 1 1+A 0 1*A 1 0) +
    X 2 3*X 3 0*(A 0 1*A 1 2+A 0 2*A 1 1) +
    X 2 3*X 3 1*(A 0 0*A 1 2+A 0 2*A 1 0) +
    X 2 3*X 3 2*(A 0 0*A 1 1+A 0 1*A 1 0) := by
  have he := quad_eq A X
  simp only [perm4,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul] at he
  linear_combination he/2

set_option maxHeartbeats 2000000 in
lemma first_quad (x y z r f : ℂ) : quad Y (slice x y z r f) = ((f^2) * (-864 + (2520 * Complex.I))) := by
  rw [quad_explicit]
  simp only [slice,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  norm_num [fixed,Y,Z,c,Matrix.cons_val_succ]
  ring_nf
  all_goals norm_num [Complex.I_sq,pow_succ] <;> ring

set_option maxHeartbeats 2000000 in
lemma second_quad (x y z r : ℂ) : quad (Y+Z) (slice x y z r 0) = ((r^2) * (803520 + (-2426112 * Complex.I))) := by
  rw [quad_explicit]
  simp only [slice,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  norm_num [fixed,Y,Z,c,Matrix.cons_val_succ]
  ring_nf
  all_goals norm_num [Complex.I_sq,pow_succ] <;> ring

lemma fixed_zero (L : Submodule ℂ M) (lev : ∀ X ∈ L, (base+X).permanent=65)
    (x y z : ℂ) (h : fixed x y z ∈ L) : x=0 ∧ y=0 ∧ z=0 := by
  obtain ⟨_,h2,h3,h4⟩ := coeffs 0
    ((-23474 * (z^2)) + (30976 * (y^2)) + (60334 * (x^2)) + (16324 * x * z)) ((255552 * (z^3)) + (623872 * (x^3)) + (-1146112 * x * (y^2)) + (-1022208 * z * (y^2)) + (-165440 * z * (x^2)) + (30976 * x * (z^2))) ((14641 * (z^4)) + (14992384 * (y^4)) + (29343889 * (x^4)) + (-40206848 * (x^2) * (y^2)) + (6458012 * x * (z^3)) + (25848262 * (x^2) * (z^2)) + (41989596 * z * (x^3)) + (-22488576 * x * z * (y^2))) (by
    intro t
    have e := lev _ (L.smul_mem t h)
    rw [perm4] at e
    simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul] at e
    norm_num [fixed,base,Matrix.cons_val_succ] at e
    linear_combination e)
  have hy : y^2=(((-30167/15488) * (x^2)) + ((97/128) * (z^2)) + ((-371/704) * x * z)) := by linear_combination h2/30976
  rw [show y^4=(y^2)^2 by ring,hy] at h4
  rw [hy] at h3
  have hc : ((-3993 * (z^3)) + (21971 * (x^3)) + (-2299 * x * (z^2)) + (18689 * z * (x^2)))=0 := by linear_combination h3/130
  have hf : ((2122945 * (z^4)) + (40501025 * (x^4)) + (-8089818 * (x^2) * (z^2)) + (-5552932 * x * (z^3)) + (33909788 * z * (x^3)))=0 := by linear_combination 16*h4/65
  have nz : z^6=0 := by linear_combination (((-50985671379121396509125/4873325655210975798820864) * (x^3)) + ((-3472751019413767743/3661401694373385273344) * (z^3)) + ((-1426948802271372448745/443029605019179618074624) * z * (x^2)) + ((12233547944831816855/3661401694373385273344) * x * (z^2)))*hc + (((-52878536366982509/40275418638107238006784) * (z^2)) + ((27658711992367506815/4873325655210975798820864) * (x^2)) + ((403846755474266695/221514802509589809037312) * x * z))*hf
  have nx : x^6=0 := by linear_combination (((-17345881672185/2750865285028839424) * (z^3)) + ((428970582968119/2750865285028839424) * (x^3)) + ((-412464069924071/2750865285028839424) * z * (x^2)) + ((142432662501481/2750865285028839424) * x * (z^2)))*hc + (((-164787123125/2750865285028839424) * (x^2)) + ((-32625482769/2750865285028839424) * (z^2)) + ((81888214749/1375432642514419712) * x * z))*hf
  have hx : x=0 := by simpa using nx
  have hz : z=0 := by simpa using nz
  rw [hx,hz] at hy
  exact ⟨hx,by simpa using hy,hz⟩

lemma disjoint (L : Submodule ℂ M) (hY : Y ∈ L) (hZ : Z ∈ L)
    (lev : ∀ X ∈ L, (base+X).permanent=65) (v : V) (hv : pack v ∈ L) : v=0 := by
  have he := eliminate_extra L hY hZ lev v hv
  have e5 : v 5=0 := he 0
  have e6 : v 6=0 := he 1
  have e7 : v 7=0 := he 2
  have e8 : v 8=0 := he 3
  have e9 : v 9=0 := he 4
  have e10 : v 10=0 := he 5
  have e11 : v 11=0 := he 6
  have e12 : v 12=0 := he 7
  have simpPack : pack v = slice (v 0) (v 1) (v 2) (v 3) (v 4) := by
    unfold pack
    rw [e5,e6,e7,e8,e9,e10,e11,e12]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.cons_val_succ]
  rw [simpPack] at hv
  have h4 := quad_zero L lev _ _ hY hv
  rw [first_quad] at h4
  have t4 : v 4 = 0 := by
    have hn : (-864+2520*Complex.I : ℂ) ≠ 0 := by
      intro e
      have ee := congrArg Complex.re e
      norm_num [Complex.mul_re] at ee
    simpa using (mul_eq_zero.mp h4).resolve_right hn
  rw [t4] at hv
  have h3 := quad_zero L lev _ _ (L.add_mem hY hZ) hv
  rw [second_quad] at h3
  have t3 : v 3 = 0 := by
    have hn : (803520+ -2426112*Complex.I : ℂ) ≠ 0 := by
      intro e
      have ee := congrArg Complex.re e
      norm_num [Complex.mul_re] at ee
    simpa using (mul_eq_zero.mp h3).resolve_right hn
  rw [t3] at hv
  simp only [slice,zero_smul,add_zero] at hv
  obtain ⟨e0,e1,e2⟩ := fixed_zero L lev _ _ _ hv
  funext i
  fin_cases i
  · exact e0
  · exact e1
  · exact e2
  · exact t3
  · exact t4
  · exact e5
  · exact e6
  · exact e7
  · exact e8
  · exact e9
  · exact e10
  · exact e11
  · exact e12
theorem bound (L : Submodule ℂ M) (hY : Y ∈ L) (hZ : Z ∈ L)
    (lev : ∀ X ∈ L, (base+X).permanent=65) : Module.finrank ℂ L ≤ 3 := by
  let F : L × V →ₗ[ℂ] M := L.subtype.comp (LinearMap.fst ℂ L V) +
    packed.comp (LinearMap.snd ℂ L V)
  have inj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot,LinearMap.ker_eq_bot']
    rintro ⟨X,v⟩ h
    change X.val+packed v=0 at h
    have hv : pack v ∈ L := by
      change packed v ∈ L
      rw [(eq_neg_of_add_eq_zero_right h)]
      exact L.neg_mem X.property
    have ev := disjoint L hY hZ lev v hv
    subst v
    simp at h
    exact Prod.ext h rfl
  have hh := F.finrank_le_finrank_of_injective inj
  have total : Module.finrank ℂ M=16 := by simp [M,Module.finrank_matrix]
  have aux : Module.finrank ℂ V=13 := Module.finrank_fin_fun ℂ
  rw [Module.finrank_prod,aux,total] at hh
  omega

end PEqualNP.Research.SparsePairBound

