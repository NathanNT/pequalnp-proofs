import Mathlib
import PEqualNP.Research.KleinPermanent

namespace PEqualNP.Research.SparseCoexistence
abbrev M := Matrix (Fin 4) (Fin 4) ℂ
noncomputable def c : ℂ := -3*(1+Complex.I)
noncomputable def Y : M := Matrix.of ![
  ![1,Complex.I,c,c],![-Complex.I,-1,-c,-c],![0,0,0,0],![0,0,0,0]]
noncomputable def Z : M := Matrix.of ![
  ![0,0,c,-c],![0,0,c,-c],![0,0,1,-Complex.I],![0,0,Complex.I,-1]]
lemma c_ne : c ≠ 0 := by
  intro h
  have g := congrArg Complex.re h
  norm_num [c,Complex.mul_re] at g

theorem level (t u : ℂ) :
    Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      (if i=j then (2 : ℂ) else 1)+t*Y i j+u*Z i j)=65 := by
  rw [PEqualNP.Research.KleinPermanent.perm4]
  norm_num [Y,Z,c,Matrix.cons_val_succ]
  ring_nf
  norm_num [Complex.I_sq, pow_succ] <;> ring

theorem free (t u : ℂ) (h : t • Y + u • Z=0) : t=0 ∧ u=0 := by
  have p := congrArg (fun A : M => A 0 0) h
  have q := congrArg (fun A : M => A 2 2) h
  constructor
  · simpa [Y,Z,Matrix.cons_val_succ] using p
  · simpa [Y,Z,Matrix.cons_val_succ] using q

theorem supports :
    (∀ i j, Y i j ≠ 0 ↔ i = 0 ∨ i = 1) ∧
    (∀ i j, Z i j ≠ 0 ↔ j = 2 ∨ j = 3) := by
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Y,Z,c_ne, Matrix.cons_val_succ,Complex.I_ne_zero]

end PEqualNP.Research.SparseCoexistence

theorem PEqualNP.Research.SparseCoexistence :
∃ Y Z : Matrix (Fin 4) (Fin 4) ℂ,
  (∀ i j, Y i j ≠ 0 ↔ i = 0 ∨ i = 1) ∧
  (∀ i j, Z i j ≠ 0 ↔ j = 2 ∨ j = 3) ∧
  (∀ t u : ℂ, t • Y + u • Z=0 → t=0 ∧ u=0) ∧
  ∀ t u : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
    (if i=j then (2 : ℂ) else 1)+t*Y i j+u*Z i j)=65 := by
  open PEqualNP.Research.SparseCoexistence in
    exact ⟨Y,Z,supports.1,supports.2,free,level⟩
