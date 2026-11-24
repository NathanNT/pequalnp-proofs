import Mathlib
import PEqualNP.Research.SparseCoexistence

namespace PEqualNP.Research.SparseExtension
open PEqualNP.Research.SparseCoexistence
noncomputable def D (q : ℂ) : M := Matrix.of ![
  ![493*q+66*(31+5*Complex.I), (-468-155*Complex.I)*q-66*(31+5*Complex.I),-15*(31+5*Complex.I),-15*(31+5*Complex.I)],
  ![(468+155*Complex.I)*q-66*(31+5*Complex.I), -493*q+66*(31+5*Complex.I),-15*(31+5*Complex.I),-15*(31+5*Complex.I)],
  ![0,0,0,0],![0,0,0,0]]

lemma identity (q t u v : ℂ) :
    Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      (if i=j then (2 : ℂ) else 1)+t*Y i j+u*Z i j+v*D q i j) =
      65+(-2190240-725400*Complex.I)*(q^2-19)*v^2 := by
  rw [PEqualNP.Research.KleinPermanent.perm4]
  norm_num [D,Y,Z,c,Matrix.cons_val_succ]
  ring_nf
  norm_num [Complex.I_sq,pow_succ]; ring

lemma free_three (q t u v : ℂ) (h : t • Y + u • Z + v • D q=0) :
    t=0 ∧ u=0 ∧ v=0 := by
  have hu := congrArg (fun A : M => A 2 2) h
  have hu' : u=0 := by simpa [Y,Z,D,Matrix.cons_val_succ] using hu
  rw [hu',zero_smul,add_zero] at h
  have h1 := congrArg (fun A : M => A 0 2) h
  have h2 := congrArg (fun A : M => A 1 2) h
  simp [Y,D,Matrix.cons_val_succ] at h1 h2
  have prod : v*(31+5*Complex.I)=0 := by linear_combination -(h1+h2)/30
  have hn : (31+5*Complex.I : ℂ) ≠ 0 := by
    intro hh
    have e := congrArg Complex.re hh
    norm_num [Complex.mul_re] at e
  have hv := (mul_eq_zero.mp prod).resolve_right hn
  rw [hv,zero_smul,add_zero] at h
  have e := congrArg (fun A : M => A 0 0) h
  refine ⟨?_,hu',hv⟩
  simpa [Y] using e

end PEqualNP.Research.SparseExtension

theorem PEqualNP.Research.SparseExtension :
∃ Y Z D : Matrix (Fin 4) (Fin 4) ℂ,
  (∀ i j, Y i j ≠ 0 ↔ i = 0 ∨ i = 1) ∧
  (∀ i j, Z i j ≠ 0 ↔ j = 2 ∨ j = 3) ∧
  (∀ t u v : ℂ, t • Y + u • Z + v • D=0 → t=0 ∧ u=0 ∧ v=0) ∧
  ∀ t u v : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
    (if i=j then (2 : ℂ) else 1)+t*Y i j+u*Z i j+v*D i j)=65 := by
  open PEqualNP.Research.SparseCoexistence PEqualNP.Research.SparseExtension in
    obtain ⟨q,hq⟩ := IsAlgClosed.exists_pow_nat_eq (19 : ℂ) zero_lt_two
    exact ⟨Y,Z,D q,supports.1,supports.2,free_three q,fun t u v => by rw [identity,hq]; ring⟩
