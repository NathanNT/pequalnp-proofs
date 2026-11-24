import Mathlib
import PEqualNP.Research.SparsePairBound

theorem PEqualNP.Research.SparsePairSharp :
  ∃ Y Z D : Matrix (Fin 4) (Fin 4) ℂ,
  (∀ i j, Y i j ≠ 0 ↔ i = 0 ∨ i = 1) ∧
  (∀ i j, Z i j ≠ 0 ↔ j = 2 ∨ j = 3) ∧
  (∀ t u v : ℂ, t • Y + u • Z + v • D=0 → t=0 ∧ u=0 ∧ v=0) ∧
  (∀ t u v : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
    (if i=j then (2 : ℂ) else 1)+t*Y i j+u*Z i j+v*D i j)=65) ∧
  ∀ L : Submodule ℂ (Matrix (Fin 4) (Fin 4) ℂ), Y ∈ L → Z ∈ L →
    (∀ X ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      (if i=j then (2 : ℂ) else 1)+X i j)=65) →
    Module.finrank ℂ L ≤ 3 := by
  open PEqualNP.Research.SparseCoexistence PEqualNP.Research.SparseExtension in
    obtain ⟨q,hq⟩ := IsAlgClosed.exists_pow_nat_eq (19 : ℂ) zero_lt_two
    refine ⟨Y,Z,D q,supports.1,supports.2,free_three q,?_,?_⟩
    · intro t u v
      rw [identity,hq]
      ring
    · exact PEqualNP.Research.SparsePairBound.bound
