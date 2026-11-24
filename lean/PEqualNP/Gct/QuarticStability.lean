import PEqualNP.Gct.QuarticEquality

open PEqualNP.Gct.TriplePacking

-- Delete the complement of the embedded triples. The equivalence states that the
-- projected image is the full product of the specified lines.
theorem PEqualNP.Gct.QuarticStability :
∀ (m : ℕ) (X : Submodule ℂ (Fin m → ℂ)),
  (∀ x ∈ X, ∑ i, x i ^ 2 = 0) → (∀ x ∈ X, ∑ i, x i ^ 4 = 0) →
  ∃ (t : ℕ) (e : Fin t × Fin 3 ↪ Fin m) (v : Fin t → Fin 3 → ℂ),
    3 * Module.finrank ℂ X ≤ m ∧ 3 * t ≤ m ∧
    m - 3 * t ≤ 7 * (m - 3 * Module.finrank ℂ X) ∧
    (∀ b, v b ≠ 0 ∧ ∑ i, v b i ^ 2 = 0 ∧ ∑ i, v b i ^ 4 = 0) ∧
    ∀ z : Fin t → Fin 3 → ℂ,
      (∃ x ∈ X, ∀ b i, x (e (b,i)) = z b i) ↔
      ∃ c : Fin t → ℂ, ∀ b i, z b i = c b * v b i := by
  intro m X h₂ h₄
  classical
  obtain ⟨bound,T,_,⟨P⟩,count⟩ := decompose m (Fin m) (Fintype.card_fin m) X X (polarize X h₂ h₄) le_rfl
  have cap := P.coordinate_count
  rw [Fintype.card_fin] at cap
  let label := (Fintype.equivFin T).symm
  exact ⟨Fintype.card T,P.coords label,fun b => P.shape (label b),bound,cap,by omega,
    fun b => ⟨P.nonzero _,P.quadratic _,P.quartic _⟩,P.describe label⟩
