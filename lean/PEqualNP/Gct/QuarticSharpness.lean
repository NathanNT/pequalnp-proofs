import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

open Finset

private theorem mixedMoments (t : Fin 7 → ℂ)
    (moment : ∀ d : ℕ, d.Coprime 7 → ∑ i : Fin 7, t i ^ d = 0) (a b : ℂ) :
    (∑ i : Fin 7, (a * t i + b * t i ^ 3) ^ 2) = 0 ∧
    (∑ i : Fin 7, (a * t i + b * t i ^ 3) ^ 4) = 0 := by
  constructor
  · calc
      _ = ∑ i : Fin 7, (a^2 * t i^2 + (2*a*b) * t i^4 + b^2 * t i^6) := by
        apply sum_congr rfl; intro i _; ring
      _ = 0 := by simp only [sum_add_distrib,← mul_sum,moment 2 (by decide),moment 4 (by decide),
          moment 6 (by decide),mul_zero,add_zero]
  · calc
      _ = ∑ i : Fin 7, (a^4 * t i^4 + (4*a^3*b) * t i^6 + (6*a^2*b^2) * t i^8 +
          (4*a*b^3) * t i^10 + b^4 * t i^12) := by
        apply sum_congr rfl; intro i _; ring
      _ = 0 := by simp only [sum_add_distrib,← mul_sum,moment 4 (by decide),moment 6 (by decide),
          moment 8 (by decide),moment 10 (by decide),moment 12 (by decide),mul_zero,add_zero]

-- Fourier characters of frequencies one and three modulo seven. Every product of
-- two or four selected characters has nonzero frequency, so its coordinate sum vanishes.
set_option maxHeartbeats 900000 in
private theorem PEqualNP.Gct.sevenCoordinateExample :
∃ X : Submodule ℂ (Fin 7 → ℂ), Module.finrank ℂ X = 2 ∧
    (∀ x ∈ X, ∑ i, x i ^ 2 = 0) ∧ (∀ x ∈ X, ∑ i, x i ^ 4 = 0) ∧
    ∀ i j : Fin 7, i ≠ j →
      Function.Surjective (fun x : X => (x.val i,x.val j)) := by
  classical
  let ζ := Complex.exp (2 * Real.pi * Complex.I * ((1 : ℂ) / 7))
  have primitive : IsPrimitiveRoot ζ 7 := Complex.isPrimitiveRoot_exp_of_coprime 1 7 (by decide) (by decide)
  let t (i : Fin 7) := ζ ^ i.val
  have moment (d : ℕ) (coprime : d.Coprime 7) : ∑ i : Fin 7, t i ^ d = 0 := by
    have h := (primitive.pow_of_coprime d coprime).geom_sum_eq_zero (by decide)
    rw [← Fin.sum_univ_eq_sum_range] at h
    simpa only [t,← pow_mul,Nat.mul_comm] using h
  let enc : (ℂ × ℂ) →ₗ[ℂ] (Fin 7 → ℂ) :=
    { toFun := fun c i => c.1 * t i + c.2 * t i ^ 3
      map_add' := by intro x y; funext i; simp; ring
      map_smul' := by intro c x; funext i; simp; ring }
  let pair (i j : Fin 7) : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) :=
    ((LinearMap.proj i).comp enc).prod ((LinearMap.proj j).comp enc)
  have onto (i j : Fin 7) (ne : i ≠ j) : Function.Surjective (pair i j) := by
    have nz (k : Fin 7) : t k ≠ 0 := pow_ne_zero _ (primitive.ne_zero (by decide))
    have distinct : t j ^ 2 ≠ t i ^ 2 := by
      intro h
      have h' : (ζ ^ 2) ^ j.val = (ζ ^ 2) ^ i.val := by simpa only [t,← pow_mul,Nat.mul_comm] using h
      exact ne (Fin.ext ((primitive.pow_of_coprime 2 (by decide)).pow_inj j.isLt i.isLt h').symm)
    have det : t i * t j ^ 3 - t j * t i ^ 3 ≠ 0 := by
      rw [show t i * t j ^ 3 - t j * t i ^ 3 = t i * t j * (t j ^ 2 - t i ^ 2) by ring]
      exact mul_ne_zero (mul_ne_zero (nz i) (nz j)) (sub_ne_zero.mpr distinct)
    rintro ⟨u,v⟩
    let D := t i * t j ^ 3 - t j * t i ^ 3
    refine ⟨((u * t j ^ 3 - v * t i ^ 3) / D,(t i * v - t j * u) / D),?_⟩
    apply Prod.ext
    · change _ / D * t i + _ / D * t i ^ 3 = u
      rw [div_mul_eq_mul_div₀,div_mul_eq_mul_div₀,← add_div,div_eq_iff (show D ≠ 0 from det)]
      dsimp only [D]; ring
    · change _ / D * t j + _ / D * t j ^ 3 = v
      rw [div_mul_eq_mul_div₀,div_mul_eq_mul_div₀,← add_div,div_eq_iff (show D ≠ 0 from det)]
      dsimp only [D]; ring
  have inj : Function.Injective enc := by
    intro a b h
    apply (LinearMap.injective_iff_surjective.mpr (onto 0 1 (by decide)))
    exact Prod.ext (congrFun h 0) (congrFun h 1)
  refine ⟨LinearMap.range enc,?_,?_,?_,?_⟩
  · rw [LinearMap.finrank_range_of_inj inj,Module.finrank_prod]
    simp
  · rintro _ ⟨c,rfl⟩
    exact (mixedMoments t moment c.1 c.2).1
  · rintro _ ⟨c,rfl⟩
    exact (mixedMoments t moment c.1 c.2).2
  · intro i j ne w
    obtain ⟨c,hc⟩ := onto i j ne w
    exact ⟨⟨enc c,c,rfl⟩,hc⟩

-- Two independently prescribed coordinates are incompatible with a common line
-- on any retained triple.
theorem PEqualNP.Gct.QuarticSharpness :
∃ X : Submodule ℂ (Fin 7 → ℂ), Module.finrank ℂ X = 2 ∧
    (∀ x ∈ X, ∑ i, x i ^ 2 = 0) ∧ (∀ x ∈ X, ∑ i, x i ^ 4 = 0) ∧
    (∀ i j : Fin 7, i ≠ j → Function.Surjective (fun x : X => (x.val i,x.val j))) ∧
    ∀ (t : ℕ) (e : Fin t × Fin 3 ↪ Fin 7) (v : Fin t → Fin 3 → ℂ),
      (∀ x ∈ X, ∀ b, ∃ c : ℂ, ∀ i, x (e (b,i)) = c * v b i) → t = 0 := by
  obtain ⟨X,rank,h₂,h₄,onto⟩ := PEqualNP.Gct.sevenCoordinateExample
  refine ⟨X,rank,h₂,h₄,onto,?_⟩
  intro t e v fits
  by_contra positive
  let b : Fin t := ⟨0,Nat.pos_of_ne_zero positive⟩
  let i := e (b,0)
  let j := e (b,1)
  have ne : i ≠ j := fun h => (by decide : (0 : Fin 3) ≠ 1) (congrArg Prod.snd (e.injective h))
  obtain ⟨u,hu⟩ := onto i j ne (1,0)
  obtain ⟨w,hw⟩ := onto i j ne (0,1)
  obtain ⟨a,ha⟩ := fits u.val u.property b
  obtain ⟨c,hc⟩ := fits w.val w.property b
  have one : (1 : ℂ) = a * v b 0 := (congrArg Prod.fst hu).symm.trans (ha 0)
  have zero : (0 : ℂ) = c * v b 0 := (congrArg Prod.fst hw).symm.trans (hc 0)
  have last : (1 : ℂ) = c * v b 1 := (congrArg Prod.snd hw).symm.trans (hc 1)
  rcases mul_eq_zero.mp zero.symm with h | h
  · simp [h] at last
  · simp [h] at one
