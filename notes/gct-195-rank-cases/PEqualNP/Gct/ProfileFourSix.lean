import PEqualNP.Gct.QuarticEquality
import Mathlib.Tactic

namespace PEqualNP.Gct.ProfileBounds
open Finset

-- Distinct-index sum identities from the checked L-gct-180, PR 32.
private lemma sum_ite_eq_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℂ) (a : ι) :
    (∑ x : ι, if a = x then f x else 0) = f a := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro x _ hxa
    simp [hxa.symm]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

private lemma sum_omit_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℂ) (a : ι) :
    (∑ x : ι, if a = x then (0 : ℂ) else f x) = (∑ x : ι, f x) - f a := by
  have h : (∑ x : ι, if a = x then (0 : ℂ) else f x) +
      (∑ x : ι, if a = x then f x else 0) = ∑ x : ι, f x := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> ring
  rw [sum_ite_eq_self] at h
  linear_combination h

private lemma sum_omit_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℂ) {a b : ι} (hab : a ≠ b) :
    (∑ x : ι, if a = x ∨ b = x then (0 : ℂ) else f x) = (∑ x : ι, f x) - f a - f b := by
  have h : (∑ x : ι, if a = x ∨ b = x then (0 : ℂ) else f x) +
      (∑ x : ι, if a = x then f x else 0) +
      (∑ x : ι, if b = x then f x else 0) = ∑ x : ι, f x := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h1 : a = x <;> by_cases h2 : b = x
    · exact absurd (h1.trans h2.symm) hab
    · simp [h1, h2]
    · simp [h1, h2]
    · simp [h1, h2]
  rw [sum_ite_eq_self, sum_ite_eq_self] at h
  linear_combination h

private lemma sum_omit_three {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℂ) {a b c : ι} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (∑ x : ι, if a = x ∨ b = x ∨ c = x then (0 : ℂ) else f x) =
      (∑ x : ι, f x) - f a - f b - f c := by
  have h : (∑ x : ι, if a = x ∨ b = x ∨ c = x then (0 : ℂ) else f x) +
      (∑ x : ι, if a = x then f x else 0) +
      (∑ x : ι, if b = x then f x else 0) +
      (∑ x : ι, if c = x then f x else 0) = ∑ x : ι, f x := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h1 : a = x <;> by_cases h2 : b = x <;> by_cases h3 : c = x
    · exact absurd (h1.trans h2.symm) hab
    · exact absurd (h1.trans h2.symm) hab
    · exact absurd (h1.trans h3.symm) hac
    · simp [h1, h2, h3]
    · exact absurd (h2.trans h3.symm) hbc
    · simp [h1, h2, h3]
    · simp [h1, h2, h3]
    · simp [h1, h2, h3]
  rw [sum_ite_eq_self, sum_ite_eq_self, sum_ite_eq_self] at h
  linear_combination h

private lemma sum_distinct2_gen {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : ι → ℂ) :
    (∑ j : ι, ∑ l : ι, if j = l then (0 : ℂ) else f j * g l) =
      (∑ j : ι, f j) * (∑ l : ι, g l) - ∑ j : ι, f j * g j := by
  have h : ∀ j : ι, (∑ l : ι, if j = l then (0 : ℂ) else f j * g l) =
      f j * (∑ l : ι, g l) - f j * g j := by
    intro j
    have h1 : (∑ l : ι, if j = l then (0 : ℂ) else f j * g l) =
        f j * (∑ l : ι, if j = l then (0 : ℂ) else g l) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      split_ifs <;> ring
    rw [h1, sum_omit_one g j]
    ring
  simp_rw [h, Finset.sum_sub_distrib, ← Finset.sum_mul]

private lemma sum_distinct3_gen {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g h : ι → ℂ) (hg : ∑ l : ι, g l = 0) (hh : ∑ m : ι, h m = 0) :
    (∑ j : ι, ∑ l : ι, ∑ m : ι,
      if j = l ∨ j = m ∨ l = m then (0 : ℂ) else f j * g l * h m) =
      2 * (∑ j : ι, f j * g j * h j) - (∑ j : ι, f j) * (∑ l : ι, g l * h l) := by
  have step1 : ∀ j l : ι,
      (∑ m : ι, if j = l ∨ j = m ∨ l = m then (0 : ℂ) else f j * g l * h m) =
        if j = l then 0 else -(f j * h j * g l) - f j * (g l * h l) := by
    intro j l
    by_cases hjl : j = l
    · simp [hjl]
    · simp only [hjl, false_or, ite_false]
      have h1 : (∑ m : ι, if j = m ∨ l = m then (0 : ℂ) else f j * g l * h m) =
          f j * g l * (∑ m : ι, if j = m ∨ l = m then (0 : ℂ) else h m) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        split_ifs <;> ring
      rw [h1, sum_omit_two h hjl, hh]
      ring
  simp_rw [step1]
  have split_sum :
      (∑ j : ι, ∑ l : ι, if j = l then (0 : ℂ) else -(f j * h j * g l) - f j * (g l * h l)) =
        -(∑ j : ι, ∑ l : ι, if j = l then (0 : ℂ) else (f j * h j) * g l) -
        (∑ j : ι, ∑ l : ι, if j = l then (0 : ℂ) else f j * (g l * h l)) := by
    simp_rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> ring
  rw [split_sum, sum_distinct2_gen (fun j => f j * h j) g,
    sum_distinct2_gen f (fun l => g l * h l), hg]
  have hmul : (∑ j : ι, f j * h j * g j) = ∑ j : ι, f j * g j * h j :=
    Finset.sum_congr rfl fun j _ => by ring
  have hmul2 : (∑ j : ι, f j * (g j * h j)) = ∑ j : ι, f j * g j * h j :=
    Finset.sum_congr rfl fun j _ => by ring
  rw [hmul, hmul2]
  ring

private lemma sum_distinct4 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f0 f1 f2 f3 : ι → ℂ)
    (h0 : ∑ j : ι, f0 j = 0) (h1 : ∑ j : ι, f1 j = 0)
    (h2 : ∑ j : ι, f2 j = 0) (h3 : ∑ j : ι, f3 j = 0) :
    (∑ j : ι, ∑ l : ι, ∑ m : ι, ∑ n : ι,
      if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then (0 : ℂ)
      else f0 j * f1 l * f2 m * f3 n) =
      (∑ j : ι, f0 j * f3 j) * (∑ l : ι, f1 l * f2 l) +
      (∑ j : ι, f1 j * f3 j) * (∑ l : ι, f0 l * f2 l) +
      (∑ j : ι, f2 j * f3 j) * (∑ l : ι, f0 l * f1 l) -
      6 * (∑ j : ι, f0 j * f1 j * f2 j * f3 j) := by
  have step1 : ∀ j l m : ι,
      (∑ n : ι, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then (0 : ℂ)
        else f0 j * f1 l * f2 m * f3 n) =
        if j = l ∨ j = m ∨ l = m then 0
        else -(f0 j * f3 j * f1 l * f2 m) - (f1 l * f3 l * f0 j * f2 m) -
          (f2 m * f3 m * f0 j * f1 l) := by
    intro j l m
    by_cases hcond : j = l ∨ j = m ∨ l = m
    · have hcond' : ∀ n : ι, j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n := by
        intro n
        rcases hcond with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      simp [hcond, hcond']
    · push Not at hcond
      rcases hcond with ⟨hjl, hjm, hlm⟩
      have hn : ∀ n : ι,
          (if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then (0 : ℂ)
            else f0 j * f1 l * f2 m * f3 n) =
          f0 j * f1 l * f2 m * (if j = n ∨ l = n ∨ m = n then (0 : ℂ) else f3 n) := by
        intro n
        by_cases hjn : j = n <;> by_cases hln : l = n <;> by_cases hmn : m = n <;>
          simp [hjl, hjm, hlm, hjn, hln, hmn]
      simp_rw [hn, ← Finset.mul_sum, sum_omit_three f3 hjl hjm hlm, h3]
      simp only [hjl, hjm, hlm, or_self, ite_false]
      ring
  simp_rw [step1]
  have split3 :
      (∑ j : ι, ∑ l : ι, ∑ m : ι,
        if j = l ∨ j = m ∨ l = m then (0 : ℂ)
        else -(f0 j * f3 j * f1 l * f2 m) - (f1 l * f3 l * f0 j * f2 m) -
          (f2 m * f3 m * f0 j * f1 l)) =
      -(∑ j : ι, ∑ l : ι, ∑ m : ι,
          if j = l ∨ j = m ∨ l = m then (0 : ℂ) else (f0 j * f3 j) * f1 l * f2 m) -
      (∑ l : ι, ∑ j : ι, ∑ m : ι,
          if l = j ∨ l = m ∨ j = m then (0 : ℂ) else (f1 l * f3 l) * f0 j * f2 m) -
      (∑ m : ι, ∑ j : ι, ∑ l : ι,
          if m = j ∨ m = l ∨ j = l then (0 : ℂ) else (f2 m * f3 m) * f0 j * f1 l) := by
    have t2 :
        (∑ l : ι, ∑ j : ι, ∑ m : ι,
          if l = j ∨ l = m ∨ j = m then (0 : ℂ) else (f1 l * f3 l) * f0 j * f2 m) =
        ∑ j : ι, ∑ l : ι, ∑ m : ι,
          if j = l ∨ j = m ∨ l = m then (0 : ℂ) else f1 l * f3 l * f0 j * f2 m := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ =>
        Finset.sum_congr rfl fun m _ => ?_
      have heq : (l = j ∨ l = m ∨ j = m) ↔ (j = l ∨ j = m ∨ l = m) := by tauto
      simp only [heq]
    have t3 :
        (∑ m : ι, ∑ j : ι, ∑ l : ι,
          if m = j ∨ m = l ∨ j = l then (0 : ℂ) else (f2 m * f3 m) * f0 j * f1 l) =
        ∑ j : ι, ∑ l : ι, ∑ m : ι,
          if j = l ∨ j = m ∨ l = m then (0 : ℂ) else f2 m * f3 m * f0 j * f1 l := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
        (f := fun m l => if m = _ ∨ m = l ∨ _ = l then (0 : ℂ) else _)]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ =>
        Finset.sum_congr rfl fun m _ => ?_
      have heq : (m = j ∨ m = l ∨ j = l) ↔ (j = l ∨ j = m ∨ l = m) := by tauto
      simp only [heq]
    rw [t2, t3]
    simp_rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> ring
  rw [split3,
    sum_distinct3_gen (fun j => f0 j * f3 j) f1 f2 h1 h2,
    sum_distinct3_gen (fun l => f1 l * f3 l) f0 f2 h0 h2,
    sum_distinct3_gen (fun m => f2 m * f3 m) f0 f1 h0 h1]
  have q1 : (∑ j : ι, f0 j * f3 j * f1 j * f2 j) = ∑ j : ι, f0 j * f1 j * f2 j * f3 j :=
    Finset.sum_congr rfl fun j _ => by ring
  have q2 : (∑ j : ι, f1 j * f3 j * f0 j * f2 j) = ∑ j : ι, f0 j * f1 j * f2 j * f3 j :=
    Finset.sum_congr rfl fun j _ => by ring
  have q3 : (∑ j : ι, f2 j * f3 j * f0 j * f1 j) = ∑ j : ι, f0 j * f1 j * f2 j * f3 j :=
    Finset.sum_congr rfl fun j _ => by ring
  rw [q1, q2, q3]
  ring



theorem profileMoments (x : Fin 6 → ℂ)
    (h : let t : Fin 4 × Fin 6 → ℂ := fun p => (if p.1 = 3 then -1 else 3) * x p.2
    (∑ i : Fin 4, ∑ j, t (i,j)) = 0 ∧
    (∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4,
      if a < b then t (a,j) * t (b,l) else 0) = 0 ∧
    (∑ j, ∑ l, ∑ m, ∑ n, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0
      else t (0,j) * t (1,l) * t (2,m) * t (3,n)) = 0) :
    (∑ j, x j ^ 2) = 0 ∧ (∑ j, x j ^ 4) = 0 := by
  obtain ⟨h₁,h₂,h₄⟩ := h
  have sum0 : ∑ j, x j = 0 := by
    simp only [Fin.sum_univ_four] at h₁
    norm_num at h₁
    simp only [← mul_sum] at h₁
    linear_combination h₁ / 8
  have pair (j l : Fin 6) :
      (∑ a : Fin 4, ∑ b : Fin 4, if a < b then
        ((if a = 3 then (-1 : ℂ) else 3) * x j) * ((if b = 3 then (-1 : ℂ) else 3) * x l) else 0) =
      18 * (x j * x l) := by
    norm_num [Fin.sum_univ_four]; ring
  simp only [pair] at h₂
  have double : (∑ j, ∑ l, if j = l then (0 : ℂ) else x j * x l) = - ∑ j, x j ^ 2 := by
    rw [sum_distinct2_gen, sum0]; simp [pow_two]
  have pull2 : (∑ j, ∑ l, if j = l then (0 : ℂ) else 18 * (x j * x l)) =
      18 * (∑ j, ∑ l, if j = l then (0 : ℂ) else x j * x l) := by
    simp only [mul_sum]; apply sum_congr rfl; intro j _
    apply sum_congr rfl; intro l _; split_ifs <;> simp
  rw [pull2,double] at h₂
  have p₂ : (∑ j, x j ^ 2) = 0 := by linear_combination -h₂ / 18
  have fourth := sum_distinct4 x x x x sum0 sum0 sum0 sum0
  have sq : ∑ j, x j * x j = 0 := by simpa only [pow_two] using p₂
  simp only [sq,mul_zero,add_zero,zero_sub] at fourth
  have pull4 :
      (∑ j, ∑ l, ∑ m, ∑ n, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then (0 : ℂ)
        else (3*x j)*(3*x l)*(3*x m)*(-1*x n)) =
      -27 * (∑ j, ∑ l, ∑ m, ∑ n, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then (0 : ℂ)
        else x j*x l*x m*x n) := by
    simp only [mul_sum]
    repeat' (apply sum_congr rfl; intro _ _)
    split_ifs <;> ring
  change (∑ j, ∑ l, ∑ m, ∑ n, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then (0 : ℂ)
        else (3*x j)*(3*x l)*(3*x m)*(-1*x n)) = 0 at h₄
  rw [pull4,fourth] at h₄
  have p₄ : (∑ j, x j * x j * x j * x j) = 0 := by linear_combination h₄ / 162
  refine ⟨p₂,?_⟩
  simpa only [pow_succ,pow_zero,one_mul] using p₄

end PEqualNP.Gct.ProfileBounds

open PEqualNP.Gct in
theorem PEqualNP.Gct.ProfileFourSix :
∀ (X : Submodule ℂ (Fin 6 → ℂ)),
  (∀ x ∈ X, let t : Fin 4 × Fin 6 → ℂ := fun p => (if p.1 = 3 then -1 else 3) * x p.2
    (∑ i : Fin 4, ∑ j, t (i,j)) = 0 ∧
    (∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4,
      if a < b then t (a,j) * t (b,l) else 0) = 0 ∧
    (∑ j, ∑ l, ∑ m, ∑ n, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0
      else t (0,j) * t (1,l) * t (2,m) * t (3,n)) = 0) →
  Module.finrank ℂ X ≤ 2 ∧ (Module.finrank ℂ X = 2 →
    ∃ (e : Fin (Module.finrank ℂ X) × Fin 3 ≃ Fin 6)
      (v : Fin (Module.finrank ℂ X) → Fin 3 → ℂ),
      (∀ b, v b ≠ 0 ∧ ∑ i, v b i ^ 2 = 0 ∧ ∑ i, v b i ^ 4 = 0) ∧
      ∀ z : Fin (Module.finrank ℂ X) → Fin 3 → ℂ,
        (∃ x ∈ X, ∀ b i, x (e (b,i)) = z b i) ↔
        ∃ c : Fin (Module.finrank ℂ X) → ℂ, ∀ b i, z b i = c b * v b i) := by
  intro X level
  have h₂ := fun x hx => (ProfileBounds.profileMoments x (level x hx)).1
  have h₄ := fun x hx => (ProfileBounds.profileMoments x (level x hx)).2
  obtain ⟨bound,_⟩ := TriplePacking.decompose 6 (Fin 6) (Fintype.card_fin 6) X X
    (TriplePacking.polarize X h₂ h₄) le_rfl
  exact ⟨by omega, fun h => QuarticEquality 6 X h₂ h₄ (by omega)⟩

