import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_3206_418
    (support : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → ∃ (x4 : Finset ℕ), x4.card ≤ List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => !x5.op.eval [Bool.false]) x2.gates + (1 : ℕ) ∧ ∀ (x5 x6 : List Bool), x5.length = x1 → x6.length = x1 → (∀ x9 ∈ x4, x5.getD x9 Bool.false = x6.getD x9 Bool.false) → x2.eval x5 = x2.eval x6)
    (dense : ∀ x1 ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (4 : ℕ), (6 : ℕ), (8 : ℕ), (9 : ℕ), (10 : ℕ)],   ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (13 : ℕ) → 8 ≤ x3.gates.countP (fun g => !g.op.eval [false]) →         ∃ (x6 : Fin (9 : ℕ) → Bool),           have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ))];           x3.eval (x7 ++ [!x7.getD x1 Bool.false]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)))) :
    ∀ x1 ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (4 : ℕ), (6 : ℕ), (8 : ℕ), (9 : ℕ), (10 : ℕ)],   ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (13 : ℕ) →         ∃ (x6 : Fin (9 : ℕ) → Bool),           have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ))];           x3.eval (x7 ++ [!x7.getD x1 Bool.false]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  classical
  intro k hk C hfan hsize
  by_cases heavy : 8 ≤ C.gates.countP (fun g => !g.op.eval [false])
  · exact dense k hk C hfan hsize heavy
  obtain ⟨S, hS, determines⟩ := support 11 C hfan
  let F (x : Fin 9 → Bool) :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
    x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let wires (j : ℕ) (x : Fin 9 → Bool) :=
    let b := List.ofFn x ++ [x 0 && x 2]
    b ++ [!(b.getD j false)]
  change ∃ x, C.eval (wires k x) ≠ F x
  by_contra! computes
  let neighbor : Fin 9 → Fin 9 := ![1, 6, 3, 4, 3, 7, 8, 5, 6]
  let low (i j : Fin 9) := decide (j = neighbor i)
  let high (i j : Fin 9) := decide (j = neighbor i ∨ j = i)
  have flipped : ∀ i, F (low i) ≠ F (high i) := by decide
  have agree : ∀ (j : Fin 11) (i : Fin 9) (a : Fin 11),
      a.val ≠ i.val → (j.val ≠ i.val ∨ a.val ≠ 10) →
      (wires j.val (low i)).getD a.val false = (wires j.val (high i)).getD a.val false := by
    decide
  have hklt : k < 11 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    omega
  have covered (i : Fin 9) : i.val ∈ S ∨ (i.val = k ∧ 10 ∈ S) := by
    by_contra! absent
    apply flipped i
    rw [← computes (low i), ← computes (high i)]
    apply determines _ _ (by simp [wires]) (by simp [wires])
    intro a ha
    by_cases hlt : a < 11
    · apply agree ⟨k, hklt⟩ i ⟨a, hlt⟩
      · exact fun eq => absent.1 (eq ▸ ha)
      · by_cases hki : k = i.val
        · exact Or.inr (fun eq => absent.2 hki.symm (eq ▸ ha))
        · exact Or.inl hki
    · rw [List.getD_eq_default _ _ (by simpa [wires] using Nat.le_of_not_gt hlt),
          List.getD_eq_default _ _ (by simpa [wires] using Nat.le_of_not_gt hlt)]
  let pick (i : Fin 9) : ↥S := if h : i.val ∈ S then ⟨i.val, h⟩
    else ⟨10, ((covered i).resolve_left h).2⟩
  have hinj : Function.Injective pick := by
    intro i j hij
    have eq := congrArg Subtype.val hij
    by_cases hi : i.val ∈ S <;> by_cases hj : j.val ∈ S
    · exact Fin.ext (by simpa [pick, hi, hj] using eq)
    · simp [pick, hi, hj] at eq
      omega
    · simp [pick, hi, hj] at eq
      omega
    · exact Fin.ext (((covered i).resolve_left hi).1.trans ((covered j).resolve_left hj).1.symm)
  have card := Fintype.card_le_of_injective pick hinj
  simp only [Fintype.card_fin, Fintype.card_coe] at card
  omega
