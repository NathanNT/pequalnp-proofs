import PEqualNP.Defs

namespace PEqualNP.Research.Refute4669

private def col (mask : ℕ) (i : Fin 24) : Bool := mask.testBit i.val

private def base : List (Fin 24 → Bool) :=
  have x3 : Fin (24 : ℕ) → Fin (9 : ℕ) → Bool := fun (x3 : Fin (24 : ℕ)) (x4 : Fin (9 : ℕ)) => ([(3 : ℕ), (6 : ℕ), (12 : ℕ), (24 : ℕ), (17 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (264 : ℕ), (160 : ℕ), (320 : ℕ), (288 : ℕ), (42 : ℕ), (50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ)].getD ↑x3 (0 : ℕ)).testBit ↑x4;   have x4 : Fin (24 : ℕ) → List Bool := fun (x4 : Fin (24 : ℕ)) => List.ofFn (x3 x4) ++ [!x3 x4 (0 : Fin (9 : ℕ)), x3 x4 (Fin.ofNat (9 : ℕ) ((12 : ℕ) / (10 : ℕ))) || x3 x4 (Fin.ofNat (9 : ℕ) ((12 : ℕ) % (10 : ℕ)))];   have x5 : List (Fin (24 : ℕ) → Bool) := (List.ofFn fun (x5 : Fin (11 : ℕ)) (x6 : Fin (24 : ℕ)) => (x4 x6).getD (↑x5) Bool.false) ++ [fun (x5 : Fin (24 : ℕ)) => Bool.false, fun (x5 : Fin (24 : ℕ)) => Bool.true]; x5

private def initial : List (Fin 24 → Bool) := [col 5521457, col 8532035, col 3227782, col 430348, col 11083800, col 113184, col 902208, col 13501056, col 15731968, col 11255758, col 11759815, col 0, col 16777215]

private def trace : List (Fin 24 → Bool) := [col 5017400, col 560904, col 7684279, col 1045247, col 344247, col 905151, col 905215, col 15875395, col 15875007, col 15876095, col 4095]

private theorem base_table : base = initial := by
  decide +kernel

private theorem valid :
    ∀ j : Fin trace.length,
      let seen := initial ++ trace.take j.val
      (∃ a ∈ seen, trace.get j = fun i => !a i) ∨
      ∃ a ∈ seen, ∃ b ∈ seen,
        (trace.get j = fun i => a i && b i) ∨ (trace.get j = fun i => a i || b i) := by
  intro j
  change Fin 11 at j
  fin_cases j
  · exact Or.inl ⟨col 11759815, by decide +kernel, by decide +kernel⟩
  · exact Or.inr ⟨col 5017400, by decide +kernel, col 11255758, by decide +kernel, Or.inl (by decide +kernel)⟩
  · exact Or.inr ⟨col 3227782, by decide +kernel, col 5521457, by decide +kernel, Or.inr (by decide +kernel)⟩
  · exact Or.inl ⟨col 15731968, by decide +kernel, by decide +kernel⟩
  · exact Or.inr ⟨col 1045247, by decide +kernel, col 7684279, by decide +kernel, Or.inl (by decide +kernel)⟩
  · exact Or.inr ⟨col 560904, by decide +kernel, col 344247, by decide +kernel, Or.inr (by decide +kernel)⟩
  · exact Or.inr ⟨col 905151, by decide +kernel, col 902208, by decide +kernel, Or.inr (by decide +kernel)⟩
  · exact Or.inr ⟨col 15731968, by decide +kernel, col 8532035, by decide +kernel, Or.inr (by decide +kernel)⟩
  · exact Or.inl ⟨col 902208, by decide +kernel, by decide +kernel⟩
  · exact Or.inr ⟨col 15875007, by decide +kernel, col 15875395, by decide +kernel, Or.inr (by decide +kernel)⟩
  · exact Or.inr ⟨col 905215, by decide +kernel, col 15876095, by decide +kernel, Or.inl (by decide +kernel)⟩

end PEqualNP.Research.Refute4669

theorem PEqualNP.Research.Refute4669 : ¬ (∀ x1 ∈ [(12 : ℕ), (13 : ℕ), (15 : ℕ), (18 : ℕ), (23 : ℕ), (28 : ℕ)],   have x3 : Fin (24 : ℕ) → Fin (9 : ℕ) → Bool := fun (x3 : Fin (24 : ℕ)) (x4 : Fin (9 : ℕ)) => ([(3 : ℕ), (6 : ℕ), (12 : ℕ), (24 : ℕ), (17 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (264 : ℕ), (160 : ℕ), (320 : ℕ), (288 : ℕ), (42 : ℕ), (50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ)].getD ↑x3 (0 : ℕ)).testBit ↑x4;   have x4 : Fin (24 : ℕ) → List Bool := fun (x4 : Fin (24 : ℕ)) => List.ofFn (x3 x4) ++ [!x3 x4 (0 : Fin (9 : ℕ)), x3 x4 (Fin.ofNat (9 : ℕ) (x1 / (10 : ℕ))) || x3 x4 (Fin.ofNat (9 : ℕ) (x1 % (10 : ℕ)))];   have x5 : List (Fin (24 : ℕ) → Bool) := (List.ofFn fun (x5 : Fin (11 : ℕ)) (x6 : Fin (24 : ℕ)) => (x4 x6).getD (↑x5) Bool.false) ++ [fun (x5 : Fin (24 : ℕ)) => Bool.false, fun (x5 : Fin (24 : ℕ)) => Bool.true];   ∀ (x6 : List (Fin (24 : ℕ) → Bool)),     x6.length ≤ (13 : ℕ) →       (∀ (x8 : Fin x6.length),           have x9 : List (Fin (24 : ℕ) → Bool) := x5 ++ List.take (↑x8) x6;           (∃ x10 ∈ x9, x6.get x8 = fun (x11 : Fin (24 : ℕ)) => !x10 x11) ∨ ∃ x10 ∈ x9, ∃ x11 ∈ x9, (x6.get x8 = fun (x12 : Fin (24 : ℕ)) => x10 x12 && x11 x12) ∨ x6.get x8 = fun (x12 : Fin (24 : ℕ)) => x10 x12 || x11 x12) →         (fun (x9 : Fin (24 : ℕ)) => Decidable.decide (↑x9 < (12 : ℕ))) ∉ x5 ++ x6) := by
  intro h
  have h' := h 12 (by decide +kernel)
  change ∀ (x6 : List (Fin (24 : ℕ) → Bool)),     x6.length ≤ (13 : ℕ) →       (∀ (x8 : Fin x6.length),           have x9 : List (Fin (24 : ℕ) → Bool) := PEqualNP.Research.Refute4669.base ++ List.take (↑x8) x6;           (∃ x10 ∈ x9, x6.get x8 = fun (x11 : Fin (24 : ℕ)) => !x10 x11) ∨ ∃ x10 ∈ x9, ∃ x11 ∈ x9, (x6.get x8 = fun (x12 : Fin (24 : ℕ)) => x10 x12 && x11 x12) ∨ x6.get x8 = fun (x12 : Fin (24 : ℕ)) => x10 x12 || x11 x12) →         (fun (x9 : Fin (24 : ℕ)) => Decidable.decide (↑x9 < (12 : ℕ))) ∉ PEqualNP.Research.Refute4669.base ++ x6 at h'
  rw [PEqualNP.Research.Refute4669.base_table] at h'
  exact (h' PEqualNP.Research.Refute4669.trace (by decide +kernel) PEqualNP.Research.Refute4669.valid) (by decide +kernel)
