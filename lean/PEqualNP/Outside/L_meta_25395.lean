import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_25395 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6408637 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨(⟨[⟨.or, [2, 3]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [1, 7]⟩, ⟨.and, [6, 5]⟩, ⟨.or, [3, 0]⟩, ⟨.or, [4, 10]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [9, 12]⟩, ⟨.not, [13]⟩, ⟨.and, [14, 8]⟩], 15⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
