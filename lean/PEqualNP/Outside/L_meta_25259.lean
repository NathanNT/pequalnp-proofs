import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_25259 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50862 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨(⟨[⟨.or, [5, 3]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [10, 5]⟩, ⟨.not, [11]⟩, ⟨.and, [8, 12]⟩, ⟨.or, [7, 13]⟩], 14⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
