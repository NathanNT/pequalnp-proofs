import Mathlib.Data.Finset.Card
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3266

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def cost (g : Gate) : ℕ :=
  if !g.op.eval [false] then 1 else 0

lemma gateSupport (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) :
    ∃ R : Finset ℕ, R.card ≤ cost g + 1 ∧
      ∀ x y : List Bool, (∀ i ∈ R, x.getD i false = y.getD i false) →
        g.op.eval (g.inputs.map fun i => x.getD i false) =
        g.op.eval (g.inputs.map fun i => y.getD i false) := by
  rcases g with ⟨op, inputs⟩
  rcases hg with ⟨hop, hlen⟩
  have allInputs (x y : List Bool)
      (h : ∀ i ∈ inputs.toFinset, x.getD i false = y.getD i false) :
      (inputs.map fun i => x.getD i false) =
        (inputs.map fun i => y.getD i false) :=
    List.map_congr_left (fun i hi => h i (List.mem_toFinset.mpr hi))
  cases op with
  | and =>
      refine ⟨inputs.toFinset, ?_, ?_⟩
      · simpa [cost, GateOp.eval] using (List.toFinset_card_le inputs).trans hlen
      · intro x y h
        rw [allInputs x y h]
  | or =>
      refine ⟨inputs.toFinset, ?_, ?_⟩
      · simpa [cost, GateOp.eval] using (List.toFinset_card_le inputs).trans hlen
      · intro x y h
        rw [allInputs x y h]
  | not =>
      cases inputs with
      | nil =>
          exact ⟨∅, by simp, fun _ _ _ => rfl⟩
      | cons i rest =>
          refine ⟨{i}, by simp, ?_⟩
          intro x y h
          have hi := h i (Finset.mem_singleton_self i)
          simpa [GateOp.eval] using congrArg Bool.not hi
  | mod m => simp at hop
  | maj => simp at hop

lemma getD_push (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  by_cases hlt : i < w.length
  · have hne : i ≠ w.length := Nat.ne_of_lt hlt
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, hne]
  · by_cases heq : i = w.length
    · subst i
      rw [ite_eq_left rfl, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)]
      simp
    · have hge : w.length ≤ i := by omega
      have hsub : i - w.length ≠ 0 := by omega
      rw [ite_eq_right heq, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right hge, List.getElem?_eq_none hge]
      simp [hsub]

lemma foldSupport (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) (n : ℕ) (S : Finset ℕ) :
    ∃ T : Finset ℕ, T.card ≤ gs.countP (fun g => !g.op.eval [false]) + S.card ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
        (∀ i ∈ T, x.getD i false = y.getD i false) →
        ∀ i ∈ S, (gs.foldl step x).getD i false = (gs.foldl step y).getD i false := by
  induction gs generalizing n S with
  | nil =>
      exact ⟨S, by simp, fun _ _ _ _ h => h⟩
  | cons g gs ih =>
      obtain ⟨T, hTcard, hT⟩ := ih (fun h hh => hg h (List.mem_cons_of_mem _ hh)) (n + 1) S
      obtain ⟨R, hRcard, hR⟩ := gateSupport g (hg g (List.mem_cons_self ..))
      let U := if n ∈ T then R else ∅
      refine ⟨T.erase n ∪ U, ?_, ?_⟩
      · rw [List.countP_cons]
        change (T.erase n ∪ U).card ≤ gs.countP (fun g => !g.op.eval [false]) + cost g + S.card
        have hUnion := Finset.card_union_le (T.erase n) U
        by_cases hn : n ∈ T
        · have hErase := Finset.card_erase_add_one hn
          have hUcard : U.card = R.card := by simp [U, hn]
          omega
        · simpa [U, hn, Finset.erase_eq_of_notMem hn] using
            hTcard.trans (show _ ≤ _ by omega)
      · intro x y hx hy hxy j hj
        have hx' : (step x g).length = n + 1 := by simp [step, hx]
        have hy' : (step y g).length = n + 1 := by simp [step, hy]
        apply hT _ _ hx' hy' _ j hj
        intro i hi
        simp only [step, getD_push, hx, hy]
        by_cases heq : i = n
        · subst i
          have hreads : ∀ k ∈ R, x.getD k false = y.getD k false := by
            intro k hk
            exact hxy k (Finset.mem_union_right _ (by simpa [U, hi] using hk))
          simpa using hR x y hreads
        · simp only [ite_eq_right heq]
          exact hxy i (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq, hi⟩))

end PEqualNP.Outside.L_meta_3266

theorem PEqualNP.Outside.L_meta_3266 :
    ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 →
      ∃ (x4 : Finset ℕ),
        x4.card ≤ List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) =>
          !x5.op.eval [Bool.false]) x2.gates + (1 : ℕ) ∧
        ∀ (x5 x6 : List Bool), x5.length = x1 → x6.length = x1 →
          (∀ x9 ∈ x4, x5.getD x9 Bool.false = x6.getD x9 Bool.false) → x2.eval x5 = x2.eval x6 := by
  intro n C hC
  obtain ⟨T, hcard, hT⟩ := PEqualNP.Outside.L_meta_3266.foldSupport C.gates hC n {C.output}
  refine ⟨T, by simpa using hcard, ?_⟩
  intro x y hx hy h
  exact hT x y hx hy h C.output (Finset.mem_singleton_self _)
