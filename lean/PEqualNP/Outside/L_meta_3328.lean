import Mathlib.Data.List.Nodup

theorem PEqualNP.Outside.L_meta_3328 : have x1 : List ℕ → ℕ → Prop := fun (x1 : List ℕ) (x2 : ℕ) => ∃ x3 ∈ x1, ∃ x4 ∈ x1, x2 = x3 &&& x4 ∨ x2 = x3 ||| x4; have x2 : List ℕ → List ℕ → Prop := fun (x2 x3 : List ℕ) => ∀ (x4 : Fin x3.length), x1 (x2 ++ List.take (↑x4) x3) (x3.get x4); ∀ (x3 : List ℕ) (x4 x5 : ℕ) (x6 : List ℕ), x5 ∉ x3 → x1 x3 x4 → x2 (x4 :: x3) x6 → x1 (x4 :: x3 ++ x6) x5 → ∃ (x11 : List ℕ), x11.length ≤ x6.length + (2 : ℕ) ∧ x11.Nodup ∧ (∀ x12 ∈ x11, x12 ∉ x3) ∧ x5 ∈ x11 ∧ x2 x3 x11 := by
  intro make valid base first goal steps absent first_ok steps_ok last_ok
  have transport {u v : List ℕ} (sub : ∀ a ∈ u, a ∈ v) {x : ℕ} (h : make u x) : make v x := by
    obtain ⟨a, ha, b, hb, op⟩ := h
    exact ⟨a, sub _ ha, b, sub _ hb, op⟩
  have extend {u v : List ℕ} (sub : ∀ a ∈ u, a ∈ v) (s : List ℕ) (h : valid u s) : valid v s := by
    intro i
    apply transport (u := u ++ s.take i.val) _ (h i)
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact List.mem_append_left _ (sub _ h)
    · exact List.mem_append_right _ h
  have consRule (u : List ℕ) (a : ℕ) (s : List ℕ) :
      valid u (a :: s) ↔ make u a ∧ valid (u ++ [a]) s := by
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · simpa using h ⟨0, by simp⟩
      · intro i
        simpa [List.append_assoc] using h ⟨i.val+1, by simpa using i.isLt⟩
    · rintro ⟨ha, hs⟩ i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using ha
      · simpa [List.append_assoc] using hs j
  have normalize (s : List ℕ) : ∀ (u : List ℕ), valid u s →
      ∃ t : List ℕ, t.length ≤ s.length ∧ t.Nodup ∧ (∀ z ∈ t, z ∉ u) ∧
      (∀ z ∈ s, z ∈ u ++ t) ∧ valid u t := by
    induction s with
    | nil =>
      intro u _
      exact ⟨[], by simp, by simp, by simp, by simp, fun i => Fin.elim0 i⟩
    | cons a s ih =>
      intro u h
      obtain ⟨ha, hs⟩ := (consRule u a s).mp h
      by_cases seen : a ∈ u
      · have sub : ∀ z ∈ u ++ [a], z ∈ u := by
          intro z hz
          rcases List.mem_append.mp hz with hz | hz
          · exact hz
          · simpa only [List.mem_singleton.mp hz] using seen
        obtain ⟨t, hl, hn, hf, hc, hv⟩ := ih u (extend sub s hs)
        refine ⟨t, by simpa using Nat.le_trans hl (Nat.le_succ _), hn, hf, ?_, hv⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact List.mem_append_left _ seen
        · exact hc z hz
      · obtain ⟨t, hl, hn, hf, hc, hv⟩ := ih (u ++ [a]) hs
        have fresh : a ∉ t := fun h => hf a h (by simp)
        refine ⟨a :: t, by simpa using hl, List.nodup_cons.mpr ⟨fresh, hn⟩, ?_, ?_, (consRule u a t).mpr ⟨ha, hv⟩⟩
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact seen
          · exact fun m => hf z hz (List.mem_append_left _ m)
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · simp
          · simpa [List.append_assoc] using hc z hz
  have start : valid base (first :: steps) := by
    apply (consRule base first steps).mpr
    exact ⟨first_ok, extend (by intro z hz; simpa [or_comm] using hz) steps steps_ok⟩
  let raw := first :: steps
  have all_ok : valid base (raw ++ [goal]) := by
    intro i
    by_cases hi : i.val < raw.length
    · have h := start ⟨i.val, hi⟩
      change make (base ++ (raw ++ [goal]).take i.val) ((raw ++ [goal]).get i)
      rw [List.take_append_of_le_length (Nat.le_of_lt hi), List.get_eq_getElem, List.getElem_append_left hi]
      exact h
    · have he : i.val = raw.length := by have := i.isLt; simp at this; omega
      have htake : (raw ++ [goal]).take i.val = raw := by rw [he, List.take_left]
      have hget : (raw ++ [goal]).get i = goal := by simp [List.get_eq_getElem, he]
      rw [htake, hget]
      apply transport (u := first :: base ++ steps) _ last_ok
      intro z hz
      simpa [raw, or_left_comm, or_assoc, or_comm] using hz
  obtain ⟨t, hl, hn, hf, hc, hv⟩ := normalize (raw ++ [goal]) base all_ok
  exact ⟨t, by simpa [raw] using hl, hn, hf, (List.mem_append.mp (hc goal (by simp))).resolve_left absent, hv⟩
