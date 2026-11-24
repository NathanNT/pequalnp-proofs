import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3420_549
    (padding :
      let init : List (BitVec 24) := [5521457, 8532035, 3227782, 430348, 11083800, 113184, 902208, 13501056, 15731968, 5689661]
      ∀ w : List (BitVec 24), w.length ≤ 24 →
        ∃ r : BitVec 24, r ∉ w ∧ r ≠ 0 ∧ r ≠ 16777215 ∧
          ∃ a ∈ init, ∃ b ∈ init, r = a ||| b)
    (core :
      ¬∃ w : List (BitVec 24), w.length = 24 ∧
        w.take 10 = [5521457, 8532035, 3227782, 430348, 11083800, 113184, 902208, 13501056, 15731968, 5689661] ∧
        w.getD 23 0 = 4095 ∧ (0 :: w).Nodup ∧ (16777215 : BitVec 24) ∉ w ∧
        (∀ j : ℕ, 0 < j → j < 14 →
          ∃ a ∈ w.take (9 + j), ∃ b ∈ w.take (9 + j),
            w.getD (9 + j) 0 = a &&& b ∨ w.getD (9 + j) 0 = a ||| b) ∧
        (∃ a ∈ (w.take 23).drop 10, ∃ b ∈ (w.take 23).drop 10,
          (4095 : BitVec 24) = a &&& b ∨ (4095 : BitVec 24) = a ||| b)) :
    ¬∃ (x1 : List (BitVec (24 : ℕ))), x1.length = (24 : ℕ) ∧
      List.take (10 : ℕ) x1 = [(5521457 : BitVec (24 : ℕ)), (8532035 : BitVec (24 : ℕ)), (3227782 : BitVec (24 : ℕ)), (430348 : BitVec (24 : ℕ)), (11083800 : BitVec (24 : ℕ)), (113184 : BitVec (24 : ℕ)), (902208 : BitVec (24 : ℕ)), (13501056 : BitVec (24 : ℕ)), (15731968 : BitVec (24 : ℕ)), (5689661 : BitVec (24 : ℕ))] ∧
      x1.getD (23 : ℕ) (0 : BitVec (24 : ℕ)) = (4095 : BitVec (24 : ℕ)) ∧
      ((0 : BitVec (24 : ℕ)) :: x1).Nodup ∧
      ∀ (x2 : ℕ), (0 : ℕ) < x2 →
        x2 < (15 : ℕ) →
        have x5 : BitVec (24 : ℕ) := x1.getD ((9 : ℕ) + x2) (0 : BitVec (24 : ℕ)); x5 = (16777215 : BitVec (24 : ℕ)) ∨ ∃ (x6 : BitVec (24 : ℕ)) (x7 : BitVec (24 : ℕ)), x6 ∈ List.take ((9 : ℕ) + x2) x1 ∧
      x7 ∈ List.take ((9 : ℕ) + x2) x1 ∧
      (x5 = x6 &&& x7 ∨ x5 = x6 ||| x7) := by
  intro candidate
  obtain ⟨w, hlen, hstart, hout, hnodup, hgate⟩ := candidate
  let init : List (BitVec 24) := [5521457, 8532035, 3227782, 430348, 11083800, 113184, 902208, 13501056, 15731968, 5689661]
  let full : BitVec 24 := 16777215
  let out : BitVec 24 := 4095
  have hfull : full = BitVec.allOnes 24 := rfl
  obtain ⟨r, hr, hr0, hrfull, p, hp, q, hq, hrdef⟩ := padding w (by omega)
  have hrfull' : r ≠ full := hrfull
  let rename (a : BitVec 24) := if a = full then r else a
  let v := w.map rename
  have hz : rename 0 = 0 := rfl
  have hlen' : v.length = 24 := by simp [v, hlen]
  have hinit : init.all (fun a => a != full) = true := by decide
  have hstart' : v.take 10 = init := by
    change (w.map rename).take 10 = init
    rw [← List.map_take, hstart]
    change init.map rename = init
    conv_rhs => rw [← List.map_id init]
    apply List.map_congr_left
    intro a ha
    have h := List.all_eq_true.mp hinit a ha
    have hne : a ≠ full := by simpa using h
    simp [rename, hne]
  have readMap (i : ℕ) : v.getD i 0 = rename (w.getD i 0) := by
    simpa only [v, hz] using List.getD_map w (0 : BitVec 24) (n := i) rename
  have hout' : v.getD 23 0 = out := by
    rw [readMap, hout]
    rfl
  have hnodup' : (0 :: v).Nodup := by
    have hi : ∀ a ∈ (0 :: w), ∀ b ∈ (0 :: w), rename a = rename b → a = b := by
      intro a ha b hb heq
      have hnot : r ∉ (0 :: w) := fun h => (List.mem_cons.mp h).elim hr0 hr
      by_cases ha' : a = full <;> by_cases hb' : b = full
      · exact ha'.trans hb'.symm
      · simp [rename, ha', hb'] at heq
        exact False.elim (hnot (heq ▸ hb))
      · simp [rename, ha', hb'] at heq
        exact False.elim (hnot (heq.symm ▸ ha))
      · simpa [rename, ha', hb'] using heq
    simpa only [List.map_cons, hz, v] using hnodup.map_on hi
  have hnofull : full ∉ v := by
    intro h
    obtain ⟨a, _, he⟩ := List.mem_map.mp h
    by_cases h' : a = full
    · exact hrfull' (by simpa only [rename, h', ite_eq_left rfl] using he)
    · exact h' (by simpa only [rename, ite_eq_right h'] using he)
  have noPrev (i : ℕ) (hi : i < w.length) : w.getD i 0 ∉ w.take i := by
    intro hm
    obtain ⟨k, hk, he⟩ := List.mem_take_iff_getElem.mp hm
    have hklen : k < w.length := by omega
    have eq : w[k] = w[i] := by
      rw [← List.getD_eq_getElem w (0 : BitVec 24) hi]
      exact he
    have same := List.nodup_iff_eq_of_getElem_eq.mp hnodup.of_cons k i hklen hi eq
    omega
  have build (j : ℕ) (hj : 0 < j) (hj' : j < 15) :
      ∃ a ∈ v.take (9 + j), ∃ b ∈ v.take (9 + j),
        v.getD (9 + j) 0 = a &&& b ∨ v.getD (9 + j) 0 = a ||| b := by
    by_cases htop : w.getD (9 + j) 0 = full
    · have mono := List.take_subset_take_left v (by omega : 10 ≤ 9 + j)
      have hpm : p ∈ v.take 10 := hstart'.symm ▸ hp
      have hqm : q ∈ v.take 10 := hstart'.symm ▸ hq
      refine ⟨p, mono hpm, q, mono hqm, Or.inr ?_⟩
      rw [readMap, htop]
      simpa only [rename, ite_eq_left rfl] using hrdef
    have hfresh := noPrev (9 + j) (by omega)
    rcases hgate j hj hj' with ht | ⟨a, b, ha, hb, hop⟩
    · exact False.elim (htop ht)
    have ha' : a ≠ full := by
      intro hf
      subst a
      apply hfresh
      rcases hop with han | hor
      · simpa only [han, hfull, BitVec.allOnes_and] using hb
      · simpa only [hor, hfull, BitVec.allOnes_or] using ha
    have hb' : b ≠ full := by
      intro hf
      subst b
      apply hfresh
      rcases hop with han | hor
      · simpa only [han, hfull, BitVec.and_allOnes] using ha
      · simpa only [hor, hfull, BitVec.or_allOnes] using hb
    have mem' (a : BitVec 24) (hm : a ∈ w.take (9 + j)) (hne : a ≠ full) :
        a ∈ v.take (9 + j) := by
      change a ∈ (w.map rename).take (9 + j)
      rw [← List.map_take]
      exact List.mem_map.mpr ⟨a, hm, by simp [rename, hne]⟩
    refine ⟨a, mem' a ha ha', b, mem' b hb hb', ?_⟩
    simpa only [readMap, rename, ite_eq_right htop] using hop
  have forbids (a b : BitVec 24) (ha : a ∈ init) :
      out ≠ a &&& b ∧ out ≠ a ||| b := by
    have check : init.all (fun t => (t &&& out != out) && (t ||| out != out)) = true := by
      decide
    have h : a &&& out ≠ out ∧ a ||| out ≠ out := by
      simpa using List.all_eq_true.mp check a ha
    constructor
    · intro he
      apply h.1
      rw [he, ← BitVec.and_assoc, BitVec.and_self]
    · intro he
      apply h.2
      rw [he, ← BitVec.or_assoc, BitVec.or_self]
  obtain ⟨a, ha, b, hb, hab⟩ := build 14 (by decide) (by decide)
  change a ∈ v.take 23 at ha
  change b ∈ v.take 23 at hb
  change v.getD 23 0 = a &&& b ∨ v.getD 23 0 = a ||| b at hab
  rw [hout'] at hab
  have late (a : BitVec 24) (ha : a ∈ v.take 23) (hn : a ∉ init) :
      a ∈ (v.take 23).drop 10 := by
    have hm : a ∈ (v.take 23).take 10 ++ (v.take 23).drop 10 := by simpa using ha
    rcases List.mem_append.mp hm with hl | hr
    · have h : (v.take 23).take 10 = init := by rw [List.take_take]; exact hstart'
      exact False.elim (hn (h ▸ hl))
    · exact hr
  have ha' : a ∉ init := fun hm => hab.elim (forbids a b hm).1 (forbids a b hm).2
  have hb' : b ∉ init := by
    intro hm
    have bad := forbids b a hm
    exact hab.elim
      (fun he => bad.1 (he.trans (BitVec.and_comm ..)))
      (fun he => bad.2 (he.trans (BitVec.or_comm ..)))
  exact core ⟨v, hlen', hstart', hout', hnodup', hnofull,
    fun j hj h => build j hj (by omega), ⟨a, late a ha ha', b, late b hb hb', hab⟩⟩
