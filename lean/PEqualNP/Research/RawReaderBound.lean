import PEqualNP.Defs.CircuitLowerBounds
import PEqualNP.Research.SensitiveProjection

namespace PEqualNP.Research.RawReaderBound

open PEqualNP.CircuitLowerBounds

private def gateValue (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map (fun i => w.getD i false))

private def Agrees (v : ℕ) (w z : List Bool) : Prop :=
  ∀ i, i ≠ v → w.getD i false = z.getD i false

private theorem prefix_value {w : List Bool} {i : ℕ} (h : i < w.length) (b : Bool) :
    (w ++ [b]).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left h]

private theorem append_agrees {v : ℕ} {w z : List Bool} (hlen : w.length = z.length)
    (h : Agrees v w z) (b : Bool) : Agrees v (w ++ [b]) (z ++ [b]) := by
  intro i hi
  by_cases hlt : i < w.length
  · simpa only [prefix_value hlt, prefix_value (hlen ▸ hlt)] using h i hi
  · simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (Nat.le_of_not_gt hlt),
      List.getElem?_append_right (show z.length ≤ i by omega),hlen]

private def Covered {n : ℕ} (v : Fin n) (S T : Finset (Fin n)) (g : Gate) : Prop :=
  v.val ∈ g.inputs → ∃ p ∈ S, p.val ∈ g.inputs ∧
    ((p ∈ T ∧ g.op = .or) ∨ (p ∉ T ∧ g.op = .and))

private theorem pinned_gate {n : ℕ} {v : Fin n} {S T : Finset (Fin n)} {g : Gate}
    {w z : List Bool} (hv : v ∉ S) (hcov : Covered v S T g) (h : Agrees v.val w z)
    (pins : ∀ p ∈ S, w.getD p.val false = decide (p ∈ T)) :
    gateValue w g = gateValue z g := by
  by_cases hread : v.val ∈ g.inputs
  · obtain ⟨p, hp, hpin, hor | hand⟩ := hcov hread
    · obtain ⟨ht, hop⟩ := hor
      have hw : w.getD p.val false = true := by simpa [ht] using pins p hp
      have hz := (h p.val (fun he => hv (Fin.ext he ▸ hp))).symm.trans hw
      have force (l : List Bool) (hl : l.getD p.val false = true) : gateValue l g = true := by
        simp only [gateValue, hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
        exact ⟨true, ⟨p.val,hpin,hl⟩,rfl⟩
      exact (force w hw).trans (force z hz).symm
    · obtain ⟨ht, hop⟩ := hand
      have hw : w.getD p.val false = false := by simpa [ht] using pins p hp
      have hz := (h p.val (fun he => hv (Fin.ext he ▸ hp))).symm.trans hw
      have force (l : List Bool) (hl : l.getD p.val false = false) : gateValue l g = false := by
        apply Bool.eq_false_iff.mpr
        intro hval
        have ht := List.all_eq_true.mp (show (g.inputs.map (fun i => l.getD i false)).all id = true by
          simpa only [gateValue,hop,GateOp.eval] using hval)
        exact Bool.false_ne_true (ht false (List.mem_map.mpr ⟨p.val,hpin,hl⟩))
      exact (force w hw).trans (force z hz).symm
  · apply congrArg g.op.eval
    exact List.map_congr_left (fun i hi => h i (fun he => hread (he ▸ hi)))

private theorem run_pinned {n : ℕ} {v : Fin n} {S T : Finset (Fin n)} (hv : v ∉ S)
    (gs : List Gate) (hcov : ∀ g ∈ gs, Covered v S T g) (w z : List Bool)
    (hlen : w.length = z.length) (hlenN : n ≤ w.length) (h : Agrees v.val w z)
    (pins : ∀ p ∈ S, w.getD p.val false = decide (p ∈ T)) :
    Agrees v.val (gs.foldl (fun l g => l ++ [gateValue l g]) w)
      (gs.foldl (fun l g => l ++ [gateValue l g]) z) := by
  induction gs generalizing w z with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have he := pinned_gate hv (hcov g (by simp)) h pins
    rw [he]
    apply ih (fun t ht => hcov t (by simp [ht])) _ _ (by simp [hlen])
      (by simp; omega) (append_agrees hlen h _)
    intro p hp
    rw [prefix_value (lt_of_lt_of_le p.isLt hlenN)]
    exact pins p hp

private theorem raw {n : ℕ} (x : Fin n → Bool) (p : Fin n) :
    (List.ofFn x).getD p.val false = x p := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

private theorem raw_output {n : ℕ} (C : Circuit) (x : Fin n → Bool) (v : Fin n)
    (hout : C.output = v.val) : C.eval (List.ofFn x) = x v := by
  have keep (gs : List Gate) (w : List Bool) (hlt : v.val < w.length) :
      (gs.foldl (fun l g => l ++ [gateValue l g]) w).getD v.val false = w.getD v.val false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [ih _ (by simp; omega), prefix_value hlt]
  unfold Circuit.eval Circuit.wires
  rw [hout]
  exact (keep C.gates _ (by simp)).trans (raw x v)

end PEqualNP.Research.RawReaderBound

open PEqualNP.CircuitLowerBounds PEqualNP.Research.SensitiveProjection
open PEqualNP.Research.RawReaderBound in
theorem PEqualNP.Research.RawReaderBound :
∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n),
  (∀ w : G.Walk v v, w.IsCycle → w.length ≠ 4) →
  ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
  (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
    ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) →
  ∀ (S T : Finset (Fin n)), v ∉ S → T ⊆ S → (¬ ∃ i ∈ T, ∃ j ∈ T, G.Adj i j) →
  (∀ g ∈ C.gates, v.val ∈ g.inputs → ∃ p ∈ S, p.val ∈ g.inputs ∧
    ((p ∈ T ∧ g.op = .or) ∨ (p ∉ T ∧ g.op = .and))) →
  G.degree v ≤ S.card := by
  intro n G _ v hs C correct S T hv hTS hn readers
  by_contra! small
  have hout : C.output ≠ v.val := by
    intro he
    let x : Fin n → Bool := fun i => decide (i = v)
    obtain ⟨i,j,hij,hi,hj⟩ := (correct x).mp ((raw_output C x v he).trans (by simp [x]))
    have ei : i = v := of_decide_eq_true hi
    have ej : j = v := of_decide_eq_true hj
    exact hij.ne (ei.trans ej.symm)
  obtain ⟨X,hX,hproj⟩ := small_projection G (separated_of_no_square G hs) hv hTS small hn
  let x : Fin n → Bool := fun i => decide (i ∈ X)
  let y : Fin n → Bool := fun i => decide (i ∈ insert v X)
  have eqbits : Agrees v.val (List.ofFn x) (List.ofFn y) := by
    intro i hi
    by_cases hlt : i < n
    · let j : Fin n := ⟨i,hlt⟩
      change (List.ofFn x).getD j.val false = (List.ofFn y).getD j.val false
      rw [raw,raw]
      simp [x,y, show j ≠ v from fun he => hi (congrArg Fin.val he)]
    · simp [List.getD_eq_getElem?_getD,hlt]
  have pins (p : Fin n) (hp : p ∈ S) : (List.ofFn x).getD p.val false = decide (p ∈ T) := by
    rw [raw, ← hproj]
    simp [x,hp]
  have eq := run_pinned hv C.gates readers _ _ (by simp) (by simp) eqbits pins C.output hout
  change C.eval (List.ofFn x) = C.eval (List.ofFn y) at eq
  obtain ⟨a,ha,b,hb,hab⟩ := hX.2.2
  have hy : C.eval (List.ofFn y) = true := (correct y).mpr ⟨a,b,hab,by simpa [y] using ha,by simpa [y] using hb⟩
  obtain ⟨i,j,hij,hi,hj⟩ := (correct x).mp (eq.trans hy)
  exact hX.2.1 ⟨i,of_decide_eq_true hi,j,of_decide_eq_true hj,hij⟩

#print axioms PEqualNP.Research.RawReaderBound
