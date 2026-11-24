import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3172_521
    (hBinary : ∀ C : Circuit, FanInTwo C →
      (∀ (x8 : Fin 9 → Bool), C.eval (List.ofFn x8) = (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)))) →
      13 ≤ List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => !g.op.eval [Bool.false]) C.gates)
    (hTwelve : ∀ (x1 : List ℕ), x1.length = (2 : ℕ) → x1.Nodup →
      (∀ x3 ∈ x1, x3 = (1 : ℕ) ∨ x3 = (2 : ℕ) ∨ x3 = (3 : ℕ) ∨ x3 = (5 : ℕ) ∨ x3 = (8 : ℕ)) →
      (∀ x4 ∈ x1, x4 = (2 : ℕ) ∨ x4 = (3 : ℕ) ∨ x4 = (8 : ℕ)) →
      ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 → x5.size ≤ (13 : ℕ) → List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => !g.op.eval [Bool.false]) x5.gates = 12 →
      ∃ (x8 : Fin (9 : ℕ) → Bool), have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))]; x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))))
    (hThirteen : ∀ (pins : List ℕ), pins.length = 2 →
      (∀ i ∈ pins, i = 2 ∨ i = 3 ∨ i = 8) → ∀ C : Circuit, FanInTwo C →
      C.size ≤ 13 → C.gates.countP (fun g => !g.op.eval [false]) = 13 →
      ∃ r ∈ ([3, 6, 12, 13, 17, 24, 33, 42, 50, 66, 69, 104, 116, 132, 133, 138, 160, 200, 201, 208, 261, 264, 265, 276, 288, 320, 321, 385, 402] : List ℕ),
        have x : Fin 9 → Bool := fun i => r.testBit i;
        have w := List.ofFn x ++ [!x 0];
        C.eval (w ++ [GateOp.or.eval (pins.map fun i => w.getD i false)]) ≠
          ([3, 6, 12, 13, 17, 24, 33, 66, 132, 133, 160, 264, 265, 288, 320, 321] : List ℕ).contains r) :
    ∀ (x1 : List ℕ), x1.length = (2 : ℕ) →
      (∀ x3 ∈ x1, x3 = (1 : ℕ) ∨ x3 = (2 : ℕ) ∨ x3 = (3 : ℕ) ∨ x3 = (5 : ℕ) ∨ x3 = (8 : ℕ)) →
      (∀ x4 ∈ x1, x4 = (2 : ℕ) ∨ x4 = (3 : ℕ) ∨ x4 = (8 : ℕ)) →
      ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 → x5.size ≤ (13 : ℕ) →
      ∃ (x8 : Fin (9 : ℕ) → Bool), have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))]; x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  intro pins hlen hallowed hpins C hfan hsize
  let n := List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => !g.op.eval [Bool.false]) C.gates
  have hn : n ≤ 13 := (List.countP_le_length ..).trans hsize
  by_cases h12 : n = 12
  · by_cases hUnique : pins.Nodup
    · exact hTwelve pins hlen hUnique hallowed hpins C hfan hsize h12
    obtain ⟨a, b, rfl⟩ : ∃ a b, pins = [a, b] := by
      rcases pins with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · simp at hlen
      · simp at hlen
      · have hr : rest = [] := by simpa using hlen
        exact ⟨a, b, by rw [hr]⟩
    have hab : a = b := by simpa using hUnique
    subst b
    have ha : a < 10 := by
      rcases hpins a (by simp) with h | h | h <;> omega
    let index (i : ℕ) := if i < 10 then i else if i = 10 then a else i - 1
    let gate (g : Gate) : Gate := ⟨g.op, g.inputs.map index⟩
    let push (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have reading (w : List Bool) (v : Bool) (i : ℕ) :
        (w ++ [v]).getD i false = if i = w.length then v else w.getD i false := by
      by_cases hit : i < w.length
      · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hit, Nat.ne_of_lt hit]
      · by_cases he : i = w.length
        · subst i
          rw [ite_eq_left rfl, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)]
          simp
        · have hlo : w.length ≤ i := by omega
          have hsub : i - w.length ≠ 0 := by omega
          rw [ite_eq_right he, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_append_right hlo, List.getElem?_eq_none hlo]
          simp [hsub]
    have traces (gs : List Gate) (old new : List Bool) (hnew : 10 ≤ new.length)
        (hl : old.length = new.length + 1)
        (hrel : ∀ i, old.getD i false = new.getD (index i) false) (j : ℕ) :
        (gs.foldl push old).getD j false =
          ((gs.map gate).foldl push new).getD (index j) false := by
      induction gs generalizing old new with
      | nil =>
          exact hrel j
      | cons g gs ih =>
          change (gs.foldl push (push old g)).getD j false =
            ((gs.map gate).foldl push (push new (gate g))).getD (index j) false
          apply ih
          · simp [push]; omega
          · simp [push, hl]
          · intro i
            change (old ++ [g.op.eval (g.inputs.map fun k => old.getD k false)]).getD i false =
              (new ++ [g.op.eval ((g.inputs.map index).map fun k =>
                new.getD k false)]).getD (index i) false
            have hv : (g.inputs.map fun k => old.getD k false) =
                ((g.inputs.map index).map fun k => new.getD k false) := by
              rw [List.map_map]
              exact List.map_congr_left (fun k _ => hrel k)
            have he : i = old.length ↔ index i = new.length := by
              simp only [index]
              split
              · omega
              · split <;> omega
            simp only [reading]
            rw [hv]
            simp only [he, hrel]
    by_contra hfailure
    let first : Gate := ⟨.not, [0]⟩
    let D : Circuit := ⟨first :: C.gates.map gate, index C.output⟩
    have hD : FanInTwo D := by
      intro g hg
      change g ∈ first :: C.gates.map gate at hg
      rcases List.mem_cons.mp hg with rfl | hg
      · simp [first]
      · obtain ⟨old, hm, rfl⟩ := List.mem_map.mp hg
        simpa [gate] using hfan old hm
    have hEval (x : Fin 9 → Bool) : D.eval (List.ofFn x) = (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ))) := by
      let base : List Bool := List.ofFn x ++ [!x 0]
      have hbase : base.length = 10 := by simp [base]
      have hrel (i : ℕ) : (base ++ [base.getD a false]).getD i false = base.getD (index i) false := by
        rw [reading, hbase]
        by_cases hlo : i < 10
        · simp [index, hlo, Nat.ne_of_lt hlo]
        · by_cases heq : i = 10
          · simp [index, heq]
          · have hb : base.length ≤ i := by omega
            have hr : base.length ≤ i - 1 := by omega
            simp [index, hlo, heq, List.getD_eq_getElem?_getD,
              List.getElem?_eq_none hb, List.getElem?_eq_none hr]
      have same : GateOp.or.eval ([a, a].map fun i => base.getD i false) = base.getD a false := by
        change (base.getD a false || (base.getD a false || false)) = base.getD a false
        simp
      have h0 : (List.ofFn x).getD 0 false = x 0 := by
        simp [List.getD_eq_getElem?_getD]
      have hd : D.eval (List.ofFn x) =
          ((C.gates.map gate).foldl push base).getD (index C.output) false := by
        have hh : D.eval (List.ofFn x) =
            ((C.gates.map gate).foldl push (List.ofFn x ++
              [!((List.ofFn x).getD 0 false)])).getD (index C.output) false := rfl
        rw [hh, h0]
      have he := not_ne_iff.mp (fun hne => hfailure ⟨x, hne⟩)
      change (C.gates.foldl push (base ++
        [GateOp.or.eval ([a, a].map fun i => base.getD i false)])).getD C.output false = _ at he
      rw [same] at he
      rw [hd, ← traces C.gates (base ++ [base.getD a false]) base (by omega)
        (by simp) hrel C.output]
      exact he
    have hCost :
        List.countP (fun (g : Gate) => !g.op.eval [false]) D.gates = n := by
      change (first :: C.gates.map gate).countP (fun g => !g.op.eval [false]) = n
      rw [List.countP_cons, List.countP_map]
      rfl
    have hlo := hBinary D hD hEval
    omega
  by_cases h13 : n = 13
  · obtain ⟨r, hr, hdiff⟩ := hThirteen pins hlen hpins C hfan hsize h13
    have hTable :
        ([3, 6, 12, 13, 17, 24, 33, 42, 50, 66, 69, 104, 116, 132, 133, 138, 160, 200, 201, 208, 261, 264, 265, 276, 288, 320, 321, 385, 402] : List ℕ).all (fun i =>
          have x8 : Fin 9 → Bool := fun j => i.testBit j;
          (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) ==
            ([3, 6, 12, 13, 17, 24, 33, 66, 132, 133, 160, 264, 265, 288, 320, 321] : List ℕ).contains i) = true := by
      decide
    have hrow := List.all_eq_true.mp hTable r hr
    refine ⟨fun i => r.testBit i, ?_⟩
    change C.eval _ ≠ _
    intro heq
    exact hdiff (heq.trans (by simpa using hrow))
  by_contra hfailure
  let g : Gate := ⟨.not, [0]⟩
  let h : Gate := ⟨.or, pins⟩
  let D : Circuit := ⟨g :: h :: C.gates, C.output⟩
  have hD : FanInTwo D := by
    intro i hi
    change i ∈ g :: h :: C.gates at hi
    rcases List.mem_cons.mp hi with rfl | hi
    · simp [g]
    rcases List.mem_cons.mp hi with rfl | hi
    · simp [h, hlen]
    · exact hfan i hi
  have hEval (x : Fin 9 → Bool) : D.eval (List.ofFn x) = (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ))) := by
    have h0 : (List.ofFn x).getD 0 false = x 0 := by
      simp [List.getD_eq_getElem?_getD]
    have he := not_ne_iff.mp (fun hne => hfailure ⟨x, hne⟩)
    have hd : D.eval (List.ofFn x) =
        C.eval ((List.ofFn x ++ [!((List.ofFn x).getD 0 false)]) ++
          [GateOp.or.eval (pins.map fun i =>
            (List.ofFn x ++ [!((List.ofFn x).getD 0 false)]).getD i false)]) := rfl
    rw [hd, h0]
    exact he
  have hCost : List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => !g.op.eval [Bool.false]) D.gates = n + 1 := by
    change (g :: h :: C.gates).countP (fun j => !j.op.eval [false]) = n + 1
    rw [List.countP_cons, List.countP_cons]
    rfl
  have hlo := hBinary D hD hEval
  rw [hCost] at hlo
  omega
