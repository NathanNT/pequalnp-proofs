import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.ReadK

namespace PEqualNP.Outside.L_meta_3477

-- The dependency-set argument and wire evaluation lemmas are adapted from L_meta_2074.
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma dep (n : ℕ) (C : Circuit) (hR : ∀ j < C.gates.length, (gateAt C j).inputs.length = 2) :
    ∀ k, k ≤ C.gates.length → ∀ W : Finset ℕ, (∀ w ∈ W, w < n + k) →
      ∃ T : Finset (Fin n), T.card ≤ k + W.card ∧
        ∀ x y : Fin n → Bool, (∀ i ∈ T, x i = y i) →
          ∀ w ∈ W, val C (List.ofFn x) w = val C (List.ofFn y) w := by
  intro k
  induction k with
  | zero =>
    intro _ W hW
    refine ⟨Finset.univ.filter (fun i : Fin n => (i : ℕ) ∈ W), ?_, ?_⟩
    · rw [Nat.zero_add, ← Finset.card_image_of_injective _ Fin.val_injective]
      apply Finset.card_le_card
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
      exact (Finset.mem_filter.1 hi).2
    · intro x y h w hw
      have hw' : w < n := by simpa using hW w hw
      have e : ∀ z : Fin n → Bool, (List.ofFn z).getD w false = z ⟨w, hw'⟩ := by
        intro z; simp [List.getD_eq_getElem?_getD, hw']
      rw [val_input (by simp) hw', val_input (by simp) hw', e, e]
      exact h ⟨w, hw'⟩ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hw⟩)
  | succ k ih =>
    intro hk W hW
    by_cases hmem : n + k ∈ W
    · obtain ⟨W2, hW2⟩ : ∃ W2 : Finset ℕ, W2 = W.erase (n + k) ∪
          ((gateAt C k).inputs.filter (fun i => i < n + k)).toFinset := ⟨_, rfl⟩
      have hlt2 : ∀ w ∈ W2, w < n + k := by
        intro w hw
        rw [hW2] at hw
        rcases Finset.mem_union.1 hw with h | h
        · have h1 := hW w (Finset.mem_of_mem_erase h)
          have h2 := Finset.ne_of_mem_erase h
          omega
        · simp at h; exact h.2
      have hs1 : ∀ w ∈ W, w ≠ n + k → w ∈ W2 := by
        intro w hw hne
        rw [hW2]
        exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hne, hw⟩)
      have hs2 : ∀ i ∈ (gateAt C k).inputs, i < n + k → i ∈ W2 := by
        intro i hi hlt
        rw [hW2]
        exact Finset.mem_union_right _ (by simp [hi, hlt])
      have hc : W2.card + 1 ≤ W.card + 2 := by
        rw [hW2]
        have h1 := Finset.card_union_le (W.erase (n + k))
          ((gateAt C k).inputs.filter (fun i => i < n + k)).toFinset
        have h2 : ((gateAt C k).inputs.filter (fun i => i < n + k)).toFinset.card ≤ 2 :=
          (List.toFinset_card_le _).trans
            ((List.length_filter_le _ _).trans (hR k (by omega)).le)
        have h3 := Finset.card_erase_of_mem hmem
        have h4 : 0 < W.card := Finset.card_pos.2 ⟨_, hmem⟩
        omega
      obtain ⟨T, hT, hdep⟩ := ih (by omega) W2 hlt2
      refine ⟨T, by omega, ?_⟩
      intro x y h w hw
      by_cases hwk : w = n + k
      · rw [hwk, val_gate (by simp) (by omega), val_gate (by simp) (by omega)]
        congr 1
        apply List.map_congr_left
        intro i hi
        by_cases hlt : i < n + k
        · simp only [ite_eq_left hlt]
          exact hdep x y h i (hs2 i hi hlt)
        · simp only [ite_eq_right hlt]
      · exact hdep x y h w (hs1 w hw hwk)
    · obtain ⟨T, hT, hdep⟩ := ih (by omega) W (by
        intro w hw
        have h1 := hW w hw
        have h2 : w ≠ n + k := fun h => hmem (h ▸ hw)
        omega)
      exact ⟨T, by omega, hdep⟩


def Compatible (a : Bool × Bool) (b : Bool) := (a.1 = true ∨ a.2 = true) → b = true

lemma compat_get {A : List (Bool × Bool)} {B : List Bool} (h : List.Forall₂ Compatible A B)
    (i : ℕ) : Compatible (A.getD i (false,false)) (B.getD i false) := by
  induction h generalizing i with
  | nil => simp [List.getD_eq_getElem?_getD, Compatible]
  | cons ha _ ih =>
    cases i with
    | zero => exact ha
    | succ i => exact ih i

lemma initial (tag : ℕ → Bool) (x : List Bool) (k : ℕ) :
    List.Forall₂ Compatible ((x.zipIdx k).map fun (b,i) => if tag i then (false,b) else (b,false)) x := by
  induction x generalizing k with
  | nil => exact .nil
  | cons b bs ih =>
    simp only [List.zipIdx_cons, List.map_cons]
    apply List.Forall₂.cons _ (ih _)
    cases tag k <;> simp [Compatible]

def stepParts (w : List (Bool × Bool)) (g : Gate) :=
  let ins := g.inputs.map fun i => w.getD i (false,false)
  w ++ [match g.op with
    | .or => (ins.any (·.1), ins.any (·.2))
    | .and => ins.foldl (fun (a : Bool × Bool) b => (a.1 && b.1, (a.1 && b.2) || (a.2 && b.1))) (true,false)
    | _ => (false,false)]

lemma compat_fold (gs : List Gate) (valid : ∀ g ∈ gs, g.inputs.length = 2)
    (A : List (Bool × Bool)) (B : List Bool) (rel : List.Forall₂ Compatible A B) :
    List.Forall₂ Compatible (gs.foldl stepParts A) (gs.foldl stepWire B) := by
  induction gs generalizing A B with
  | nil => exact rel
  | cons g gs ih =>
    apply ih (fun k hk => valid k (List.mem_cons_of_mem _ hk))
    obtain ⟨i,j,e⟩ := List.length_eq_two.mp (valid g (by simp))
    unfold stepParts stepWire
    apply List.rel_append rel
    apply List.Forall₂.cons _ .nil
    have hi := compat_get rel i
    have hj := compat_get rel j
    generalize hae : A.getD i (false,false) = a at *
    generalize hbe : A.getD j (false,false) = b at *
    generalize hce : B.getD i false = c at *
    generalize hde : B.getD j false = d at *
    rw [e]
    simp only [List.map_cons, List.map_nil, hae, hbe, hce, hde]
    rcases a with ⟨a₀,a₁⟩
    rcases b with ⟨b₀,b₁⟩
    cases g.op <;> simp_all [Compatible, GateOp.eval, List.all_cons, List.any_cons]
    all_goals grind

lemma single_accepts (C : Circuit) (valid : ∀ g ∈ C.gates, g.inputs.length = 2)
    (N p l : ℕ) (tag : ℕ → Bool) (h : lineSingle C N tag p l = true) :
    C.eval ((List.range N).map fun i => i == p || i == l) = true := by
  let x := (List.range N).map fun i => i == p || i == l
  exact compat_get (compat_fold C.gates valid _ x (initial tag x 0)) C.output (Or.inr h)

end PEqualNP.Outside.L_meta_3477

open PEqualNP.Outside.L_meta_3477 in
theorem PEqualNP.Outside.L_meta_3477 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x1 ≤ (9 : ℕ) → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → Fintype.card { x13 : Fin x2 × Fin x2 // x3 x13.1 x13.2 ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x14 : ℕ) => Decidable.decide (x14 < x2)) (↑x13.1) (x2 + ↑x13.2) = Bool.true } ≤ (10 : ℕ) * x5.size := by
  intro q n I _ C hq qsmall _ degree _ hao sound
  classical
  let test (p l : Fin n) (k : Fin (n+n)) := decide (k = Fin.castAdd n p ∨ k = Fin.natAdd n l)
  let only (v : Fin (n+n)) (k : Fin (n+n)) := decide (k = v)
  let single (p l : Fin n) := lineSingle C (n+n) (fun k => decide (k<n)) p.val (n+l.val)
  let E := Finset.univ.filter (fun e : Fin n × Fin n => I e.1 e.2 ∧ single e.1 e.2 = true)
  have cardE : Fintype.card {e : Fin n × Fin n // I e.1 e.2 ∧ single e.1 e.2 = true} = E.card := by
    simp only [Fintype.card_subtype, E]
  change Fintype.card {e : Fin n × Fin n // I e.1 e.2 ∧ single e.1 e.2 = true} ≤ _
  rw [cardE]
  by_cases hEmpty : E = ∅
  · simp [hEmpty]
  have sep (a b : Fin n) : Fin.castAdd n a ≠ Fin.natAdd n b := by
    intro eq
    have := congrArg Fin.val eq
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    have := a.isLt
    omega
  have reject (v : Fin (n+n)) : circuitFun (n+n) C (only v) = false := by
    apply sound
    · by_cases hl : ∃ l : Fin n, Fin.natAdd n l = v
      · obtain ⟨l,rfl⟩ := hl
        have hcard : Fintype.card {b : Fin n // only (Fin.natAdd n l) (Fin.natAdd n b) = true} = 1 := by
          simp [only]
        omega
      · have hempty : ∀ l : Fin n, Fin.natAdd n l ≠ v := fun l e => hl ⟨l,e⟩
        simp only [only, Fintype.card_subtype, decide_eq_true_eq, hempty, Finset.filter_false,
          Finset.card_empty, Nat.zero_le]
    · rintro ⟨a,b,_,ha,hb⟩
      simp only [only, decide_eq_true_eq] at ha hb
      exact sep a b (ha.trans hb.symm)
  have acc (e : Fin n × Fin n) (he : e ∈ E) : circuitFun (n+n) C (test e.1 e.2) = true := by
    have ha := single_accepts C hao.2.2 (n+n) e.1.val (n+e.2.val) (fun k => decide (k<n))
      (Finset.mem_filter.mp he).2.2
    have key : List.ofFn (test e.1 e.2) = (List.range (n+n)).map
        (fun i => i == e.1.val || i == n+e.2.val) := by
      apply List.ext_getElem
      · simp
      · intro k hk hk'
        simp [test, Fin.ext_iff, Bool.beq_eq_decide_eq, Nat.add_comm n]
    simpa only [circuitFun, key] using ha
  obtain ⟨T, hT, depends⟩ : ∃ T : Finset (Fin (n+n)), T.card ≤ C.gates.length+1 ∧
      ∀ x y : Fin (n+n) → Bool, (∀ i ∈ T, x i = y i) →
        val C (List.ofFn x) C.output = val C (List.ofFn y) C.output := by
    by_cases ho : C.output < (n+n) + C.gates.length
    · obtain ⟨T,hT,hd⟩ := dep (n+n) C (fun j hj => hao.2.2 _ (gateAt_mem hj)) C.gates.length le_rfl
        {C.output} (by simpa using ho)
      exact ⟨T,by simpa using hT,fun x y h => hd x y h _ (by simp)⟩
    · exact ⟨∅,by simp,fun x y _ => by
        rw [val_ge (n := n+n) (by simp) (by omega), val_ge (n := n+n) (by simp) (by omega)]⟩
  have needed (e : Fin n × Fin n) (he : e ∈ E) :
      Fin.castAdd n e.1 ∈ T ∧ Fin.natAdd n e.2 ∈ T := by
    constructor
    · by_contra h
      have eq := depends (test e.1 e.2) (only (Fin.natAdd n e.2)) (fun k hk => by
        have ne : k ≠ Fin.castAdd n e.1 := fun eq => h (eq ▸ hk)
        simp only [test,only,ne,false_or])
      change circuitFun _ C _ = circuitFun _ C _ at eq
      rw [acc e he, reject] at eq
      contradiction
    · by_contra h
      have eq := depends (test e.1 e.2) (only (Fin.castAdd n e.1)) (fun k hk => by
        have ne : k ≠ Fin.natAdd n e.2 := fun eq => h (eq ▸ hk)
        simp only [test,only,ne,or_false])
      change circuitFun _ C _ = circuitFun _ C _ at eq
      rw [acc e he, reject] at eq
      contradiction
  let lines := E.image Prod.snd
  obtain ⟨e,he⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
  have lineCount : lines.card ≤ C.size := by
    have le : lines.card ≤ (T.erase (Fin.castAdd n e.1)).card := by
      apply Finset.card_le_card_of_injOn (Fin.natAdd n)
      · intro b hb
        obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hb
        exact Finset.mem_erase.mpr ⟨(sep e.1 f.2).symm, (needed f hf).2⟩
      · intro a _ b _ h
        simpa using h
    rw [Finset.card_erase_of_mem (needed e he).1] at le
    have pos := Finset.card_pos.mpr ⟨_,(needed e he).1⟩
    change lines.card ≤ C.gates.length
    omega
  calc
    E.card = ∑ b ∈ lines, (E.filter fun e => e.2 = b).card :=
      Finset.card_eq_sum_card_image Prod.snd E
    _ ≤ ∑ _b ∈ lines, (q+1) := by
      apply Finset.sum_le_sum
      intro b _
      have bound : (E.filter fun e => e.2 = b).card ≤ (Finset.univ.filter (fun p => I p b)).card := by
        apply Finset.card_le_card_of_injOn Prod.fst
        · intro f hf
          obtain ⟨hmem,hb⟩ := Finset.mem_filter.mp hf
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb ▸ (Finset.mem_filter.mp hmem).2.1⟩
        · intro f hf g hg heq
          exact Prod.ext heq ((Finset.mem_filter.mp hf).2.trans (Finset.mem_filter.mp hg).2.symm)
      simpa only [← Fintype.card_subtype, degree b] using bound
    _ = lines.card * (q+1) := by simp
    _ ≤ C.size * 10 := Nat.mul_le_mul lineCount (by omega)
    _ = _ := Nat.mul_comm _ _
