import PEqualNP.Defs

-- The block evaluation and size lemmas are adapted from the project's CoverCircB and CoverCircB2.
namespace PEqualNP.Outside.L_meta_3493

namespace Builder
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem block_length (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
    (blockGates B a t v1 rest lead).length = rest.length + 1 + (if lead then 0 else 1) := by
  cases lead <;> simp [blockGates]

theorem gates_length_false : ∀ (own : List (ℕ × List ℕ)) (B a : ℕ), (∀ p ∈ own, p.2 ≠ []) →
    (coverGatesB B false a own).length =
      (own.map (fun p : ℕ × List ℕ => p.2.length)).sum + own.length
  | [], _, _, _ => by simp [coverGatesB]
  | (t, []) :: os, B, a, h => by simp at h
  | (t, v1 :: rest) :: os, B, a, h => by
      have ih := gates_length_false os (B + (blockGates B a t v1 rest false).length)
        (B + (blockGates B a t v1 rest false).length - 1)
        (fun p hp => h p (List.mem_cons_of_mem _ hp))
      simp only [coverGatesB, List.length_append]
      rw [ih, block_length]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      simp
      omega

theorem circuit_size (n : ℕ) (own : List (ℕ × List ℕ)) (hne : own ≠ [])
    (h : ∀ p ∈ own, p.2 ≠ []) :
    (coverCircuitB n own).size + 1 =
      (own.map (fun p : ℕ × List ℕ => p.2.length)).sum + own.length := by
  match own, hne, h with
  | (t, []) :: os, _, h => simp at h
  | (t, v1 :: rest) :: os, _, h =>
      have ih := gates_length_false os (n + (blockGates n 0 t v1 rest true).length)
        (n + (blockGates n 0 t v1 rest true).length - 1)
        (fun p hp => h p (List.mem_cons_of_mem _ hp))
      have hgl : (coverGatesB n true 0 ((t, v1 :: rest) :: os)).length =
          rest.length + 1 + ((os.map (fun p : ℕ × List ℕ => p.2.length)).sum + os.length) := by
        simp only [coverGatesB, List.length_append]
        rw [ih, block_length]
        simp
      have hnn : coverGatesB n true 0 ((t, v1 :: rest) :: os) ≠ [] := by
        intro h0
        have h1 := congrArg List.length h0
        rw [hgl] at h1
        simp at h1
      unfold coverCircuitB Circuit.size
      rw [if_neg hnn]
      simp only [hgl, List.map_cons, List.sum_cons, List.length_cons]
      omega




def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem fold_app (gs : List Gate) : ∀ w : List Bool, ∃ t : List Bool,
    gs.foldl step w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    refine ⟨(g.op.eval (g.inputs.map fun i => w.getD i false)) :: t, ?_, ?_⟩
    · rw [List.foldl_cons, ht]; simp [step]
    · simp [hl]

theorem getD_app_left {w t : List Bool} {i : ℕ} (h : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]

theorem getD_app_right {w t : List Bool} {i : ℕ} :
    (w ++ t).getD (w.length + i) false = t.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    ← List.getD_eq_getElem?_getD]

theorem getD_snoc' (l : List Bool) (b : Bool) (i : ℕ) (h : i = l.length) :
    (l ++ [b]).getD i false = b := by
  subst h
  simpa using getD_app_right (w := l) (t := [b]) (i := 0)

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := fold_app gs w
  rw [ht, List.length_append, hl]

theorem fold_keep (gs : List Gate) (w : List Bool) {i : ℕ} (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := fold_app gs w
  rw [ht, getD_app_left h]

theorem any_congr_mem {l : List ℕ} {f g : ℕ → Bool} (h : ∀ u ∈ l, f u = g u) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.any_cons]
    rw [h b (by simp), ih (fun u hu => h u (by simp [hu]))]


def cv (w : List Bool) (v1 : ℕ) (rest : List ℕ) (k : ℕ) : Bool :=
  w.getD v1 false || (rest.take k).any (fun u => w.getD u false)

theorem chain_read (w : List Bool) (B v1 : ℕ) (rest : List ℕ) (hw : w.length = B)
    (hv1 : v1 < B) (k : ℕ) (hk : k ≤ rest.length) :
    (w ++ (List.range k).map (fun i => cv w v1 rest (i + 1))).getD
        ((v1 :: (List.range rest.length).map (fun j => B + j)).getD k 0) false
      = cv w v1 rest k := by
  cases k with
  | zero =>
    simp only [List.getD_cons_zero]
    rw [getD_app_left (by omega)]
    simp [cv]
  | succ j =>
    have hj : j < rest.length := by omega
    have e1 : (v1 :: (List.range rest.length).map (fun j => B + j)).getD (j + 1) 0 = B + j := by
      simp [List.getD_cons_succ, List.getD_eq_getElem?_getD, hj]
    rw [e1, ← hw, getD_app_right]
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show j < j + 1 by omega)]

theorem chain (w : List Bool) (B v1 : ℕ) (rest : List ℕ) (hw : w.length = B)
    (hv1 : v1 < B) (hrest : ∀ u ∈ rest, u < B) :
    ∀ k ≤ rest.length,
      ((List.range k).map (fun i => (⟨GateOp.or,
          [(v1 :: (List.range rest.length).map (fun j => B + j)).getD i 0, rest.getD i 0]⟩ : Gate))).foldl
        step w = w ++ (List.range k).map (fun i => cv w v1 rest (i + 1)) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    rw [List.range_succ, List.map_append, List.foldl_append, ih (by omega)]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, step]
    rw [List.append_assoc]
    congr 2
    have hkr : k < rest.length := by omega
    have hrk : rest.getD k 0 = rest[k] := by
      simp [List.getD_eq_getElem?_getD, hkr]
    have hlt : rest[k] < w.length := by rw [hw]; exact hrest _ (List.getElem_mem hkr)
    simp only [List.map_cons, List.map_nil, GateOp.eval]
    rw [chain_read w B v1 rest hw hv1 k (by omega), hrk, getD_app_left hlt]
    simp only [cv, List.take_succ, List.getElem?_eq_getElem hkr, Option.toList_some,
      List.any_append, List.any_cons, List.any_nil, List.any_cons, Bool.or_false, id]
    simp [Bool.or_assoc, List.getElem?_eq_getElem hkr]

theorem block_val (w : List Bool) (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool)
    (hw : w.length = B) (ha : lead = false → a < B) (ht : t < B) (hv1 : v1 < B)
    (hrest : ∀ u ∈ rest, u < B) :
    ((blockGates B a t v1 rest lead).foldl step w).getD
        (B + (blockGates B a t v1 rest lead).length - 1) false
      = if lead then (w.getD t false && (w.getD v1 false || rest.any (fun u => w.getD u false)))
        else (w.getD a false ||
          (w.getD t false && (w.getD v1 false || rest.any (fun u => w.getD u false)))) := by
  have hc := chain w B v1 rest hw hv1 hrest rest.length le_rfl
  have hr := chain_read w B v1 rest hw hv1 rest.length le_rfl
  have hcvr : cv w v1 rest rest.length = (w.getD v1 false || rest.any (fun u => w.getD u false)) := by
    simp [cv]
  set L := (List.range rest.length).map (fun i => cv w v1 rest (i + 1)) with hL
  have hLl : L.length = rest.length := by simp [hL]
  have htW : (w ++ L).getD t false = w.getD t false := getD_app_left (by omega)
  rw [block_length]
  cases lead with
  | true =>
    simp only [blockGates, ↓reduceIte, List.foldl_append, hc, List.foldl_cons, List.foldl_nil,
      step]
    rw [getD_snoc']
    · simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil]
      rw [htW, hr, hcvr]
      simp
    · simp [hLl, hw]
  | false =>
    have ha' : a < B := ha rfl
    simp only [blockGates, Bool.false_eq_true, ↓reduceIte, List.foldl_append, hc, List.foldl_cons,
      List.foldl_nil, step]
    rw [getD_snoc']
    · simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil]
      rw [getD_app_left (by simp; omega), getD_app_left (by omega), getD_snoc']
      · simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil]
        rw [htW, hr, hcvr]
        simp
      · simp [hLl, hw]
    · simp [hLl, hw]

def F (x : List Bool) (own : List (ℕ × List ℕ)) : Bool :=
  own.any (fun p => x.getD p.1 false && p.2.any (fun u => x.getD u false))

theorem gates_nil_F (x : List Bool) : ∀ (own : List (ℕ × List ℕ)) (B : ℕ) (lead : Bool) (a : ℕ),
    coverGatesB B lead a own = [] → F x own = false
  | [], _, _, _, _ => rfl
  | (t, []) :: os, B, lead, a, h => by
      simp only [coverGatesB] at h
      have := gates_nil_F x os B lead a h
      simp only [F, List.any_cons, List.any_nil, Bool.and_false, Bool.false_or] at this ⊢
      exact this
  | (t, v1 :: rest) :: os, B, lead, a, h => by
      simp only [coverGatesB] at h
      cases lead <;> simp [blockGates] at h

theorem main (n : ℕ) (x : List Bool) :
    ∀ (own : List (ℕ × List ℕ)) (B : ℕ) (lead : Bool) (a : ℕ) (w : List Bool),
      (∀ p ∈ own, p.1 < n ∧ ∀ u ∈ p.2, u < n) → w.length = B → n ≤ B →
      (∀ i < n, w.getD i false = x.getD i false) → (lead = false → a < B) →
      coverGatesB B lead a own ≠ [] →
      ((coverGatesB B lead a own).foldl step w).getD
          (B + (coverGatesB B lead a own).length - 1) false
        = if lead then F x own else (w.getD a false || F x own)
  | [], _, _, _, _, _, _, _, _, _, hne => by simp [coverGatesB] at hne
  | (t, []) :: os, B, lead, a, w, hown, hw, hnB, hwx, ha, hne => by
      simp only [coverGatesB] at hne ⊢
      rw [main n x os B lead a w (fun p hp => hown p (List.mem_cons_of_mem _ hp)) hw hnB hwx ha
        hne]
      simp [F]
  | (t, v1 :: rest) :: os, B, lead, a, w, hown, hw, hnB, hwx, ha, _ => by
      have hp := hown (t, v1 :: rest) (by simp)
      have ht : t < n := hp.1
      have hv1 : v1 < n := hp.2 v1 (by simp)
      have hrest : ∀ u ∈ rest, u < n := fun u hu => hp.2 u (by simp [hu])
      have hos : ∀ p ∈ os, p.1 < n ∧ ∀ u ∈ p.2, u < n :=
        fun p hp => hown p (List.mem_cons_of_mem _ hp)
      have hbv := block_val w B a t v1 rest lead hw ha (by omega) (by omega)
        (fun u hu => by have := hrest u hu; omega)
      have hrx : rest.any (fun u => w.getD u false) = rest.any (fun u => x.getD u false) :=
        any_congr_mem (fun u hu => hwx u (hrest u hu))
      rw [hrx, hwx t ht, hwx v1 hv1] at hbv
      set bg := blockGates B a t v1 rest lead with hbg
      have hm : 0 < bg.length := by rw [hbg, block_length]; omega
      set W1 := bg.foldl step w with hW1
      have hW1l : W1.length = B + bg.length := by rw [hW1, fold_length, hw]
      have hW1x : ∀ i < n, W1.getD i false = x.getD i false := by
        intro i hi
        rw [hW1, fold_keep bg w (by omega)]
        exact hwx i hi
      have hW1a : lead = false → W1.getD a false = w.getD a false := by
        intro hl
        rw [hW1, fold_keep bg w (by have := ha hl; omega)]
      have hcons : F x ((t, v1 :: rest) :: os) =
          ((x.getD t false && (x.getD v1 false || rest.any (fun u => x.getD u false))) || F x os) :=
        rfl
      rw [hcons]
      simp only [coverGatesB]
      rw [← hbg, List.foldl_append, ← hW1, List.length_append]
      by_cases hnil : coverGatesB (B + bg.length) false (B + bg.length - 1) os = []
      · have hF := gates_nil_F x os _ false _ hnil
        rw [hnil, List.foldl_nil, List.length_nil, Nat.add_zero, hbv]
        rw [hF]
        cases lead <;> simp
      · have ih := main n x os (B + bg.length) false (B + bg.length - 1) W1 hos hW1l (by omega)
          hW1x (fun _ => by omega) hnil
        have hidx : B + (bg.length + (coverGatesB (B + bg.length) false (B + bg.length - 1) os).length) - 1
            = B + bg.length + (coverGatesB (B + bg.length) false (B + bg.length - 1) os).length - 1 := by
          omega
        rw [hidx, ih, hbv]
        cases lead <;> simp [Bool.or_assoc]

theorem circuit_fun (n : ℕ) (own : List (ℕ × List ℕ))
    (h : ∀ p ∈ own, p.1 < n ∧ ∀ w ∈ p.2, w < n) (x : Fin n → Bool) :
    ((coverCircuitB n own).eval (List.ofFn x) = true ↔
      ∃ p ∈ own, (List.ofFn x).getD p.1 false = true ∧
        ∃ w ∈ p.2, (List.ofFn x).getD w false = true) := by
  have hF : (∃ p ∈ own, (List.ofFn x).getD p.1 false = true ∧
        ∃ w ∈ p.2, (List.ofFn x).getD w false = true) ↔ F (List.ofFn x) own = true := by
    simp [F, List.any_eq_true]
  rw [hF]
  unfold coverCircuitB Circuit.eval
  split_ifs with hnil
  · rw [gates_nil_F _ own n true 0 hnil, wires_eq]
    simp [List.getD_eq_getElem?_getD]
  · rw [wires_eq]
    simp only
    rw [main n (List.ofFn x) own n true 0 (List.ofFn x) h (by simp) le_rfl (fun _ _ => rfl)
      (by simp) hnil]
    simp

end Builder

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3493.Builder in

theorem build_semantics : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : List (ℕ × List ℕ)),   let x6 : ℕ := x1 + x2;   (∀ x7 ∈ x5, x7.2 ≠ [] ∧ ((x7.1 < x1 ∧ ∀ x9 ∈ x7.2, x1 ≤ x9 ∧ x9 < x6) ∨ x1 ≤ x7.1 ∧ x7.1 < x6 ∧ ∀ x9 ∈ x7.2, x9 < x1)) →     (∀ (x8 : Fin x1) (x9 : Fin x2), x3 x8 x9 ↔ ∃ x10 ∈ x5, x10.1 = ↑x8 ∧ x1 + ↑x9 ∈ x10.2 ∨ x10.1 = x1 + ↑x9 ∧ ↑x8 ∈ x10.2) →       have x9 : PEqualNP.CircuitLowerBounds.Circuit := PEqualNP.MetaComplexity.coverCircuitB x6 x5;       x9.size = (List.map (fun (x10 : ℕ × List ℕ) => x10.2.length) x5).sum + x5.length - (1 : ℕ) ∧ ∀ (x10 : Fin x6 → Bool), PEqualNP.MetaComplexity.circuitFun x6 x9 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ∧ x10 (Fin.castAdd x2 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true) := by
  intro P L I inst own n shape relation C
  constructor
  · by_cases he : own = []
    · subst own
      rfl
    · have h := circuit_size n own he (fun e h => (shape e h).1)
      change (coverCircuitB n own).size = _
      omega
  · intro x
    have bounds : ∀ e ∈ own, e.1 < n ∧ ∀ w ∈ e.2, w < n := by
      intro e he
      rcases (shape e he).2 with ⟨hp, hl⟩ | ⟨_, hl, hp⟩
      · exact ⟨by dsimp [n]; omega, fun w h => (hl w h).2⟩
      · refine ⟨hl, ?_⟩
        intro w hw
        have := hp w hw
        dsimp [n]; omega
    have leftRead (p : Fin P) : (List.ofFn x).getD p.val false = x (Fin.castAdd L p) := by
      rw [List.getD_eq_getElem _ _ (by simp [n] <;> omega), List.getElem_ofFn]
      rfl
    have rightRead (l : Fin L) : (List.ofFn x).getD (P + l.val) false = x (Fin.natAdd P l) := by
      rw [List.getD_eq_getElem _ _ (by simp [n] <;> omega), List.getElem_ofFn]
      rfl
    change (coverCircuitB n own).eval (List.ofFn x) = decide _
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq, circuit_fun n own bounds x]
    constructor
    · rintro ⟨e, he, ha, t, ht, hb⟩
      rcases (shape e he).2 with ⟨hp, hl⟩ | ⟨hlo, hhi, hps⟩
      · obtain ⟨lo, hi⟩ := hl t ht
        let p : Fin P := ⟨e.1,hp⟩
        let l : Fin L := ⟨t-P,by dsimp [n] at hi; omega⟩
        have eq : P+l.val = t := by dsimp [l]; omega
        refine ⟨p,l,(relation p l).mpr ⟨e,he,Or.inl ⟨rfl,eq ▸ ht⟩⟩, ?_, ?_⟩
        · exact (leftRead p).symm.trans ha
        · rw [← rightRead, eq]; exact hb
      · let p : Fin P := ⟨t,hps t ht⟩
        let l : Fin L := ⟨e.1-P,by dsimp [n] at hhi; omega⟩
        have eq : P+l.val = e.1 := by dsimp [l]; omega
        refine ⟨p,l,(relation p l).mpr ⟨e,he,Or.inr ⟨eq.symm,ht⟩⟩, ?_, ?_⟩
        · exact (leftRead p).symm.trans hb
        · rw [← rightRead, eq]; exact ha
    · rintro ⟨p,l,hi,hp,hl⟩
      obtain ⟨e,he, alt⟩ := (relation p l).mp hi
      rcases alt with ⟨eq,ht⟩ | ⟨eq,ht⟩
      · exact ⟨e,he,eq ▸ (leftRead p).trans hp,P+l.val,ht,(rightRead l).trans hl⟩
      · exact ⟨e,he,eq ▸ (rightRead l).trans hl,p.val,ht,(leftRead p).trans hp⟩

-- The block invariant is adapted from fededevi's proof of L_meta_3245.
namespace Shape

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def Inv (p q : ℕ → Prop) (B : ℕ) (L : List Gate) (S T : Finset ℕ) : Prop :=
  (∀ (k : ℕ) (g : Gate), L[k]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧
    ∀ i ∈ g.inputs, i < B + k) ∧
  (∀ w ∈ S, ∃ (k : ℕ) (g : Gate), L[k]? = some g ∧ w = B + k ∧ g.op = GateOp.or ∧ ∀ i ∈ g.inputs, p i ∨ i ∈ S) ∧
  (∀ w ∈ T, ∃ (k : ℕ) (g : Gate), L[k]? = some g ∧ w = B + k ∧ g.op = GateOp.or ∧ ∀ i ∈ g.inputs, q i ∨ i ∈ T) ∧
  (∀ (k : ℕ) (g : Gate), L[k]? = some g → g.op = GateOp.and → ∃ a b, g.inputs = [a, b] ∧
     (((p a ∨ a ∈ S) ∧ (q b ∨ b ∈ T)) ∨ ((q a ∨ a ∈ T) ∧ (p b ∨ b ∈ S))))

theorem inv_swap {p q : ℕ → Prop} {B : ℕ} {L : List Gate} {S T : Finset ℕ}
    (h : Inv p q B L S T) : Inv q p B L T S := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h3, h2, ?_⟩
  intro k g hk ho
  obtain ⟨a, b, e, h⟩ := h4 k g hk ho
  exact ⟨a, b, e, h.symm⟩

theorem inv_nil (p q : ℕ → Prop) (B : ℕ) : Inv p q B [] ∅ ∅ := by
  simp [Inv]

theorem app_cases {L1 L2 : List Gate} {k : ℕ} {g : Gate} (h : (L1 ++ L2)[k]? = some g) :
    L1[k]? = some g ∨ ∃ k2, k = L1.length + k2 ∧ L2[k2]? = some g := by
  rw [List.getElem?_append] at h
  split at h
  · exact Or.inl h
  · exact Or.inr ⟨k - L1.length, by omega, h⟩

theorem app_left {L1 L2 : List Gate} {k : ℕ} {g : Gate} (h : L1[k]? = some g) :
    (L1 ++ L2)[k]? = some g := by
  have hk : k < L1.length := (List.getElem?_eq_some_iff.mp h).1
  rw [List.getElem?_append_left hk]
  exact h

theorem app_right {L1 L2 : List Gate} {k : ℕ} {g : Gate} (h : L2[k]? = some g) :
    (L1 ++ L2)[L1.length + k]? = some g := by
  rw [List.getElem?_append_right (by omega)]
  simpa using h

theorem inv_app {p q : ℕ → Prop} {B : ℕ} {L1 L2 : List Gate} {S1 T1 S2 T2 : Finset ℕ}
    (h : Inv p q B L1 S1 T1) (h' : Inv p q (B + L1.length) L2 S2 T2) :
    Inv p q B (L1 ++ L2) (S1 ∪ S2) (T1 ∪ T2) := by
  obtain ⟨a1, a2, a3, a4⟩ := h
  obtain ⟨b1, b2, b3, b4⟩ := h'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k g hk
    rcases app_cases hk with h | ⟨k2, rfl, h⟩
    · exact a1 k g h
    · obtain ⟨x, y, z⟩ := b1 k2 g h
      exact ⟨x, y, fun i hi => by have := z i hi; omega⟩
  · intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨k, g, e1, e2, e3, e4⟩ := a2 w hw
      exact ⟨k, g, app_left e1, e2, e3, fun i hi => (e4 i hi).imp id (fun h => Finset.mem_union_left _ h)⟩
    · obtain ⟨k, g, e1, e2, e3, e4⟩ := b2 w hw
      exact ⟨L1.length + k, g, app_right e1, by omega, e3,
        fun i hi => (e4 i hi).imp id (fun h => Finset.mem_union_right _ h)⟩
  · intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨k, g, e1, e2, e3, e4⟩ := a3 w hw
      exact ⟨k, g, app_left e1, e2, e3, fun i hi => (e4 i hi).imp id (fun h => Finset.mem_union_left _ h)⟩
    · obtain ⟨k, g, e1, e2, e3, e4⟩ := b3 w hw
      exact ⟨L1.length + k, g, app_right e1, by omega, e3,
        fun i hi => (e4 i hi).imp id (fun h => Finset.mem_union_right _ h)⟩
  · intro k g hk ho
    rcases app_cases hk with h | ⟨k2, rfl, h⟩
    · obtain ⟨a, b, e, hh⟩ := a4 k g h ho
      refine ⟨a, b, e, ?_⟩
      simp only [Finset.mem_union]
      tauto
    · obtain ⟨a, b, e, hh⟩ := b4 k2 g h ho
      refine ⟨a, b, e, ?_⟩
      simp only [Finset.mem_union]
      tauto

theorem cval (B v1 m i : ℕ) (hi : i ≤ m) :
    (i = 0 ∧ (v1 :: (List.range m).map (fun j => B + j)).getD i 0 = v1) ∨
    (0 < i ∧ (v1 :: (List.range m).map (fun j => B + j)).getD i 0 = B + (i - 1)) := by
  cases i with
  | zero => left; simp
  | succ j =>
    right
    have hj : j < m := by omega
    simp [List.getD_eq_getElem?_getD, hj]

theorem block_get {B a t v1 : ℕ} {rest : List ℕ} {lead : Bool} {k : ℕ} {g : Gate}
    (h : (blockGates B a t v1 rest lead)[k]? = some g) :
    (k < rest.length ∧ g = ⟨GateOp.or,
      [(v1 :: (List.range rest.length).map (fun j => B + j)).getD k 0, rest.getD k 0]⟩) ∨
    (k = rest.length ∧ g = ⟨GateOp.and,
      [t, (v1 :: (List.range rest.length).map (fun j => B + j)).getD rest.length 0]⟩) ∨
    (k = rest.length + 1 ∧ lead = false ∧ g = ⟨GateOp.or, [a, B + rest.length]⟩) := by
  unfold blockGates at h
  rcases app_cases h with h | ⟨k2, hk, h⟩
  · left
    have hk : k < rest.length := by
      have := (List.getElem?_eq_some_iff.mp h).1
      simpa using this
    refine ⟨hk, ?_⟩
    simp only [List.getElem?_map, List.getElem?_range hk, Option.map_some, Option.some.injEq] at h
    exact h.symm
  · right
    simp only [List.length_map, List.length_range] at hk
    cases k2 with
    | zero =>
      left
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      exact ⟨by omega, h.symm⟩
    | succ k3 =>
      right
      cases lead with
      | true => simp at h
      | false =>
        cases k3 with
        | zero =>
          simp only [List.getElem?_cons_succ, Bool.false_eq_true, ite_false,
            List.getElem?_cons_zero, Option.some.injEq] at h
          exact ⟨by omega, rfl, h.symm⟩
        | succ k4 => simp at h

theorem block_chain {B a t v1 : ℕ} {rest : List ℕ} {lead : Bool} {k : ℕ} (hk : k < rest.length) :
    (blockGates B a t v1 rest lead)[k]? = some ⟨GateOp.or,
      [(v1 :: (List.range rest.length).map (fun j => B + j)).getD k 0, rest.getD k 0]⟩ := by
  unfold blockGates
  apply app_left
  simp [hk]

theorem rest_mem {rest : List ℕ} {k : ℕ} (hk : k < rest.length) : rest.getD k 0 ∈ rest := by
  simp [List.getD_eq_getElem?_getD, hk]

theorem inv_block {p q : ℕ → Prop} {B a t v1 : ℕ} {rest : List ℕ} {lead : Bool}
    (hp : ∀ i, p i → i < B) (hq : ∀ i, q i → i < B) (ha : lead = false → a < B)
    (ht : q t) (hv : p v1) (hr : ∀ v ∈ rest, p v) :
    Inv p q B (blockGates B a t v1 rest lead)
      ((Finset.range rest.length).image (fun j => B + j)) ∅ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k g hk
    rcases block_get hk with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, rfl⟩
    · refine ⟨Or.inr rfl, rfl, ?_⟩
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · rcases cval B v1 rest.length k (by omega) with ⟨_, e⟩ | ⟨h0, e⟩
        · rw [e]; have := hp _ hv; omega
        · rw [e]; omega
      · have := hp _ (hr _ (rest_mem h1)); omega
    · refine ⟨Or.inl rfl, rfl, ?_⟩
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · have := hq _ ht; omega
      · rcases cval B v1 rest.length rest.length (le_refl _) with ⟨_, e⟩ | ⟨h0, e⟩
        · rw [e]; have := hp _ hv; omega
        · rw [e]; omega
    · refine ⟨Or.inr rfl, rfl, ?_⟩
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      have := ha h2
      rcases hi with rfl | rfl <;> omega
  · intro w hw
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
    have hk : k < rest.length := Finset.mem_range.mp hk
    refine ⟨k, _, block_chain hk, rfl, rfl, ?_⟩
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · rcases cval B v1 rest.length k (by omega) with ⟨_, e⟩ | ⟨h0, e⟩
      · rw [e]; exact Or.inl hv
      · rw [e]; right
        exact Finset.mem_image.mpr ⟨k - 1, Finset.mem_range.mpr (by omega), rfl⟩
    · exact Or.inl (hr _ (rest_mem hk))
  · intro w hw
    simp at hw
  · intro k g hk ho
    rcases block_get hk with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, rfl⟩
    · simp at ho
    · refine ⟨_, _, rfl, Or.inr ⟨Or.inl ht, ?_⟩⟩
      rcases cval B v1 rest.length rest.length (le_refl _) with ⟨_, e⟩ | ⟨h0, e⟩
      · rw [e]; exact Or.inl hv
      · rw [e]; right
        exact Finset.mem_image.mpr ⟨rest.length - 1, Finset.mem_range.mpr (by omega), rfl⟩
    · simp at ho

theorem block_len (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
    1 ≤ (blockGates B a t v1 rest lead).length := by
  unfold blockGates
  simp
  omega

theorem inv_cover (p q : ℕ → Prop) (own : List (ℕ × List ℕ)) :
    ∀ (B : ℕ) (lead : Bool) (a : ℕ), (∀ i, p i → i < B) → (∀ i, q i → i < B) →
      (lead = false → a < B) →
      (∀ o ∈ own, (q o.1 ∧ ∀ v ∈ o.2, p v) ∨ (p o.1 ∧ ∀ v ∈ o.2, q v)) →
      ∃ S T, Inv p q B (coverGatesB B lead a own) S T := by
  induction own with
  | nil =>
    intro B lead a _ _ _ _
    exact ⟨∅, ∅, by simpa [coverGatesB] using inv_nil p q B⟩
  | cons o os ih =>
    intro B lead a hp hq ha ho
    obtain ⟨t, l⟩ := o
    have hos : ∀ o ∈ os, (q o.1 ∧ ∀ v ∈ o.2, p v) ∨ (p o.1 ∧ ∀ v ∈ o.2, q v) :=
      fun o h => ho o (List.mem_cons_of_mem _ h)
    cases l with
    | nil =>
      simp only [coverGatesB]
      exact ih B lead a hp hq ha hos
    | cons v1 rest =>
      simp only [coverGatesB]
      have hl := block_len B a t v1 rest lead
      obtain ⟨S2, T2, h2⟩ := ih (B + (blockGates B a t v1 rest lead).length) false
        (B + (blockGates B a t v1 rest lead).length - 1)
        (fun i h => by have := hp i h; omega) (fun i h => by have := hq i h; omega)
        (fun _ => by omega) hos
      have h0 := ho (t, v1 :: rest) List.mem_cons_self
      simp only [List.mem_cons, forall_eq_or_imp] at h0
      rcases h0 with ⟨h1, h3, h4⟩ | ⟨h1, h3, h4⟩
      · exact ⟨_, _, inv_app (inv_block hp hq ha h1 h3 h4) h2⟩
      · exact ⟨_, _, inv_app (inv_swap (inv_block hq hp ha h1 h3 h4)) h2⟩

theorem gates_eq (n : ℕ) (own : List (ℕ × List ℕ)) :
    (coverCircuitB n own).gates = coverGatesB n true 0 own := by
  unfold coverCircuitB
  split <;> simp_all

theorem gateAt_get (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    C.gates[j]? = some (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  simp [List.getD_eq_getElem?_getD, hj]

end Shape

open PEqualNP.Outside.L_meta_3493.Shape in
theorem build_shape : ∀ (x1 x2 : ℕ) (x3 : List (ℕ × List ℕ)),   have x4 : ℕ := x1 + x2;   (∀ x5 ∈ x3, x5.2 ≠ [] ∧ ((x5.1 < x1 ∧ ∀ x7 ∈ x5.2, x1 ≤ x7 ∧ x7 < x4) ∨ x1 ≤ x5.1 ∧ x5.1 < x4 ∧ ∀ x7 ∈ x5.2, x7 < x1)) →     have x6 : PEqualNP.CircuitLowerBounds.Circuit := PEqualNP.MetaComplexity.coverCircuitB x4 x3;     have x7 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x6;     ∃ (x8 : Finset ℕ) (x9 : Finset ℕ), PEqualNP.TopForm.IsAO2 x4 x6 ∧ (∀ x10 ∈ x8, x10 < x1 ∨ ∃ x12 < x6.gates.length, x10 = x4 + x12 ∧ (x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (x7 x12).inputs, x13 ∈ x8) ∧ (∀ x10 ∈ x9, x1 ≤ x10 ∧ x10 < x4 ∨ ∃ x12 < x6.gates.length, x10 = x4 + x12 ∧ (x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (x7 x12).inputs, x13 ∈ x9) ∧ ∀ x10 < x6.gates.length, (x7 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ), (x7 x10).inputs = [x13, x14] ∧ (x13 ∈ x8 ∧ x14 ∈ x9 ∨ x13 ∈ x9 ∧ x14 ∈ x8) := by
  intro x1 x2 x3 x4 hyp x6 x7
  obtain ⟨S, T, h1, h2, h3, h4⟩ := inv_cover (fun i => i < x1) (fun i => x1 ≤ i ∧ i < x4) x3 x4 true 0
    (fun i h => by show i < x1 + x2; omega) (fun i h => h.2) (fun h => by simp at h)
    (fun o ho => by
      rcases (hyp o ho).2 with h | h
      · exact Or.inr h
      · exact Or.inl ⟨⟨h.1, h.2.1⟩, h.2.2⟩)
  have hg : x6.gates = PEqualNP.MetaComplexity.coverGatesB x4 true 0 x3 := gates_eq x4 x3
  rw [← hg] at h1 h2 h3 h4
  have key : ∀ k g, x6.gates[k]? = some g → k < x6.gates.length ∧ x7 k = g := by
    intro k g h
    have hk : k < x6.gates.length := (List.getElem?_eq_some_iff.mp h).1
    refine ⟨hk, ?_⟩
    have := gateAt_get x6 k hk
    rw [h] at this
    exact (Option.some.inj this).symm
  refine ⟨Finset.range x1 ∪ S, Finset.Ico x1 x4 ∪ T, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro g hg2
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hg2
    exact (h1 k g hk).1
  · intro j hj i hi
    exact (h1 j _ (gateAt_get x6 j hj)).2.2 i hi
  · intro g hg2
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hg2
    exact (h1 k g hk).2.1
  · intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Or.inl (Finset.mem_range.mp hw)
    · right
      obtain ⟨k, g, e1, e2, e3, e4⟩ := h2 w hw
      obtain ⟨hk, rfl⟩ := key k g e1
      refine ⟨k, hk, e2, e3, fun i hi => ?_⟩
      rcases e4 i hi with h | h
      · exact Finset.mem_union_left _ (Finset.mem_range.mpr h)
      · exact Finset.mem_union_right _ h
  · intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Or.inl (Finset.mem_Ico.mp hw)
    · right
      obtain ⟨k, g, e1, e2, e3, e4⟩ := h3 w hw
      obtain ⟨hk, rfl⟩ := key k g e1
      refine ⟨k, hk, e2, e3, fun i hi => ?_⟩
      rcases e4 i hi with h | h
      · exact Finset.mem_union_left _ (Finset.mem_Ico.mpr h)
      · exact Finset.mem_union_right _ h
  · intro k hk ho
    obtain ⟨a, b, e, h⟩ := h4 k _ (gateAt_get x6 k hk) ho
    refine ⟨a, b, e, ?_⟩
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    exact h

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem reorient : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Finset ℕ), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ x6 < x2.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x9 : ℕ) (x10 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).inputs = [x9, x10] ∧ (x9 ∈ x3 ∧ x10 ∈ x4 ∨ x9 ∈ x4 ∧ x10 ∈ x3)) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x7 ∧ x7.size = x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.circuitFun x1 x2 ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op) ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8 = PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8) ∧ ∀ x8 < x7.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x11 : ℕ) (x12 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).inputs = [x11, x12] ∧ x11 ∈ x4 ∧ x12 ∈ x3 := by
  classical
  intro n C A B initial cross
  let oriented (g : Gate) := ∃ a b, g.inputs = [a,b] ∧ a ∈ B ∧ b ∈ A
  let reorder (g : Gate) : Gate :=
    if g.op = GateOp.and ∧ ¬ oriented g then { g with inputs := g.inputs.reverse } else g
  let D : Circuit := ⟨C.gates.map reorder, C.output⟩
  have ops (g : Gate) : (reorder g).op = g.op := by
    unfold reorder
    split <;> rfl
  have len (g : Gate) : (reorder g).inputs.length = g.inputs.length := by
    unfold reorder
    split <;> simp
  have mem (g : Gate) (k : ℕ) : k ∈ (reorder g).inputs ↔ k ∈ g.inputs := by
    unfold reorder
    split <;> simp
  have atGate (j : ℕ) : gateAt D j = reorder (gateAt C j) := by
    simp only [gateAt, D, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases C.gates[j]? <;> simp [reorder]
  have same (g : Gate) (f : ℕ → Bool) :
      (reorder g).op.eval ((reorder g).inputs.map f) = g.op.eval (g.inputs.map f) := by
    unfold reorder
    split
    · rename_i h
      simp [h.1, GateOp.eval, List.map_reverse]
    · rfl
  let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have run (gs : List Gate) (w : List Bool) : (gs.map reorder).foldl step w = gs.foldl step w := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons]
      rw [ih]
      exact congrArg (gs.foldl step) (congrArg (fun b => w ++ [b]) (same g _))
  refine ⟨D, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
    simpa only [ops] using initial.1 h hh
  · intro j hj k hk
    apply initial.2.1 j (by simpa [D] using hj) k
    exact (mem _ _).mp (atGate j ▸ hk)
  · intro g hg
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
    exact (len h).trans (initial.2.2 h hh)
  · simp [D, Circuit.size]
  · funext x
    exact congrArg (fun w : List Bool => w.getD C.output false) (run C.gates (List.ofFn x))
  · intro j
    rw [atGate, ops]
  · intro j hj
    simp [atGate, reorder, hj]
  · intro j hj hOp
    rw [atGate, ops] at hOp
    obtain ⟨a,b,hab,hs⟩ := cross j (by simpa [D] using hj) hOp
    rw [atGate]
    by_cases ho : oriented (gateAt C j)
    · rw [show reorder (gateAt C j) = gateAt C j by simp [reorder, ho]]
      exact ho
    · have hba : a ∈ A ∧ b ∈ B := hs.resolve_right (fun h => ho ⟨a,b,hab,h⟩)
      exact ⟨b,a,by simp [reorder, hOp, ho, hab],hba.2,hba.1⟩

theorem owner_lists (p l : ℕ) (I : Fin p → Fin l → Prop) [DecidableRel I]
    (T : Finset (Fin (p+l))) (covers : ∀ a b, I a b → Fin.castAdd l a ∈ T ∨ Fin.natAdd p b ∈ T) :
    ∃ own : List (ℕ × List ℕ),
      (∀ z ∈ own, z.2 ≠ [] ∧
        ((z.1 < p ∧ ∀ j ∈ z.2, p ≤ j ∧ j < p+l) ∨
         (p ≤ z.1 ∧ z.1 < p+l ∧ ∀ j ∈ z.2, j < p))) ∧
      (∀ (a : Fin p) (b : Fin l), I a b ↔ ∃ z ∈ own,
        (z.1 = a.val ∧ p+b.val ∈ z.2) ∨ (z.1 = p+b.val ∧ a.val ∈ z.2)) ∧
      (own.map (fun z => z.2.length)).sum = (PEqualNP.ReadTwo.incid I).card ∧
      own.length ≤ T.card := by
  classical
  let E := PEqualNP.ReadTwo.incid I
  let owner (e : Fin p × Fin l) : Fin (p+l) :=
    if Fin.castAdd l e.1 ∈ T then Fin.castAdd l e.1 else Fin.natAdd p e.2
  let leaf (e : Fin p × Fin l) : ℕ := if Fin.castAdd l e.1 ∈ T then p+e.2.val else e.1.val
  let S := E.image owner
  let fiber (v : Fin (p+l)) := E.filter (fun e => owner e = v)
  let leaves (v : Fin (p+l)) := (fiber v).toList.map leaf
  let row (v : Fin (p+l)) : ℕ × List ℕ := (v.val, leaves v)
  have incident (e : Fin p × Fin l) : e ∈ E ↔ I e.1 e.2 := by simp [E, PEqualNP.ReadTwo.incid]
  have endpoints (e : Fin p × Fin l) :
      ((owner e).val = e.1.val ∧ leaf e = p+e.2.val) ∨
      ((owner e).val = p+e.2.val ∧ leaf e = e.1.val) := by
    by_cases h : Fin.castAdd l e.1 ∈ T <;> simp [owner, leaf, h, Fin.val_natAdd]
  have leaf_mem (v : Fin (p+l)) (j : ℕ) :
      j ∈ leaves v ↔ ∃ e ∈ E, owner e = v ∧ leaf e = j := by
    simp [leaves, fiber, and_assoc]
  have covered : S ⊆ T := by
    intro v hv
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hv
    by_cases h : Fin.castAdd l e.1 ∈ T
    · simp [owner,h]
    · simpa [owner,h] using (covers _ _ ((incident e).mp he)).resolve_left h
  refine ⟨S.toList.map row, ?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
    have hvS := Finset.mem_toList.mp hv
    obtain ⟨e, he, hv'⟩ := Finset.mem_image.mp hvS
    have witness := (leaf_mem v (leaf e)).mpr ⟨e, he, hv', rfl⟩
    change leaves v ≠ [] ∧ _
    refine ⟨fun h => by rw [h] at witness; exact List.not_mem_nil witness, ?_⟩
    by_cases h : v.val < p
    · refine Or.inl ⟨h, ?_⟩
      intro j hj
      obtain ⟨f, _, eq, rfl⟩ := (leaf_mem v j).mp hj
      have ve := congrArg Fin.val eq
      rcases endpoints f with h' | h' <;> have := f.2.isLt <;> omega
    · refine Or.inr ⟨Nat.le_of_not_gt h, v.isLt, ?_⟩
      intro j hj
      obtain ⟨f, _, eq, rfl⟩ := (leaf_mem v j).mp hj
      have ve := congrArg Fin.val eq
      rcases endpoints f with h' | h' <;> have := f.1.isLt <;> omega
  · intro a b
    constructor
    · intro hab
      let e : Fin p × Fin l := (a,b)
      have he : e ∈ E := (incident e).mpr hab
      refine ⟨row (owner e), List.mem_map.mpr ⟨_, Finset.mem_toList.mpr (Finset.mem_image_of_mem _ he), rfl⟩, ?_⟩
      have hl := (leaf_mem (owner e) (leaf e)).mpr ⟨e,he,rfl,rfl⟩
      rcases endpoints e with ⟨ho,hv⟩ | ⟨ho,hv⟩
      · exact Or.inl ⟨ho, hv ▸ hl⟩
      · exact Or.inr ⟨ho, hv ▸ hl⟩
    · rintro ⟨z, hz, hr⟩
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hz
      rcases hr with ⟨hown, hleaf⟩ | ⟨hown, hleaf⟩
      all_goals
        change v.val = _ at hown
        obtain ⟨e, he, hv, hj⟩ := (leaf_mem v _).mp hleaf
        have ve := congrArg Fin.val hv
        have ha := a.isLt
        have hp := e.1.isLt
        have hpair : e = (a,b) := by
          apply Prod.ext <;> apply Fin.ext <;> rcases endpoints e with hh | hh <;> dsimp <;> omega
        simpa only [hpair] using (incident e).mp he
  · change ((S.toList.map row).map (fun z => z.2.length)).sum = E.card
    simp only [List.map_map]
    have hlen (v : Fin (p+l)) : (row v).2.length = (fiber v).card := by simp [row, leaves]
    simp only [Function.comp_def, hlen, Finset.sum_map_toList]
    exact (Finset.card_eq_sum_card_image owner E).symm
  · simpa using Finset.card_le_card covered

end PEqualNP.Outside.L_meta_3493

open PEqualNP.Outside.L_meta_3493 in
theorem PEqualNP.Outside.L_meta_3493 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : Finset (Fin (x1 + x2))), (∀ (x6 : Fin x1) (x7 : Fin x2), x3 x6 x7 → Fin.castAdd x2 x6 ∈ x5 ∨ Fin.natAdd x1 x7 ∈ x5) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : Finset ℕ) (x9 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧ (∀ (x10 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ∧ x10 (Fin.castAdd x2 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) ∧ x7.size ≤ (PEqualNP.ReadTwo.incid x3).card + x5.card - (1 : ℕ) ∧ (∀ x10 ∈ x8, x10 < x1 ∨ ∃ x12 < x7.gates.length, x10 = x1 + x2 + x12 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x12).inputs, x13 ∈ x8) ∧ (∀ x10 ∈ x9, x1 ≤ x10 ∧ x10 < x1 + x2 ∨ ∃ x12 < x7.gates.length, x10 = x1 + x2 + x12 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x12).inputs, x13 ∈ x9) ∧ ∀ x10 < x7.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x10).inputs = [x13, x14] ∧ x13 ∈ x9 ∧ x14 ∈ x8 := by
  intro p l I inst T hcover
  obtain ⟨own, hvalid, hrep, hsum, hcount⟩ := owner_lists p l I T hcover
  let C := PEqualNP.MetaComplexity.coverCircuitB (p+l) own
  obtain ⟨hsize, hfun⟩ := build_semantics p l I own hvalid hrep
  obtain ⟨P,L,hC,hP,hL,hAnd⟩ := build_shape p l own hvalid
  obtain ⟨D,hD,ds,df,_,sameOr,doneAnd⟩ := reorient (p+l) C P L hC hAnd
  have sameLen : D.gates.length = C.gates.length := ds
  refine ⟨D,P,L,hD,fun x => (congrFun df x).trans (hfun x), ?_, ?_, ?_, doneAnd⟩
  · change D.size ≤ _
    rw [ds]
    change (PEqualNP.MetaComplexity.coverCircuitB (p+l) own).size ≤ _
    rw [hsize, hsum]
    omega
  · intro w hw
    rcases hP w hw with h | ⟨i,hi,he,ho,hs⟩
    · exact Or.inl h
    · exact Or.inr ⟨i, sameLen ▸ hi, he, by rwa [sameOr i ho], by rwa [sameOr i ho]⟩
  · intro w hw
    rcases hL w hw with h | ⟨i,hi,he,ho,hs⟩
    · exact Or.inl h
    · exact Or.inr ⟨i, sameLen ▸ hi, he, by rwa [sameOr i ho], by rwa [sameOr i ho]⟩