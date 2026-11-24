import Mathlib
import PEqualNP.Outside.L_meta_2672

namespace PEqualNP.MetaComplexity.WeightedIncidence
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.ReadK PEqualNP.Outside.L_meta_2672

-- One tag fixes the point. Its possible lines all contain the same two distinct points.
private theorem tagRectangle {n : ℕ} {side : ℕ → Bool} {R : ℕ → ℕ → Bool}
    {G H : (Fin n → Bool) → Prop} {p l : ℕ}
    (mono : ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) → G x → G y)
    (first : Tg side R G H p l) :
    ∃ a b, a ≠ b ∧ side a = false ∧ side b = false ∧
      ∀ u v, Tg side R G H u v → u = p ∧ R a v = true ∧ R b v = true := by
  obtain ⟨_,⟨a,b,hab,ha,hb,hGa,hGb⟩,_,_,unique⟩ := first
  refine ⟨a,b,hab,ha,hb,?_⟩
  intro u v witness
  obtain ⟨negative,_,hu,hHu,_⟩ := witness
  have incident (r : ℕ) (hs : side r = false) (hg : G (sg n r)) : R r v = true := by
    by_contra no
    exact negative (mono _ _ (sg_le_off n side R r v hs (by simpa using no)) hg)
  exact ⟨unique u hu hHu, incident a ha hGa, incident b hb hGb⟩

private theorem slotRectangle {n : ℕ} {C : Circuit} {side : ℕ → Bool} {R : ℕ → ℕ → Bool}
    (legal : Legal C.gates) (e₀ : ℕ × ℕ) (t : (ℕ × ℕ) × Bool)
    (first : TT C.gates C.output n side R e₀ t) :
    ∃ a b, a ≠ b ∧ side a = false ∧ side b = false ∧
      ∀ e, TT C.gates C.output n side R e t →
        e.1 = e₀.1 ∧ R a e.2 = true ∧ R b e.2 = true := by
  rcases first with ⟨ht,g,u,hg,hu,hT⟩ | ⟨ht,g,u,hg,hu,hT⟩
  · obtain ⟨a,b,hn,ha,hb,all⟩ := tagRectangle
      (fun x y hxy hd => D_mono C.gates C.output legal x y hxy u hd) hT
    refine ⟨a,b,hn,ha,hb,?_⟩
    rintro e (⟨_,g',u',hg',hu',h'⟩ | ⟨ht',_⟩)
    · rw [hg] at hg'; cases hg'
      rw [hu] at hu'; cases hu'
      exact all _ _ h'
    · rw [ht] at ht'; contradiction
  · obtain ⟨a,b,hn,ha,hb,all⟩ := tagRectangle
      (fun x y hxy hv => val_mono C.gates legal x y hxy (n+t.1.1) hv) hT
    refine ⟨a,b,hn,ha,hb,?_⟩
    rintro e (⟨ht',_⟩ | ⟨_,g',u',hg',hu',h'⟩)
    · rw [ht] at ht'; contradiction
    · rw [hg] at hg'; cases hg'
      rw [hu] at hu'; cases hu'
      exact all _ _ h'

-- A forward tag requires two active point singletons at the output and one at the chosen input.
-- An AND would pass both singletons to that input.
private theorem forward_or {n : ℕ} {C : Circuit} {side : ℕ → Bool} {R : ℕ → ℕ → Bool}
    (legal : Legal C.gates) {k s p l : ℕ} (tag : T2 C.gates n side R k s p l) :
    (gateAt C k).op = GateOp.or := by
  obtain ⟨g,u,hg,hs,_,⟨a,b,ne,ha,hb,hga,hgb⟩,_,_,unique⟩ := tag
  have hk := (List.getElem?_eq_some_iff.mp hg).1
  have ge : C.gates[k] = g := (List.getElem?_eq_some_iff.mp hg).2
  have atg : gateAt C k = g := by simp [gateAt,List.getD_eq_getElem?_getD,hg]
  rw [atg]
  rcases (legal g (List.mem_of_getElem? hg)).1 with hand | hor
  · have input (r : ℕ) (h : val C.gates (n+k) (sg n r) = true) :
        val C.gates u (sg n r) = true :=
      ((val_and C.gates _ k hk (by rw [ge]; exact hand)).mp h u
        (by rw [ge]; exact List.mem_of_getElem? hs)).2
    exact (ne ((unique a ha (input a hga)).trans (unique b hb (input b hgb)).symm)).elim
  · exact hor

end PEqualNP.MetaComplexity.WeightedIncidence

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.ReadK PEqualNP.Outside.L_meta_2672
open PEqualNP.MetaComplexity.WeightedIncidence

-- The budget bounds how much weight one point shares with any other point.
-- The conclusion counts every visible incidence whose line has a second visible point in S.
-- Soundness is tested on one negative input per represented line.
theorem PEqualNP.MetaComplexity.WeightedIncidence :
    ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (side : ℕ → Bool)
    (R : ℕ → ℕ → Bool) (S : Finset (ℕ × ℕ)) (weight : ℕ × ℕ → NNReal) (B : NNReal),
    PEqualNP.ReadK.AndOrFanInTwo C → PEqualNP.MetaComplexity.NestedCover.ReadsBack n C →
    (∀ e ∈ S, e.2 < n ∧ side e.1 = false ∧ side e.2 = true ∧ R e.1 e.2 = true ∧
      PEqualNP.ReadK.lineSingle C n side e.1 e.2 = true) →
    (∀ l ∈ S.image Prod.snd, PEqualNP.MetaComplexity.circuitFun n C
      (fun i => (!side i.val && !R i.val l) || decide (i.val = l)) = false) →
    (∀ p r : ℕ, p ≠ r → side r = false →
      (∑ e ∈ S.filter (fun e => e.1 = p ∧ R r e.2 = true), weight e) ≤ B) →
    (∑ e ∈ S.filter (fun e => ∃ f ∈ S, f.2 = e.2 ∧ f.1 ≠ e.1), weight e) ≤
      2 * ((C.size : NNReal) + ((Finset.range C.size).filter (fun k =>
        @decide ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or) (Classical.propDecidable _) = true)).card) * B := by
  classical
  intro n C side R S weight B hao back visible negative capacity
  have legal : Legal C.gates := fun g hg => ⟨hao.1 g hg,hao.2 g hg⟩
  have rb : RB n C.gates := by
    intro k g hg i hi
    apply back k (List.getElem?_eq_some_iff.mp hg).1 i
    simpa [gateAt,List.getD_eq_getElem?_getD,hg] using hi
  let heavy := S.filter (fun e => ∃ f ∈ S, f.2 = e.2 ∧ f.1 ≠ e.1)
  let slots := Finset.range C.size ×ˢ Finset.range 2
  let ors := (Finset.range C.size).filter (fun k => @decide ((gateAt C k).op = GateOp.or) (Classical.propDecidable _) = true)
  let forward := ors ×ˢ Finset.range 2
  let tags := (slots.image (fun z => (z,true))) ∪ (forward.image (fun z => (z,false)))
  let rel := TT C.gates C.output n side R
  have path (e : ℕ × ℕ) (he : e ∈ S) : D C.gates C.output (sg n e.1) e.2 := by
    obtain ⟨_,hp,hl,_,hs⟩ := visible e he
    let xs := (List.range n).map (fun i => i == e.1 || i == e.2)
    have hlen : xs.length = n := by simp [xs]
    have hon (i : ℕ) (hi : i < n) : xs.getD i false = true ↔ i = e.1 ∨ i = e.2 := by
      simp [xs,List.getD_eq_getElem?_getD,hi]
    exact lpB C.gates C.output n side rb legal xs hlen e.1 e.2 hp hl hon C.output hs
      (D_out _ _ _)
  have pays (e : ℕ × ℕ) (he : e ∈ heavy) : ∃ t ∈ tags, rel e t := by
    obtain ⟨heS,f,hf,eq,ne⟩ := Finset.mem_filter.mp he
    obtain ⟨bound,hp,_,_,_⟩ := visible e heS
    obtain ⟨depth,hd⟩ := path e heS
    have hbad : ¬ D C.gates C.output (off n side R e.2) e.2 := by
      rintro ⟨d,hd'⟩
      have accepted := snd C.gates C.output legal rb (off n side R e.2)
        (fun i => off n side R e.2 i || decide (i.val = e.2))
        (fun v hv => by simp [hv]) d e.2 hd' (by rw [val_input _ _ _ bound]; simp)
      have rejected := negative e.2 (Finset.mem_image_of_mem _ heS)
      exact Bool.noConfusion (accepted.symm.trans rejected)
    have other := path f hf
    rw [eq] at other
    obtain ⟨k,s,hk,hs,tag⟩ := uc C.gates C.output n side R legal e.2 e.1 hp depth e.2 hd hbad
      ⟨f.1,ne,(visible f hf).2.1,other⟩
    rcases tag with tag | tag
    · refine ⟨((k,s),true), Finset.mem_union_left _ (Finset.mem_image_of_mem _ ?_), Or.inl ⟨rfl,tag⟩⟩
      simp [slots,Circuit.size,hk,hs]
    · refine ⟨((k,s),false), Finset.mem_union_right _ (Finset.mem_image_of_mem _ ?_), Or.inr ⟨rfl,tag⟩⟩
      simp [forward,ors,Circuit.size,hk,hs,forward_or legal tag]
  have cost (t) : (∑ e ∈ heavy, if rel e t then weight e else 0) ≤ B := by
    rw [← Finset.sum_filter]
    by_cases active : ∃ e₀ ∈ heavy, rel e₀ t
    · obtain ⟨e₀,_,first⟩ := active
      obtain ⟨a,b,ne,ha,hb,rectangle⟩ := slotRectangle legal e₀ t first
      obtain ⟨r,diff,hr,shared⟩ : ∃ r, e₀.1 ≠ r ∧ side r = false ∧
          ∀ e, rel e t → R r e.2 = true := by
        by_cases eq : e₀.1 = a
        · exact ⟨b,eq.symm ▸ ne,hb,fun e he => (rectangle e he).2.2⟩
        · exact ⟨a,eq,ha,fun e he => (rectangle e he).2.1⟩
      apply le_trans _ (capacity e₀.1 r diff hr)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro e he
        obtain ⟨hh,hrel⟩ := Finset.mem_filter.mp he
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hh).1,(rectangle e hrel).1,shared e hrel⟩
      · intros; positivity
    · have empty : heavy.filter (fun e => rel e t) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro e he
        exact active ⟨e,(Finset.mem_filter.mp he).1,(Finset.mem_filter.mp he).2⟩
      simp [empty]
  change (∑ e ∈ heavy, weight e) ≤ _
  calc
    _ ≤ ∑ e ∈ heavy, ∑ t ∈ tags, if rel e t then weight e else 0 := by
      apply Finset.sum_le_sum
      intro e he
      obtain ⟨t,ht,hrel⟩ := pays e he
      have h := Finset.single_le_sum (s := tags)
        (f := fun t => if rel e t then weight e else 0) (fun _ _ => zero_le) ht
      simpa [hrel] using h
    _ = ∑ t ∈ tags, ∑ e ∈ heavy, if rel e t then weight e else 0 := Finset.sum_comm
    _ ≤ ∑ _t ∈ tags, B := Finset.sum_le_sum (fun t _ => cost t)
    _ ≤ _ := by
      have count : tags.card ≤ 2 * (C.size + ors.card) := calc
        _ ≤ _ := Finset.card_union_le _ _
        _ ≤ slots.card + forward.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
        _ = _ := by simp [slots,forward,Finset.card_product]; omega
      rw [Finset.sum_const,nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ zero_le
      exact_mod_cast count

namespace PEqualNP.MetaComplexity.WeightedIncidence

-- Bounded codegree replaces uniqueness, and a line with just one visible incidence costs one.
theorem boundedCodegree (n : ℕ) (C : Circuit) (side : ℕ → Bool) (R : ℕ → ℕ → Bool)
    (S : Finset (ℕ × ℕ)) (d : ℕ) (hao : AndOrFanInTwo C) (back : ReadsBack n C)
    (visible : ∀ e ∈ S, e.2 < n ∧ side e.1 = false ∧ side e.2 = true ∧ R e.1 e.2 = true ∧
      lineSingle C n side e.1 e.2 = true)
    (negative : ∀ l ∈ S.image Prod.snd, circuitFun n C
      (fun i => (!side i.val && !R i.val l) || decide (i.val = l)) = false)
    (overlap : ∀ p r : ℕ, p ≠ r → side r = false →
      (S.filter (fun e => e.1 = p ∧ R r e.2 = true)).card ≤ d) :
    S.card ≤ 2 * (C.size + ((Finset.range C.size).filter (fun k =>
      @decide ((gateAt C k).op = GateOp.or) (Classical.propDecidable _) = true)).card) * d +
      (S.image Prod.snd).card := by
  classical
  let multiple (e : ℕ × ℕ) := ∃ f ∈ S, f.2 = e.2 ∧ f.1 ≠ e.1
  have weighted := PEqualNP.MetaComplexity.WeightedIncidence n C side R S (fun _ => 1) d
    hao back visible negative (by
      intro p r ne hr
      simpa only [Finset.sum_const,nsmul_eq_mul,mul_one,Nat.cast_le] using
        (show (((S.filter (fun e => e.1 = p ∧ R r e.2 = true)).card : ℕ) : NNReal) ≤ d by
          exact_mod_cast overlap p r ne hr))
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one] at weighted
  have heavy : (S.filter multiple).card ≤ 2 * (C.size + ((Finset.range C.size).filter (fun k =>
      @decide ((gateAt C k).op = GateOp.or) (Classical.propDecidable _) = true)).card) * d := by
    exact_mod_cast weighted
  have light : (S.filter (fun e => ¬ multiple e)).card ≤ (S.image Prod.snd).card := by
    apply Finset.card_le_card_of_injOn Prod.snd
    · intro e he
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.mp he).1
    · intro e he f hf eq
      apply Prod.ext _ eq
      by_contra ne
      exact (Finset.mem_filter.mp he).2 ⟨f,(Finset.mem_filter.mp hf).1,eq.symm,Ne.symm ne⟩
  rw [← Finset.card_filter_add_card_filter_not (s := S) multiple]
  exact Nat.add_le_add heavy light

end PEqualNP.MetaComplexity.WeightedIncidence
