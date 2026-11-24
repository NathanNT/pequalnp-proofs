import PEqualNP.MetaComplexity.WeightedIncidence

namespace PEqualNP.MetaComplexity.WeightedIncidence
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.ReadK

noncomputable def orCount (C : Circuit) : ℕ :=
  ((Finset.range C.size).filter (fun k =>
    @decide ((gateAt C k).op = GateOp.or) (Classical.propDecidable _) = true)).card

private theorem visibleBound (n : ℕ) (C : Circuit) (side : ℕ → Bool) (R : ℕ → ℕ → Bool)
    (E : Finset (ℕ × ℕ)) (mono : AndOrFanInTwo C) (back : ReadsBack n C)
    (sides : ∀ p l, R p l = true → side p = false ∧ side l = true)
    (valid : ∀ e ∈ E, R e.1 e.2 = true ∧ e.2 < n)
    (sound : ∀ z : Fin n → Bool, circuitFun n C z = true →
      ∃ i j : Fin n, R i j = true ∧ z i = true ∧ z j = true)
    (linear : ∀ p r l k, R p l = true → R r l = true → R p k = true → R r k = true →
      p ≠ r → l = k) :
    (E.filter (fun e => lineSingle C n side e.1 e.2)).card ≤
      2 * (C.size + orCount C) + (E.image Prod.snd).card := by
  classical
  let S := E.filter (fun e => lineSingle C n side e.1 e.2)
  have inside {e} (he : e ∈ S) : e ∈ E := (Finset.mem_filter.mp he).1
  have h := boundedCodegree n C side R S 1 mono back (by
    intro e he
    obtain ⟨hr,hn⟩ := valid e (inside he)
    exact ⟨hn,(sides _ _ hr).1,(sides _ _ hr).2,hr,(Finset.mem_filter.mp he).2⟩) (by
    intro l hl
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hl
    have sl := (sides _ _ (valid e (inside he)).1).2
    by_contra! ht
    obtain ⟨i,j,hij,hi,hj⟩ := sound _ (Bool.eq_true_of_not_eq_false ht)
    obtain ⟨si,sj⟩ := sides _ _ hij
    have je : j.val = e.2 := by simpa [sj] using hj
    have ine : i.val ≠ e.2 := fun h => by rw [h,sl] at si; contradiction
    have hit : R i.val e.2 = true := je ▸ hij
    simp [si,ine,hit] at hi) (by
    intro p r hpr _
    apply Finset.card_le_one.mpr
    intro e he f hf
    obtain ⟨em,ep,er⟩ := Finset.mem_filter.mp he
    obtain ⟨fm,fp,fr⟩ := Finset.mem_filter.mp hf
    have ie := (valid e (inside em)).1
    have jf := (valid f (inside fm)).1
    rw [ep] at ie
    rw [fp] at jf
    exact Prod.ext (ep.trans fp.symm) (linear p r _ _ ie er jf fr hpr))
  have subset : S.image Prod.snd ⊆ E.image Prod.snd :=
    Finset.image_mono _ (Finset.filter_subset _ _)
  change S.card ≤ _
  simpa [orCount] using h.trans (Nat.add_le_add_left (Finset.card_le_card subset) _)

-- Both orientations use the same gate count. The uncovered pairs are exactly the two-sided rereads.
theorem twoSidedLinear (n : ℕ) (C : Circuit) (side : ℕ → Bool) (R : ℕ → ℕ → Bool)
    (E : Finset (ℕ × ℕ)) (mono : AndOrFanInTwo C) (back : ReadsBack n C)
    (sides : ∀ p l, R p l = true → side p = false ∧ side l = true)
    (valid : ∀ e ∈ E, R e.1 e.2 = true ∧ e.1 < n ∧ e.2 < n)
    (sound : ∀ z : Fin n → Bool, circuitFun n C z = true →
      ∃ i j : Fin n, R i j = true ∧ z i = true ∧ z j = true)
    (linear : ∀ p r l k, R p l = true → R r l = true → R p k = true → R r k = true →
      p ≠ r → l = k) :
    E.card ≤ 4 * (C.size + orCount C) + (E.image Prod.fst).card + (E.image Prod.snd).card +
      (E.filter (fun e => !(lineSingle C n side e.1 e.2) &&
        !(lineSingle C n (fun i => !side i) e.1 e.2))).card := by
  classical
  let S := E.filter (fun e => lineSingle C n side e.1 e.2)
  let T := E.filter (fun e => lineSingle C n (fun i => !side i) e.1 e.2)
  let D := E.filter (fun e => !(lineSingle C n side e.1 e.2) &&
        !(lineSingle C n (fun i => !side i) e.1 e.2))
  have hs := visibleBound n C side R E mono back sides
    (fun e he => ⟨(valid e he).1,(valid e he).2.2⟩) sound linear
  have ht := visibleBound n C (fun i => !side i) (fun a b => R b a) (E.image Prod.swap) mono back
    (by intro a b h; simp [(sides b a h).1,(sides b a h).2])
    (by intro e he; obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
        exact ⟨(valid f hf).1,(valid f hf).2.1⟩)
    (by intro z hz; obtain ⟨i,j,hr,hi,hj⟩ := sound z hz; exact ⟨j,i,hr,hj,hi⟩)
    (by intro p r l k hlp hlr hkp hkr hpr; by_contra hlk
        exact hpr (linear l k p r hlp hkp hlr hkr hlk))
  have swapSingle (a b : ℕ) : lineSingle C n (fun i => !side i) a b =
      lineSingle C n (fun i => !side i) b a := by simp only [lineSingle,Bool.or_comm]
  have swapSet : T.image Prod.swap = (E.image Prod.swap).filter
      (fun e => lineSingle C n (fun i => !side i) e.1 e.2) := by
    ext e
    simp [T,Finset.mem_image,swapSingle e.1 e.2,Prod.swap_eq_iff_eq_swap]
  rw [← swapSet,Finset.card_image_of_injective _ Prod.swap_injective,Finset.image_image] at ht
  change T.card ≤ 2 * (C.size + orCount C) + (E.image Prod.fst).card at ht
  have cover : E ⊆ (S ∪ T) ∪ D := by
    intro e he
    cases h : lineSingle C n side e.1 e.2 <;>
      cases h' : lineSingle C n (fun i => !side i) e.1 e.2 <;> simp [S,T,D,he,h,h']
  have hc := Finset.card_le_card cover
  have h1 := Finset.card_union_le (S ∪ T) D
  have h2 := Finset.card_union_le S T
  change S.card ≤ _ at hs
  change E.card ≤ _ + D.card
  omega

end PEqualNP.MetaComplexity.WeightedIncidence

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK
open PEqualNP.MetaComplexity.NestedCover PEqualNP.MetaComplexity.WeightedIncidence
open PEqualNP.Outside.L_meta_2672

-- The line-size and uniqueness hypotheses suffice, independently of the numerical plane-order axiom.
theorem PEqualNP.MetaComplexity.ProjectivePlaneIncidence (q N : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (C : Circuit)
    (lineSize : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (uniqueLine : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (mono : AndOrFanInTwo C) (back : ReadsBack (N + N) C)
    (computes : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = decide (∃ p l : Fin N,
      I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) :
    N * q ≤ 4 * (C.size + orCount C) + N +
      (doubleReread C (N + N) (fun i => decide (N ≤ i))
        ((List.finRange N).flatMap (fun p => ((List.finRange N).filter
          (fun l => decide (I p l))).map (fun l => (p.val, N + l.val))))).length := by
  classical
  let pack (e : Fin N × Fin N) := (e.1.val,N + e.2.val)
  let incidences : Finset (Fin N × Fin N) := Finset.univ.filter (fun e => I e.1 e.2)
  let E := incidences.image pack
  let ls := (List.finRange N).flatMap (fun p => ((List.finRange N).filter
          (fun l => decide (I p l))).map (fun l => (p.val, N + l.val)))
  let side (i : ℕ) := decide (N ≤ i)
  have inj : Function.Injective pack := by
    intro a b h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    exact Prod.ext (Fin.ext h1) (Fin.ext (Nat.add_left_cancel (show N + _ = N + _ from h2)))
  have count : E.card = N * (q + 1) := by
    rw [show E.card = incidences.card from Finset.card_image_of_injective _ inj,
      show incidences.card = ∑ e : Fin N × Fin N, if I e.1 e.2 then 1 else 0 from Finset.card_filter _ _,
      Fintype.sum_prod_type_right]
    have h (l : Fin N) : (∑ p : Fin N, if I p l then 1 else 0) = q + 1 := by
      rw [← lineSize l, Finset.card_filter]
    simp [h]
  have sides (a b : ℕ) (hab : Rr N I a b = true) : side a = false ∧ side b = true := by
    obtain ⟨p,l,rfl,rfl,_⟩ := (Rr_iff N I _ _).mp hab
    simp [side,p.isLt]
  have valid (e) (he : e ∈ E) : Rr N I e.1 e.2 = true ∧ e.1 < N+N ∧ e.2 < N+N := by
    obtain ⟨⟨p,l⟩,hm,rfl⟩ := Finset.mem_image.mp he
    exact ⟨(Rr_iff N I _ _).mpr ⟨p,l,rfl,rfl,(Finset.mem_filter.mp hm).2⟩,
      by have := p.isLt; change p.val < _; omega, Nat.add_lt_add_left l.isLt N⟩
  have sound (z : Fin (N+N) → Bool) (hz : circuitFun (N+N) C z = true) :
      ∃ i j : Fin (N+N), Rr N I i j = true ∧ z i = true ∧ z j = true := by
    rw [computes,decide_eq_true_eq] at hz
    obtain ⟨p,l,hi,hp,hl⟩ := hz
    exact ⟨Fin.castAdd N p,Fin.natAdd N l,(Rr_iff N I _ _).mpr ⟨p,l,rfl,rfl,hi⟩,hp,hl⟩
  have rect (a b l k : ℕ) (al : Rr N I a l = true) (bl : Rr N I b l = true)
      (ak : Rr N I a k = true) (bk : Rr N I b k = true) (ne : a ≠ b) : l = k := by
    obtain ⟨p,u,rfl,rfl,hpu⟩ := (Rr_iff N I _ _).mp al
    obtain ⟨r,v,rfl,hv,hrv⟩ := (Rr_iff N I _ _).mp bl
    obtain ⟨p',w,hp,rfl,hpw⟩ := (Rr_iff N I _ _).mp ak
    obtain ⟨r',w',hr,hw,hrw⟩ := (Rr_iff N I _ _).mp bk
    obtain rfl : u = v := Fin.ext (Nat.add_left_cancel hv)
    obtain rfl : p = p' := Fin.ext hp
    obtain rfl : r = r' := Fin.ext hr
    obtain rfl : w = w' := Fin.ext (Nat.add_left_cancel hw)
    obtain ⟨_,_,uniq⟩ := uniqueLine p r (fun h => ne (congrArg Fin.val h))
    rw [(uniq u ⟨hpu,hrv⟩).trans (uniq w ⟨hpw,hrw⟩).symm]
  have bound := twoSidedLinear (N+N) C side (Rr N I) E mono back sides valid sound rect
  have nr : (E.image Prod.fst).card ≤ N := by
    apply le_trans (Finset.card_le_card (t := Finset.range N) ?_) (by simp)
    intro x hx
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_range.mpr f.1.isLt
  have nc : (E.image Prod.snd).card ≤ N := by
    let cols := (Finset.univ : Finset (Fin N)).image (fun l => N + l.val)
    apply le_trans (Finset.card_le_card (t := cols) ?_) (Finset.card_image_le.trans (by simp))
    intro x hx
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_image.mpr ⟨f.2,Finset.mem_univ _,rfl⟩
  have asList : E ⊆ ls.toFinset := by
    intro e he
    obtain ⟨⟨p,l⟩,hm,rfl⟩ := Finset.mem_image.mp he
    simpa only [List.mem_toFinset,ls,List.mem_flatMap,List.mem_map,List.mem_filter,
      List.mem_finRange,true_and,decide_eq_true_eq] using
      (show ∃ p' l' : Fin N, I p' l' ∧ (p'.val,N+l'.val) = pack (p,l) from
        ⟨p,l,(Finset.mem_filter.mp hm).2,rfl⟩)
  let missed (e : ℕ × ℕ) := !(lineSingle C (N+N) side e.1 e.2) &&
    !(lineSingle C (N+N) (fun i => !side i) e.1 e.2)
  have nd : (E.filter (fun e => missed e)).card ≤ (doubleReread C (N+N) side ls).length := by
    apply le_trans (Finset.card_le_card (t := (doubleReread C (N+N) side ls).toFinset) ?_)
      (List.toFinset_card_le _)
    intro e he
    obtain ⟨hm,hd⟩ := Finset.mem_filter.mp he
    exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨List.mem_toFinset.mp (asList hm),hd⟩)
  change E.card ≤ _ + (E.filter (fun e => missed e)).card at bound
  change _ ≤ _ + (doubleReread C (N+N) side ls).length
  rw [count,Nat.mul_add,Nat.mul_one] at bound
  omega
