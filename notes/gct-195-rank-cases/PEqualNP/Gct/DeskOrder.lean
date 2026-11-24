import PEqualNP.Gct.DeskPolarization
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Subperm

namespace PEqualNP.Gct.DeskPolar
set_option maxRecDepth 30000
private theorem reorder_perm {q u : Word} (hu : u ∈ permutationsOf q) : u.Perm q := by
  rcases q with _|⟨a,_|⟨b,_|⟨c,_|⟨d,_|⟨e,t⟩⟩⟩⟩⟩
  all_goals simp only [permutationsOf, List.mem_cons, List.not_mem_nil, or_false] at hu
  all_goals first | contradiction | skip
  · rcases hu with rfl <;> apply List.perm_iff_count.mpr <;> intro i <;>
      simp only [List.count_cons,List.count_nil] <;> omega
  · rcases hu with rfl|rfl <;> apply List.perm_iff_count.mpr <;> intro i <;>
      simp only [List.count_cons,List.count_nil] <;> omega
  · rcases hu with rfl|rfl|rfl|rfl|rfl|rfl <;> apply List.perm_iff_count.mpr <;> intro i <;>
      simp only [List.count_cons,List.count_nil] <;> omega
  · rcases hu with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> apply List.perm_iff_count.mpr <;> intro i <;>
      simp only [List.count_cons,List.count_nil] <;> omega
private lemma build_word (w : Word) (rs cs : List Nat) (hr : (w.map Prod.fst).Nodup)
    (hc : (w.map Prod.snd).Nodup) (ar : ∀ p∈w, p.1 ∈ rs) (ac : ∀ p∈w, p.2 ∈ cs) :
    w ∈ words w.length rs cs := by
  induction w generalizing rs cs with
  | nil => simp [words]
  | cons p w ih =>
    rcases p with ⟨r,j⟩
    simp only [List.map_cons,List.nodup_cons] at hr hc
    simp only [List.length_cons,words,List.mem_flatMap,List.mem_map]
    refine ⟨r,ar (r,j) (by simp),j,ac (r,j) (by simp),w,ih _ _ hr.2 hc.2 ?_ ?_,rfl⟩
    · intro t ht
      apply (List.mem_erase_of_ne _).mpr (ar t (by simp [ht]))
      intro he
      exact hr.1 (List.mem_map.mpr ⟨t,ht,he⟩)
    · intro t ht
      apply (List.mem_erase_of_ne _).mpr (ac t (by simp [ht]))
      intro he
      exact hc.1 (List.mem_map.mpr ⟨t,ht,he⟩)

private lemma permNoDup {q : Word} (h : q.Nodup) : (permutationsOf q).Nodup := by
  rcases q with _|⟨a,_|⟨b,_|⟨c,_|⟨d,_|⟨e,t⟩⟩⟩⟩⟩
  all_goals try simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at h
  all_goals simp_all [permutationsOf,ne_comm]
private def orderKey (k : Nat) (q : Word) : Nat :=
  if k=1 then q.foldl (fun n p => 24*n+6*p.1+p.2) 0 else
    256*q.foldl (fun n p => 6*n+p.2) 0 + q.foldl (fun n p => 4*n+p.1) 0
private lemma noDesk (k : Nat) (h : ((desk k).map (orderKey k)).IsChain (· < ·)) :
    (desk k).Nodup := (List.isChain_iff_pairwise.mp h).nodup.of_map
private def fall : Nat → Nat → Nat
  | 0,_ => 1
  | n+1,m => m*fall n (m-1)
private lemma sumConst {α : Type*} (l : List α) (f : α → Nat) (v : Nat)
    (h : ∀ a∈l,f a=v) : (l.map f).sum=l.length*v := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp [h a (by simp),ih (fun i hi => h i (by simp [hi])),Nat.add_mul,Nat.add_comm]
private lemma lengthWords (k : Nat) (rs cs : List Nat) :
    (words k rs cs).length=fall k rs.length*fall k cs.length := by
  induction k generalizing rs cs with
  | zero => simp [words,fall]
  | succ k ih =>
    simp only [words,List.length_flatMap,List.length_map]
    calc
      _ = rs.length*(cs.length*(fall k (rs.length-1)*fall k (cs.length-1))) := by
        apply sumConst; intro r hr
        apply sumConst; intro j hj
        rw [ih,List.length_erase_of_mem hr,List.length_erase_of_mem hj]
      _ = _ := by simp only [fall]; ring

private lemma countReorders (q : Word) (h : q.length≤4) : (permutationsOf q).length=(if q.length=0 then 0 else q.length.factorial) := by
  rcases q with _|⟨a,_|⟨b,_|⟨c,_|⟨d,_|⟨e,t⟩⟩⟩⟩⟩ <;> first | rfl | (simp at h; omega)
private lemma expandedLength (k : Nat) (hk : k≤4)
    (hl : (desk k).all (fun q => q.length==k)=true) :
    ((desk k).flatMap permutationsOf).length=(desk k).length*(if k=0 then 0 else k.factorial) := by
  rw [List.length_flatMap]
  apply sumConst
  intro q hq
  have e := eq_of_beq (List.all_eq_true.mp hl q hq)
  rw [countReorders q (e ▸ hk),e]

private def valid (k : Nat) (q : Word) : Prop :=
    q.length=k ∧ (q.map Prod.fst).Nodup ∧ (q.map Prod.snd).Nodup ∧
    (∀ p ∈ q, p.1<4 ∧ p.2<6) ∧ q.Pairwise (fun a b => a.1 < b.1)
private instance (k : Nat) (q : Word) : Decidable (valid k q) := by unfold valid; infer_instance
private lemma orderProof (k : Nat)
    (hv : (desk k).all (fun q => decide (valid k q))=true)
    (hn : (desk k).Nodup)
    (hl : (words k (List.range 4) (List.range 6)).length=((desk k).flatMap permutationsOf).length) :
    (words k (List.range 4) (List.range 6)).Perm ((desk k).flatMap permutationsOf) := by
  have good {q : Word} (h : q∈desk k) : valid k q := of_decide_eq_true (List.all_eq_true.mp hv q h)
  have no : ((desk k).flatMap permutationsOf).Nodup := by
    apply List.nodup_flatMap.mpr
    constructor
    · exact fun q h => permNoDup ((good h).2.1.of_map)
    · apply hn.imp_of_mem
      intro x y hx hy xy u ux uy
      apply xy
      have hp := (reorder_perm ux).symm.trans (reorder_perm uy)
      exact hp.eq_of_pairwise (le := fun a b => a.1 < b.1) (fun _ _ _ _ a b => by omega)
        (good hx).2.2.2.2 (good hy).2.2.2.2
  have incl : ((desk k).flatMap permutationsOf) ⊆ (words k (List.range 4) (List.range 6)) := by
    intro u hu
    obtain ⟨q,hq,huq⟩ := List.mem_flatMap.mp hu
    have hp := reorder_perm huq
    obtain ⟨hlen,hr,hc,mem,_⟩ := good hq
    rw [← hlen,← hp.length_eq]
    exact build_word u _ _ ((hp.map Prod.fst).nodup_iff.mpr hr) ((hp.map Prod.snd).nodup_iff.mpr hc)
      (fun p h => List.mem_range.mpr (mem p (hp.subset h)).1)
      (fun p h => List.mem_range.mpr (mem p (hp.subset h)).2)
  obtain ⟨v,hp,hs⟩ := List.subperm_of_subset no incl
  have he := hs.eq_of_length (hp.length_eq.trans hl.symm)
  exact he ▸ hp
set_option maxHeartbeats 0 in
theorem perm1 : (words 1 (List.range 4) (List.range 6)).Perm ((desk 1).flatMap permutationsOf) :=
  orderProof 1 (by decide) (noDesk 1 (by decide)) (by rw [lengthWords,expandedLength _ (by decide) (by decide)]; decide)
set_option maxHeartbeats 0 in
theorem perm2 : (words 2 (List.range 4) (List.range 6)).Perm ((desk 2).flatMap permutationsOf) :=
  orderProof 2 (by decide) (noDesk 2 (by decide)) (by rw [lengthWords,expandedLength _ (by decide) (by decide)]; decide)
set_option maxHeartbeats 0 in
theorem perm3 : (words 3 (List.range 4) (List.range 6)).Perm ((desk 3).flatMap permutationsOf) :=
  orderProof 3 (by decide) (noDesk 3 (by decide)) (by rw [lengthWords,expandedLength _ (by decide) (by decide)]; decide)
set_option maxHeartbeats 0 in
theorem perm4 : (words 4 (List.range 4) (List.range 6)).Perm ((desk 4).flatMap permutationsOf) :=
  orderProof 4 (by decide) (noDesk 4 (by decide)) (by rw [lengthWords,expandedLength _ (by decide) (by decide)]; decide)
end PEqualNP.Gct.DeskPolar


