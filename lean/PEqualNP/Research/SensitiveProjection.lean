import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths

namespace PEqualNP.Research.SensitiveProjection

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The graph edge predicate on the set of vertices assigned true. -/
def HasEdge (X : Finset V) : Prop := ∃ a ∈ X, ∃ b ∈ X, G.Adj a b

/-- The two assignments differ only at v; the assignment not containing v is negative. -/
def Sensitive (v : V) (X : Finset V) : Prop :=
  v ∉ X ∧ ¬ HasEdge G X ∧ HasEdge G (insert v X)

omit [Fintype V] [DecidableRel G.Adj] in
theorem sensitive_iff {v : V} {X : Finset V} (hv : v ∉ X) :
    Sensitive G v X ↔ ¬ HasEdge G X ∧ ∃ a ∈ X, G.Adj v a := by
  constructor
  · rintro ⟨_, hn, a, ha, b, hb, hab⟩
    refine ⟨hn, ?_⟩
    rcases Finset.mem_insert.mp ha with rfl | haX
    · exact ⟨b, (Finset.mem_insert.mp hb).resolve_left hab.ne.symm, hab⟩
    · rcases Finset.mem_insert.mp hb with rfl | hb
      · exact ⟨a, haX, hab.symm⟩
      · exact (hn ⟨a, haX, b, hb, hab⟩).elim
  · rintro ⟨hn, a, ha, h⟩
    exact ⟨hv, hn, v, Finset.mem_insert_self .., a, Finset.mem_insert_of_mem ha, h⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- A partial assignment T ⊆ S extends to a row where v is pivotal exactly when
T contains no edge and either sees v or leaves a compatible unpinned neighbor. -/
theorem projection_iff {v : V} {S T : Finset V} (hv : v ∉ S) (hTS : T ⊆ S) :
    (∃ X, Sensitive G v X ∧ X ∩ S = T) ↔
    ¬ HasEdge G T ∧ ((∃ a ∈ T, G.Adj v a) ∨
      ∃ a, G.Adj v a ∧ a ∉ S ∧ ∀ p ∈ T, ¬ G.Adj p a) := by
  constructor
  · rintro ⟨X, hX, rfl⟩
    obtain ⟨hn, a, ha, hva⟩ := (sensitive_iff G hX.1).mp hX
    refine ⟨?_, ?_⟩
    · rintro ⟨i, hi, j, hj, hij⟩
      exact hn ⟨i, (Finset.mem_inter.mp hi).1, j, (Finset.mem_inter.mp hj).1, hij⟩
    · by_cases haS : a ∈ S
      · exact Or.inl ⟨a, Finset.mem_inter.mpr ⟨ha,haS⟩, hva⟩
      · exact Or.inr ⟨a, hva, haS, fun p hp hpa =>
          hn ⟨p, (Finset.mem_inter.mp hp).1, a, ha, hpa⟩⟩
  · rintro ⟨hn, h | ⟨a,hva,haS,hsep⟩⟩
    · exact ⟨T, (sensitive_iff G (fun hvt => hv (hTS hvt))).mpr ⟨hn,h⟩,
        Finset.inter_eq_left.mpr hTS⟩
    · have hvX : v ∉ insert a T := fun h => (Finset.mem_insert.mp h).elim hva.ne
          (fun hvT => hv (hTS hvT))
      refine ⟨insert a T, (sensitive_iff G hvX).mpr ⟨?_, a, Finset.mem_insert_self .., hva⟩, ?_⟩
      · rintro ⟨i, hi, j, hj, hij⟩
        rcases Finset.mem_insert.mp hi with rfl | hiT <;> rcases Finset.mem_insert.mp hj with rfl | hjT
        · exact hij.ne rfl
        · exact hsep j hjT hij.symm
        · exact hsep i hiT hij
        · exact hn ⟨i,hiT,j,hjT,hij⟩
      · ext i
        simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hi,his⟩
          · exact (haS his).elim
          · exact hi
        · exact fun hi => ⟨Or.inr hi, hTS hi⟩

/-- Two distinct neighbors of v have no common neighbor outside the closed neighborhood of v. -/
def BranchSeparated (v : V) : Prop :=
  ∀ p, p ≠ v → ¬ G.Adj v p → ∀ a b, G.Adj v a → G.Adj v b →
    G.Adj p a → G.Adj p b → a = b

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem separated_of_no_square {v : V} (h : ∀ w : G.Walk v v, w.IsCycle → w.length ≠ 4) :
    BranchSeparated G v := by
  intro p hp _ a b hva hvb hpa hpb
  by_contra hne
  let w : G.Walk v v := .cons hva (.cons hpa.symm (.cons hpb (.cons hvb.symm .nil)))
  apply h w _ rfl
  apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · rw [SimpleGraph.Walk.isPath_def]
    change [a,p,b,v].Nodup
    simp [hne,hpa.ne.symm,hva.ne.symm,hpb.ne,hp,hvb.ne.symm]
  · exact (by decide : 3 ≤ 4)

/-- Every independent pattern on fewer than degree(v) other coordinates occurs on
a sensitive row. At degree(v) the all-false neighborhood is a sharp obstruction. -/
theorem small_projection {v : V} (hsep : BranchSeparated G v) {S T : Finset V}
    (hv : v ∉ S) (hTS : T ⊆ S) (hcard : S.card < G.degree v) (hn : ¬ HasEdge G T) :
    ∃ X, Sensitive G v X ∧ X ∩ S = T := by
  classical
  apply (projection_iff G hv hTS).mpr
  refine ⟨hn, ?_⟩
  by_contra! h
  have block (a : ↥(G.neighborFinset v)) :
      ∃ p : S, (p.val = a.val ∧ p.val ∉ T) ∨ (p.val ∈ T ∧ G.Adj p.val a.val) := by
    have hva := (G.mem_neighborFinset v _).mp a.property
    by_cases ha : a.val ∈ S
    · exact ⟨⟨_,ha⟩, Or.inl ⟨rfl, fun ht => h.1 _ ht hva⟩⟩
    · obtain ⟨p, hp, hpa⟩ := h.2 a.val hva ha
      exact ⟨⟨p, hTS hp⟩, Or.inr ⟨hp,hpa⟩⟩
  choose f hf using block
  have inj : Function.Injective f := by
    intro a b hab
    have hb := hf b
    rw [← hab] at hb
    apply Subtype.ext
    rcases hf a with ⟨ha, hna⟩ | ⟨ha, hap⟩ <;> rcases hb with ⟨hb,hnb⟩ | ⟨hb,hbp⟩
    · exact ha.symm.trans hb
    · exact (hna hb).elim
    · exact (hnb ha).elim
    · exact hsep _ (fun eq => hv (eq ▸ (f a).property)) (h.1 _ ha) a b
        ((G.mem_neighborFinset v _).mp a.property) ((G.mem_neighborFinset v _).mp b.property) hap hbp
  have bound := Finset.card_le_card_of_injective inj
  exact hcard.not_ge (by simpa using bound)

theorem neighborhood_obstruction (v : V) :
    ¬ ∃ X, Sensitive G v X ∧ X ∩ G.neighborFinset v = ∅ := by
  rintro ⟨X,hX,hzero⟩
  obtain ⟨_,a,ha,hva⟩ := (sensitive_iff G hX.1).mp hX
  have ham : a ∈ X ∩ G.neighborFinset v := Finset.mem_inter.mpr ⟨ha, (G.mem_neighborFinset v _).mpr hva⟩
  simp [hzero] at ham

/-- A decoder receives the unmodified other inputs X and a single bit through which v
is observed. If this bit is a function of v and the pins in S, its two values must
differ on every independent pin pattern below the degree threshold. -/
theorem reader_separates {v : V} (hsep : BranchSeparated G v) {S : Finset V}
    (hv : v ∉ S) (hcard : S.card < G.degree v)
    (wire : Finset V → Bool → Bool) (decode : Finset V → Bool → Prop)
    (correct : ∀ X, v ∉ X → ∀ b : Bool, decode X (wire (X ∩ S) b) ↔
      HasEdge G (if b then insert v X else X)) (T : Finset V) (hTS : T ⊆ S) (hn : ¬ HasEdge G T) :
    wire T false ≠ wire T true := by
  obtain ⟨X,hX,hproj⟩ := small_projection G hsep hv hTS hcard hn
  have h0 := correct X hX.1 false
  have h1 := correct X hX.1 true
  rw [hproj] at h0 h1
  intro eq
  exact hX.2.1 (h0.mp (eq ▸ h1.mpr hX.2.2))

end PEqualNP.Research.SensitiveProjection

theorem PEqualNP.Research.SensitiveProjection :
∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n),
  (∀ w : G.Walk v v, w.IsCycle → w.length ≠ 4) →
  ∀ (S : Finset (Fin n)), v ∉ S → S.card < G.degree v →
  ∀ (wire : Finset (Fin n) → Bool → Bool) (decode : Finset (Fin n) → Bool → Prop),
  (∀ X : Finset (Fin n), v ∉ X → ∀ b : Bool, decode X (wire (X ∩ S) b) ↔
    ∃ i ∈ (if b then insert v X else X), ∃ j ∈ (if b then insert v X else X), G.Adj i j) →
  ∀ T : Finset (Fin n), T ⊆ S → (¬ ∃ i ∈ T, ∃ j ∈ T, G.Adj i j) →
    wire T false ≠ wire T true := by
  intro n G _ v h S hv hsize wire decode correct T hTS hn
  exact SensitiveProjection.reader_separates G (SensitiveProjection.separated_of_no_square G h)
    hv hsize wire decode correct T hTS hn

#print axioms PEqualNP.Research.SensitiveProjection
