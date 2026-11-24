import PEqualNP.Research.SensitiveProjection

namespace PEqualNP.Research.PairOrDecoder

open PEqualNP.Research.SensitiveProjection

private theorem mono {n : ℕ} (G : SimpleGraph (Fin n)) {X Y : Finset (Fin n)}
    (h : X ⊆ Y) : HasEdge G X → HasEdge G Y := by
  rintro ⟨a,ha,b,hb,hab⟩
  exact ⟨a,h ha,b,h hb,hab⟩

private theorem insert_independent {n : ℕ} (G : SimpleGraph (Fin n)) {X : Finset (Fin n)}
    {u : Fin n} (hx : ¬ HasEdge G X) (hf : ∀ p ∈ X, ¬ G.Adj u p) :
    ¬ HasEdge G (insert u X) := by
  rintro ⟨a,ha,b,hb,hab⟩
  simp only [Finset.mem_insert] at ha hb
  rcases ha with rfl | haX <;> rcases hb with rfl | hbX
  · exact hab.ne rfl
  · exact hf _ hbX hab
  · exact hf _ haX hab.symm
  · exact hx ⟨a,haX,b,hbX,hab⟩

end PEqualNP.Research.PairOrDecoder

open PEqualNP.Research.SensitiveProjection
open PEqualNP.Research.PairOrDecoder in
theorem PEqualNP.Research.PairOrDecoder :
∀ (n : ℕ) (G H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
  (∃ decode : (Fin n → Fin n → Prop) → Prop, ∀ X : Finset (Fin n),
    decode (fun i j => H.Adj i j ∧ (i ∈ X ∨ j ∈ X)) ↔
      ∃ a ∈ X, ∃ b ∈ X, G.Adj a b) ↔
  (∀ v a, G.Adj v a → ∃ i ∈ insert a (H.neighborFinset v),
    ∃ j ∈ insert a (H.neighborFinset v), G.Adj i j) := by
  classical
  intro n G H _
  let obs (X : Finset (Fin n)) := fun i j => H.Adj i j ∧ (i ∈ X ∨ j ∈ X)
  constructor
  · rintro ⟨decode,works⟩ v a hva
    let X := insert a (H.neighborFinset v)
    have hObs : obs (insert v X) = obs X := by
      funext i j
      apply propext
      constructor
      · rintro ⟨hij,hi | hj⟩
        · rcases Finset.mem_insert.mp hi with rfl | hiX
          · exact ⟨hij, Or.inr (Finset.mem_insert_of_mem ((H.mem_neighborFinset _ _).mpr hij))⟩
          · exact ⟨hij, Or.inl hiX⟩
        · rcases Finset.mem_insert.mp hj with rfl | hjX
          · exact ⟨hij, Or.inl (Finset.mem_insert_of_mem ((H.mem_neighborFinset _ _).mpr hij.symm))⟩
          · exact ⟨hij, Or.inr hjX⟩
      · exact fun ⟨hij,h⟩ => ⟨hij,h.imp Finset.mem_insert_of_mem Finset.mem_insert_of_mem⟩
    have edge : HasEdge G (insert v X) :=
      ⟨v, Finset.mem_insert_self .., a, Finset.mem_insert_of_mem (Finset.mem_insert_self ..), hva⟩
    have pos : decode (obs (insert v X)) := (works _).mpr edge
    rw [hObs] at pos
    exact (works _).mp pos
  · intro localTest
    let recover (o : Fin n → Fin n → Prop) :=
      Finset.univ.filter (fun i => ∀ j, H.Adj i j → o i j)
    have mem_recover (o : Fin n → Fin n → Prop) (i : Fin n) :
        i ∈ recover o ↔ ∀ j, H.Adj i j → o i j := by simp [recover]
    refine ⟨fun o => HasEdge G (recover o), ?_⟩
    intro X
    change HasEdge G (recover (obs X)) ↔ HasEdge G X
    have extendsX : X ⊆ recover (obs X) := by
      intro i hi
      exact (mem_recover _ _).mpr (fun j h => ⟨h,Or.inl hi⟩)
    have full {v : Fin n} (h : v ∈ recover (obs X)) (hv : v ∉ X) : H.neighborFinset v ⊆ X := by
      intro j hj
      exact ((mem_recover _ _).mp h j ((H.mem_neighborFinset _ _).mp hj)).2.resolve_left hv
    refine ⟨?_, mono G extendsX⟩
    intro positive
    by_contra hx
    have noCross {v : Fin n} (hv : v ∈ recover (obs X)) {a : Fin n} (ha : a ∈ X) :
        ¬ G.Adj v a := by
      intro hva
      by_cases hvX : v ∈ X
      · exact hx ⟨v,hvX,a,ha,hva⟩
      · exact hx (mono G (Finset.insert_subset ha (full hv hvX)) (localTest v a hva))
    obtain ⟨v,hv,a,ha,hva⟩ := positive
    by_cases hvX : v ∈ X
    · exact noCross ha hvX hva.symm
    · have noNeighborEdge : ¬ HasEdge G (H.neighborFinset v) :=
        fun h => hx (mono G (full hv hvX) h)
      exact insert_independent G noNeighborEdge (fun p hp => noCross ha (full hv hvX hp))
        (localTest v a hva)

#print axioms PEqualNP.Research.PairOrDecoder
