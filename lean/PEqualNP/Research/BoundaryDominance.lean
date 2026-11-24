import PEqualNP.Outside.L_meta_2668

/- The bypass and monotonicity lemmas used below are from the upstream proof of L-meta-2668.
   We compare a gate against every earlier wire on the two extremal parts of its truth table. -/
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_2668 PEqualNP.TopForm

theorem PEqualNP.Research.BoundaryDominance :
∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.IsLeastAO G C → ∀ r < C.gates.length, ∀ i < n + r,
  let w := fun (x : Fin n → Bool) (k : ℕ) => (C.wires (List.ofFn x)).getD k false
  ¬ ((∀ a b : Fin n, G.Adj a b →
        w (PEqualNP.EdgeOwnership.pairInput a b) (n+r) = true →
        w (PEqualNP.EdgeOwnership.pairInput a b) i = true) ∧
     (∀ x : Fin n → Bool, Maximal (fun y => PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ y = false) x →
        w x i = true → w x (n+r) = true)) := by
  intro n G _ C least r hr i hi w profiles
  let D := bypass n C r i
  have model := least.1
  have hm : Monotone2 C := fun g hg => ⟨model.1 _ hg, (model.2.2 _ hg).le⟩
  have dm : Monotone2 D := bypass_mono hm
  have exactAO : IsAO2 n D := by
    refine ⟨?_,bypass_readsBack hi model.2.1,?_⟩
    · intro g hg
      exact (dm g hg).1
    · intro g hg
      obtain ⟨g',hg',_,hlen⟩ := bypass_mem (n := n) (C := C) (r := r) (i := i) g hg
      exact hlen.trans (model.2.2 _ hg')
  have spec (x : Fin n → Bool) : C.eval (List.ofFn x) = graphFun G ∅ x :=
    congrFun least.2.1 x
  have positive (a b : Fin n) (h : G.Adj a b) :
      D.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput a b)) = true := by
    apply bypass_eval_rel (R := fun a b => a = true → b = true) (fun _ => id) opMono_imp
      (by simp) (mono_ops hm) hr (Or.inl hi) (profiles.1 a b h)
    rw [spec]
    exact pair_true G a b h
  have neg (x : Fin n → Bool) (maximal : Maximal (fun y => graphFun G ∅ y = false) x) :
      D.eval (List.ofFn x) ≠ true := by
    intro hd
    have hc := bypass_eval_rel (R := fun a b => b = true → a = true) (fun _ => id) opMono_reverse
      (n := n) (C := C) (x := List.ofFn x) (by simp) (mono_ops hm) hr (Or.inl hi)
      (profiles.2 x maximal) hd
    rw [spec, maximal.1] at hc
    contradiction
  have equal : circuitFun n D = graphFun G ∅ := by
    funext x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      cases hf : graphFun G ∅ x
      · obtain ⟨y,hxy,hy⟩ := Finite.exists_le_maximal (p := fun y => graphFun G ∅ y = false) hf
        apply False.elim (neg y hy ?_)
        apply circuit_monotone n D dm x y _ hx
        intro v hv
        have hle := hxy v
        rw [hv] at hle
        exact top_unique hle
      · rfl
    · intro hx
      obtain ⟨a,b,hab,ha,hb⟩ := (graph_true G x).mp hx
      apply circuit_monotone n D dm _ x _ (positive a b hab)
      intro v hv
      obtain rfl | rfl : v = a ∨ v = b := by simpa [PEqualNP.EdgeOwnership.pairInput] using hv
      · exact ha
      · exact hb
  have smaller := least.2.2 D exactAO equal
  have sizeD : D.size = C.gates.length - 1 := bypass_length n C r i
  change C.gates.length ≤ D.size at smaller
  omega

#print axioms PEqualNP.Research.BoundaryDominance

