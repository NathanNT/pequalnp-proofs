import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Research.RowPair
abbrev V := Fin 4 → ℂ
abbrev M := Matrix (Fin 4) (Fin 4) ℂ

lemma obstruction (T : M) (i j k : Fin 4) (hij : i ≠ j)
    (hi : ∀ l, l ≠ k → T i l=0) (hj : ∀ l, l ≠ k → T j l=0) : T.permanent=0 := by
  unfold Matrix.permanent
  apply Finset.sum_eq_zero
  intro σ _
  by_cases he : σ.symm i=k
  · have hn : σ.symm j≠k := fun h => hij (σ.symm.injective (he.trans h.symm))
    exact Finset.prod_eq_zero (Finset.mem_univ (σ.symm j)) (by simpa using hj _ hn)
  · exact Finset.prod_eq_zero (Finset.mem_univ (σ.symm i)) (by simpa using hi _ he)

lemma nonzero_row (T : M) (hn : T.permanent ≠ 0) (i : Fin 4) : T i ≠ 0 := by
  intro h
  apply hn
  unfold Matrix.permanent
  apply Finset.sum_eq_zero
  intro σ _
  exact Finset.prod_eq_zero (Finset.mem_univ (σ.symm i)) (by simpa using congrFun h (σ.symm i))

noncomputable def readRow (L : Submodule ℂ M) (i : Fin 4) : L →ₗ[ℂ] V where
  toFun X := X.val i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma normal (L : Submodule ℂ M) (B : M) (lev : ∀ X ∈ L, (B+X).permanent ≠ 0) (i : Fin 4) :
    ∃ f : V →ₗ[ℂ] ℂ, f (B i)=1 ∧ ∀ X : L, f (X.val i)=0 := by
  have he : B i ∉ LinearMap.range (readRow L i) := by
    rintro ⟨X,hX⟩
    apply nonzero_row _ (lev _ (L.neg_mem X.property)) i
    change (X : M) i = B i at hX
    change B i + -(X : M) i = 0
    rw [hX,add_neg_cancel]
  obtain ⟨f,hb,hker⟩ := Submodule.exists_le_ker_of_notMem he
  refine ⟨(f (B i))⁻¹ • f,by simp [hb],?_⟩
  intro X
  have h : f (X.val i)=0 := hker ⟨X,rfl⟩
  simp [h]

lemma expand (f : V →ₗ[ℂ] ℂ) (x : V) : f x = ∑ k, x k * f (Pi.single k 1) := by
  have e : x = ∑ k, x k • (Pi.single k 1 : V) := by
    funext i
    simp [Finset.sum_apply,Pi.single_apply]
  calc
    f x = f (∑ k, x k • (Pi.single k 1 : V)) := congrArg f e
    _ = _ := by simp

theorem rigid (L : Submodule ℂ M) (B : M)
    (hd : Module.finrank ℂ L=6) (lev : ∀ X ∈ L, (B+X).permanent ≠ 0)
    (hinj : ∀ i j : Fin 4, i≠j → Function.Injective (fun X : L => (X.val i,X.val j))) :
    ∃ σ : Equiv.Perm (Fin 4), ∀ X ∈ L, ∀ i, X i (σ i)=0 := by
  classical
  choose f hb hL using normal L B lev
  have dim (i : Fin 4) : Module.finrank ℂ (LinearMap.ker (f i)) ≤ 3 := by
    have hn : LinearMap.ker (f i) < ⊤ := lt_top_iff_ne_top.mpr (by
      intro h
      have e : B i ∈ LinearMap.ker (f i) := h ▸ Submodule.mem_top
      have e' : f i (B i)=0 := e
      rw [hb] at e'
      norm_num at e')
    have e := Submodule.finrank_lt_finrank_of_lt hn
    have : Module.finrank ℂ (LinearMap.ker (f i)) < 4 := by simpa using e
    omega
  let row (i : Fin 4) := (readRow L i).codRestrict (LinearMap.ker (f i)) (hL i)
  have disjoint (i j k : Fin 4) (hij : i≠j) (hi : f i (Pi.single k 1)≠0)
      (hj : f j (Pi.single k 1)≠0) : False := by
    let pair := (row i).prod (row j)
    have inj : Function.Injective pair := by
      intro X Y h
      apply hinj i j hij
      exact Prod.ext (congrArg Subtype.val (congrArg Prod.fst h))
        (congrArg Subtype.val (congrArg Prod.snd h))
    have lower := pair.finrank_le_finrank_of_injective inj
    rw [Module.finrank_prod,hd] at lower
    have eqd : Module.finrank ℂ L = Module.finrank ℂ (LinearMap.ker (f i) × LinearMap.ker (f j)) := by
      rw [Module.finrank_prod,hd]
      have := dim i
      have := dim j
      omega
    have onto := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank eqd).mp inj
    let w (r : Fin 4) : V := (f r (Pi.single k 1))⁻¹ • Pi.single k 1 - B r
    have mem (r : Fin 4) (hr : f r (Pi.single k 1)≠0) : w r ∈ LinearMap.ker (f r) := by
      change f r (_ - _) = 0
      simp [hb,hr]
    obtain ⟨X,hX⟩ := onto (⟨w i,mem i hi⟩,⟨w j,mem j hj⟩)
    have xi : X.val i = w i := congrArg Subtype.val (congrArg Prod.fst hX)
    have xj : X.val j = w j := congrArg Subtype.val (congrArg Prod.snd hX)
    apply lev X X.property
    apply obstruction _ i j k hij
    · intro l hl
      change B i l + X.val i l=0
      rw [xi]
      simp [w,Ne.symm hl]
    · intro l hl
      change B j l + X.val j l=0
      rw [xj]
      simp [w,Ne.symm hl]
  have exist (i : Fin 4) : ∃ k, f i (Pi.single k 1)≠0 := by
    by_contra! ha
    have h := expand (f i) (B i)
    simp [ha,hb] at h
  choose p hp using exist
  have pinj : Function.Injective p := by
    intro i j e
    by_contra hij
    exact disjoint i j (p i) hij (hp i) (e ▸ hp j)
  let σ := Equiv.ofBijective p (Finite.injective_iff_bijective.mp pinj)
  refine ⟨σ,fun X hX i => ?_⟩
  have zeros (k : Fin 4) (hk : k ≠ σ i) : f i (Pi.single k 1)=0 := by
    obtain ⟨j,rfl⟩ := σ.surjective k
    by_contra hn
    exact disjoint i j (σ j) (fun e => hk (congrArg σ e.symm)) hn (hp j)
  have e := expand (f i) (X i)
  rw [Finset.sum_eq_single (σ i)] at e
  · rw [hL i ⟨X,hX⟩] at e
    exact (mul_eq_zero.mp e.symm).resolve_right (hp i)
  · intro k _ hk
    simp [zeros k hk]
  · simp

end PEqualNP.Research.RowPair


theorem PEqualNP.Research.RowPair :
∀ (L : Submodule ℂ (Matrix (Fin 4) (Fin 4) ℂ)) (B : Matrix (Fin 4) (Fin 4) ℂ),
  Module.finrank ℂ L = 6 →
  (∀ X ∈ L, (B+X).permanent ≠ 0) →
  (∀ i j : Fin 4, i≠j → Function.Injective (fun X : L => (X.val i,X.val j))) →
  ∃ σ : Equiv.Perm (Fin 4), ∀ X ∈ L, ∀ i, X i (σ i)=0 := by
  exact PEqualNP.Research.RowPair.rigid
