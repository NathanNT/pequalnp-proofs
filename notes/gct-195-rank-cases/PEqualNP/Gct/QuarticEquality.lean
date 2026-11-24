import PEqualNP.Defs
import PEqualNP.Gct.L065
import PEqualNP.Gct.Helpers.FermatFromKneser
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

-- The polarization and stabilizer calculations adapt the proofs in
-- open-goat/pequalnp-proofs PRs 874 and 2858. The packing and coupling arguments are new.
namespace PEqualNP.Gct.TriplePacking

open Module Finset PEqualNP.Gct.Helpers

section General

variable {ι : Type} [Fintype ι]

def QuarticIso (X : Submodule ℂ (ι → ℂ)) : Prop :=
  (∀ u ∈ X, ∀ v ∈ X, ∑ i, u i * v i = 0) ∧
    (∀ u ∈ X, ∀ v ∈ X, ∀ w ∈ X, ∀ z ∈ X, ∑ i, u i * v i * w i * z i = 0)

theorem sq_sum_zero {X : Submodule ℂ (ι → ℂ)} (hX : QuarticIso X) :
    ∀ y ∈ X * X, ∑ i, y i = 0 := by
  intro y hy
  refine Submodule.mul_induction_on hy ?_ ?_
  · intro u hu v hv
    exact hX.1 u hu v hv
  · intro a b ha hb
    simp only [Pi.add_apply, sum_add_distrib, ha, hb, add_zero]

theorem sq_perp {X : Submodule ℂ (ι → ℂ)} (hX : QuarticIso X) :
    ∀ y ∈ X * X, ∀ z ∈ X * X, ∑ i, y i * z i = 0 := by
  intro y hy
  refine Submodule.mul_induction_on hy ?_ ?_
  · intro u hu v hv z hz
    refine Submodule.mul_induction_on hz ?_ ?_
    · intro w hw t ht
      have h := hX.2 u hu v hv w hw t ht
      convert h using 1
      refine sum_congr rfl fun i _ => ?_
      simp only [Pi.mul_apply]
      ring
    · intro a b ha hb
      simp only [Pi.add_apply, mul_add, sum_add_distrib, ha, hb, add_zero]
  · intro a b ha hb z hz
    simp only [Pi.add_apply, add_mul, sum_add_distrib, ha z hz, hb z hz, add_zero]

theorem restr_quarticIso {X : Submodule ℂ (ι → ℂ)} (hX : QuarticIso X) {p : ι → ℂ}
    (hp : p ∈ stab (X * X)) (hp01 : ∀ k, p k = 0 ∨ p k = 1) :
    QuarticIso (X.map (restr p)) := by
  have hsum := sq_sum_zero hX
  have hperp := sq_perp hX
  constructor
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    simp only [restr_apply]
    rw [sum_restr p hp01 (fun k => u k * v k)]
    have h := hsum _ (hp _ (Submodule.mul_mem_mul hu hv))
    simpa only [Pi.mul_apply, mul_assoc] using h
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩ _ ⟨z, hz, rfl⟩
    simp only [restr_apply]
    rw [sum_restr p hp01 (fun k => u k * v k * w k * z k)]
    have h := hperp _ (hp _ (Submodule.mul_mem_mul hu hv)) _ (Submodule.mul_mem_mul hw hz)
    convert h using 1
    refine sum_congr rfl fun k _ => ?_
    simp only [Pi.mul_apply]
    ring

theorem polarize (X : Submodule ℂ (ι → ℂ)) (h2 : ∀ u ∈ X, ∑ i, u i ^ 2 = 0)
    (h4 : ∀ u ∈ X, ∑ i, u i ^ 4 = 0) : QuarticIso X := by
  have hQ : ∀ u ∈ X, ∀ v ∈ X, ∑ i, u i * v i = 0 := by
    intro u hu v hv
    have key : ∑ i, (2 : ℂ) * (u i * v i) =
        (∑ i, (u + v) i ^ 2) - (∑ i, u i ^ 2) - (∑ i, v i ^ 2) := by
      simp only [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply]; ring
    rw [h2 _ (X.add_mem hu hv), h2 u hu, h2 v hv, ← Finset.mul_sum] at key
    simpa using key
  have hF : ∀ u ∈ X, ∀ v ∈ X, ∀ w ∈ X, ∀ z ∈ X, ∑ i, u i * v i * w i * z i = 0 := by
    intro u hu v hv w hw z hz
    have key : ∑ i, (24 : ℂ) * (u i * v i * w i * z i) =
        (∑ i, (u + v + w + z) i ^ 4)
        - (∑ i, (u + v + w) i ^ 4) - (∑ i, (u + v + z) i ^ 4)
        - (∑ i, (u + w + z) i ^ 4) - (∑ i, (v + w + z) i ^ 4)
        + (∑ i, (u + v) i ^ 4) + (∑ i, (u + w) i ^ 4) + (∑ i, (u + z) i ^ 4)
        + (∑ i, (v + w) i ^ 4) + (∑ i, (v + z) i ^ 4) + (∑ i, (w + z) i ^ 4)
        - (∑ i, u i ^ 4) - (∑ i, v i ^ 4) - (∑ i, w i ^ 4) - (∑ i, z i ^ 4) := by
      simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply]; ring
    rw [h4 _ (X.add_mem (X.add_mem (X.add_mem hu hv) hw) hz),
      h4 _ (X.add_mem (X.add_mem hu hv) hw),
      h4 _ (X.add_mem (X.add_mem hu hv) hz),
      h4 _ (X.add_mem (X.add_mem hu hw) hz),
      h4 _ (X.add_mem (X.add_mem hv hw) hz),
      h4 _ (X.add_mem hu hv), h4 _ (X.add_mem hu hw), h4 _ (X.add_mem hu hz),
      h4 _ (X.add_mem hv hw), h4 _ (X.add_mem hv hz), h4 _ (X.add_mem hw hz),
      h4 u hu, h4 v hv, h4 w hw, h4 z hz, ← Finset.mul_sum] at key
    have h24 : (24 : ℂ) ≠ 0 := by norm_num
    simpa [h24] using key
  exact ⟨hQ,hF⟩

theorem scalar_bound (W : Submodule ℂ (ι → ℂ)) (hW : QuarticIso W) (hW0 : W ≠ ⊥)
    (constant : ∀ x ∈ stab (W * W), ∀ j k, x j = x k) :
    4 * finrank ℂ W ≤ Fintype.card ι + 1 := by
  classical
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨i₀, -⟩ := Function.ne_iff.1 hu0
  have : Nonempty ι := ⟨i₀⟩
  set V := W * W with hVdef
  have hone : (1 : ι → ℂ) ∉ V := by
    intro h
    have := sq_perp hW 1 h 1 h
    simp only [Pi.one_apply, mul_one, sum_const, card_univ, nsmul_eq_mul] at this
    exact Fintype.card_ne_zero (Nat.cast_eq_zero.1 this)
  have hSt : finrank ℂ (stab V) ≤ 1 := by
    have : stab V ≤ Submodule.span ℂ {(1 : ι → ℂ)} := by
      intro x hx
      rw [Submodule.mem_span_singleton]
      refine ⟨x i₀, ?_⟩
      funext k
      simp [constant x hx i₀ k]
    exact (Submodule.finrank_mono this).trans (finrank_span_singleton one_ne_zero).le
  have hU : finrank ℂ ↥(V ⊔ Submodule.span ℂ {(1 : ι → ℂ)}) = finrank ℂ V + 1 := by
    have hinf : V ⊓ Submodule.span ℂ {(1 : ι → ℂ)} = ⊥ := by
      rw [eq_bot_iff]
      intro x ⟨hxV, hx1⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx1
      rw [Submodule.mem_bot]
      by_contra hc
      have hc' : c ≠ 0 := by rintro rfl; exact hc (zero_smul _ _)
      apply hone
      have := V.smul_mem c⁻¹ hxV
      rwa [smul_smul, inv_mul_cancel₀ hc', one_smul] at this
    have h := Submodule.finrank_sup_add_finrank_inf_eq V (Submodule.span ℂ {(1 : ι → ℂ)})
    rw [hinf, finrank_bot, add_zero,
      finrank_span_singleton (one_ne_zero : (1 : ι → ℂ) ≠ 0)] at h
    exact h
  have hk := kneserFor_of_fin PEqualNP.Gct.L065 ι W W (stab V) hW0 hW0 (fun x => Iff.rfl)
  have hperp : ∀ v ∈ V ⊔ Submodule.span ℂ {(1 : ι → ℂ)}, ∀ z ∈ V, ∑ i, v i * z i = 0 := by
    intro v hv z hz
    obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    have h1 := sq_perp hW y hy z hz
    have h2 := sq_sum_zero hW z hz
    calc ∑ i, (y + c • 1) i * z i
        = ∑ i, y i * z i + c * ∑ i, z i := by
          rw [mul_sum, ← sum_add_distrib]
          refine sum_congr rfl fun i _ => ?_
          simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul]
          ring
      _ = 0 := by rw [h1, h2, mul_zero, add_zero]
  have hp := perp_bound (V ⊔ Submodule.span ℂ {(1 : ι → ℂ)}) V hperp
  have hWpos : 1 ≤ finrank ℂ W := by
    rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact hW0
  change _ + _ ≤ finrank ℂ V + _ at hk
  omega

end General

-- The injection selects disjoint coordinate triples. The two inclusions describe the
-- projected subspace exactly, even when the original space couples different blocks.
structure Packing {ι : Type} (X Y : Submodule ℂ (ι → ℂ)) (T : Type) where
  coord : T → Fin 3 → ι
  separate : ∀ a i b j, coord a i = coord b j → a = b ∧ i = j
  shape : T → Fin 3 → ℂ
  nonzero : ∀ b, shape b ≠ 0
  quadratic : ∀ b, ∑ i, shape b i ^ 2 = 0
  quartic : ∀ b, ∑ i, shape b i ^ 4 = 0
  fits : ∀ x ∈ X, ∀ b, ∃ c : ℂ, ∀ i, x (coord b i) = c * shape b i
  onto : ∀ c : T → ℂ, ∃ x ∈ Y, ∀ b i, x (coord b i) = c b * shape b i

namespace Packing

variable {ι : Type} {X Y : Submodule ℂ (ι → ℂ)}

def empty (X Y : Submodule ℂ (ι → ℂ)) : Packing X Y (Fin 0) where
  coord := Fin.elim0
  separate a := Fin.elim0 a
  shape := Fin.elim0
  nonzero b := Fin.elim0 b
  quadratic b := Fin.elim0 b
  quartic b := Fin.elim0 b
  fits _ _ b := Fin.elim0 b
  onto _ := ⟨0,Y.zero_mem,fun b => Fin.elim0 b⟩

theorem single [Fintype ι] (hcard : Fintype.card ι = 3)
    (iso : QuarticIso X) (dim : finrank ℂ X = 1) (sub : Y ≤ X) (nontrivial : Y ≠ ⊥) :
    Nonempty (Packing X Y (Fin 1)) := by
  classical
  obtain ⟨v,hv,vne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot nontrivial
  let e : Fin 3 ≃ ι := (Fintype.equivFinOfCardEq hcard).symm
  have span_eq : Submodule.span ℂ {v} = X := Submodule.eq_of_le_of_finrank_le
    (Submodule.span_le.mpr (by simpa using sub hv)) (by rw [finrank_span_singleton vne,dim])
  refine ⟨⟨fun _ i => e i,fun _ _ _ _ h => ⟨Subsingleton.elim _ _,e.injective h⟩,
    fun _ i => v (e i),?_,?_,?_,?_,?_⟩⟩
  · intro b h
    apply vne
    funext j
    simpa using congrFun h (e.symm j)
  · intro b
    rw [Equiv.sum_comp e (fun j => v j ^ 2)]
    simpa [pow_two] using iso.1 v (sub hv) v (sub hv)
  · intro b
    rw [Equiv.sum_comp e (fun j => v j ^ 4)]
    simpa [pow_succ] using iso.2 v (sub hv) v (sub hv) v (sub hv) v (sub hv)
  · intro x hx b
    rw [← span_eq] at hx
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hx
    exact ⟨a,fun _ => rfl⟩
  · intro c
    exact ⟨c 0 • v,Y.smul_mem _ hv,fun b i => by rw [Subsingleton.elim b 0]; rfl⟩

variable (Y : Submodule ℂ (ι → ℂ)) (e f : ι → ℂ)

noncomputable def leftEval := (restr e).comp Y.subtype

noncomputable def rightEval :=
  (restr f).comp (Y.subtype.comp (LinearMap.ker (leftEval Y e)).subtype)

theorem rank_split (cover : ∀ i, e i = 1 ∨ f i = 1) [Fintype ι] :
    finrank ℂ (LinearMap.range (leftEval Y e)) +
    finrank ℂ (LinearMap.range (rightEval Y e f)) = finrank ℂ Y := by
  have inj : Function.Injective (rightEval Y e f) := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    funext i
    rcases cover i with h | h
    · exact congrFun (x.property.trans y.property.symm : leftEval Y e x.val = leftEval Y e y.val) ⟨i,h⟩
    · exact congrFun hxy ⟨i,h⟩
  rw [LinearMap.finrank_range_of_inj inj]
  exact (leftEval Y e).finrank_range_add_finrank_ker

variable {Y e f} {A B : Type}

noncomputable def glue
    (disj : ∀ i, e i = 1 → f i = 1 → False) (sub : Y ≤ X)
    (P : Packing (X.map (restr e)) (LinearMap.range (leftEval Y e)) A)
    (Q : Packing (X.map (restr f)) (LinearMap.range (rightEval Y e f)) B) :
    Packing X Y (A ⊕ B) where
  coord := Sum.elim (fun b i => (P.coord b i).val) (fun b i => (Q.coord b i).val)
  separate a i b j := by
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        intro h
        obtain ⟨rfl,rfl⟩ := P.separate a i b j (Subtype.ext h)
        exact ⟨rfl,rfl⟩
      | inr b =>
        intro h
        change (P.coord a i).val = (Q.coord b j).val at h
        exact (disj _ (P.coord a i).property ((congrArg f h).trans (Q.coord b j).property)).elim
    | inr a =>
      cases b with
      | inl b =>
        intro h
        change (Q.coord a i).val = (P.coord b j).val at h
        exact (disj _ ((congrArg e h).trans (P.coord b j).property)
          (Q.coord a i).property).elim
      | inr b =>
        intro h
        obtain ⟨rfl,rfl⟩ := Q.separate a i b j (Subtype.ext h)
        exact ⟨rfl,rfl⟩
  shape := Sum.elim P.shape Q.shape
  nonzero := fun b => by cases b with | inl b => exact P.nonzero b | inr b => exact Q.nonzero b
  quadratic := fun b => by cases b with | inl b => exact P.quadratic b | inr b => exact Q.quadratic b
  quartic := fun b => by cases b with | inl b => exact P.quartic b | inr b => exact Q.quartic b
  fits x hx b := by
    cases b with
    | inl b => exact P.fits _ ⟨x,hx,rfl⟩ b
    | inr b => exact Q.fits _ ⟨x,hx,rfl⟩ b
  onto c := by
    obtain ⟨_,⟨u,rfl⟩,hu⟩ := P.onto (fun b => c (.inl b))
    choose a ha using Q.fits (restr f u.val) ⟨u.val,sub u.property,rfl⟩
    obtain ⟨_,⟨v,rfl⟩,hv⟩ := Q.onto (fun b => c (.inr b) - a b)
    refine ⟨u.val + v.val.val,Y.add_mem u.property v.val.property,?_⟩
    intro b i
    cases b with
    | inl b =>
      have zero := congrFun (show leftEval Y e v.val = 0 from v.property) (P.coord b i)
      change v.val.val (P.coord b i).val = 0 at zero
      change u.val (P.coord b i).val + v.val.val (P.coord b i).val = _
      rw [zero,add_zero]
      exact hu b i
    | inr b =>
      change u.val (Q.coord b i).val + v.val.val (Q.coord b i).val = c (.inr b) * Q.shape b i
      change ∀ b i, v.val.val (Q.coord b i).val = _ at hv
      rw [show u.val (Q.coord b i).val = _ from ha b i,hv]
      ring

end Packing


-- Keep a subsidiary space Y during the induction. On a split, the second set of
-- coefficients is realized in the kernel of the first projection.
theorem decompose : ∀ n (ι : Type) [Fintype ι], Fintype.card ι = n →
    ∀ (X Y : Submodule ℂ (ι → ℂ)), QuarticIso X → Y ≤ X →
      3 * finrank ℂ X ≤ n ∧ ∃ (T : Type) (_ : Fintype T), Nonempty (Packing X Y T) ∧
        finrank ℂ Y + 6 * finrank ℂ X ≤ 2 * n + Fintype.card T := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro ι _ hcard X Y iso sub
  classical
  have rank_le := Submodule.finrank_mono sub
  by_cases zero : X = ⊥
  · have dim : finrank ℂ X = 0 := by rw [zero,finrank_bot]
    exact ⟨by omega,Fin 0,inferInstance,⟨Packing.empty X Y⟩,by omega⟩
  by_cases constant : ∀ x ∈ stab (X * X), ∀ j k, x j = x k
  · have length := scalar_bound X iso zero constant
    rw [hcard] at length
    have pos : 0 < finrank ℂ X := by
      rwa [Nat.pos_iff_ne_zero,ne_eq,Submodule.finrank_eq_zero]
    refine ⟨by omega,?_⟩
    by_cases tight : n = 3 ∧ finrank ℂ X = 1 ∧ Y ≠ ⊥
    · exact ⟨Fin 1,inferInstance,Packing.single (hcard.trans tight.1) iso tight.2.1 sub tight.2.2,
        by simp only [Fintype.card_fin]; omega⟩
    · refine ⟨Fin 0,inferInstance,⟨Packing.empty X Y⟩,?_⟩
      simp only [Fintype.card_fin]
      by_cases h : Y = ⊥
      · rw [h,finrank_bot]; omega
      · have exc : ¬ (n = 3 ∧ finrank ℂ X = 1) := fun h' => tight ⟨h'.1,h'.2,h⟩
        omega
  · push Not at constant
    obtain ⟨x,hx,j,k,ne⟩ := constant
    obtain ⟨e,he,ev⟩ := exists_indicator hx j
    have e01 : ∀ l, e l = 0 ∨ e l = 1 := fun l => by rw [ev]; split_ifs <;> simp
    let f : ι → ℂ := 1 - e
    have hf : f ∈ stab (X * X) := (stab _).sub_mem (one_mem_stab _) he
    have f01 : ∀ l, f l = 0 ∨ f l = 1 := fun l => by
      rcases e01 l with h | h <;> simp [f,h]
    have cover : ∀ i, e i = 1 ∨ f i = 1 := fun i => by
      rcases e01 i with h | h
      · right; simp [f,h]
      · exact Or.inl h
    have disj : ∀ i, e i = 1 → f i = 1 → False := fun i h => by simp [f,h]
    have hej : e j = 1 := by rw [ev]; simp
    have hek : e k = 0 := by rw [ev]; simp [Ne.symm ne]
    have smallL : Fintype.card {l // e l = 1} < n := by
      rw [← hcard]; exact Fintype.card_subtype_lt (x := k) (by rw [hek]; exact zero_ne_one)
    have smallR : Fintype.card {l // f l = 1} < n := by
      rw [← hcard]; exact Fintype.card_subtype_lt (x := j) (by simp [f,hej])
    have lengths : Fintype.card {l // e l = 1} + Fintype.card {l // f l = 1} ≤ n := by
      rw [Fintype.card_subtype,Fintype.card_subtype,← hcard,← Finset.card_union_of_disjoint]
      · exact Finset.card_le_univ _
      · rw [Finset.disjoint_filter]
        exact fun l _ => disj l
    obtain ⟨boundL,A,_,⟨P⟩,countL⟩ := IH _ smallL _ rfl _ (LinearMap.range (Packing.leftEval Y e))
      (restr_quarticIso iso he e01) (by rintro _ ⟨u,rfl⟩; exact ⟨u.val,sub u.property,rfl⟩)
    obtain ⟨boundR,B,_,⟨Q⟩,countR⟩ := IH _ smallR _ rfl _ (LinearMap.range (Packing.rightEval Y e f))
      (restr_quarticIso iso hf f01) (by rintro _ ⟨u,rfl⟩; exact ⟨u.val.val,sub u.val.property,rfl⟩)
    have size := finrank_split X e f cover
    have dimension := Packing.rank_split Y e f cover
    exact ⟨by omega,A ⊕ B,inferInstance,⟨Packing.glue disj sub P Q⟩,by rw [Fintype.card_sum]; omega⟩

theorem Packing.coordinate_count {ι T : Type} [Fintype ι] [Fintype T]
    {X Y : Submodule ℂ (ι → ℂ)} (P : Packing X Y T) : 3 * Fintype.card T ≤ Fintype.card ι := by
  have inj : Function.Injective (fun p : T × Fin 3 => P.coord p.1 p.2) := by
    rintro ⟨a,i⟩ ⟨b,j⟩ h
    exact Prod.ext (P.separate a i b j h).1 (P.separate a i b j h).2
  simpa [Nat.mul_comm] using Fintype.card_le_of_injective _ inj

end PEqualNP.Gct.TriplePacking


namespace PEqualNP.Gct.TriplePacking

open Module Finset

variable {m : ℕ} {X : Submodule ℂ (Fin m → ℂ)} {T : Type}

noncomputable def Packing.coords {t : ℕ} (P : Packing X X T) (label : Fin t ≃ T) :
    Fin t × Fin 3 ↪ Fin m where
  toFun p := P.coord (label p.1) p.2
  inj' := by
    rintro ⟨a,i⟩ ⟨b,j⟩ h
    obtain ⟨eq,rfl⟩ := P.separate _ _ _ _ h
    exact Prod.ext (label.injective eq) rfl

theorem Packing.describe {t : ℕ} (P : Packing X X T) (label : Fin t ≃ T)
    (z : Fin t → Fin 3 → ℂ) :
    (∃ x ∈ X, ∀ b i, x (P.coords label (b,i)) = z b i) ↔
    ∃ c : Fin t → ℂ, ∀ b i, z b i = c b * P.shape (label b) i := by
  constructor
  · rintro ⟨x,hx,he⟩
    choose c hc using P.fits x hx
    exact ⟨fun b => c (label b),fun b i => (he b i).symm.trans (hc _ _)⟩
  · rintro ⟨c,hc⟩
    obtain ⟨x,hx,h⟩ := P.onto (fun b => c (label.symm b))
    refine ⟨x,hx,?_⟩
    intro b i
    change x (P.coord (label b) i) = z b i
    rw [hc b i]
    simpa only [Equiv.symm_apply_apply] using h (label b) i

-- At equality the coordinate embedding is onto, so these triples describe X itself.
theorem _root_.PEqualNP.Gct.QuarticEquality (m : ℕ) (X : Submodule ℂ (Fin m → ℂ))
    (h₂ : ∀ x ∈ X, ∑ i, x i ^ 2 = 0) (h₄ : ∀ x ∈ X, ∑ i, x i ^ 4 = 0)
    (tight : m = 3 * finrank ℂ X) :
    ∃ (e : Fin (finrank ℂ X) × Fin 3 ≃ Fin m) (v : Fin (finrank ℂ X) → Fin 3 → ℂ),
      (∀ b, v b ≠ 0 ∧ ∑ i, v b i ^ 2 = 0 ∧ ∑ i, v b i ^ 4 = 0) ∧
      ∀ z : Fin (finrank ℂ X) → Fin 3 → ℂ,
        (∃ x ∈ X, ∀ b i, x (e (b,i)) = z b i) ↔
        ∃ c : Fin (finrank ℂ X) → ℂ, ∀ b i, z b i = c b * v b i := by
  classical
  obtain ⟨_,T,_,⟨P⟩,count⟩ := decompose m (Fin m) (Fintype.card_fin m) X X (polarize X h₂ h₄) le_rfl
  have cap := P.coordinate_count
  rw [Fintype.card_fin] at cap
  have card : Fintype.card T = finrank ℂ X := by omega
  let label := (Fintype.equivFinOfCardEq card).symm
  let emb := P.coords label
  have bij : Function.Bijective emb := (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨emb.injective,by simp [Fintype.card_prod]; omega⟩
  exact ⟨Equiv.ofBijective emb bij,fun b => P.shape (label b),
    fun b => ⟨P.nonzero _,P.quadratic _,P.quartic _⟩,P.describe label⟩

end PEqualNP.Gct.TriplePacking
