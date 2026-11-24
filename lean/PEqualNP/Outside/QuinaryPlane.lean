import Mathlib

namespace PEqualNP.Outside.QuinaryPlane

open Finset Module

abbrev F := ZMod 5

def squareClass {m : ℕ} (x : Fin m → F) (c : F) : Finset (Fin m) :=
  univ.filter fun i => x i ^ 2 = c

lemma class_dvd {m : ℕ} {x : Fin m → F}
    (h2 : ∑ i, x i ^ 2 = 0) (h4 : ∑ i, x i ^ 4 = 0) :
    5 ∣ (squareClass x 1).card ∧ 5 ∣ (squareClass x 4).card := by
  have h : ∀ (z : F), (if z ^ 2 = 1 then 1 else 0 : F) = 3 * (z ^ 4 + z ^ 2) ∧
      (if z ^ 2 = 4 then 1 else 0 : F) = 3 * (z ^ 4 - z ^ 2) := by decide
  constructor
  · apply (ZMod.natCast_eq_zero_iff _ _).mp
    calc
      ((squareClass x 1).card : F) = ∑ i, (if x i ^ 2 = 1 then 1 else 0 : F) := by
        simp [squareClass]
      _ = ∑ i, 3 * (x i ^ 4 + x i ^ 2) := sum_congr rfl fun i _ => (h _).1
      _ = 0 := by rw [← mul_sum, sum_add_distrib, h2, h4]; simp
  · apply (ZMod.natCast_eq_zero_iff _ _).mp
    calc
      ((squareClass x 4).card : F) = ∑ i, (if x i ^ 2 = 4 then 1 else 0 : F) := by
        simp [squareClass]
      _ = ∑ i, 3 * (x i ^ 4 - x i ^ 2) := sum_congr rfl fun i _ => (h _).2
      _ = 0 := by rw [← mul_sum, sum_sub_distrib, h2, h4]; simp

lemma two_pivots {m : ℕ} (X : Submodule F (Fin m → F)) (hd : 2 ≤ finrank F X) :
    ∃ (p q : Fin m) (u v : Fin m → F), u ∈ X ∧ v ∈ X ∧
      u p = 1 ∧ u q = 0 ∧ v p = 0 ∧ v q = 1 := by
  classical
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hX : X ≠ ⊥ := by rintro rfl; simp at hd
  obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX
  obtain ⟨p,hp⟩ := Function.ne_iff.mp hx0
  change x p ≠ 0 at hp
  let a := (x p)⁻¹ • x
  have ha : a ∈ X := X.smul_mem _ hx
  have hap : a p = 1 := by simp [a,hp]
  let ev : X →ₗ[F] F := (LinearMap.proj p).comp X.subtype
  have hk : LinearMap.ker ev ≠ ⊥ := by
    intro H
    have h := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp H)
    simp at h
    omega
  obtain ⟨y,hy,hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  have hyp : y.val p = 0 := hy
  have hy' : y.val ≠ 0 := fun h => hy0 (Subtype.ext h)
  obtain ⟨q,hq⟩ := Function.ne_iff.mp hy'
  change y.val q ≠ 0 at hq
  let v := (y.val q)⁻¹ • y.val
  have hv : v ∈ X := X.smul_mem _ y.property
  have hvp : v p = 0 := by simp [v,hyp]
  have hvq : v q = 1 := by simp [v,hq]
  refine ⟨p,q,a - a q • v,v,X.sub_mem ha (X.smul_mem _ hv),hv,?_,?_,hvp,hvq⟩
  · simp [hvp,hap]
  · simp [hvq]

def combine {m : ℕ} (u v : Fin m → F) : F × F →ₗ[F] (Fin m → F) :=
  (LinearMap.fst F F F).smulRight u + (LinearMap.snd F F F).smulRight v

lemma pivot_rank {m : ℕ} {u v : Fin m → F} {p q : Fin m}
    (up : u p = 1) (uq : u q = 0) (vp : v p = 0) (vq : v q = 1) :
    finrank F (LinearMap.range (combine u v)) = 2 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hi : Function.Injective (combine u v) := by
    intro a b h
    apply Prod.ext
    · simpa [combine,up,vp] using congrFun h p
    · simpa [combine,uq,vq] using congrFun h q
  rw [LinearMap.finrank_range_of_inj hi, Module.finrank_prod]
  simp


def supp {m : ℕ} (x : Fin m → F) := univ.filter fun i => x i ≠ 0

lemma weight {m : ℕ} (x : Fin m → F) :
    (supp x).card = (squareClass x 1).card + (squareClass x 4).card := by
  have hj : supp x = squareClass x 1 ∪ squareClass x 4 := by
    ext i
    simp only [supp,squareClass,mem_filter,mem_univ,true_and,mem_union]
    exact (by decide : ∀ z : F, z ≠ 0 ↔ z ^ 2 = 1 ∨ z ^ 2 = 4) _
  rw [hj, card_union_of_disjoint]
  rw [Finset.disjoint_left]
  intro i h1 h4
  exact (by decide : (1:F) ≠ 4) ((mem_filter.mp h1).2.symm.trans (mem_filter.mp h4).2)

lemma mixed {m : ℕ} {x : Fin m → F}
    (h2 : ∑ i, x i ^ 2 = 0) (h4 : ∑ i, x i ^ 4 = 0)
    {p q : Fin m} (hp : x p = 1) (hq : x q = 2) : 10 ≤ (supp x).card := by
  obtain ⟨h,k⟩ := class_dvd h2 h4
  have ha : 0 < (squareClass x 1).card := card_pos.mpr ⟨p, by simp [squareClass,hp]⟩
  have hb : 0 < (squareClass x 4).card := card_pos.mpr ⟨q, by
    apply mem_filter.mpr
    exact ⟨mem_univ _,hq ▸ (by decide : (2:F)^2 = 4)⟩⟩
  rw [weight]
  omega

lemma short_row {m : ℕ} (hm : m ≤ 10) {x : Fin m → F}
    (h2 : ∑ i, x i ^ 2 = 0) (h4 : ∑ i, x i ^ 4 = 0)
    {p q : Fin m} (hp : x p = 1) (hq : x q = 0) :
    (supp x).card = 5 ∧ ∀ i, x i ≠ 0 → x i ^ 2 = 1 := by
  obtain ⟨h,k⟩ := class_dvd h2 h4
  have ha : 0 < (squareClass x 1).card := card_pos.mpr ⟨p, by simp [squareClass,hp]⟩
  have hw : (supp x).card < m := by
    have hn : supp x ≠ univ := by
      intro he
      have hh : q ∈ supp x := he ▸ mem_univ _
      simp [supp,hq] at hh
    simpa using (((supp x).card_lt_iff_ne_univ).mpr hn)
  have hw' := weight x
  have hz : (squareClass x 4).card = 0 := by omega
  refine ⟨by omega, fun i hi => ?_⟩
  rcases ((by decide : ∀ z : F, z ≠ 0 → z ^ 2 = 1 ∨ z ^ 2 = 4) _ hi) with h1 | h4'
  · exact h1
  · have : 0 < (squareClass x 4).card := card_pos.mpr ⟨i, mem_filter.mpr ⟨mem_univ _,h4'⟩⟩
    omega

lemma plane {m : ℕ} (X : Submodule F (Fin m → F)) (hr : finrank F X = 2)
    (h2 : ∀ x ∈ X, ∑ i, x i ^ 2 = 0) (h4 : ∀ x ∈ X, ∑ i, x i ^ 4 = 0) :
    10 ≤ m ∧ (m = 10 → ∃ u v : Fin m → F,
      (supp u).card = 5 ∧ (supp v).card = 5 ∧
      (∀ i, (u i ^ 2 = 1 ∧ v i = 0) ∨ (u i = 0 ∧ v i ^ 2 = 1)) ∧
      ∀ z, z ∈ X ↔ ∃ a b : F, z = a • u + b • v) := by
  obtain ⟨p,q,u,v,hu,hv,up,uq,vp,vq⟩ := two_pivots X hr.ge
  let w := u + (2:F) • v
  have hw : w ∈ X := X.add_mem hu (X.smul_mem _ hv)
  have wp : w p = 1 := by simp [w,up,vp]
  have wq : w q = 2 := by simp [w,uq,vq]
  have hmix := mixed (h2 w hw) (h4 w hw) wp wq
  have bound : (supp w).card ≤ m := by simpa using (supp w).card_le_univ
  refine ⟨by omega, fun hm => ?_⟩
  obtain ⟨cu,su⟩ := short_row hm.le (h2 u hu) (h4 u hu) up uq
  obtain ⟨cv,sv⟩ := short_row hm.le (h2 v hv) (h4 v hv) vq vp
  have full : supp w = univ := (supp w).card_eq_iff_eq_univ.mp (by simpa using (show (supp w).card = m by omega))
  have cover : supp u ∪ supp v = univ := by
    apply eq_univ_of_forall
    intro i
    have hi : i ∈ supp w := full ▸ mem_univ _
    simp only [supp,mem_union,mem_filter,mem_univ,true_and] at hi ⊢
    by_contra! H
    simp [w,H.1,H.2] at hi
  have dis : Disjoint (supp u) (supp v) := by
    have h := card_union_add_card_inter (supp u) (supp v)
    rw [cover, card_univ, Fintype.card_fin, cu,cv] at h
    rw [disjoint_iff_inter_eq_empty, ← card_eq_zero]
    omega
  refine ⟨u,v,cu,cv,?_,?_⟩
  · intro i
    have h : i ∈ supp u ∪ supp v := cover ▸ mem_univ _
    rcases mem_union.mp h with h | h
    · left
      exact ⟨su i (mem_filter.mp h).2, by
        by_contra hv'
        exact Finset.disjoint_left.mp dis h (mem_filter.mpr ⟨mem_univ _,hv'⟩)⟩
    · right
      exact ⟨by
        by_contra hu'
        exact Finset.disjoint_left.mp dis (mem_filter.mpr ⟨mem_univ _,hu'⟩) h, sv i (mem_filter.mp h).2⟩
  · let : Fact (Nat.Prime 5) := ⟨by decide⟩
    have hl : LinearMap.range (combine u v) ≤ X := by
      rintro _ ⟨c,rfl⟩
      exact X.add_mem (X.smul_mem c.1 hu) (X.smul_mem c.2 hv)
    have he := Submodule.eq_of_le_of_finrank_le hl (by rw [pivot_rank up uq vp vq,hr])
    intro z
    constructor
    · rw [← he]
      rintro ⟨⟨a,b⟩,rfl⟩
      exact ⟨a,b,rfl⟩
    · rintro ⟨a,b,rfl⟩
      exact X.add_mem (X.smul_mem a hu) (X.smul_mem b hv)


lemma attained : ∃ X : Submodule F (Fin 10 → F), finrank F X = 2 ∧
    ∀ x ∈ X, (∑ i, x i ^ 2) = 0 ∧ (∑ i, x i ^ 4) = 0 := by
  let u : Fin 10 → F := fun i => if i.val < 5 then 1 else 0
  let v : Fin 10 → F := fun i => if i.val < 5 then 0 else 1
  refine ⟨LinearMap.range (combine u v),pivot_rank (p := 0) (q := 5) (by decide)
    (by decide) (by decide) (by decide), ?_⟩
  rintro _ ⟨⟨a,b⟩,rfl⟩
  have h : ∀ a b : F, (∑ i : Fin 10, (if i.val < 5 then a else b)^2) = 0 ∧
      (∑ i : Fin 10, (if i.val < 5 then a else b)^4) = 0 := by decide
  have e : combine u v (a,b) = fun i => if i.val < 5 then a else b := by
    funext i
    by_cases hi : i.val < 5 <;> simp [combine,u,v,hi]
  rw [e]
  exact h a b

end PEqualNP.Outside.QuinaryPlane

theorem PEqualNP.Outside.QuinaryPlane :
    (∀ (m : ℕ) (X : Submodule (ZMod 5) (Fin m → ZMod 5)),
      Module.finrank (ZMod 5) X = 2 →
      (∀ x ∈ X, ∑ i, x i ^ 2 = 0) → (∀ x ∈ X, ∑ i, x i ^ 4 = 0) →
      10 ≤ m ∧ (m = 10 → ∃ u v : Fin m → ZMod 5,
        (Finset.univ.filter fun i => u i ≠ 0).card = 5 ∧
        (Finset.univ.filter fun i => v i ≠ 0).card = 5 ∧
        (∀ i, (u i ^ 2 = 1 ∧ v i = 0) ∨ (u i = 0 ∧ v i ^ 2 = 1)) ∧
        ∀ z, z ∈ X ↔ ∃ a b : ZMod 5, z = a • u + b • v)) ∧
    (∃ X : Submodule (ZMod 5) (Fin 10 → ZMod 5), Module.finrank (ZMod 5) X = 2 ∧
      ∀ x ∈ X, (∑ i, x i ^ 2) = 0 ∧ (∑ i, x i ^ 4) = 0) := by
  exact ⟨fun _ => QuinaryPlane.plane, QuinaryPlane.attained⟩
