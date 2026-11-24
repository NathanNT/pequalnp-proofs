import Mathlib
import PEqualNP.Research.KleinPermanent
import PEqualNP.Research.RowPair
import PEqualNP.Research.MatchingData

namespace PEqualNP.Research.RowPairDirection
open PEqualNP.Research.MatchingData
abbrev M := Matrix I I ℂ
abbrev V := N → ℂ
noncomputable abbrev base := PEqualNP.Research.KleinPermanent.base
noncomputable def grad (X : M) : ℂ := ∑ a : Pos, X a.1 a.2 * (g a : ℂ)
noncomputable def bil (X Y : M) : ℂ :=
  ∑ a : Pos, ∑ b : Pos, X a.1 a.2 * (h a b : ℂ) * Y b.1 b.2

set_option maxHeartbeats 5000000 in
lemma first_two (L : Submodule ℂ M) (lev : ∀ X ∈ L, (base+X).permanent=65)
    (X : M) (hx : X ∈ L) : grad X=0 ∧ bil X X=0 := by
  have ev (t : ℂ) := lev _ (L.smul_mem t hx)
  let f (t : ℂ) := (base+t • X).permanent
  have he (t : ℂ) : f t=65 := ev t
  have g1 : 12*grad X=8*(f 1-f (-1))-(f 2-f (-2)) := by
    simp only [f, PEqualNP.Research.KleinPermanent.perm4,
      grad,Fintype.sum_prod_type, Fin.sum_univ_four, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, base, PEqualNP.Research.KleinPermanent.base,Matrix.of_apply]
    norm_num [g]; ring
  have g2 : 12*bil X X=16*(f 1+f (-1))-(f 2+f (-2))-30*f 0 := by
    simp only [f, PEqualNP.Research.KleinPermanent.perm4,
      bil,Fintype.sum_prod_type, Fin.sum_univ_four, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, base, PEqualNP.Research.KleinPermanent.base,Matrix.of_apply]
    norm_num [h]; ring
  simp only [he] at g1 g2
  constructor
  · linear_combination g1/12
  · linear_combination g2/12

lemma symm_h (a b : Pos) : h a b = h b a := by
  rcases a with ⟨i,j⟩
  rcases b with ⟨k,l⟩
  revert i j k l
  decide +kernel

lemma vanish (L : Submodule ℂ M) (lev : ∀ X ∈ L, (base+X).permanent=65)
    (X Y : M) (hx : X ∈ L) (hy : Y ∈ L) : bil X Y=0 := by
  have sym : bil Y X=bil X Y := by
    unfold bil
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [symm_h j i]
    ring
  have e : bil (X+Y) (X+Y)=bil X X+bil X Y+bil Y X+bil Y Y := by
    simp only [bil, Matrix.add_apply,add_mul,mul_add,Finset.sum_add_distrib]
    ring
  rw [(first_two L lev _ (L.add_mem hx hy)).2,(first_two L lev _ hx).2,
    (first_two L lev _ hy).2,sym] at e
  linear_combination -e/2

lemma compress (p : I → I) (F : Pos → ℂ) (hz : ∀ i, F (i,p i)=0) :
    ∑ a : I × Fin 3, F (addr p a) = ∑ a : Pos, F a := by
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_succAbove (fun j => F (i,j)) (p i),hz,zero_add]
  rfl

def mat (p : I → I) : Matrix N N ℂ := (gram p).map (Int.castRingHom ℂ)

noncomputable def pack (L : Submodule ℂ M) (p : I → I) : ℂ × L →ₗ[ℂ] V where
  toFun u := fun n => match n with
    | none => u.1
    | some a => u.2.val (addr p a).1 (addr p a).2
  map_add' _ _ := by funext n; cases n <;> rfl
  map_smul' _ _ := by funext n; cases n <;> rfl

lemma packed (L : Submodule ℂ M) (p : I → I) (zero : ∀ X ∈ L, ∀ i, X i (p i)=0)
    (x y : ℂ × L) :
    (mat p).toBilin' (pack L p x) (pack L p y) =
    x.1*grad y.2.val + y.1*grad x.2.val + bil x.2.val y.2.val := by
  have gx (u : L) : (∑ a, u.val (addr p a).1 (addr p a).2 * (g (addr p a) : ℂ))=grad u.val :=
    compress p (fun a => u.val a.1 a.2 * (g a : ℂ)) (by intro i; simp [zero _ u.property])
  have hh (a : Pos) :
      (∑ b : I × Fin 3, x.2.val a.1 a.2*(h a (addr p b) : ℂ)*y.2.val (addr p b).1 (addr p b).2) =
      ∑ b : Pos, x.2.val a.1 a.2*(h a b : ℂ)*y.2.val b.1 b.2 :=
    compress p (fun b => x.2.val a.1 a.2 * (h a b : ℂ) * y.2.val b.1 b.2) (by intro i; simp [zero _ y.2.property])
  have hh' : (∑ a : I × Fin 3, ∑ b : Pos, x.2.val (addr p a).1 (addr p a).2 *
      (h (addr p a) b : ℂ)*y.2.val b.1 b.2)=bil x.2.val y.2.val :=
    compress p (fun a => ∑ b : Pos, x.2.val a.1 a.2 * (h a b : ℂ)*y.2.val b.1 b.2) (by intro i; simp [zero _ x.2.property])
  rw [Matrix.toBilin'_apply]
  simp only [Fintype.sum_option,pack, LinearMap.coe_mk,AddHom.coe_mk,mat,Matrix.map_apply,
    gram, Matrix.of_apply,map_zero,mul_zero,zero_mul,zero_add,
    Finset.sum_add_distrib]
  have castE (z : ℤ) : (Int.castRingHom ℂ) z = (z : ℂ) := rfl
  simp only [castE]
  simp_rw [hh]
  rw [hh', ← Finset.sum_mul, gx]
  have gy : (∑ a : I × Fin 3, x.1*(g (addr p a) : ℂ)*y.2.val (addr p a).1 (addr p a).2)
      = x.1*grad y.2.val := by
    rw [← gx,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [gy]
  ring

lemma nonsing (p : I → I) (hp : Function.Injective p) : Function.Injective (mat p).toBilin' := by
  obtain ⟨hs,he⟩ := check_all p hp
  have d := congrArg Matrix.det he
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one,mul_one] at d
  have nonz : (gram p).det ≠ 0 := by
    intro h
    rw [h,mul_zero] at d
    exact (pow_ne_zero _ hs) d.symm
  have d' : (mat p).det ≠ 0 := by
    change ((Int.castRingHom ℂ).mapMatrix (gram p)).det ≠ 0
    rw [← RingHom.map_det]
    change ((gram p).det : ℂ) ≠ 0
    exact_mod_cast nonz
  exact LinearMap.ker_eq_bot.mp
    (LinearMap.separatingLeft_iff_ker_eq_bot.mp ((LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr d').1))

lemma no_matching (L : Submodule ℂ M) (p : Equiv.Perm I)
    (zero : ∀ X ∈ L, ∀ i, X i (p i)=0)
    (lev : ∀ X ∈ L, (base+X).permanent=65) : Module.finrank ℂ L ≤ 5 := by
  let f := pack L p
  have inj : Function.Injective f := by
    intro x y he
    refine Prod.ext (congrFun he none) (Subtype.ext ?_)
    ext i j
    rcases Fin.eq_self_or_eq_succAbove (p i) j with rfl|⟨k,rfl⟩
    · rw [zero _ x.2.property,zero _ y.2.property]
    · exact congrFun he (some (i,k))
  let S := LinearMap.range f
  let A := (mat p).toBilin'
  have hA : Function.Injective A := nonsing p p.injective
  have incl : S.map A ≤ S.dualAnnihilator := by
    rintro _ ⟨_,⟨x,rfl⟩,rfl⟩
    apply (Submodule.mem_dualAnnihilator _).mpr
    rintro _ ⟨y,rfl⟩
    change (mat p).toBilin' (pack L p x) (pack L p y)=0
    rw [packed L p zero,(first_two L lev _ y.2.property).1,(first_two L lev _ x.2.property).1,
      vanish L lev _ _ x.2.property y.2.property]
    ring
  have hle := Submodule.finrank_mono incl
  have eqr := (Submodule.equivMapOfInjective A hA S).finrank_eq
  have sum := Subspace.finrank_add_finrank_dualAnnihilator_eq S
  have dim : Module.finrank ℂ V=13 := by simp [V,N,I]
  have rank : Module.finrank ℂ S = 1 + Module.finrank ℂ L := by
    rw [LinearMap.finrank_range_of_inj inj,Module.finrank_prod,Module.finrank_self]
  change Module.finrank ℂ S + Module.finrank ℂ S.dualAnnihilator = Module.finrank ℂ V at sum
  rw [dim] at sum
  have half : Module.finrank ℂ S ≤ Module.finrank ℂ S.dualAnnihilator := eqr.le.trans hle
  have dbl : Module.finrank ℂ S + Module.finrank ℂ S ≤ 13 :=
    (Nat.add_le_add_left half _).trans_eq sum
  rw [rank] at dbl
  omega

lemma rows (L : Submodule ℂ M) (hd : Module.finrank ℂ L=6)
    (lev : ∀ X ∈ L, (base+X).permanent=65) :
    ∃ i j : I, i ≠ j ∧ ∃ X ∈ L, X ≠ 0 ∧ (∀ k, X i k=0) ∧ (∀ k, X j k=0) := by
  classical
  by_contra hn
  have inj (i j : I) (hij : i≠j) : Function.Injective (fun X : L => (X.val i,X.val j)) := by
    intro x y he
    by_contra hne
    apply hn
    refine ⟨i,j,hij,x.val-y.val,L.sub_mem x.property y.property,?_,?_,?_⟩
    · intro hz
      exact hne (Subtype.ext (sub_eq_zero.mp hz))
    · intro k
      exact sub_eq_zero.mpr (congrFun (congrArg Prod.fst he) k)
    · intro k
      exact sub_eq_zero.mpr (congrFun (congrArg Prod.snd he) k)
  obtain ⟨p,hp⟩ := PEqualNP.Research.RowPair.rigid L base hd
    (fun X hX => by rw [lev X hX]; norm_num) inj
  have h := no_matching L p hp lev
  omega

lemma both (L : Submodule ℂ M) (hd : Module.finrank ℂ L=6)
    (lev : ∀ X ∈ L, (base+X).permanent=65) :
    (∃ i j : I, i ≠ j ∧ ∃ X ∈ L, X ≠ 0 ∧ (∀ k, X i k=0) ∧ (∀ k, X j k=0)) ∧
    (∃ i j : I, i ≠ j ∧ ∃ X ∈ L, X ≠ 0 ∧ (∀ k, X k i=0) ∧ (∀ k, X k j=0)) := by
  refine ⟨rows L hd lev,?_⟩
  let T := Matrix.transposeLinearEquiv I I ℂ ℂ
  let S := L.map T.toLinearMap
  have rank : Module.finrank ℂ S=6 :=
    (Submodule.equivMapOfInjective T.toLinearMap T.injective L).finrank_eq.symm.trans hd
  have level (X : M) (hX : X ∈ S) : (base+X).permanent=65 := by
    obtain ⟨Y,hY,rfl⟩ := hX
    change (base+Y.transpose).permanent=65
    have fixed : base.transpose=base := by
      ext i j
      simp [base,PEqualNP.Research.KleinPermanent.base,Matrix.transpose_apply,eq_comm]
    rw [← fixed, ← Matrix.transpose_add, Matrix.permanent_transpose]
    exact lev Y hY
  obtain ⟨i,j,hn,X,⟨Y,hY,rfl⟩,hX,hi,hj⟩ := rows S rank level
  exact ⟨i,j,hn,Y,hY,fun hy => hX (hy ▸ T.map_zero),hi,hj⟩


end PEqualNP.Research.RowPairDirection


theorem PEqualNP.Research.RowPairDirection :
  ∀ L : Submodule ℂ (Matrix (Fin 4) (Fin 4) ℂ), Module.finrank ℂ L=6 →
  (∀ X ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
    (if i=j then (2 : ℂ) else 1) + X i j)=65) →
  (∃ i j : Fin 4, i ≠ j ∧ ∃ X ∈ L, X ≠ 0 ∧ (∀ k, X i k=0) ∧ (∀ k, X j k=0)) ∧
  (∃ i j : Fin 4, i ≠ j ∧ ∃ X ∈ L, X ≠ 0 ∧ (∀ k, X k i=0) ∧ (∀ k, X k j=0)) := by
  exact PEqualNP.Research.RowPairDirection.both
