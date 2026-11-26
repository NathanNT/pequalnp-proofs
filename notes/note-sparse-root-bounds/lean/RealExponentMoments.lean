import PEqualNP.Outside.L_gct_234

/-!
# The moment step of L-gct-234 for real exponents

The file `PEqualNP/Outside/L_gct_234.lean` (Aargau) proves that a positive root of a nonzero signed sum of three
cubes of real polynomials with at most two terms has order at most 9.  Its algebraic lemmas have real parameters.
This file repeats the part of that proof that refers to natural-number exponents, with real exponents instead, and
reuses all the other lemmas of that file unchanged.

Main statement, `SparseRootBounds.RealExponents.real_exponent_moments`.  For i = 0, 1, 2 let `s i` be a nonzero real
number and let `g i` be a pair of distinct real exponents `left`, `right` with nonzero real coefficients `A`, `B`.
Write

  T n t = sum over i of  s i * ( A^3 (3 left - 3 t)^n + 3 A^2 B (2 left + right - 3 t)^n
                               + 3 A B^2 (left + 2 right - 3 t)^n + B^3 (3 right - 3 t)^n ),

which is the n-th derivative at u = 0 of  exp(-3 t u) * sum_i s i (A exp(left u) + B exp(right u))^3.
If `T n t = 0` for all n < 10 and all real t (`LowMoments`), then there is a real t with `T n t = 0` for ALL n
(`Cancelled`).

What is not in this file: the passage from "the function vanishes to order 10 at u = 0" to `LowMoments`, and from
`Cancelled` to "the function is identically zero" (a Vandermonde argument).  Both are ordinary arguments given in the
note, Proposition 10.

Provenance.  The observation that the proof of L-gct-234 applies to real exponents, and this file, are due to the
second review of the note (GPT-6.2 Astra, an AI system); the file was then recompiled independently.  All the
mathematics is that of the file of L-gct-234.  Apache-2.0, as open-goat/pequalnp-proofs.

To compile: from the `lean/` directory of the repository, after building `PEqualNP.Outside.L_gct_234`,
  lake env lean ../notes/note-sparse-root-bounds/lean/RealExponentMoments.lean
-/
open PEqualNP.Outside.L_gct_234.SparseCubes
open scoped BigOperators
namespace SparseRootBounds.RealExponents
noncomputable section
structure Arm where
  left : ℝ
  right : ℝ
  A : ℝ
  B : ℝ
def Arm.leftMass (g : Arm) (_ : ℝ) := g.A
def Arm.rightMass (g : Arm) (_ : ℝ) := g.B
def W (t r : ℝ) (n : ℕ) (g : Arm) := cubeFour (g.leftMass r) (g.rightMass r) (g.left-t/3) (g.right-t/3) n
theorem moment_arm_cube (g : Arm) (r t : ℝ) (n : ℕ) : W (3*t) r n g = cubeFour (g.leftMass r) (g.rightMass r) (g.left-t) (g.right-t) n := by simp [W]
def Arm.variance (g : Arm) (r : ℝ) : ℝ :=
  let t := g.leftMass r / (g.leftMass r + g.rightMass r)
  t*(1-t)*((g.left:ℝ)-g.right)^2

def Arm.mean (g : Arm) (r : ℝ) : ℝ :=
  let t := g.leftMass r / (g.leftMass r + g.rightMass r)
  t*g.left+(1-t)*g.right

def Arm.skew (g : Arm) (r : ℝ) : ℝ := (g.left:ℝ)+g.right-2*g.mean r

theorem arm_normalized (g : Arm) (r t : ℝ) (n : ℕ)
    (hne : g.leftMass r + g.rightMass r ≠ 0) :
    W (3*t) r n g =
      (g.leftMass r + g.rightMass r)^3 *
      Chart.rawMoment (g.mean r-t) (g.variance r) (g.skew r) n := by
  let L := g.leftMass r
  let R := g.rightMass r
  let a := L/(L+R)
  have hL : (L+R)*a=L := by dsimp [a,L,R]; field_simp
  have hR : (L+R)*(1-a)=R := by linear_combination -hL
  rw [moment_arm_cube]
  calc
    _ = cubeFour ((L+R)*a) ((L+R)*(1-a)) ((g.left:ℝ)-t) ((g.right:ℝ)-t) n := by rw [hL,hR]
    _ = _ := by
      rw [cubeFour_scale, normalized_cubeFour]
      apply congrArg ((L+R)^3 * ·)
      congr 1 <;> dsimp [Arm.mean, Arm.skew, Arm.variance, a, L, R] <;> ring

def Arm.value (g : Arm) (r : ℝ) : ℝ := g.leftMass r + g.rightMass r
def Arm.Genuine (g : Arm) : Prop := g.A ≠ 0 ∧ g.B ≠ 0 ∧ g.left ≠ g.right
theorem Arm.variance_ne (g : Arm) (r : ℝ) (hr : r ≠ 0) (hg : g.Genuine)
    (hval : g.value r ≠ 0) : g.variance r ≠ 0 := by
  have hL : g.leftMass r ≠ 0 := hg.1
  have hR : g.rightMass r ≠ 0 := hg.2.1
  have hn : (g.left:ℝ) ≠ g.right := by exact_mod_cast hg.2.2
  have hsum : g.leftMass r + g.rightMass r ≠ 0 := hval
  have ha : 1 - g.leftMass r/(g.leftMass r+g.rightMass r) ≠ 0 := by
    rw [← div_self hsum, ← sub_div]
    simpa using div_ne_zero hR hsum
  exact mul_ne_zero (mul_ne_zero (div_ne_zero hL hsum) ha) (pow_ne_zero _ (sub_ne_zero.mpr hn))


def LowMoments (s : Fin 3 → ℝ) (g : Fin 3 → Arm) (r : ℝ) := ∀ n < 10, ∀ t : ℝ, ∑ i, s i * W (3*t) r n (g i) = 0
def Cancelled (s : Fin 3 → ℝ) (g : Fin 3 → Arm) (r : ℝ) := ∃ t : ℝ, ∀ n : ℕ, ∑ i, s i * W (3*t) r n (g i) = 0
theorem normalized_low (s : Fin 3 → ℝ) (g : Fin 3 → Arm) (r : ℝ)
    (hn : ∀ i, (g i).value r ≠ 0) (h : LowMoments s g r) (t : ℝ) (n : ℕ) (hlt : n < 10) :
    (∑ i, (s i * ((g i).value r)^3) *
      Chart.rawMoment ((g i).mean r-t) ((g i).variance r) ((g i).skew r) n) = 0 := by
  convert h n hlt t using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [arm_normalized _ _ _ _ (hn i)]
  simp only [Arm.value, mul_assoc]

theorem same_mean_zero (s : Fin 3 → ℝ) (g : Fin 3 → Arm) (r : ℝ) (hr : r ≠ 0)
    (hs : ∀ i, s i ≠ 0) (hg : ∀ i, (g i).Genuine) (hn : ∀ i, (g i).value r ≠ 0)
    (he : ∀ i, (g i).mean r = (g 0).mean r) (hl : LowMoments s g r) : Cancelled s g r := by
  let m := fun i => s i * ((g i).value r)^3
  let V := fun i => (g i).variance r
  let S := fun i => (g i).skew r
  have hm (i) : m i ≠ 0 := mul_ne_zero (hs i) (pow_ne_zero _ (hn i))
  have hv (i) := Arm.variance_ne (g i) r hr (hg i) (hn i)
  have hraw (n : ℕ) (hlt : n < 10) :
      m 0 * Chart.rawMoment 0 (V 0) (S 0) n + m 1 * Chart.rawMoment 0 (V 1) (S 1) n +
      m 2 * Chart.rawMoment 0 (V 2) (S 2) n = 0 := by
    simpa only [Fin.sum_univ_three, he, sub_self, m, V, S] using
      normalized_low s g r hn hl ((g 0).mean r) n hlt
  have hm0 : m 0 + m 1 + m 2 = 0 := by simpa [Chart.rawMoment] using hraw 0 (by decide)
  obtain ⟨p,hp,hq,hmix⟩ := mixtureWeights _ _ _ (hm 0) (hm 1) (hm 2) hm0
  obtain ⟨hS0,hS1,hV0,hV1⟩ := equalMean_mixture p (S 0) (S 1) (S 2) (V 0) (V 1) (V 2)
    hp hq (hv 0) (hv 1) (hv 2) (by
      intro n hn'
      apply hmix
      simpa only [← centered_raw _ _ n hn'] using hraw n (by omega))
  refine ⟨(g 0).mean r, ?_⟩
  intro n
  simp only [Fin.sum_univ_three]
  rw [arm_normalized _ _ _ _ (hn 0), arm_normalized _ _ _ _ (hn 1),
      arm_normalized _ _ _ _ (hn 2), he 1, he 2, sub_self]
  simp only [← mul_assoc]
  change m 0 * ((Chart.rawMoment 0 (V 0) (S 0) n)) +
    m 1 * (Chart.rawMoment 0 (V 1) (S 1) n) + m 2 * (Chart.rawMoment 0 (V 2) (S 2) n) = 0
  rw [hS0,hS1,hV0,hV1,← add_mul,← add_mul,hm0,zero_mul]
theorem nonvanishing_cases (s : Fin 3 → ℝ) (g : Fin 3 → Arm) (r : ℝ) (hr : r ≠ 0)
    (hs : ∀ i, s i ≠ 0) (hg : ∀ i, (g i).Genuine) (hn : ∀ i, (g i).value r ≠ 0)
    (hl : LowMoments s g r) :
    Cancelled s g r ∨ ∃ m x v u : Fin 3 → ℝ,
      (∀ i, m i ≠ 0) ∧ Function.Injective x ∧ (∀ i, v i ≠ 0) ∧
      (∑ i, x i) = 0 ∧ ∀ n < 10, ∑ i, m i * Chart.rawMoment (x i) (v i) (u i) n = 0 := by
  let t : ℝ := ((g 0).mean r+(g 1).mean r+(g 2).mean r)/3
  let x : Fin 3 → ℝ := fun i => (g i).mean r-t
  let m : Fin 3 → ℝ := fun i => s i*((g i).value r)^3
  let v : Fin 3 → ℝ := fun i => (g i).variance r
  let u : Fin 3 → ℝ := fun i => (g i).skew r
  have hm (i) : m i ≠ 0 := mul_ne_zero (hs i) (pow_ne_zero _ (hn i))
  have H (n : ℕ) (hn' : n<10) : ∑ i, m i * Chart.rawMoment (x i) (v i) (u i) n = 0 :=
    normalized_low s g r hn hl t n hn'
  have h0 : m 0+m 1+m 2=0 := by simpa only [Fin.sum_univ_three, Chart.rawMoment,mul_one] using H 0 (by decide)
  have h1 : m 0*x 0+m 1*x 1+m 2*x 2=0 := by
    have h := H 1 (by decide)
    simp only [Fin.sum_univ_three, Chart.rawMoment] at h
    linarith only [h]
  rcases three_nodes m x hm h0 h1 with he|hd
  · left
    apply same_mean_zero s g r hr hs hg hn _ hl
    intro i
    exact sub_left_inj.mp (he i)
  · right
    refine ⟨m,x,v,u,hm,hd,fun i => Arm.variance_ne _ _ hr (hg i) (hn i),?_,H⟩
    simp only [Fin.sum_univ_three,x,t]
    ring
def Arm.vanWeight (g : Arm) (r : ℝ) := (g.leftMass r*((g.left:ℝ)-g.right))^3
def Arm.vanMean (g : Arm) : ℝ := 3*((g.left:ℝ)+g.right)/2
def Arm.vanVariance (g : Arm) : ℝ := ((g.left:ℝ)-g.right)^2/4
theorem arm_vanMoment (g : Arm) (r t : ℝ) (hg : g.leftMass r+g.rightMass r=0)
    (n : ℕ) (hn : n≤6) :
    W (3*t) r (n+3) g = g.vanWeight r*
      (((n:ℝ)+1)*((n:ℝ)+2)*((n:ℝ)+3))*uniformCubeMoment n (g.vanMean-3*t) g.vanVariance := by
  have hr : g.rightMass r = -g.leftMass r := by linarith
  rw [moment_arm_cube,hr]
  interval_cases n <;> norm_num [cubeFour,Arm.vanWeight,Arm.vanMean,Arm.vanVariance,uniformCubeMoment] <;> ring

theorem arm_vanMoment_low (g : Arm) (r t : ℝ) (hg : g.leftMass r+g.rightMass r=0)
    (n : ℕ) (hn : n<3) : W (3*t) r n g=0 := by
  have hr : g.rightMass r = -g.leftMass r := by linarith
  rw [moment_arm_cube,hr]
  interval_cases n <;> simp [cubeFour] <;> ring

private def vanishingSequence (m v : ℝ) : ℕ → ℝ
  | 0 | 1 | 2 => 0
  | 3 => 6
  | n+4 =>
    let s := 2*m/3
    let p := (m/3)^2-v
    let k := 3*s
    let o := 9*p
    let i := 2*s^2+p
    2*k*vanishingSequence m v (n+3) - (k^2+o+i)*vanishingSequence m v (n+2) +
      k*(o+i)*vanishingSequence m v (n+1) - o*i*vanishingSequence m v n

private theorem vanishingSequence_four (A a b : ℝ) (n : ℕ) :
    cubeFour A (-A) a b n = (A*(a-b))^3*vanishingSequence (3*(a+b)/2) ((a-b)^2/4) n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 | 1 | 2 | 3 => simp [cubeFour,vanishingSequence]; ring
    | n+4 =>
      rw [cubeFour_step,vanishingSequence]
      rw [ih (n+3) (by omega),ih (n+2) (by omega),ih (n+1) (by omega),ih n (by omega)]
      ring

private theorem arm_vanMoment_all (g : Arm) (r : ℝ) (hg : g.leftMass r+g.rightMass r=0)
    (n : ℕ) : W 0 r n g =
      g.vanWeight r * vanishingSequence g.vanMean g.vanVariance n := by
  have hr : g.rightMass r = -g.leftMass r := by linarith
  simpa [hr,vanishingSequence_four,Arm.vanWeight,Arm.vanMean,Arm.vanVariance]
    using moment_arm_cube g r 0 n


theorem allVanishing_arms (a b c : Arm) (u v w r : ℝ)
    (ha : a.leftMass r+a.rightMass r=0) (hb : b.leftMass r+b.rightMass r=0)
    (hc : c.leftMass r+c.rightMass r=0)
    (hu : u*a.vanWeight r≠0) (hv : v*b.vanWeight r≠0) (hw : w*c.vanWeight r≠0)
    (H : ∀ n : ℕ, n<10 → ∀ t : ℝ, u*W (3*t) r n a +
        v*W (3*t) r n b + w*W (3*t) r n c=0) :
    ∀ n : ℕ, u*W 0 r n a + v*W 0 r n b +
      w*W 0 r n c=0 := by
  have U (n : ℕ) (hn : n≤6) :
      (u*a.vanWeight r)*uniformCubeMoment n a.vanMean a.vanVariance +
      (v*b.vanWeight r)*uniformCubeMoment n b.vanMean b.vanVariance +
      (w*c.vanWeight r)*uniformCubeMoment n c.vanMean c.vanVariance=0 := by
    have e := H (n+3) (by omega) 0
    rw [arm_vanMoment a r 0 ha n hn,arm_vanMoment b r 0 hb n hn,arm_vanMoment c r 0 hc n hn] at e
    simp only [mul_zero,sub_zero] at e
    have hfac : (((n:ℝ)+1)*((n:ℝ)+2)*((n:ℝ)+3))≠0 := by positivity
    apply (mul_eq_zero.mp ?_).resolve_left hfac
    linear_combination e
  have sumw := U 0 (by decide)
  simp only [uniformCubeMoment,mul_one] at sumw
  obtain ⟨p,hp,hq,hm⟩ := mixtureWeights _ _ _ hu hv hw sumw
  obtain ⟨haM,hbM,haV,hbV⟩ := threeVanish_mixture p _ _ _ _ _ _ hp hq (fun n hn => hm _ _ _ (U n hn))
  intro n
  rw [arm_vanMoment_all _ _ ha,arm_vanMoment_all _ _ hb,arm_vanMoment_all _ _ hc,haM,hbM,haV,hbV]
  linear_combination vanishingSequence c.vanMean c.vanVariance n * sumw


theorem oneVanishing_arms (a b c : Arm) (u v w r : ℝ)
    (ha : a.leftMass r+a.rightMass r≠0) (hb : b.leftMass r+b.rightMass r≠0)
    (hc : c.leftMass r+c.rightMass r=0)
    (hu : u≠0) (hv : v≠0) (hw : w*c.vanWeight r≠0) (hvar : a.variance r≠0)
    (H : ∀ n : ℕ, n<10 → ∀ t : ℝ, u*W (3*t) r n a +
        v*W (3*t) r n b + w*W (3*t) r n c=0) : False := by
  let A := u*(a.leftMass r + a.rightMass r)^3
  let B := v*(b.leftMass r + b.rightMass r)^3
  let C := w*c.vanWeight r
  have hA : A≠0 := mul_ne_zero hu (pow_ne_zero _ ha)
  have hB : B≠0 := mul_ne_zero hv (pow_ne_zero _ hb)
  have raw (n : ℕ) (hn : n<10) (t : ℝ) :
      A*Chart.rawMoment (a.mean r-t) (a.variance r) (a.skew r) n +
      B*Chart.rawMoment (b.mean r-t) (b.variance r) (b.skew r) n +
      w*W (3*t) r n c=0 := by
    have e := H n hn t
    rw [arm_normalized a r t n ha,arm_normalized b r t n hb] at e
    dsimp [A,B]; linear_combination e
  have h0 := raw 0 (by decide) 0
  rw [arm_vanMoment_low _ _ _ hc _ (by decide)] at h0
  simp only [Chart.rawMoment, mul_one,mul_zero,add_zero] at h0
  have Bval : B= -A := by linarith
  have h1 := raw 1 (by decide) 0
  rw [arm_vanMoment_low _ _ _ hc _ (by decide),Bval] at h1
  simp only [Chart.rawMoment, sub_zero,mul_zero,add_zero] at h1
  have sameMean : b.mean r=a.mean r := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp ?_).resolve_left hA
    linear_combination -h1/3
  have centered (n : ℕ) (hn : n<10) :
      A*centeredCubeMoment n (a.skew r) (a.variance r) -
      A*centeredCubeMoment n (b.skew r) (b.variance r) +
      w*W (3*a.mean r) r n c=0 := by
    have e := raw n hn (a.mean r)
    rw [Bval,sameMean] at e
    simp only [sub_self,centeredCubeMoment_raw n (by omega)] at e
    linear_combination e
  have h2 := centered 2 (by decide)
  rw [arm_vanMoment_low _ _ _ hc _ (by decide)] at h2
  simp only [centeredCubeMoment,mul_zero,add_zero] at h2
  have sameVar : b.variance r=a.variance r := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp ?_).resolve_left hA
    linear_combination -h2/3
  let h := (a.skew r+b.skew r)/2
  let d := (a.skew r-b.skew r)/2
  have sa : h+d=a.skew r := by dsimp [h,d]; ring
  have sb : h-d=b.skew r := by dsimp [h,d]; ring
  have e3 := centered 3 (by decide)
  rw [arm_vanMoment _ _ _ hc 0 (by decide),sameVar] at e3
  norm_num [centeredCubeMoment,uniformCubeMoment] at e3
  have relation : C = -A*(a.variance r)*d := by dsimp [C,d]; linear_combination e3/6
  have hd : d≠0 := by
    intro h0
    exact hw (show C=0 by rw [relation,h0,mul_zero])
  apply oneVanish_excludes h d (a.variance r) (c.vanMean-3*a.mean r) c.vanVariance hd hvar
  intro n hn
  have e := centered (n+3) (by omega)
  rw [arm_vanMoment _ _ _ hc n hn,sameVar] at e
  rw [sa,sb]
  apply sub_eq_zero.mp
  apply (mul_eq_zero.mp ?_).resolve_left hA
  dsimp [C] at relation
  linear_combination e -
    (((n:ℝ)+1)*((n:ℝ)+2)*((n:ℝ)+3)*uniformCubeMoment n (c.vanMean-3*a.mean r) c.vanVariance)*relation


theorem nonvanishing_result (s : Fin 3 → ℝ) (g : Fin 3 → Arm)
    (hs : ∀ i, s i ≠ 0) (hg : ∀ i, (g i).Genuine) (hn : ∀ i, (g i).value 1 ≠ 0)
    (hl : LowMoments s g 1) : Cancelled s g 1 := by
  rcases nonvanishing_cases s g 1 one_ne_zero hs hg hn hl with h|⟨m,x,v,u,hm,hx,hv,hc,H⟩
  · exact h
  · exact (Chart.distinct_mean_excludes m x v u hm hx hv hc H).elim
theorem last_zero (s : Fin 3 → ℝ) (g : Fin 3 → Arm)
    (hs : ∀ i, s i ≠ 0) (hg : ∀ i, (g i).Genuine) (hz : (g 2).value 1 = 0)
    (hl : LowMoments s g 1) : Cancelled s g 1 := by
  have H (n : ℕ) (hn : n<10) (t : ℝ) := hl n hn t
  simp only [Fin.sum_univ_three] at H
  have eval (a : Arm) : W 0 1 0 a = (a.value 1)^3 := by
    simp [W,cubeFour,Arm.value]; ring
  have h := H 0 (by decide) 0
  simp only [mul_zero,eval,hz,zero_pow (by decide : 3 ≠ 0),add_zero] at h
  have v (i) : s i*(g i).vanWeight 1 ≠ 0 :=
    mul_ne_zero (hs i) (pow_ne_zero 3 (mul_ne_zero (hg i).1 (sub_ne_zero.mpr (hg i).2.2)))
  by_cases h0 : (g 0).value 1 = 0
  · have h1 : (g 1).value 1 = 0 := by simpa [h0, hs 1] using h
    refine ⟨0, ?_⟩
    intro n
    simpa only [Fin.sum_univ_three,mul_zero] using
      allVanishing_arms _ _ _ _ _ _ 1 h0 h1 hz (v 0) (v 1) (v 2) H n
  · have h1 : (g 1).value 1 ≠ 0 := by
      intro h1
      simpa [h1,hs 0,h0] using h
    exact (oneVanishing_arms _ _ _ _ _ _ 1 h0 h1 hz (hs 0) (hs 1) (v 2)
      (Arm.variance_ne _ _ one_ne_zero (hg 0) h0) H).elim
theorem real_exponent_moments (s : Fin 3 → ℝ) (g : Fin 3 → Arm)
    (hs : ∀ i, s i ≠ 0) (hg : ∀ i, (g i).Genuine)
    (hl : LowMoments s g 1) : Cancelled s g 1 := by
  by_cases hz : ∃ i, (g i).value 1 = 0
  · obtain ⟨i, hi⟩ := hz
    let e := Equiv.swap i (2 : Fin 3)
    have H (t : ℝ) (n : ℕ) :
        (∑ j, (s ∘ e) j * W (3*t) 1 n ((g ∘ e) j)) =
         ∑ j, s j * W (3*t) 1 n (g j) := Equiv.sum_comp e (fun j => s j * W (3*t) 1 n (g j))
    obtain ⟨t,ht⟩ := last_zero (s ∘ e) (g ∘ e) (fun j => hs _) (fun j => hg _) (by simpa [e] using hi)
      (fun n hn t => (H t n).trans (hl n hn t))
    exact ⟨t,fun n => (H t n).symm.trans (ht n)⟩
  · exact nonvanishing_result s g hs hg (fun i hi => hz ⟨i,hi⟩) hl
end
end SparseRootBounds.RealExponents
#print axioms SparseRootBounds.RealExponents.real_exponent_moments
#print axioms SparseRootBounds.RealExponents.nonvanishing_result
#print axioms SparseRootBounds.RealExponents.allVanishing_arms
#print axioms SparseRootBounds.RealExponents.oneVanishing_arms
