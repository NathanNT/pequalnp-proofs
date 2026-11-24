import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Research.KleinPermanent

abbrev V := Fin 4 → ℂ
abbrev M := Matrix (Fin 4) (Fin 4) ℂ
lemma sum_perm_succ {n : ℕ} (f : Equiv.Perm (Fin (n + 1)) → ℂ) :
    ∑ σ, f σ = ∑ p : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n), f (Equiv.Perm.decomposeFin.symm (p, τ)) := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]

lemma perm4 (M : Matrix (Fin 4) (Fin 4) ℂ) : Matrix.permanent M =
    M 0 0 * M 1 1 * M 2 2 * M 3 3 + M 0 0 * M 1 1 * M 3 2 * M 2 3 + M 0 0 * M 2 1 * M 1 2 * M 3 3
  + M 0 0 * M 2 1 * M 3 2 * M 1 3 + M 0 0 * M 3 1 * M 1 2 * M 2 3 + M 0 0 * M 3 1 * M 2 2 * M 1 3
  + M 1 0 * M 0 1 * M 2 2 * M 3 3 + M 1 0 * M 0 1 * M 3 2 * M 2 3 + M 1 0 * M 2 1 * M 0 2 * M 3 3
  + M 1 0 * M 2 1 * M 3 2 * M 0 3 + M 1 0 * M 3 1 * M 0 2 * M 2 3 + M 1 0 * M 3 1 * M 2 2 * M 0 3
  + M 2 0 * M 0 1 * M 1 2 * M 3 3 + M 2 0 * M 0 1 * M 3 2 * M 1 3 + M 2 0 * M 1 1 * M 0 2 * M 3 3
  + M 2 0 * M 1 1 * M 3 2 * M 0 3 + M 2 0 * M 3 1 * M 0 2 * M 1 3 + M 2 0 * M 3 1 * M 1 2 * M 0 3
  + M 3 0 * M 0 1 * M 1 2 * M 2 3 + M 3 0 * M 0 1 * M 2 2 * M 1 3 + M 3 0 * M 1 1 * M 0 2 * M 2 3
  + M 3 0 * M 1 1 * M 2 2 * M 0 3 + M 3 0 * M 2 1 * M 0 2 * M 1 3 + M 3 0 * M 2 1 * M 1 2 * M 0 3 := by
  simp only [Matrix.permanent]
  rw [sum_perm_succ]
  simp only [sum_perm_succ (n := 2), sum_perm_succ (n := 1), sum_perm_succ (n := 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Fintype.sum_unique]
  simp +decide [Equiv.swap_apply_def]
  ring



def addK (i j : Fin 4) : Fin 4 := i ^^^ j

def signK (k r : Fin 4) : ℂ :=
  ![![1,1,1,1], ![1,-1,1,-1], ![1,1,-1,-1], ![1,-1,-1,1]] k r

noncomputable def base : M := Matrix.of fun i j => if i = j then 2 else 1
noncomputable def twist (k : Fin 4) (u : V) : M := Matrix.of fun i j => signK k i * u (addK i j)
noncomputable def form (a b c d : ℂ) : ℂ := (a^2+b^2+c^2+d^2)^2+8*a*b*c*d
noncomputable def quart (u : V) : ℂ := form (u 0) (u 1) (u 2) (u 3)

theorem perm_twist (k : Fin 4) (u : V) : (twist k u).permanent = quart u := by
  rw [perm4]
  fin_cases k <;> norm_num [twist,signK,quart,form,addK, Matrix.cons_val_succ] <;> ring

lemma no_chart (a b c d : ℂ)
    (h : ∀ x y : ℂ, form x y (a*x+b*y) (c*x+d*y) = 0) : False := by
  have A : 1+a^2+c^2 = 0 := by
    have e := h 1 0
    simpa [form, sq_eq_zero_iff] using e
  have B : 1+b^2+d^2 = 0 := by
    have e := h 0 1
    simpa [form, sq_eq_zero_iff] using e
  have reduce (x y : ℂ) : form x y (a*x+b*y) (c*x+d*y) =
      (2*(a*b+c*d)*x*y)^2 + 8*x*y*(a*x+b*y)*(c*x+d*y) := by
    unfold form
    have eqn : x^2+y^2+(a*x+b*y)^2+(c*x+d*y)^2 = 2*(a*b+c*d)*x*y := by
      linear_combination x^2*A+y^2*B
    rw [eqn]
  have h1 := h 1 1
  have h2 := h 1 (-1)
  have h3 := h 1 2
  rw [reduce] at h1 h2 h3
  have hc : a*c=0 := by linear_combination (6*h1-2*h2-h3)/48
  have hd : b*d=0 := by linear_combination (-3*h1-h2)/48+h3/48
  have hm : (a*b+c*d)^2+2*(a*d+b*c)=0 := by linear_combination (h1+h2)/8
  rcases mul_eq_zero.mp hc with ha|hc <;> rcases mul_eq_zero.mp hd with hb|hd
  all_goals subst_vars; simp [mul_eq_zero] at hm; rcases hm with h0|h0 <;> subst_vars <;> norm_num at *

lemma chart_order (i j : Fin 4) (hij : i ≠ j) :
    ∃ k l : Fin 4, (∀ u : V, quart u = form (u i) (u j) (u k) (u l)) := by
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact ⟨2,3, fun u => by change quart u = form (u 0) (u 1) (u 2) (u 3); unfold quart form; ring⟩
  · exact ⟨1,3, fun u => by change quart u = form (u 0) (u 2) (u 1) (u 3); unfold quart form; ring⟩
  · exact ⟨1,2, fun u => by change quart u = form (u 0) (u 3) (u 1) (u 2); unfold quart form; ring⟩
  · exact ⟨2,3, fun u => by change quart u = form (u 1) (u 0) (u 2) (u 3); unfold quart form; ring⟩
  · exact False.elim (hij rfl)
  · exact ⟨0,3, fun u => by change quart u = form (u 1) (u 2) (u 0) (u 3); unfold quart form; ring⟩
  · exact ⟨0,2, fun u => by change quart u = form (u 1) (u 3) (u 0) (u 2); unfold quart form; ring⟩
  · exact ⟨1,3, fun u => by change quart u = form (u 2) (u 0) (u 1) (u 3); unfold quart form; ring⟩
  · exact ⟨0,3, fun u => by change quart u = form (u 2) (u 1) (u 0) (u 3); unfold quart form; ring⟩
  · exact False.elim (hij rfl)
  · exact ⟨0,1, fun u => by change quart u = form (u 2) (u 3) (u 0) (u 1); unfold quart form; ring⟩
  · exact ⟨1,2, fun u => by change quart u = form (u 3) (u 0) (u 1) (u 2); unfold quart form; ring⟩
  · exact ⟨0,2, fun u => by change quart u = form (u 3) (u 1) (u 0) (u 2); unfold quart form; ring⟩
  · exact ⟨0,1, fun u => by change quart u = form (u 3) (u 2) (u 0) (u 1); unfold quart form; ring⟩
  · exact False.elim (hij rfl)

lemma coordinate (U : Submodule ℂ V) (hu : ∀ u ∈ U, quart u = 0) :
    ∃ i : Fin 4, ∀ u ∈ U, u i = 0 → u = 0 := by
  classical
  by_cases ht : ∀ u ∈ U, u = 0
  · exact ⟨0, fun u h _ => ht u h⟩
  push Not at ht
  obtain ⟨v,hv,hne⟩ := ht
  obtain ⟨i,hi⟩ : ∃ i, v i ≠ 0 := by simpa [funext_iff] using hne
  refine ⟨i, fun u hu' hz => ?_⟩
  by_contra hne'
  obtain ⟨j,hj⟩ : ∃ j, u j ≠ 0 := by simpa [funext_iff] using hne'
  obtain ⟨k,l,horder⟩ := chart_order i j (by rintro rfl; exact hj hz)
  let w : V := (u j)⁻¹ • u
  let z : V := (v i)⁻¹ • (v-v j • w)
  have hw : w ∈ U := U.smul_mem _ hu'
  have hzz : z ∈ U := U.smul_mem _ (U.sub_mem hv (U.smul_mem _ hw))
  have wi : w i = 0 := by simp [w,hz]
  have wj : w j = 1 := by simp [w,hj]
  have zi : z i = 1 := by simp [z,wi,hi]
  have zj : z j = 0 := by simp [z,wj]
  apply no_chart (z k) (w k) (z l) (w l)
  intro x y
  have e := hu _ (U.add_mem (U.smul_mem x hzz) (U.smul_mem y hw))
  rw [horder] at e
  simpa [wi,wj,zi,zj,mul_comm] using e
lemma top_zero (L : Submodule ℂ M) (lev : ∀ X ∈ L, (base + X).permanent = 65)
    (X : M) (hx : X ∈ L) : X.permanent = 0 := by
  have h (t : ℂ) := lev (t • X) (L.smul_mem t hx)
  have idn : 24 * X.permanent = (base + (2 : ℂ) • X).permanent -
      4*(base + X).permanent + 6*base.permanent -
      4*(base + (-1 : ℂ) • X).permanent + (base + (-2 : ℂ) • X).permanent := by
    simp only [Matrix.permanent, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    simp only [Fin.prod_univ_four,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
    ring
  have h0 : base.permanent = 65 := by simpa using h 0
  rw [h 2,lev X hx,h0,h (-1),h (-2)] at idn
  linear_combination idn/24

lemma coeffs (w x y z : ℂ) (h : ∀ t : ℂ, w*t+x*t^2+y*t^3+z*t^4=0) :
    w=0 ∧ x=0 ∧ y=0 ∧ z=0 := by
  refine ⟨?_,?_,?_,?_⟩
  · linear_combination 2/3*(h 1-h (-1))-(h 2-h (-2))/12
  · linear_combination 2/3*(h 1+h (-1))-(h 2+h (-2))/24
  · linear_combination -(h 1-h (-1))/6+(h 2-h (-2))/12
  · linear_combination -(h 1+h (-1))/6+(h 2+h (-2))/24

lemma fixed_form (a b c d : ℂ)
    (h : ∀ t : ℂ, form (2+t*a) (1+t*b) (1+t*c) (1+t*d) = 65) :
    a=0 ∧ b=0 ∧ c=0 ∧ d=0 := by
  let s := b+c+d
  let p := b*c+b*d+c*d
  let r := b*c*d
  let m := a^2+s^2-2*p
  obtain ⟨h1,h2,h3,h4⟩ := coeffs (64*a+44*s) (4*(2*a+s)^2+14*m+8*(2*p+a*s))
      (4*(2*a+s)*m+8*(2*r+a*p)) (m^2+8*a*r) (by
    intro t
    have ht := h t
    unfold form at ht
    dsimp [m,s,p,r]
    linear_combination ht)
  have hs : s = -16*a/11 := by linear_combination h1/44
  dsimp only [m] at h2 h3 h4
  rw [hs] at h2 h3 h4
  have hp : p=669*a^2/242 := by linear_combination -h2/12
  rw [hp] at h3 h4
  have hr : r= -5607*a^3/5324 := by linear_combination h3/16
  rw [hr] at h4
  have ha : a^4=0 := by linear_combination -14641*h4/38090
  have ha' : a=0 := by simpa using ha
  rw [ha'] at hs hp hr
  norm_num at hs hp hr
  dsimp [s,p,r] at hs hp hr
  refine ⟨ha',?_,?_,?_⟩
  all_goals
    apply (pow_eq_zero_iff (n := 3) (by decide)).mp
  · linear_combination b^2*hs-b*hp+hr
  · linear_combination c^2*hs-c*hp+hr
  · linear_combination d^2*hs-d*hp+hr

lemma fixed_zero (L : Submodule ℂ M) (lev : ∀ X ∈ L, (base + X).permanent = 65)
    (u : V) (hm : twist 0 u ∈ L) : u=0 := by
  have h (t : ℂ) : form (2+t*u 0) (1+t*u 1) (1+t*u 2) (1+t*u 3) = 65 := by
    let v : V := ![2+t*u 0,1+t*u 1,1+t*u 2,1+t*u 3]
    have he : base+t • twist 0 u = twist 0 v := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [v,base,twist,signK,addK, Matrix.cons_val_succ]
    have h' := lev _ (L.smul_mem t hm)
    rw [he,perm_twist] at h'
    exact h'
  obtain ⟨h0,h1,h2,h3⟩ := fixed_form _ _ _ _ h
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

noncomputable def translation (g : Fin 4) (X : M) : M :=
  Matrix.of fun i j => X (addK i g) (addK j g)

noncomputable def fourier (k : Fin 4) : M →ₗ[ℂ] V where
  toFun X d := (∑ i, signK k i * X i (addK i d))/4
  map_add' X Y := by
    funext d
    simp [mul_add,Finset.sum_add_distrib,add_div]
  map_smul' c X := by
    funext d
    simp only [Matrix.smul_apply,smul_eq_mul,RingHom.id_apply,Pi.smul_apply]
    simp_rw [show ∀ a b : ℂ, a*(c*b)=c*(a*b) from fun a b => by ring, ← Finset.mul_sum]
    ring

lemma avg (k : Fin 4) (X : M) : twist k (fourier k X) =
    ∑ g : Fin 4, (signK k g/4) • translation g X := by
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [fourier,twist,translation,signK,addK, Fin.sum_univ_four, Matrix.cons_val_succ,
      Matrix.add_apply] <;> ring

lemma reconstruct (X : M) : ∑ k : Fin 4, twist k (fourier k X) = X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fourier,twist,signK,addK,Fin.sum_univ_four, Matrix.cons_val_succ,
      Matrix.add_apply] <;> ring

theorem bound (L : Submodule ℂ M)
    (stable : ∀ g X, X ∈ L → translation g X ∈ L)
    (lev : ∀ X ∈ L, (base + X).permanent = 65) : Module.finrank ℂ L ≤ 3 := by
  classical
  have member (k : Fin 4) (X : M) (hx : X ∈ L) : twist k (fourier k X) ∈ L := by
    rw [avg]
    exact L.sum_mem fun g _ => L.smul_mem _ (stable g X hx)
  have vanish (k : Fin 4) (u : V) (hu : u ∈ L.map (fourier k)) : quart u = 0 := by
    obtain ⟨X,hX,rfl⟩ := hu
    rw [← perm_twist k]
    exact top_zero L lev _ (member k X hX)
  choose pivot hp using fun k => coordinate (L.map (fourier k)) (vanish k)
  let code : L →ₗ[ℂ] (Fin 3 → ℂ) := LinearMap.pi fun k =>
    (LinearMap.proj (pivot k.succ)).comp ((fourier k.succ).comp L.subtype)
  have inj : Function.Injective code := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro X hx
    have hz (k : Fin 4) : fourier k (X : M) = 0 := by
      refine Fin.cases ?_ (fun j => ?_) k
      · exact fixed_zero L lev _ (member 0 X X.property)
      · apply hp _ _ ⟨X, X.property,rfl⟩
        exact congrFun hx j
    apply Subtype.ext
    change (X : M) = 0
    rw [← reconstruct (X : M)]
    apply Finset.sum_eq_zero
    intro k _
    rw [hz]
    ext i j
    simp [twist]
  simpa using code.finrank_le_finrank_of_injective inj

end PEqualNP.Research.KleinPermanent

theorem PEqualNP.Research.KleinPermanent :
  ∀ L : Submodule ℂ (Matrix (Fin 4) (Fin 4) ℂ),
  (∀ (g : Fin 4) (X : Matrix (Fin 4) (Fin 4) ℂ), X ∈ L →
    (Matrix.of fun (i j : Fin 4) => X (i ^^^ g) (j ^^^ g)) ∈ L) →
  (∀ X ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
    (if i = j then (2 : ℂ) else 1) + X i j) = 65) →
  Module.finrank ℂ L ≤ 3 := by
  exact PEqualNP.Research.KleinPermanent.bound
