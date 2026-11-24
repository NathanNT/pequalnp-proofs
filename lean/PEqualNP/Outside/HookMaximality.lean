import Mathlib

namespace PEqualNP.Outside.HookMaximality

-- The 24-term expansion is from the checked upstream L-gct-222.
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


noncomputable def test (a b c d e f g h i j x y t : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of ![![1+t*a, 1+x+t*b, 1+y+t*c, 1-x-y+t*d],
    ![1+x+t*b, 1+t*e, 1+t*f, 1+t*g],
    ![1+y+t*c, 1+t*f, 1+t*h, 1+t*i],
    ![1-x-y+t*d, 1+t*g, 1+t*i, 1+t*j]]

-- This four-point difference extracts twelve times the coefficient of t.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma firstVariation (a b c d e f g h i j x y : ℂ)
    (level : ∀ t, (test a b c d e f g h i j x y t).permanent = 24) :
    6*(a+2*(b+c+d)+e+2*(f+g+i)+h+j)
      + 4*(-e-f+i+j)*x + 4*(-f+g-h+j)*y
      + (e-2*g+j)*x^2 + 2*(f-g-i+j)*x*y + (h-2*i+j)*y^2 = 0 := by
  have u := level 1
  have v := level (-1)
  have w := level 2
  have z := level (-2)
  simp [perm4, test] at u v w z
  linear_combination (8*u-8*v-w+z)/12

lemma extend_iff (a b c d e f g h i j : ℂ) :
    (∀ x y t, (test a b c d e f g h i j x y t).permanent = 24) ↔
      a = 0 ∧ b+c+d = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0 ∧ i = 0 ∧ j = 0 := by
  constructor
  · intro level
    have v := fun x y => firstVariation a b c d e f g h i j x y (level x y)
    have v0 := v 0 0
    have v1 := v 1 0
    have v2 := v (-1) 0
    have v3 := v 0 1
    have v4 := v 0 (-1)
    have v5 := v 1 1
    have eq1 : e=j := by linear_combination (-2)*v0/3 + (5)*v1/12 + (1)*v2/4 + (1)*v3/3 + (-1)*v5/3
    have eq2 : f=j := by linear_combination (5)*v0/6 + (-3)*v1/8 + (-1)*v2/8 + (-3)*v3/8 + (-1)*v4/8 + (1)*v5/6
    have eq3 : g=j := by linear_combination (1)*v0/6 + (-1)*v1/24 + (-1)*v2/8 + (1)*v3/6 + (-1)*v5/6
    have eq4 : h=j := by linear_combination (-2)*v0/3 + (1)*v1/3 + (5)*v3/12 + (1)*v4/4 + (-1)*v5/3
    have eq5 : i=j := by linear_combination (1)*v0/6 + (1)*v1/6 + (-1)*v3/24 + (-1)*v4/8 + (-1)*v5/6
    subst e
    subst f
    subst g
    subst h
    subst i
    have hj : j = 0 := by
      by_contra hj
      have hk : 1+(-j⁻¹)*j = 0 := by field_simp; ring
      have q := level 0 0 (-j⁻¹)
      simp only [perm4, test, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, hk, mul_zero, zero_mul, add_zero, zero_add] at q
      norm_num at q
    subst j
    have h0 : a + 2*(b+c+d) = 0 := by linear_combination v0/6
    have q := level 0 0 1
    simp [perm4, test] at q
    have hs : (b+c+d)^2 = 0 := by linear_combination q/2 - 3*h0
    have hs' := sq_eq_zero_iff.mp hs
    exact ⟨by linear_combination h0 - 2*hs', hs', rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rintro ⟨rfl, hs, rfl, rfl, rfl, rfl, rfl, rfl⟩ x y t
    have hd : d = -(b+c) := by linear_combination hs
    subst d
    simp [test, perm4]
    ring

end PEqualNP.Outside.HookMaximality

theorem PEqualNP.Outside.HookMaximality : ∀ D : Matrix (Fin 4) (Fin 4) ℂ, D.IsSymm →
  let H := fun (x y : ℂ) => Matrix.of ![![0, x, y, -x-y],
    ![x, 0, 0, 0], ![y, 0, 0, 0], ![-x-y, 0, 0, 0]]
  (∀ x y t : ℂ, (Matrix.of fun i j => 1 + H x y i j + t * D i j).permanent = 24) ↔
    D = H (D 0 1) (D 0 2) := by
  intro D hD H
  have asTest (x y t : ℂ) :
      (Matrix.of fun i j => 1 + H x y i j + t * D i j) =
        PEqualNP.Outside.HookMaximality.test (D 0 0) (D 0 1) (D 0 2) (D 0 3)
          (D 1 1) (D 1 2) (D 1 3) (D 2 2) (D 2 3) (D 3 3) x y t := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [H, PEqualNP.Outside.HookMaximality.test,
        hD.apply 0 1, hD.apply 0 2, hD.apply 0 3, hD.apply 1 2,
        hD.apply 1 3, hD.apply 2 3] <;> ring
  simp only [asTest]
  rw [PEqualNP.Outside.HookMaximality.extend_iff]
  constructor
  · rintro ⟨a, s, e, f, g, h, i, j⟩
    have d : D 0 3 = -D 0 1 - D 0 2 := by linear_combination s
    ext u v
    fin_cases u <;> fin_cases v <;>
      simp [H, hD.apply 0 1, hD.apply 0 2, hD.apply 0 3, hD.apply 1 2,
        hD.apply 1 3, hD.apply 2 3, a, d, e, f, g, h, i, j]
  · intro eqH
    have ent (i j : Fin 4) := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M i j) eqH
    refine ⟨ent 0 0, ?_, ent 1 1, ent 1 2, ent 1 3, ent 2 2, ent 2 3, ent 3 3⟩
    have d := ent 0 3
    change D 0 3 = -D 0 1 - D 0 2 at d
    linear_combination d
