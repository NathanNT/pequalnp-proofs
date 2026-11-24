import Mathlib

namespace PEqualNP.Outside.CyclicPlane

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


noncomputable def plane (x y : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of ![![0, -x - 3*y, -x + 3*y, 2*y],
    ![-x - 3*y, 0, 2*x, -x - y],
    ![-x + 3*y, 2*x, 0, x - y],
    ![2*y, -x - y, x - y, 0]]

noncomputable def test (a b c d e f g h i j x y t : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of ![![a*t + 1, b*t - x - 3*y + 1, c*t - x + 3*y + 1, d*t + 2*y + 1],
    ![b*t - x - 3*y + 1, e*t + 1, f*t + 2*x + 1, g*t - x - y + 1],
    ![c*t - x + 3*y + 1, f*t + 2*x + 1, h*t + 1, i*t + x - y + 1],
    ![d*t + 2*y + 1, g*t - x - y + 1, i*t + x - y + 1, j*t + 1]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 12000000 in
lemma variation (a b c d e f g h i j x y : ℂ)
    (level : ∀ t, (test a b c d e f g h i j x y t).permanent = 24) :
    a * (-2*(2*x^3 - 2*x^2 - 2*x*y^2 + 4*x*y - 4*x - 2*y^2 + 4*y - 3))
      + b * (-4*(x^2 - 2*x*y - x + y^2 + y - 3))
      + c * (-4*(x^2 + 2*x*y + x + y^2 + y - 3))
      + d * (4*(4*x*y + 2*x + 3))
      + e * (-2*(2*x^2*y - 8*x*y^2 + 6*y^3 - 8*y^2 - 8*y - 3))
      + f * (-4*(4*y^2 - 2*y - 3))
      + g * (4*(x^2 - 2*x*y - x - 3*y^2 + 3*y + 3))
      + h * (2*(2*x^2*y + 2*x^2 + 8*x*y^2 + 4*x*y - 4*x + 6*y^3 + 2*y^2 - 4*y + 3))
      + i * (-4*(x^2 + 2*x*y + x - 3*y^2 + 3*y - 3))
      + j * (2*(2*x^3 - 18*x*y^2 + 3)) = 0 := by
  have u := level 1
  have v := level (-1)
  have w := level 2
  have z := level (-2)
  simp [perm4, test] at u v w z
  linear_combination (8*u-8*v-w+z)/12

lemma level_coordinates (a b c d e f g h i j : ℂ)
    (level : ∀ x y t, (test a b c d e f g h i j x y t).permanent = 24) :
    a = j ∧ b = 2*g + i + 6*j ∧ c = -g - 2*i - 4*j ∧ d = -g - i - 5*j ∧ e = j ∧ f = -g + i + j ∧ h = j := by
  have v0 := variation a b c d e f g h i j (0) (0) (level (0) (0))
  have v1 := variation a b c d e f g h i j (0) (1) (level (0) (1))
  have v2 := variation a b c d e f g h i j (0) (-1) (level (0) (-1))
  have v3 := variation a b c d e f g h i j (0) (2) (level (0) (2))
  have v4 := variation a b c d e f g h i j (1) (0) (level (1) (0))
  have v5 := variation a b c d e f g h i j (1) (1) (level (1) (1))
  have v6 := variation a b c d e f g h i j (1) (-1) (level (1) (-1))
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ ⟩
  · linear_combination (1)*v0/148 + (-35)*v1/888 + (-65)*v2/2664 + (1)*v3/333 + (3)*v4/148 + (1)*v5/296 + (9)*v6/296
  · linear_combination (167)*v0/888 + (-191)*v1/888 + (5)*v2/1332 + (-61)*v3/2664 + (-55)*v4/296 + (17)*v5/148 + (5)*v6/148
  · linear_combination (-73)*v0/1776 + (35)*v1/296 + (7)*v2/222 + (7)*v3/592 + (19)*v4/296 + (-43)*v5/592 + (-17)*v6/592
  · linear_combination (-523)*v0/3552 + (21)*v1/148 + (41)*v2/888 + (43)*v3/3552 + (45)*v4/296 + (-81)*v5/1184 + (-63)*v6/1184
  · linear_combination (17)*v0/1776 + (3)*v1/296 + (-5)*v2/888 + (-13)*v3/1776 + (-5)*v4/148 + (9)*v5/592 + (7)*v6/592
  · linear_combination (59)*v0/1184 + (-13)*v1/888 + (-151)*v2/2664 + (-23)*v3/10656 + (-1)*v4/148 + (11)*v5/1184 + (25)*v6/1184
  · linear_combination (91)*v0/1776 + (-7)*v1/222 + (-13)*v2/666 + (35)*v3/5328 + (-5)*v4/148 + (9)*v5/592 + (7)*v6/592

lemma plane_level (x y : ℂ) :
    (Matrix.of fun i j => 1 + plane x y i j).permanent = 24 := by
  simp [perm4, plane]
  ring

lemma plane_injective : Function.Injective (fun z : ℂ × ℂ => plane z.1 z.2) := by
  rintro ⟨x,y⟩ ⟨u,v⟩ he
  have h1 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℂ => A 1 2) he
  have h2 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℂ => A 0 3) he
  change 2*x = 2*u at h1
  change 2*y = 2*v at h2
  exact Prod.ext (by linear_combination h1/2) (by linear_combination h2/2)

lemma maximal (D : Matrix (Fin 4) (Fin 4) ℂ) (hD : D.IsSymm)
    (level : ∀ x y t : ℂ, (Matrix.of fun i j => 1 + plane x y i j + t*D i j).permanent = 24) :
    ∃ p q, D = plane p q := by
  have coord (x y t : ℂ) :
      (Matrix.of fun i j => 1 + plane x y i j + t*D i j) =
        test (D 0 0) (D 0 1) (D 0 2) (D 0 3) (D 1 1) (D 1 2)
          (D 1 3) (D 2 2) (D 2 3) (D 3 3) x y t := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [plane, test, hD.apply 0 1, hD.apply 0 2, hD.apply 0 3,
        hD.apply 1 2, hD.apply 1 3, hD.apply 2 3] <;> ring
  have hc := level
  simp only [coord] at hc
  obtain ⟨e00,e01,e02,e03,e11,e12,e22⟩ := level_coordinates _ _ _ _ _ _ _ _ _ _ hc
  let p := (D 2 3 - D 1 3)/2
  let q := -(D 2 3 + D 1 3)/2
  let K : Matrix (Fin 4) (Fin 4) ℂ :=
    Matrix.of ![![1,6,-4,-5], ![6,1,1,0], ![-4,1,1,0], ![-5,0,0,1]]
  have split : ∀ i j, D i j = plane p q i j + D 3 3 * K i j := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [plane,p,q,K,hD.apply 0 1,hD.apply 0 2,hD.apply 0 3,
        hD.apply 1 2,hD.apply 1 3,hD.apply 2 3,e00,e01,e02,e03,e11,e12,e22] <;> ring
  have hj : D 3 3 = 0 := by
    by_contra hn
    let t := (D 3 3)⁻¹
    have hm : (Matrix.of fun i j => 1 + plane (-t*p) (-t*q) i j + t*D i j) =
        (Matrix.of fun i j => 1 + K i j) := by
      ext i j
      simp only [Matrix.of_apply]
      rw [split i j]
      fin_cases i <;> fin_cases j <;> simp [plane,K,t] <;> field_simp <;> ring
    have hh := level (-t*p) (-t*q) t
    rw [hm] at hh
    norm_num [K,perm4] at hh
  refine ⟨p,q,?_⟩
  ext i j
  simpa [hj] using split i j

end PEqualNP.Outside.CyclicPlane

theorem PEqualNP.Outside.CyclicPlane :
  let P := fun (x y : ℂ) => Matrix.of ![![0, -x - 3*y, -x + 3*y, 2*y],
    ![-x - 3*y, 0, 2*x, -x - y],
    ![-x + 3*y, 2*x, 0, x - y],
    ![2*y, -x - y, x - y, 0]]
  Function.Injective (fun z : ℂ × ℂ => P z.1 z.2) ∧
  (∀ x y : ℂ, (Matrix.of fun i j => 1 + P x y i j).permanent = 24) ∧
  ∀ D : Matrix (Fin 4) (Fin 4) ℂ, D.IsSymm →
    (∀ x y t : ℂ, (Matrix.of fun i j => 1 + P x y i j + t*D i j).permanent = 24) →
    ∃ p q, D = P p q := by
  exact ⟨PEqualNP.Outside.CyclicPlane.plane_injective, PEqualNP.Outside.CyclicPlane.plane_level, PEqualNP.Outside.CyclicPlane.maximal⟩
