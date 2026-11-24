import PEqualNP.Gct.RankSeven
import Mathlib.LinearAlgebra.Matrix.Dual

open Module
open PEqualNP.Gct.RankSeven

/-- The five hyperbolic pairs and the residual five coordinates of the two-triple tangent space. -/
theorem PEqualNP.Gct.FourSixBound (W : Submodule ℂ (Fin 15 → ℂ))
    (q20 : ∀ x ∈ W, x 4*x 12 + x 6*x 10 = 0)
    (q11 : ∀ x ∈ W, -108*x 0*x 2 + x 5*x 14 + x 8*x 11 = 0)
    (q02 : ∀ x ∈ W, x 3*x 13 + x 7*x 9 = 0)
    (s : ∀ x ∈ W, (∀ j ∈ ([0,2,4,5,6,8,10,11,12,14] : List (Fin 15)), x j = 0) →
      18*(x 1)^2 + x 3*x 9 = 0 ∧ x 7*x 13 = 0 ∧
      (x 3)^3+(x 7)^3+(x 9)^3+(x 13)^3-36*x 1*x 3*x 9 = 0) :
    finrank ℂ W ≤ 6 := by
  let atc (i : Fin 15) := (LinearMap.proj (R:=ℂ) (φ:=fun _ : Fin 15 => ℂ) i).domRestrict W
  let left : Fin 5 → Fin 15 := ![4,6,0,5,8]
  let right : Fin 5 → Fin 15 := ![12,10,2,14,11]
  let weight : Fin 5 → ℂ := ![1,1,-108,1,1]
  let p : W →ₗ[ℂ] (Fin 5 → ℂ) := LinearMap.pi (fun j => atc (left j))
  let c : W →ₗ[ℂ] (Fin 5 → ℂ) := LinearMap.pi (fun j => weight j • atc (right j))
  let eqv := dotProductEquiv ℂ (Fin 5)
  let q := eqv.toLinearMap.comp c
  have zeros (x : W) (hp : p x=0) (hq : q x=0) :
      ∀ j ∈ ([0,2,4,5,6,8,10,11,12,14] : List (Fin 15)), x.val j=0 := by
    have hc : c x=0 := eqv.injective (by simpa [q] using hq)
    have hp' (j : Fin 5) : x.val (left j)=0 := congrFun hp j
    have hc' (j : Fin 5) : weight j*x.val (right j)=0 := congrFun hc j
    have l0 := hp' 0; have l1 := hp' 1; have l2 := hp' 2
    have l3 := hp' 3; have l4 := hp' 4
    have r0 := hc' 0; have r1 := hc' 1; have r2 := hc' 2
    have r3 := hc' 3; have r4 := hc' 4
    norm_num [left,right,weight,Matrix.cons_val] at *
    exact ⟨l2,r2,l0,l3,l1,l4,r1,r4,r0,r3⟩
  apply normalFormBound p q (atc 1) (atc 3) (atc 7) (atc 9) (atc 13)
  · intro x
    change (∑ j : Fin 5, (weight j*x.val (right j)) * x.val (left j))=0
    simp only [Fin.sum_univ_succ]
    norm_num [left,right,weight,Matrix.cons_val]
    linear_combination q20 x.val x.property + q11 x.val x.property
  · intro x hp hq
    obtain ⟨e₀,e₁,e₃⟩ := s x.val x.property (zeros x hp hq)
    exact ⟨e₀,e₁,q02 x.val x.property,e₃⟩
  · intro x hp hq h1 h3 h7 h9 h13
    apply Subtype.ext
    funext i
    change x.val i=0
    have hz := zeros x hp hq
    change x.val 1=0 at h1
    change x.val 3=0 at h3
    change x.val 7=0 at h7
    change x.val 9=0 at h9
    change x.val 13=0 at h13
    fin_cases i <;> first | assumption | exact hz _ (by decide)

