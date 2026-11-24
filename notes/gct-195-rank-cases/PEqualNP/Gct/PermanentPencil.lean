import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace PEqualNP.Gct.PermanentPencil
abbrev Pos := Fin 4 × Fin 6
def first {R : Type*} [CommRing R] (m : Pos → R) : R := ∑ i : Fin 4, ∑ j, m (i,j)
def second {R : Type*} [CommRing R] (m : Pos → R) : R :=
  ∑ j, ∑ l, if j=l then 0 else ∑ a : Fin 4, ∑ b : Fin 4,
    if a<b then m (a,j)*m (b,l) else 0
def third {R : Type*} [CommRing R] (m : Pos → R) : R :=
  ∑ j, ∑ l, ∑ n, if j=l ∨ j=n ∨ l=n then 0 else
    ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
      if a<b ∧ b<c then m (a,j)*m (b,l)*m (c,n) else 0
def fourth {R : Type*} [CommRing R] (m : Pos → R) : R :=
  ∑ j, ∑ l, ∑ n, ∑ o, if j=l ∨ j=n ∨ j=o ∨ l=n ∨ l=o ∨ n=o then 0 else
      m (0,j)*m (1,l)*m (2,n)*m (3,o)
def level (m : Pos → ℂ) : Prop := first m=0 ∧ second m=0 ∧ third m=0 ∧ fourth m=0

open MvPolynomial
noncomputable def pencil (x a b : Pos → ℂ) (ij : Pos) : MvPolynomial (Fin 3) ℂ :=
  X 0*C (x ij) + X 1*C (a ij) + X 2*C (b ij)

theorem coefficients (L : Submodule ℂ (Pos → ℂ)) (lev : ∀ m ∈ L, level m)
    {x a b : Pos → ℂ} (hx : x ∈ L) (ha : a ∈ L) (hb : b ∈ L) (d : Fin 3 →₀ ℕ) :
    (first (pencil x a b)).coeff d=0 ∧ (second (pencil x a b)).coeff d=0 ∧
    (third (pencil x a b)).coeff d=0 ∧ (fourth (pencil x a b)).coeff d=0 := by
  classical
  let lin (t : Fin 3 → ℂ) := t 0 • x + t 1 • a + t 2 • b
  have van (t : Fin 3 → ℂ) := lev (lin t) (L.add_mem (L.add_mem (L.smul_mem _ hx) (L.smul_mem _ ha)) (L.smul_mem _ hb))
  have ev (t : Fin 3 → ℂ) (ij : Pos) : eval t (pencil x a b ij)=lin t ij := by
    simp [pencil,lin]
  have f1 : first (pencil x a b)=0 := by
    apply MvPolynomial.funext
    intro t
    simpa [first,ev] using (show first (lin t)=0 from (van t).1)
  have f2 : second (pencil x a b)=0 := by
    apply MvPolynomial.funext
    intro t
    simpa [second,apply_ite,ev] using (show second (lin t)=0 from (van t).2.1)
  have f3 : third (pencil x a b)=0 := by
    apply MvPolynomial.funext
    intro t
    simpa [third,apply_ite,ev] using (show third (lin t)=0 from (van t).2.2.1)
  have f4 : fourth (pencil x a b)=0 := by
    apply MvPolynomial.funext
    intro t
    simpa [fourth,apply_ite,ev] using (show fourth (lin t)=0 from (van t).2.2.2)
  simp [f1,f2,f3,f4]
end PEqualNP.Gct.PermanentPencil
