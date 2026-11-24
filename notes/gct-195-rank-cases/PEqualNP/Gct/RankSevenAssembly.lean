import PEqualNP.Gct.CanonicalCap
import PEqualNP.Gct.ReindexKernel
namespace PEqualNP.Gct.RankSeven
open Module PermanentPencil
def contrast (L : Submodule ℂ (Pos → ℂ)) : L →ₗ[ℂ] (Fin 3 × Fin 6 → ℂ) where
  toFun m p := m.val (p.1.castSucc,p.2)+3*m.val (3,p.2)
  map_add' := by intro x y; ext p; simp; ring
  map_smul' := by intro c x; ext p; simp; ring
noncomputable def profileEquiv (L : Submodule ℂ (Pos → ℂ)) :
    (L.comap profile) ≃ₗ[ℂ] LinearMap.ker (contrast L) := by
  have recov (t : LinearMap.ker (contrast L)) :
      profile (fun j => -t.val.val (3,j))=t.val.val := by
    funext p
    obtain ⟨i,j⟩ := p
    have eqn (r : Fin 3) : t.val.val (r.castSucc,j)+3*t.val.val (3,j)=0 :=
      congrFun (show contrast L t.val=0 from t.property) (r,j)
    fin_cases i
    · change 3 * -t.val.val (3,j) = t.val.val (0,j)
      have he : t.val.val (0,j)+3*t.val.val (3,j)=0 := eqn 0
      linear_combination -he
    · change 3 * -t.val.val (3,j) = t.val.val (1,j)
      have he : t.val.val (1,j)+3*t.val.val (3,j)=0 := eqn 1
      linear_combination -he
    · change 3 * -t.val.val (3,j) = t.val.val (2,j)
      have he : t.val.val (2,j)+3*t.val.val (3,j)=0 := eqn 2
      linear_combination -he
    · change -1 * -t.val.val (3,j) = t.val.val (3,j)
      ring
  have kp (x : L.comap profile) : (⟨profile x,x.property⟩ : L) ∈ LinearMap.ker (contrast L) := by
    change contrast L _=0
    funext p
    rcases p with ⟨r,j⟩
    fin_cases r <;> simp [contrast,profile] <;> ring
  have im (t : LinearMap.ker (contrast L)) : (fun j => -t.val.val (3,j)) ∈ L.comap profile := by
    change profile _∈L
    rw [recov]; exact t.val.property
  exact { toFun := fun x => ⟨⟨profile x,x.property⟩,kp x⟩
          invFun := fun t => ⟨fun j => -t.val.val (3,j),im t⟩
          left_inv := by intro x; apply Subtype.ext; funext j; simp [profile]
          right_inv := fun t => Subtype.ext (Subtype.ext (recov t))
          map_add' := fun x y => Subtype.ext (Subtype.ext (map_add profile _ _))
          map_smul' := fun c x => Subtype.ext (Subtype.ext (map_smul profile _ _)) }


theorem forced [DeskPolar.Orders] (L : Submodule ℂ (Pos → ℂ)) (lev : ∀ m∈L,level m)
    (rk : finrank ℂ (LinearMap.range (contrast L))=7) :
    finrank ℂ (LinearMap.ker (contrast L)) ≤ 1 := by
  have small := (PEqualNP.Gct.ProfileFourSix (L.comap profile) (by
    intro x hx
    have lv := lev (profile x) hx
    exact ⟨lv.1,lv.2.1,lv.2.2.2⟩)).1
  have eqn := (profileEquiv L).finrank_eq
  by_contra! h
  have dim : finrank ℂ (L.comap profile)=2 := by omega
  let w : ℂ := (-1 + (Real.sqrt 3 : ℂ)*Complex.I)/2
  have hw : w^2+w+1=0 := by
    have h3 : (Real.sqrt 3 : ℂ)^2=3 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
    dsimp [w]
    linear_combination (norm := ring_nf) ((Real.sqrt 3:ℂ)^2 / 4)*(Complex.I_sq) - h3/4
  obtain ⟨M,hd,hm,ha,hb⟩ := normalize w hw L lev dim
  have bound := canonicalCap hw M hm ha hb
  have tot := (contrast L).finrank_range_add_finrank_ker
  omega
end PEqualNP.Gct.RankSeven

