import PEqualNP.Gct.PureRowEquations
import PEqualNP.Gct.PureSixth
namespace PEqualNP.Gct.PureRows
open Module PureGeometry PermanentPencil
noncomputable def pw (f : Row) (k : ℕ) : Row := fun j => f j^k
theorem powerDot (f : Row) (a b : ℕ) : pw f a ⬝ᵥ pw f b=moment f (a+b) := by
  simp [dotProduct,pw,moment,pow_add]
theorem momentZero (f : Row) : moment f 0=6 := by simp [moment]
set_option maxHeartbeats 1800000 in
theorem criterion (L : Submodule ℂ (Pos → ℂ)) (lev : ∀ m∈L,level m)
    (f : Row) (hf : RankSeven.profile f∈L) (hn : f≠0)
    (i j : Fin 4) (ij : i≠j) (hi : 2≤finrank ℂ (pureSpace L i))
    (hj : 2≤finrank ℂ (pureSpace L j)) : False := by
  let U := pureSpace L i
  let V := pureSpace L j
  have la := lev _ hf
  have pp := ProfileBounds.profileMoments f ⟨la.1,la.2.1,la.2.2.2⟩
  have p2 : moment f 2=0 := pp.1
  have p4 : moment f 4=0 := pp.2
  have p1 : moment f 1=0 := by
    have e := la.1
    change (∑ i : Fin 4, ∑ j, (if i=3 then (-1:ℂ) else 3)*f j)=0 at e
    simp only [Fin.sum_univ_four] at e
    norm_num at e
    simp only [← Finset.mul_sum] at e
    simp only [moment,pow_one]
    linear_combination e/8
  have orth (k : Fin 4) (r : Fin 4) (x : Row) (hx : x∈pureSpace L r) :
      pw f k.val ⬝ᵥ x=0 := by
    rw [dotProduct_comm]; exact rowMoments L lev f hf r x hx k
  have cross (x : Row) (hx : x∈V) (y : Row) (hy : y∈U) := distinctOrth L lev j i ij.symm x y hx hy
  have p3 : moment f 3=0 := by
    by_contra h
    let w : Fin 3 → Row := ![pw f 0,pw f 1,pw f 2]
    apply threeImpossible U V hi hj cross w
    · intro k x hx; fin_cases k 
      · exact orth 0 i x hx
      · exact orth 1 i x hx
      · exact orth 2 i x hx
    · intro k x hx; fin_cases k
      · exact orth 0 j x hx
      · exact orth 1 j x hx
      · exact orth 2 j x hx
    · intro c hc
      have e0 := hc 0
      have e1 := hc 1
      have e2 := hc 2
      norm_num [blend_dot,Fin.sum_univ_three,w,Matrix.cons_val,powerDot,momentZero,p1,p2,p4] at e0 e1 e2
      have a0 : c 0=0 := by simpa using e0
      have a2 : c 2=0 := e1.resolve_right h
      have a1 : c 1=0 := (mul_eq_zero.mp (by simpa [a2] using e2 : c 1*moment f 3=0)).resolve_right h
      funext k; fin_cases k <;> assumption
  have p5 : moment f 5=0 := by
    by_contra h
    let w : Fin 3 → Row := ![pw f 0,pw f 2,pw f 3]
    apply threeImpossible U V hi hj cross w
    · intro k x hx; fin_cases k 
      · exact orth 0 i x hx
      · exact orth 2 i x hx
      · exact orth 3 i x hx
    · intro k x hx; fin_cases k
      · exact orth 0 j x hx
      · exact orth 2 j x hx
      · exact orth 3 j x hx
    · intro c hc
      have e0 := hc 0
      have e1 := hc 1
      have e2 := hc 2
      norm_num [blend_dot,Fin.sum_univ_three,w,Matrix.cons_val,powerDot,momentZero,p1,p2,p4,p3] at e0 e1 e2
      have a0 : c 0=0 := by simpa using e0
      have a2 : c 2=0 := e1.resolve_right h
      have a1 : c 1=0 := (mul_eq_zero.mp (by simpa [a2] using e2 : c 1*moment f 5=0)).resolve_right h
      funext k; fin_cases k <;> assumption
  have low (k : Fin 5) : moment f (k.val+1)=0 := by fin_cases k <;> assumption
  have p6 := momentSix f hn low
  change moment f 6≠0 at p6
  let w : Fin 4 → Row := fun k => pw f k.val
  have independent : Function.Injective (blend w) := by
    apply LinearMap.ker_eq_bot.mp; apply le_antisymm _ bot_le
    intro c hc
    have hzero : blend w c=0 := hc
    have van (k : ℕ) := congrArg (fun r : Row => r ⬝ᵥ pw f k) hzero
    have e0 := van 0
    have e3 := van 3
    have e4 := van 4
    have e5 := van 5
    norm_num [blend_dot,Fin.sum_univ_four,w,powerDot,momentZero,p1,p2,p3,p4,p5] at e0 e3 e4 e5
    have a0 : c 0=0 := by simpa using e0
    have a3 : c 3=0 := e3.resolve_right p6
    have a2 : c 2=0 := (mul_eq_zero.mp (by simpa [a3] using e4 : c 2*moment f 6=0)).resolve_right p6
    have a1 : c 1=0 := (mul_eq_zero.mp (by simpa [a2,a3] using e5 : c 1*moment f 6=0)).resolve_right p6
    show c=0
    funext k; fin_cases k <;> assumption
  have mem (r : Fin 4) (hr : 2≤finrank ℂ (pureSpace L r)) : pw f 2∈pureSpace L r := by
    apply fourSpan w independent _ hr (fun k x hx => orth k r x hx)
    intro k
    change pw f k.val ⬝ᵥ pw f 2=0
    rw [powerDot]; fin_cases k <;> assumption
  exact p6 (quarticObstruction L lev f hf i j ij (mem i hi) (mem j hj) low)
end PEqualNP.Gct.PureRows
