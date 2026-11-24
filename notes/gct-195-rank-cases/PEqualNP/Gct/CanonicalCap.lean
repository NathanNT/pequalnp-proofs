import PEqualNP.Gct.ChartGradient
import PEqualNP.Gct.DeskPolarization

namespace PEqualNP.Gct.RankSeven
open Module FourierTable DeskPolar PermanentPencil
noncomputable def restr : Mat →ₗ[ℂ] (Pos → ℂ) where
  toFun := restrict
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
noncomputable def smallMap (w : ℂ) : (Fin 15 → ℂ) →ₗ[ℂ] (Pos → ℂ) where
  toFun x := restrict (combo w x)
  map_add' x y := by ext p; simp [restrict,combo,add_mul,Finset.sum_add_distrib]
  map_smul' c x := by ext p; simp [restrict,combo,Finset.mul_sum,mul_assoc]

theorem canonicalCap [Orders] {w : ℂ} (hw : w^2+w+1=0) (L : Submodule ℂ (Pos → ℂ))
    (lev : ∀ m∈L, level m) (ha : restrict (atom w 15)∈L) (hb : restrict (atom w 16)∈L) :
    finrank ℂ L ≤ 8 := by
  let S := L.comap restr
  have ls (m : Mat) (hm : m∈S) := lev _ hm
  have a : atom w 15∈S := ha
  have b : atom w 16∈S := hb
  have ae : extAtom w 15∈S := (ext_small w (by decide : 15<17)) ▸ a
  have be : extAtom w 16∈S := (ext_small w (by decide : 16<17)) ▸ b
  let W := L.comap (smallMap w)
  have small : finrank ℂ W ≤ 6 := by
    apply PEqualNP.Gct.SaturatedMatrixBound w hw W
    intro x hx
    have h : combo w x∈S := hx
    exact ⟨van4 S ls h h a a,van4 S ls h h a b,van4 S ls h h b b,
      van2 S ls h h,van3 S ls h h b,van3 S ls h h h⟩
  let p : (W × (ℂ × ℂ)) →ₗ[ℂ] (Pos → ℂ) :=
    { toFun := fun v => smallMap w v.1 + v.2.1 • restrict (atom w 15) + v.2.2 • restrict (atom w 16)
      map_add' := by intro x y; simp [add_smul]; abel
      map_smul' := by intro c x; simp [smul_add,smul_smul] }
  have incl : L ≤ LinearMap.range p := by
    intro m hm
    obtain ⟨z,hz⟩ := chart_surj hw m
    have mm : chart w z ∈ S := by change restrict (chart w z)∈L; rwa [hz]
    have hc := noComplement hw z (by
      intro seeds hs
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
      rcases hs with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact van1 S ls mm
      · exact van2 S ls mm be
      · exact van3 S ls mm be be
      · exact van4 S ls mm be be be
      · exact van2 S ls mm ae
      · exact van3 S ls mm ae ae
      · exact van4 S ls mm ae ae ae)
    have repr : smallMap w (first15 z) + z 15 • restrict (atom w 15) + z 16 • restrict (atom w 16)=m :=
      (congrArg restrict (chart_split w z hc)).symm.trans hz
    have mem : first15 z ∈ W := by
      change smallMap w (first15 z) ∈ L
      have hmem := L.sub_mem (L.sub_mem hm (L.smul_mem (z 16) hb)) (L.smul_mem (z 15) ha)
      rwa [← repr,add_sub_cancel_right,add_sub_cancel_right] at hmem
    exact ⟨(⟨first15 z,mem⟩,z 15,z 16),repr⟩
  have hi := Submodule.finrank_mono incl
  have rr := p.finrank_range_le
  simp only [Module.finrank_prod,Module.finrank_self] at rr
  omega
end PEqualNP.Gct.RankSeven
