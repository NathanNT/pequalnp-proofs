import PEqualNP.Gct.OrderedPermanent

namespace PEqualNP.Gct.FourierTable
noncomputable def mixed (ms : List Mat) : ℂ := rect ms (List.range 4) (List.range 6)

private lemma sameIntegrate (x : Fin 15 → ℂ) {f g : Fin 15 → ℂ} (h : ∀ i, f i=g i) :
    integrate x f=integrate x g := congrArg (integrate x) (funext h)

theorem mixedTwo {w : ℂ} (hw : w^2+w+1=0) (x : Fin 15 → ℂ) (seed : List Nat) :
    mixed (combo w x :: combo w x :: seed.map (atom w)) = bil w x seed := by
  apply (expandSlot w x [] (combo w x :: seed.map (atom w)) (List.range 4) (List.range 6)).trans
  apply sameIntegrate
  intro i
  apply (expandSlot w x [atom w i] (seed.map (atom w)) (List.range 4) (List.range 6)).trans
  apply sameIntegrate
  intro j
  exact atomContraction hw (i.val::j.val::seed)

theorem mixedThree {w : ℂ} (hw : w^2+w+1=0) (x : Fin 15 → ℂ) :
    mixed [combo w x,combo w x,combo w x] = cub w x := by
  apply (expandSlot w x [] [combo w x,combo w x] (List.range 4) (List.range 6)).trans
  apply sameIntegrate
  intro i
  apply (expandSlot w x [atom w i] [combo w x] (List.range 4) (List.range 6)).trans
  apply sameIntegrate
  intro j
  apply (expandSlot w x [atom w i,atom w j] [] (List.range 4) (List.range 6)).trans
  apply sameIntegrate
  intro k
  exact atomContraction hw [i.val,j.val,k.val]

end PEqualNP.Gct.FourierTable

open Module PEqualNP.Gct.FourierTable
theorem PEqualNP.Gct.SaturatedMatrixBound (w : ℂ) (hw : w^2+w+1=0)
    (W : Submodule ℂ (Fin 15 → ℂ))
    (level : ∀ x ∈ W, let m := combo w x; let a := atom w 15; let b := atom w 16
      mixed [m,m,a,a]=0 ∧ mixed [m,m,a,b]=0 ∧ mixed [m,m,b,b]=0 ∧
      mixed [m,m]=0 ∧ mixed [m,m,b]=0 ∧ mixed [m,m,m]=0) :
    finrank ℂ W ≤ 6 := by
  apply PEqualNP.Gct.SaturatedTensorBound w W
  intro x hx
  obtain ⟨qaa,qab,qbb,qq,qqb,qqq⟩ := level x hx
  exact ⟨(mixedTwo hw x [15,15]).symm.trans qaa,(mixedTwo hw x [15,16]).symm.trans qab,
    (mixedTwo hw x [16,16]).symm.trans qbb,(mixedTwo hw x []).symm.trans qq,
    (mixedTwo hw x [16]).symm.trans qqb,(mixedThree hw x).symm.trans qqq⟩
