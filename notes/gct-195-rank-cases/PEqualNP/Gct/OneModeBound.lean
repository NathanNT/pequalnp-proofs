import PEqualNP.Gct.OneModeCubic
import PEqualNP.Gct.CanonicalCap
namespace PEqualNP.Gct.OneMode
open Module FourierTable DeskPolar PermanentPencil
abbrev Row := Fin 6 → ℂ
noncomputable def blockMap (w : ℂ) : (Row × Row) →ₗ[ℂ] (Pos → ℂ) where
  toFun u := block w u.1 u.2
  map_add' x y := by funext p; by_cases h : p.1=3 <;> simp [block,h,mul_add]
  map_smul' c x := by funext p; by_cases h : p.1=3 <;> simp [block,h] <;> ring
noncomputable def aMat (w : ℂ) (p : Pos) : ℂ :=
  (if p.1=3 then -1 else 3)*(![1,w,w^2,0,0,0] p.2)
theorem ak {w : ℂ} (hw : w^2+w+1=0) : restrict (atom w 15)=aMat w := by
  funext p; obtain ⟨r,j⟩ := p
  fin_cases r <;> fin_cases j <;>
    norm_num [restrict,atom,row,col,wave,c,val,aMat,Matrix.cons_val] <;>
    first | linear_combination hw | linear_combination -hw | linear_combination 3*hw | linear_combination -3*hw
theorem lastIsBlock (w : ℂ) (y : Row) : restrict (lastRow y)=block w y 0 := by
  funext p; obtain ⟨r,j⟩ := p
  fin_cases r <;> simp [restrict,lastRow,block]

theorem blockBound {w : ℂ} (hw : w^2+w+1=0) (L : Submodule ℂ (Pos → ℂ))
    (lev : ∀ m∈L,level m) (aL : aMat w ∈ L)
    (shape : ∀ m∈L, ∃ (t : ℂ) (y z : Row), m=t • aMat w + block w y z) :
    finrank ℂ L≤6 := by
  haveI : Orders := ⟨perm1,perm2,perm3,perm4⟩
  let S := L.comap PEqualNP.Gct.RankSeven.restr
  have sl (m : Mat) (hm : m∈S) := lev _ hm
  have ka : atom w 15 ∈ S := by change restrict (atom w 15)∈L; rwa [ak hw]
  let U := L.comap (blockMap w)
  let proj : U →ₗ[ℂ] Row := (LinearMap.snd ℂ Row Row).domRestrict U
  have zCap := CubicSix.dimension (LinearMap.range proj) (by
    rintro _ ⟨u,rfl⟩
    exact cubicConstraint hw u.val.1 u.val.2 (lev _ u.property))
  let K := LinearMap.ker proj
  let read : K →ₗ[ℂ] (Fin 2 → ℂ) := LinearMap.pi fun j =>
    ((LinearMap.proj (R:=ℂ) (φ:=fun _ : Fin 6 => ℂ) (![3,4] j)).comp (LinearMap.fst ℂ Row Row)).comp
      (U.subtype.comp K.subtype)
  have zero (x : K) (hx : read x=0) : x=0 := by
    have pd : x.val.val.2=0 := x.property
    have mem : lastRow x.val.val.1 ∈ S := by
      change restrict (lastRow x.val.val.1)∈L
      rw [lastIsBlock w,← pd]
      exact x.val.property
    obtain ⟨h0,h1,h2,hs⟩ := lastConstraint hw x.val.val.1 (by
      intro k
      fin_cases k
      · exact van1 S sl mem
      · exact van2 S sl mem ka
      · exact van3 S sl mem ka ka
      · exact van4 S sl mem ka ka ka)
    have x3 : x.val.val.1 3=0 := congrFun (show read x=0 from hx) 0
    have x4 : x.val.val.1 4=0 := congrFun (show read x=0 from hx) 1
    rw [x3,x4] at hs
    apply Subtype.ext; apply Subtype.ext; apply Prod.ext _ pd
    funext i; fin_cases i <;> simp_all
  have inj : Function.Injective read := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply zero
    funext j
    change x.val.val.1 (![3,4] j) - y.val.val.1 (![3,4] j)=0
    exact sub_eq_zero.mpr (congrFun hxy j)
  have yCap := read.finrank_le_finrank_of_injective inj
  simp only [Module.finrank_pi,Fintype.card_fin] at yCap
  have total := proj.finrank_range_add_finrank_ker
  have uCap : finrank ℂ U≤5 := by rw [← total]; exact Nat.add_le_add zCap yCap
  let join : (ℂ × U) →ₗ[ℂ] (Pos → ℂ) :=
    { toFun := fun v => v.1 • aMat w + blockMap w v.2.val
      map_add' := by intro x y; simp [add_smul]; abel
      map_smul' := by intro t x; simp [smul_add,smul_smul] }
  have incl : L≤LinearMap.range join := by
    intro m hm
    obtain ⟨t,y,z,rfl⟩ := shape m hm
    have mem : (y,z)∈U := by
      change block w y z∈L
      have h := L.sub_mem hm (L.smul_mem t aL)
      simpa [add_comm] using h
    exact ⟨(t,⟨(y,z),mem⟩),rfl⟩
  have hi := Submodule.finrank_mono incl
  have hd := join.finrank_range_le
  simp only [Module.finrank_prod,Module.finrank_self] at hd
  omega
end PEqualNP.Gct.OneMode
