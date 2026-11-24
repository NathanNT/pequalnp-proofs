import PEqualNP.Gct.PureCriterion
namespace PEqualNP.Gct.PureQuotient
open Module FourierTable DeskPolar PermanentPencil
open scoped ComplexConjugate
abbrev MatrixSpace := Pos → ℂ
noncomputable def extM (x : MatrixSpace) : Mat := fun i j => x (Fin.ofNat 4 i, Fin.ofNat 6 j)
private theorem resExt (x : MatrixSpace) : restrict (extM x)=x := by
  funext p; rcases p with ⟨r,j⟩
  change x (Fin.ofNat 4 r.val,Fin.ofNat 6 j.val)=_
  congr 2 <;> apply Fin.ext <;> exact Nat.mod_eq_of_lt (by first | exact r.isLt | exact j.isLt)
private theorem sumNat4 (f : Fin 4 → ℂ) :
    total (List.range 4) (fun i => f (Fin.ofNat 4 i))=∑ i, f i := by
  simp [total,Fin.sum_univ_succ,List.range_succ] <;> ring <;> rfl
private theorem eraseSum (l : List Nat) (f : Nat → ℂ) {j : Nat} (h : j ∈ l) :
    total (l.erase j) f=total l f-f j := by
  have e := ((List.perm_cons_erase h).map f).sum_eq
  simp [total] at *; linear_combination -e

set_option maxHeartbeats 1600000 in
theorem centeredPair (x y : MatrixSpace) (hr : ∀ i, ∑ j, x (i,j)=0)
    (hc : ∀ j, ∑ i, x (i,j)=0) :
    mixed [extM y,extM x]=∑ i : Fin 4, ∑ j : Fin 6, y (i,j)*x (i,j) := by
  let rs := List.range 4
  let cs := List.range 6
  have row (a : Nat) : total cs (extM x a)=0 :=
    (PureRows.sumLift (fun j => x (Fin.ofNat 4 a,j))).trans (hr _)
  have col (j : Nat) : total rs (fun a => extM x a j)=0 :=
    (sumNat4 (fun i => x (i,Fin.ofNat 6 j))).trans (hc _)
  have tail (a j : Nat) (ha : a∈rs) (hj : j∈cs) :
      rect [extM x] (rs.erase a) (cs.erase j)=extM x a j := by
    change total (rs.erase a) (fun r => total (cs.erase j) (fun c => extM x r c*1))=_
    simp only [mul_one]
    have e (r : Nat) : total (cs.erase j) (extM x r)=(-1)*extM x r j := by
      rw [eraseSum cs _ hj,row]; ring
    simp_rw [e]; rw [total_scale,eraseSum rs _ ha,col]; ring
  change total rs (fun a => total cs (fun j => extM y a j * rect [extM x] (rs.erase a) (cs.erase j)))=_
  trans total rs (fun a => total cs (fun j => extM y a j * extM x a j))
  · apply congrArg List.sum; apply List.map_congr_left; intro a ha
    apply congrArg List.sum; apply List.map_congr_left; intro j hj
    rw [tail a j ha hj]
  · have each (a : Nat) : total cs (fun j => extM y a j * extM x a j)=
        ∑ j, y (Fin.ofNat 4 a,j)*x (Fin.ofNat 4 a,j) :=
      PureRows.sumLift (fun j => y (Fin.ofNat 4 a,j)*x (Fin.ofNat 4 a,j))
    simp_rw [each]; exact sumNat4 (fun i => ∑ j, y (i,j)*x (i,j))

theorem centeredNoConj (L : Submodule ℂ MatrixSpace) (lev : ∀ m∈L,level m)
    (x : MatrixSpace) (hx : x∈L) (hr : ∀ i, ∑ j, x (i,j)=0) (hc : ∀ j, ∑ i, x (i,j)=0)
    (hy : (fun p => conj (x p))∈L) : x=0 := by
  haveI : Orders := ⟨perm1,perm2,perm3,perm4⟩
  let S := L.comap RankSeven.restr
  have mem (t : MatrixSpace) (ht : t∈L) : extM t ∈ S := by change restrict (extM t) ∈ L; rwa [resExt]
  have van := van2 S (fun m hm => lev _ hm) (mem _ hy) (mem _ hx)
  rw [centeredPair _ _ hr hc] at van
  simp only [Complex.conj_mul'] at van
  have h : ∑ i : Fin 4, ∑ j : Fin 6, ‖x (i,j)‖^2=0 := by exact_mod_cast van
  have row (i : Fin 4) : ∑ j : Fin 6, ‖x (i,j)‖^2=0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))).mp h i (Finset.mem_univ _)
  funext p; rcases p with ⟨r,j⟩
  have e := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp (row r) j (Finset.mem_univ _)
  simpa using e

abbrev Margins := (Fin 3 → ℂ) × (Fin 5 → ℂ)
noncomputable def margins : MatrixSpace →ₗ[ℂ] Margins where
  toFun x := (fun i => ∑ j, x (i.castSucc,j), fun j => ∑ i, x (i,j.castSucc))
  map_add' x y := by ext <;> simp [Finset.sum_add_distrib]
  map_smul' r x := by ext <;> simp [Finset.mul_sum]

theorem allMargins (x : MatrixSpace) (lev : level x) (h : margins x=0) :
    (∀ i, ∑ j, x (i,j)=0) ∧ (∀ j, ∑ i, x (i,j)=0) := by
  have r (i : Fin 3) : ∑ j, x (i.castSucc,j)=0 := congrFun (congrArg Prod.fst h) i
  have c (j : Fin 5) : ∑ i, x (i,j.castSucc)=0 := congrFun (congrArg Prod.snd h) j
  have total : ∑ i, ∑ j, x (i,j)=0 := lev.1
  have other : ∑ j, ∑ i, x (i,j)=0 := (Finset.sum_comm).trans total
  rw [Fin.sum_univ_castSucc] at total other
  simp only [r,c,Finset.sum_const_zero,zero_add] at total other
  exact ⟨Fin.lastCases total r, Fin.lastCases other c⟩

theorem quotientWitness (L : Submodule ℂ MatrixSpace) (lev : ∀ m∈L,level m)
    (P : Submodule ℂ L)
    (dim : 8 < finrank ℂ (L ⧸ P) + finrank ℂ (P.map (margins.domRestrict L))) :
    ∃ x : L, x∉P ∧ (∀ i, ∑ j,x.val (i,j)=0) ∧ (∀ j, ∑ i,x.val (i,j)=0) ∧
      (fun p => conj (x.val p))∉L := by
  let m := margins.domRestrict L
  have bad : ¬ LinearMap.ker m≤P := by
    intro contain
    let T := P.map m
    have lift : P ≤ T.comap m := fun x hx => ⟨x,hx,rfl⟩
    let g := P.mapQ T m lift
    have pre : T.comap m ≤ P := by
      intro x hx
      obtain ⟨z,hz,he⟩ := hx
      have hc : x-z∈LinearMap.ker m := by
        change m (x-z)=0
        rw [map_sub,he,sub_self]
      simpa using P.add_mem (contain hc) hz
    have inj : Function.Injective g := by
      apply LinearMap.ker_eq_bot.mp; apply le_antisymm _ bot_le
      rw [show LinearMap.ker g=(T.comap m).map P.mkQ from Submodule.ker_mapQ _ _ _ _]
      rintro q ⟨z,hz,rfl⟩
      exact (Submodule.Quotient.mk_eq_zero P).mpr (pre hz)
    have le := g.finrank_le_finrank_of_injective inj
    have d := T.finrank_quotient_add_finrank
    have ambient : finrank ℂ Margins=8 := by simp [Module.finrank_prod,Module.finrank_pi,Fintype.card_fin]
    rw [ambient] at d
    change 8 < finrank ℂ (L ⧸ P)+finrank ℂ T at dim
    omega
  obtain ⟨x,hx,hp⟩ := IsConcreteLE.not_le_iff_exists.mp bad
  have marg := allMargins x.val (lev _ x.property) hx
  refine ⟨x,hp,marg.1,marg.2,?_⟩
  intro hy
  have eqn := centeredNoConj L lev _ x.property marg.1 marg.2 hy
  exact hp ((show x=(0:L) from Subtype.ext eqn) ▸ P.zero_mem)
end PEqualNP.Gct.PureQuotient
