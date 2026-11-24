import PEqualNP.Gct.PureContractions
namespace PEqualNP.Gct.PureRows
open Module FourierTable DeskPolar PermanentPencil
def vec (n : ℕ) (j : Nat) : ℤ :=
  if n=0 then (if j=3 then -1 else 3) else (if j+1=n then 1 else 0)
def iz : List Nat → List Nat → ℤ
  | [], _ => 1
  | n::ns, l => (l.map fun j => vec n j * iz ns (l.erase j)).sum
noncomputable def rv (n : Nat) : Fn := fun j => (vec n j : ℂ)
theorem castRows (ns l : List Nat) : inj (ns.map rv) l=(iz ns l : ℂ) := by
  induction ns generalizing l with
  | nil => simp [inj,iz]
  | cons n ns ih => simp [inj,iz,total,ih,rv,Int.cast_list_sum,List.map_map,Function.comp_def]
def lift (y : Row) (j : Nat) := y (Fin.ofNat 6 j)
noncomputable def dir (n : Nat) (y : Row) := tensor (rv n,lift y)
noncomputable def single (i : Fin 4) : Row →ₗ[ℂ] (Pos → ℂ) where
  toFun y p := if p.1=i then y p.2 else 0
  map_add' a b := by funext p; by_cases h : p.1=i <;> simp [h]
  map_smul' a b := by funext p; by_cases h : p.1=i <;> simp [h]
theorem singleDir (i : Fin 4) (y : Row) : restrict (dir (i.val+1) y)=single i y := by
  funext p; rcases p with ⟨r,j⟩
  change ((vec (i.val+1) r.val : ℤ) : ℂ)*y (Fin.ofNat 6 j.val)= if r=i then y j else 0
  have hj : Fin.ofNat 6 j.val=j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
  rw [hj]; by_cases h : r=i
  · subst r; simp [vec]
  · have hn : r.val≠i.val := fun e => h (Fin.ext e)
    simp [vec,h,hn]
theorem profileDir (y : Row) : restrict (dir 0 y)=RankSeven.profile y := by
  funext p; rcases p with ⟨r,j⟩
  fin_cases r <;> simp [restrict,dir,tensor,rv,vec,lift,RankSeven.profile]
theorem test (p : List (Nat × Row)) (nr : iz (p.map Prod.fst) (List.range 4)≠0)
    (zero : mixed (p.map fun s => dir s.1 s.2)=0) :
    inj (p.map fun s => lift s.2) (List.range 6)=0 := by
  have sep := separate (p.map fun s => (rv s.1,lift s.2)) (List.range 4) (List.range 6)
  simp only [List.map_map,Function.comp_def] at sep
  change rect _ _ _=0 at zero
  rw [show inj (p.map fun s => rv s.1) (List.range 4)=_ from
    (by simpa [List.map_map,Function.comp_def] using castRows (p.map Prod.fst) (List.range 4))] at sep
  exact (mul_eq_zero.mp (sep.symm.trans zero)).resolve_left (by exact_mod_cast nr)
theorem sumLift (y : Row) : total (List.range 6) (lift y)=∑ j,y j := by
  simp [total,lift,Fin.sum_univ_succ,List.range_succ] <;> ring <;> rfl
noncomputable def moment (f : Row) (k : ℕ) := ∑ j, f j ^ k
noncomputable def weighted (y f : Row) (k : ℕ) := ∑ j, y j * f j ^ k

theorem single0 (y : Row) :
    inj [lift y] (List.range 6) =
      (1 : ℂ) * (weighted y f 0) := by
  rw [formula1]
  have h0 : total (List.range 6) (fun j => lift y j) = (weighted y f 0) := by
    rw [show total (List.range 6) (fun j => lift y j) = total (List.range 6) (lift (fun j => y j)) from rfl, sumLift]
    unfold weighted; apply Finset.sum_congr rfl; intro j _; ring
  rw [h0] <;> ring

theorem single1 (y f : Row) :
    inj [lift y,lift f] (List.range 6) =
      (1 : ℂ) * (weighted y f 0) * (moment f 1) +
      (-1 : ℂ) * (weighted y f 1) := by
  rw [formula2]
  have h0 : total (List.range 6) (fun j => lift y j) = (weighted y f 0) := by
    rw [show total (List.range 6) (fun j => lift y j) = total (List.range 6) (lift (fun j => y j)) from rfl, sumLift]
    unfold weighted; apply Finset.sum_congr rfl; intro j _; ring
  have h1 : total (List.range 6) (fun j => lift f j) = (moment f 1) := by
    rw [show total (List.range 6) (fun j => lift f j) = total (List.range 6) (lift (fun j => f j)) from rfl, sumLift]
    unfold moment; apply Finset.sum_congr rfl; intro j _; ring
  have h2 : total (List.range 6) (fun j => lift y j * lift f j) = (weighted y f 1) := by
    rw [show total (List.range 6) (fun j => lift y j * lift f j) = total (List.range 6) (lift (fun j => y j * f j)) from rfl, sumLift]
    unfold weighted; apply Finset.sum_congr rfl; intro j _; ring
  rw [h0,h1,h2] <;> ring

theorem single2 (y f : Row) :
    inj [lift y,lift f,lift f] (List.range 6) =
      (1 : ℂ) * (weighted y f 0) * (moment f 1) * (moment f 1) +
      (-1 : ℂ) * (weighted y f 1) * (moment f 1) +
      (-1 : ℂ) * (moment f 1) * (weighted y f 1) +
      (-1 : ℂ) * (weighted y f 0) * (moment f 2) +
      (2 : ℂ) * (weighted y f 2) := by
  rw [formula3]
  have h0 : total (List.range 6) (fun j => lift y j) = (weighted y f 0) := by
    rw [show total (List.range 6) (fun j => lift y j) = total (List.range 6) (lift (fun j => y j)) from rfl, sumLift]
    unfold weighted; apply Finset.sum_congr rfl; intro j _; ring
  have h1 : total (List.range 6) (fun j => lift f j) = (moment f 1) := by
    rw [show total (List.range 6) (fun j => lift f j) = total (List.range 6) (lift (fun j => f j)) from rfl, sumLift]
    unfold moment; apply Finset.sum_congr rfl; intro j _; ring
  have h2 : total (List.range 6) (fun j => lift y j * lift f j) = (weighted y f 1) := by
    rw [show total (List.range 6) (fun j => lift y j * lift f j) = total (List.range 6) (lift (fun j => y j * f j)) from rfl, sumLift]
    unfold weighted; apply Finset.sum_congr rfl; intro j _; ring
  have h3 : total (List.range 6) (fun j => lift f j * lift f j) = (moment f 2) := by
    rw [show total (List.range 6) (fun j => lift f j * lift f j) = total (List.range 6) (lift (fun j => f j * f j)) from rfl, sumLift]
    unfold moment; apply Finset.sum_congr rfl; intro j _; ring
  have h4 : total (List.range 6) (fun j => lift y j * lift f j * lift f j) = (weighted y f 2) := by
    rw [show total (List.range 6) (fun j => lift y j * lift f j * lift f j) = total (List.range 6) (lift (fun j => y j * f j * f j)) from rfl, sumLift]
    unfold weighted; apply Finset.sum_congr rfl; intro j _; ring
  rw [h0,h1,h2,h3,h4] <;> ring

theorem single3 (y f : Row) :
    inj [lift y,lift f,lift f,lift f] (List.range 6) =
      (1 : ℂ) * (weighted y f 0) * (moment f 1) * (moment f 1) * (moment f 1) +
      (-1 : ℂ) * (weighted y f 1) * (moment f 1) * (moment f 1) +
      (-1 : ℂ) * (moment f 1) * (weighted y f 1) * (moment f 1) +
      (-1 : ℂ) * (moment f 1) * (moment f 1) * (weighted y f 1) +
      (-1 : ℂ) * (weighted y f 0) * (moment f 2) * (moment f 1) +
      (2 : ℂ) * (weighted y f 2) * (moment f 1) +
      (1 : ℂ) * (moment f 2) * (weighted y f 1) +
      (-1 : ℂ) * (weighted y f 0) * (moment f 1) * (moment f 2) +
      (1 : ℂ) * (weighted y f 1) * (moment f 2) +
      (2 : ℂ) * (moment f 1) * (weighted y f 2) +
      (-1 : ℂ) * (weighted y f 0) * (moment f 1) * (moment f 2) +
      (1 : ℂ) * (weighted y f 1) * (moment f 2) +
      (2 : ℂ) * (moment f 1) * (weighted y f 2) +
      (2 : ℂ) * (weighted y f 0) * (moment f 3) +
      (-6 : ℂ) * (weighted y f 3) := by
  rw [formula4]
  have h0 : total (List.range 6) (fun j => lift y j) = (weighted y f 0) := by
    rw [show total (List.range 6) (fun j => lift y j) = total (List.range 6) (lift (fun j => y j)) from rfl, sumLift]
    unfold weighted; apply Finset.sum_congr rfl; intro j _; ring
  have h1 : total (List.range 6) (fun j => lift f j) = (moment f 1) := by
    rw [show total (List.range 6) (fun j => lift f j) = total (List.range 6) (lift (fun j => f j)) from rfl, sumLift]
    unfold moment; apply Finset.sum_congr rfl; intro j _; ring
  have h2 : total (List.range 6) (fun j => lift y j * lift f j) = (weighted y f 1) := by
    rw [show total (List.range 6) (fun j => lift y j * lift f j) = total (List.range 6) (lift (fun j => y j * f j)) from rfl, sumLift]
    unfold weighted; apply Finset.sum_congr rfl; intro j _; ring
  have h3 : total (List.range 6) (fun j => lift f j * lift f j) = (moment f 2) := by
    rw [show total (List.range 6) (fun j => lift f j * lift f j) = total (List.range 6) (lift (fun j => f j * f j)) from rfl, sumLift]
    unfold moment; apply Finset.sum_congr rfl; intro j _; ring
  have h4 : total (List.range 6) (fun j => lift y j * lift f j * lift f j) = (weighted y f 2) := by
    rw [show total (List.range 6) (fun j => lift y j * lift f j * lift f j) = total (List.range 6) (lift (fun j => y j * f j * f j)) from rfl, sumLift]
    unfold weighted; apply Finset.sum_congr rfl; intro j _; ring
  have h5 : total (List.range 6) (fun j => lift f j * lift f j * lift f j) = (moment f 3) := by
    rw [show total (List.range 6) (fun j => lift f j * lift f j * lift f j) = total (List.range 6) (lift (fun j => f j * f j * f j)) from rfl, sumLift]
    unfold moment; apply Finset.sum_congr rfl; intro j _; ring
  have h6 : total (List.range 6) (fun j => lift y j * lift f j * lift f j * lift f j) = (weighted y f 3) := by
    rw [show total (List.range 6) (fun j => lift y j * lift f j * lift f j * lift f j) = total (List.range 6) (lift (fun j => y j * f j * f j * f j)) from rfl, sumLift]
    unfold weighted; apply Finset.sum_congr rfl; intro j _; ring
  rw [h0,h1,h2,h3,h4,h5,h6] <;> ring

theorem pair2 (x y : Row) :
    inj [lift x,lift y] (List.range 6) =
      (1 : ℂ) * (∑ j, x j) * (∑ j, y j) +
      (-1 : ℂ) * (∑ j, x j * y j) := by
  rw [formula2]
  have h0 : total (List.range 6) (fun j => lift x j) = (∑ j, x j) := by
    rw [show total (List.range 6) (fun j => lift x j) = total (List.range 6) (lift (fun j => x j)) from rfl, sumLift]
  have h1 : total (List.range 6) (fun j => lift y j) = (∑ j, y j) := by
    rw [show total (List.range 6) (fun j => lift y j) = total (List.range 6) (lift (fun j => y j)) from rfl, sumLift]
  have h2 : total (List.range 6) (fun j => lift x j * lift y j) = (∑ j, x j * y j) := by
    rw [show total (List.range 6) (fun j => lift x j * lift y j) = total (List.range 6) (lift (fun j => x j * y j)) from rfl, sumLift]
  rw [h0,h1,h2] <;> ring

theorem final4 (f : Row) :
    inj [lift (fun j => f j ^ 2),lift (fun j => f j ^ 2),lift f,lift f] (List.range 6) =
      (1 : ℂ) * (moment f 2) * (moment f 2) * (moment f 1) * (moment f 1) +
      (-1 : ℂ) * (moment f 4) * (moment f 1) * (moment f 1) +
      (-1 : ℂ) * (moment f 2) * (moment f 3) * (moment f 1) +
      (-1 : ℂ) * (moment f 2) * (moment f 1) * (moment f 3) +
      (-1 : ℂ) * (moment f 2) * (moment f 3) * (moment f 1) +
      (2 : ℂ) * (moment f 5) * (moment f 1) +
      (1 : ℂ) * (moment f 3) * (moment f 3) +
      (-1 : ℂ) * (moment f 2) * (moment f 1) * (moment f 3) +
      (1 : ℂ) * (moment f 3) * (moment f 3) +
      (2 : ℂ) * (moment f 1) * (moment f 5) +
      (-1 : ℂ) * (moment f 2) * (moment f 2) * (moment f 2) +
      (1 : ℂ) * (moment f 4) * (moment f 2) +
      (2 : ℂ) * (moment f 2) * (moment f 4) +
      (2 : ℂ) * (moment f 2) * (moment f 4) +
      (-6 : ℂ) * (moment f 6) := by
  rw [formula4]
  have h0 : total (List.range 6) (fun j => lift (fun j => f j ^ 2) j) = (moment f 2) := by
    rw [show total (List.range 6) (fun j => lift (fun j => f j ^ 2) j) = total (List.range 6) (lift (fun j => (f j ^ 2))) from rfl, sumLift]
    unfold moment; apply Finset.sum_congr rfl; intro j _; ring
  have h1 : total (List.range 6) (fun j => lift f j) = (moment f 1) := by
    rw [show total (List.range 6) (fun j => lift f j) = total (List.range 6) (lift (fun j => f j)) from rfl, sumLift]
    unfold moment; apply Finset.sum_congr rfl; intro j _; ring
  have h2 : total (List.range 6) (fun j => lift (fun j => f j ^ 2) j * lift (fun j => f j ^ 2) j) = (moment f 4) := by
    rw [show total (List.range 6) (fun j => lift (fun j => f j ^ 2) j * lift (fun j => f j ^ 2) j) = total (List.range 6) (lift (fun j => (f j ^ 2) * (f j ^ 2))) from rfl, sumLift]
    unfold moment; apply Finset.sum_congr rfl; intro j _; ring
  have h3 : total (List.range 6) (fun j => lift (fun j => f j ^ 2) j * lift f j) = (moment f 3) := by
    rw [show total (List.range 6) (fun j => lift (fun j => f j ^ 2) j * lift f j) = total (List.range 6) (lift (fun j => (f j ^ 2) * f j)) from rfl, sumLift]
    unfold moment; apply Finset.sum_congr rfl; intro j _; ring
  have h4 : total (List.range 6) (fun j => lift (fun j => f j ^ 2) j * lift (fun j => f j ^ 2) j * lift f j) = (moment f 5) := by
    rw [show total (List.range 6) (fun j => lift (fun j => f j ^ 2) j * lift (fun j => f j ^ 2) j * lift f j) = total (List.range 6) (lift (fun j => (f j ^ 2) * (f j ^ 2) * f j)) from rfl, sumLift]
    unfold moment; apply Finset.sum_congr rfl; intro j _; ring
  have h5 : total (List.range 6) (fun j => lift f j * lift f j) = (moment f 2) := by
    rw [show total (List.range 6) (fun j => lift f j * lift f j) = total (List.range 6) (lift (fun j => f j * f j)) from rfl, sumLift]
    unfold moment; apply Finset.sum_congr rfl; intro j _; ring
  have h6 : total (List.range 6) (fun j => lift (fun j => f j ^ 2) j * lift f j * lift f j) = (moment f 4) := by
    rw [show total (List.range 6) (fun j => lift (fun j => f j ^ 2) j * lift f j * lift f j) = total (List.range 6) (lift (fun j => (f j ^ 2) * f j * f j)) from rfl, sumLift]
    unfold moment; apply Finset.sum_congr rfl; intro j _; ring
  have h7 : total (List.range 6) (fun j => lift (fun j => f j ^ 2) j * lift (fun j => f j ^ 2) j * lift f j * lift f j) = (moment f 6) := by
    rw [show total (List.range 6) (fun j => lift (fun j => f j ^ 2) j * lift (fun j => f j ^ 2) j * lift f j * lift f j) = total (List.range 6) (lift (fun j => (f j ^ 2) * (f j ^ 2) * f j * f j)) from rfl, sumLift]
    unfold moment; apply Finset.sum_congr rfl; intro j _; ring
  rw [h0,h1,h2,h3,h4,h5,h6,h7] <;> ring

end PEqualNP.Gct.PureRows
