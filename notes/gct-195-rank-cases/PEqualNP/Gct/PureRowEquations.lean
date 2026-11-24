import PEqualNP.Gct.PureTests
namespace PEqualNP.Gct.PureRows
open Module DeskPolar FourierTable PermanentPencil
local instance : Orders := ⟨perm1,perm2,perm3,perm4⟩
noncomputable abbrev pureSpace (L : Submodule ℂ (Pos → ℂ)) (i : Fin 4) := L.comap (single i)
private theorem nz0 : ∀ i : Fin 4, iz [i.val+1] (List.range 4)≠0 := by decide
private theorem nz1 : ∀ i : Fin 4, iz [i.val+1,0] (List.range 4)≠0 := by decide
private theorem nz2 : ∀ i : Fin 4, iz [i.val+1,0,0] (List.range 4)≠0 := by decide
private theorem nz3 : ∀ i : Fin 4, iz [i.val+1,0,0,0] (List.range 4)≠0 := by decide
private theorem nzPair : ∀ i j : Fin 4, i≠j → iz [i.val+1,j.val+1] (List.range 4)≠0 := by decide
private theorem nzQuart : ∀ i j : Fin 4, i≠j → iz [i.val+1,j.val+1,0,0] (List.range 4)≠0 := by decide
set_option maxHeartbeats 2000000 in
theorem rowMoments (L : Submodule ℂ (Pos → ℂ)) (lev : ∀ m∈L,level m)
    (f : Row) (hf : RankSeven.profile f∈L) (i : Fin 4) (y : Row) (hy : y∈pureSpace L i) :
    ∀ k : Fin 4, weighted y f k.val=0 := by
  let S := L.comap RankSeven.restr
  have sl (m : Mat) (hm : m∈S) := lev _ hm
  have ha : dir 0 f∈S := by change restrict (dir 0 f)∈L; rwa [profileDir]
  have hb : dir (i.val+1) y∈S := by change restrict (dir (i.val+1) y)∈L; rw [singleDir]; exact hy
  have z0 := test [(i.val+1,y)] (nz0 i) (van1 S sl hb)
  change inj [lift y] _=0 at z0
  rw [single0 (f:=f) y] at z0
  have e0 : weighted y f 0=0 := by
    linear_combination z0
  have z1 := test [(i.val+1,y),(0,f)] (nz1 i) (van2 S sl hb ha)
  change inj [lift y,lift f] _=0 at z1
  rw [single1] at z1
  have e1 : weighted y f 1=0 := by
    simp only [e0,mul_zero,zero_mul,zero_add,add_zero] at z1
    linear_combination -z1
  have z2 := test [(i.val+1,y),(0,f),(0,f)] (nz2 i) (van3 S sl hb ha ha)
  change inj [lift y,lift f,lift f] _=0 at z2
  rw [single2] at z2
  have e2 : weighted y f 2=0 := by
    simp only [e0,e1,mul_zero,zero_mul,zero_add,add_zero] at z2
    linear_combination z2 / 2
  have z3 := test [(i.val+1,y),(0,f),(0,f),(0,f)] (nz3 i) (van4 S sl hb ha ha ha)
  change inj [lift y,lift f,lift f,lift f] _=0 at z3
  rw [single3] at z3
  have e3 : weighted y f 3=0 := by
    simp only [e0,e1,e2,mul_zero,zero_mul,zero_add,add_zero] at z3
    linear_combination -z3 / 6
  intro k; fin_cases k <;> assumption

theorem distinctOrth (L : Submodule ℂ (Pos → ℂ)) (lev : ∀ m∈L,level m)
    (i j : Fin 4) (hij : i≠j) (x y : Row) (hx : x∈pureSpace L i) (hy : y∈pureSpace L j) :
    x ⬝ᵥ y=0 := by
  let S := L.comap RankSeven.restr
  have sl (m : Mat) (hm : m∈S) := lev _ hm
  have hx' : dir (i.val+1) x∈S := by change restrict (dir (i.val+1) x)∈L; rw [singleDir]; exact hx
  have hy' : dir (j.val+1) y∈S := by change restrict (dir (j.val+1) y)∈L; rw [singleDir]; exact hy
  have e := test [(i.val+1,x),(j.val+1,y)] (nzPair i j hij) (van2 S sl hx' hy')
  have z := test [(i.val+1,x)] (nz0 i) (van1 S sl hx')
  change inj [lift x] _=0 at z
  rw [single0 (f:=x) x] at z
  have sz : ∑ k,x k=0 := by simpa [weighted] using z
  change inj [lift x,lift y] _=0 at e
  rw [pair2,sz] at e
  change ∑ k, x k*y k=0
  linear_combination -e

theorem quarticObstruction (L : Submodule ℂ (Pos → ℂ)) (lev : ∀ m∈L,level m)
    (f : Row) (hf : RankSeven.profile f∈L) (i j : Fin 4) (hij : i≠j)
    (hi : (fun k => f k^2)∈pureSpace L i) (hj : (fun k => f k^2)∈pureSpace L j)
    (h : ∀ k : Fin 5, moment f (k.val+1)=0) : moment f 6=0 := by
  let S := L.comap RankSeven.restr
  have sl (m : Mat) (hm : m∈S) := lev _ hm
  have ha : dir 0 f∈S := by change restrict (dir 0 f)∈L; rwa [profileDir]
  let g : Row := fun k => f k^2
  have hi' : dir (i.val+1) g∈S := by change restrict (dir (i.val+1) g)∈L; rw [singleDir]; exact hi
  have hj' : dir (j.val+1) g∈S := by change restrict (dir (j.val+1) g)∈L; rw [singleDir]; exact hj
  have z := test [(i.val+1,g),(j.val+1,g),(0,f),(0,f)] (nzQuart i j hij)
    (van4 S sl hi' hj' ha ha)
  change inj [lift g,lift g,lift f,lift f] _=0 at z
  rw [final4] at z
  have h1 : moment f 1=0 := h 0
  have h2 : moment f 2=0 := h 1
  have h3 : moment f 3=0 := h 2
  have h4 : moment f 4=0 := h 3
  have h5 : moment f 5=0 := h 4
  simp only [h1,h2,h3,h4,h5,zero_mul,mul_zero,zero_add,add_zero] at z
  linear_combination -z / 6
end PEqualNP.Gct.PureRows
