import PEqualNP.Gct.DeskAlgebra
namespace PEqualNP.Gct.DeskPolar
open FourierTable PermanentPencil
class Orders : Prop where
  p1 : (words 1 (List.range 4) (List.range 6)).Perm ((desk 1).flatMap permutationsOf)
  p2 : (words 2 (List.range 4) (List.range 6)).Perm ((desk 2).flatMap permutationsOf)
  p3 : (words 3 (List.range 4) (List.range 6)).Perm ((desk 3).flatMap permutationsOf)
  p4 : (words 4 (List.range 4) (List.range 6)).Perm ((desk 4).flatMap permutationsOf)
theorem van1 [Orders] (S : Submodule ℂ Mat) (lev : ∀ m∈S, level (restrict m)) {x : Mat} (hx : x∈S) : mixed [x]=0 :=
  conditional1 Orders.p1 S lev hx
theorem van2 [Orders] (S : Submodule ℂ Mat) (lev : ∀ m∈S, level (restrict m)) {x y : Mat} (hx : x∈S) (hy : y∈S) : mixed [x,y]=0 :=
  conditional2 Orders.p2 S lev hx hy
theorem van3 [Orders] (S : Submodule ℂ Mat) (lev : ∀ m∈S, level (restrict m)) {x y z : Mat} (hx : x∈S) (hy : y∈S) (hz : z∈S) : mixed [x,y,z]=0 :=
  conditional3 Orders.p3 S lev hx hy hz
theorem van4 [Orders] (S : Submodule ℂ Mat) (lev : ∀ m∈S, level (restrict m)) {x y z u : Mat} (hx : x∈S) (hy : y∈S) (hz : z∈S) (hu : u∈S) : mixed [x,y,z,u]=0 :=
  conditional4 Orders.p4 S lev hx hy hz hu
end PEqualNP.Gct.DeskPolar
