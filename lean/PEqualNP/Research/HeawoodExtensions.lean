import Mathlib

namespace PEqualNP.Research.Heawood

def included {n} (a b : BitVec n) := a &&& b = a
def mono {n} (f : BitVec n → Bool) := ∀ a b, included a b → f a = true → f b = true
def forced : BitVec 14 → Bool := fun x => [257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112].any (fun m : BitVec 14 => x &&& m == m)
def distinguished : BitVec 14 → Bool := fun x => x &&& 129 == (129 : BitVec 14)
def cycleEdge : BitVec 8 → Bool := fun x => [3, 6, 12, 24, 48, 96, 192, 129].any (fun m : BitVec 8 => x &&& m == m)
def expand : BitVec 8 → BitVec 14 := fun y => (129 : BitVec 14) ||| (if y.getLsbD 0 then 4 else 0) ||| (if y.getLsbD 1 then 4096 else 0) ||| (if y.getLsbD 2 then 32 else 0) ||| (if y.getLsbD 3 then 512 else 0) ||| (if y.getLsbD 4 then 64 else 0) ||| (if y.getLsbD 5 then 2048 else 0) ||| (if y.getLsbD 6 then 16 else 0) ||| (if y.getLsbD 7 then 8192 else 0)
def project : BitVec 14 → BitVec 8 := fun x => (if x.getLsbD 2 then 1 else 0) ||| (if x.getLsbD 12 then 2 else 0) ||| (if x.getLsbD 5 then 4 else 0) ||| (if x.getLsbD 9 then 8 else 0) ||| (if x.getLsbD 6 then 16 else 0) ||| (if x.getLsbD 11 then 32 else 0) ||| (if x.getLsbD 4 then 64 else 0) ||| (if x.getLsbD 13 then 128 else 0)

def large := {f : BitVec 14 → Bool // mono f ∧
  (∀ x, forced x = true → f x = true) ∧
  (∀ x, f x = true → (forced x || distinguished x) = true) ∧ f 129 = false}
def small := {q : BitVec 8 → Bool // mono q ∧ q 0 = false ∧
  ∀ x, cycleEdge x = true → q x = true}

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

private theorem atBit {a b : BitVec n} (h : included a b) (i : Nat) :
    (a.getLsbD i && b.getLsbD i) = a.getLsbD i := by
  simpa only [BitVec.getLsbD_and] using congrArg (fun x : BitVec n => x.getLsbD i) h

private theorem join {a b c d : BitVec n} (hab : included a b) (hcd : included c d) :
    included (a ||| c) (b ||| d) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  have h1 := atBit hab i
  have h2 := atBit hcd i
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and]
  cases ea : a.getLsbD i <;> cases eb : b.getLsbD i <;> cases ec : c.getLsbD i <;>
    cases ed : d.getLsbD i <;> simp_all only [ea,eb,ec,ed,Bool.and_true,Bool.and_false,Bool.true_and,Bool.false_and,Bool.or_true,Bool.or_false,Bool.true_or,Bool.false_or,Bool.false_eq_true]

private theorem bitMono {a b : BitVec n} (h : included a b) (i : Nat) (v : BitVec m) :
    included (if a.getLsbD i then v else 0) (if b.getLsbD i then v else 0) := by
  have hi := atBit h i
  cases ea : a.getLsbD i <;> cases eb : b.getLsbD i <;> simp_all [included]

private theorem expMono (a b : BitVec 8) (h : included a b) : included (expand a) (expand b) := by
  unfold expand
  repeat' first | apply join | exact bitMono h _ _ | simp [included]

private theorem prMono (a b : BitVec 14) (h : included a b) : included (project a) (project b) := by
  unfold project
  repeat' first | apply join | exact bitMono h _ _

private theorem maskMono {a b m : BitVec n} (h : included a b) (ha : a &&& m = m) :
    b &&& m = m := by
  calc b &&& m = b &&& (a &&& m) := congrArg _ ha.symm
       _ = (a &&& b) &&& m := by ac_rfl
       _ = m := by rw [show a &&& b = a from h, ha]

private theorem forcedMono : mono forced := by
  intro a b h f
  simp only [forced, List.any_eq_true, beq_iff_eq] at f ⊢
  obtain ⟨m,hm,v⟩ := f
  exact ⟨m,hm,maskMono h v⟩

private theorem distinguishedMono : mono distinguished := by
  intro a b h f
  simp only [distinguished, beq_iff_eq] at f ⊢
  exact maskMono h f

private theorem edgeExpand (y : BitVec 8) : forced (expand y) = cycleEdge y := by
  revert y
  decide +kernel

private theorem roundtrip (y : BitVec 8) : project (expand y) = y := by
  revert y
  decide +kernel

private theorem freeRoundtrip (x : BitVec 14) (hf : forced x = false) (hh : distinguished x = true) :
    expand (project x) = x := by
  revert x
  decide +kernel


def restrict (f : large) : small := by
  refine ⟨fun y => f.val (expand y), ?_, ?_, ?_⟩
  · intro a b h
    exact f.property.1 _ _ (expMono _ _ h)
  · exact f.property.2.2.2
  · intro x hx
    exact f.property.2.1 _ ((edgeExpand x).trans hx)

def extend (q : small) : large := by
  refine ⟨fun x => forced x || (distinguished x && q.val (project x)), ?_, ?_, ?_, ?_⟩
  · intro a b h ha
    simp only [Bool.or_eq_true, Bool.and_eq_true] at ha ⊢
    rcases ha with ha | ⟨hd,hq⟩
    · exact Or.inl (forcedMono a b h ha)
    · exact Or.inr ⟨distinguishedMono a b h hd, q.property.1 _ _ (prMono a b h) hq⟩
  · intro x hx
    simp [hx]
  · intro x hx
    simp only [Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
    exact hx.imp_right And.left
  · change (false || (true && q.val 0)) = false
    exact q.property.2.1

def classification : large ≃ small where
  toFun := restrict
  invFun := extend
  left_inv f := by
    apply Subtype.ext
    funext x
    change (forced x || (distinguished x && f.val (expand (project x)))) = f.val x
    cases hf : forced x
    · cases hh : distinguished x
      · have upper := f.property.2.2.1 x
        cases hv : f.val x
        · rfl
        · simpa [hf,hh] using upper hv
      · simp [freeRoundtrip x hf hh]
    · simp [f.property.2.1 x hf]
  right_inv q := by
    apply Subtype.ext
    funext y
    change (forced (expand y) || (distinguished (expand y) && q.val (project (expand y)))) = q.val y
    have hd : distinguished (expand y) = true := by
      revert y
      decide +kernel
    rw [edgeExpand, hd, roundtrip]
    cases hc : cycleEdge y
    · simp
    · simp [q.property.2.2 y hc]

end PEqualNP.Research.Heawood

theorem PEqualNP.Research.HeawoodExtensions :
    ∃ e : PEqualNP.Research.Heawood.large ≃ PEqualNP.Research.Heawood.small,
       ∀ f y, (e f).val y = f.val (PEqualNP.Research.Heawood.expand y) :=
  ⟨PEqualNP.Research.Heawood.classification, fun _ _ => rfl⟩
#print axioms PEqualNP.Research.HeawoodExtensions

