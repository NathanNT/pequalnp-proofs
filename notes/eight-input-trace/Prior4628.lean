import PEqualNP.Outside.L_meta_3676

namespace PEqualNP.Research.Prior4628
open PEqualNP.Outside.L_meta_3676

def renameVertex (i : Fin 8) : Fin 8 := ![4,0,1,6,7,3,5,2] i
def input (r : Row) (i : Fin 8) : Bool := up r (renameVertex i)

def graph (x : Fin 8 → Bool) : Bool :=
  [1,12,23,5,16,27,46,57,47].any fun e : Nat =>
    x (Fin.ofNat 8 (e / 10)) && x (Fin.ofNat 8 (e % 10))

theorem sameGraph : ∀ r : Row, graph (input r) = f8 (up r) := by decide +kernel

private theorem signed {B : Set Wire} {v : Wire} (h : Av B v) (s : Bool) :
    Av B (fun r => v r ^^ s) := by
  cases s
  · simpa using h
  · simpa using av_not h

private def Step (G : Nat → Wire) (S : Finset Nat) (i : Nat) : Prop :=
  (∃ c : Bool, G i = fun _ => c) ∨
  (∃ p : Fin 8, ∃ s : Bool, G i = fun r => input r p ^^ s) ∨
  (∃ j < i, ∃ s : Bool, G i = fun r => G j r ^^ s) ∨
  i ∈ S ∧ ∃ j < i, ∃ k < i, ∃ a b d : Bool, G i =
    fun r => if d then (G j r ^^ a) && (G k r ^^ b) else (G j r ^^ a) || (G k r ^^ b)

private theorem compile (G : Nat → Wire) (S : Finset Nat) (out : Nat)
    (steps : ∀ i ≤ out, Step G S i) (fuel i : Nat) (stop : out < i + fuel)
    (B : Set Wire) (inputs : ∀ p, Av B (fun r => input r p))
    (prev : ∀ j < i, Av B (G j)) (rest : Finset Nat)
    (budget : ∀ j ∈ S, i ≤ j → j ∈ rest) : Comp rest.card B (G out) := by
  induction fuel generalizing i B rest with
  | zero =>
    exact comp_le (Nat.zero_le _) (show Comp 0 B (G out) from prev out (by omega))
  | succ fuel ih =>
    by_cases done_ : out < i
    · exact comp_le (Nat.zero_le _) (show Comp 0 B (G out) from prev out done_)
    have next (h : Av B (G i)) : Comp rest.card B (G out) := by
      apply ih (i+1) (by omega) B inputs (fun j hj => ?_) rest
        (fun j hj hle => budget j hj (by omega))
      by_cases eq : j = i
      · exact eq ▸ h
      · exact prev j (by omega)
    rcases steps i (by omega) with ⟨c,he⟩ | ⟨p,s,he⟩ | ⟨j,hj,s,he⟩ |
      ⟨hm,j,hj,k,hk,a,b,d,he⟩
    · exact next (he ▸ av_cst c)
    · exact next (he ▸ signed (inputs p) s)
    · exact next (he ▸ signed (prev j hj) s)
    · have mem := budget i hm (le_refl _)
      rw [← Finset.card_erase_add_one mem]
      apply comp_gate (d := if d then 0 else 1) (by cases d <;> decide)
        (signed (prev j hj) a) (signed (prev k hk) b)
      apply ih (i+1) (by omega) _ (fun p => av_insert (inputs p))
        (fun v hv => ?_) (rest.erase i)
        (fun v hv hle => Finset.mem_erase.mpr ⟨by omega,budget v hv (by omega)⟩)
      by_cases eq : v = i
      · subst v
        apply av_mem
        apply Or.inl
        rw [he]
        cases d <;> rfl
      · exact av_insert (prev v (by omega))



theorem _root_.PEqualNP.Research.Prior4628 : ∀ (x1 : ℕ → (Fin (8 : ℕ) → Bool) → Bool) (x2 : Finset ℕ), x2.card ≤ (11 : ℕ) → (∀ x4 < (23 : ℕ), (∃ (x6 : Bool), ∀ (x7 : Fin (8 : ℕ) → Bool), x1 x4 x7 = x6) ∨ (∃ (x6 : Fin (8 : ℕ)) (x7 : Bool), ∀ (x8 : Fin (8 : ℕ) → Bool), x1 x4 x8 = (x8 x6 ^^ x7)) ∨ (∃ x6 < x4, ∃ (x7 : Bool), ∀ (x8 : Fin (8 : ℕ) → Bool), x1 x4 x8 = (x1 x6 x8 ^^ x7)) ∨ x4 ∈ x2 ∧ ∃ x6 < x4, ∃ x7 < x4, ∃ (x8 : Bool) (x9 : Bool) (x10 : Bool), ∀ (x11 : Fin (8 : ℕ) → Bool), x1 x4 x11 = if x10 = Bool.true then (x1 x6 x11 ^^ x8) && (x1 x7 x11 ^^ x9) else x1 x6 x11 ^^ x8 || x1 x7 x11 ^^ x9) → ∀ x5 < (23 : ℕ), ∃ (x7 : Fin (8 : ℕ) → Bool), x1 x5 x7 ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (46 : ℕ), (57 : ℕ), (47 : ℕ)].any fun (x8 : ℕ) => x7 (Fin.ofNat (8 : ℕ) (x8 / (10 : ℕ))) && x7 (Fin.ofNat (8 : ℕ) (x8 % (10 : ℕ))) := by
  intro F S sz rows out bound
  by_contra! same
  let G (i : Nat) (r : Row) := F i (input r)
  have steps (i : Nat) (hi : i ≤ out) : Step G S i := by
    rcases rows i (by omega) with ⟨c,h⟩ | ⟨p,s,h⟩ | ⟨j,hj,s,h⟩ |
      ⟨hm,j,hj,k,hk,a,b,d,h⟩
    · exact Or.inl ⟨c,funext fun r => h (input r)⟩
    · exact Or.inr (Or.inl ⟨p,s,funext fun r => h (input r)⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨j,hj,s,funext fun r => h (input r)⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hm,j,hj,k,hk,a,b,d,funext fun r => h (input r)⟩))
  have hc := compile G S out steps (out+1) 0 (by omega) Inp
    (fun p => av_mem (Set.mem_range_self (renameVertex p).castSucc))
    (fun _ h => by omega) S (fun _ h _ => h)
  have eq : G out = gr 255 [] := funext fun r =>
    (same (input r)).trans ((sameGraph r).trans (f_eq r))
  rw [eq] at hc
  have lb := low255 S.card hc
  omega

#print axioms PEqualNP.Research.Prior4628
end PEqualNP.Research.Prior4628
