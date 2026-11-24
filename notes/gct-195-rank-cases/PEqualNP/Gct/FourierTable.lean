import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic

namespace PEqualNP.Gct.FourierTable
abbrev E := Int × Int
def plus (x y : E) : E := (x.1+y.1,x.2+y.2)
def times (x y : E) : E := (x.1*y.1-x.2*y.2,x.1*y.2+x.2*y.1-x.2*y.2)
def c (a : Int) : E := (a,0)
def wave (n : Nat) : E := match n%3 with | 0 => c 1 | 1 => (0,1) | _ => (-1,-1)

/-- Indices 0 to 14 are the quotient coordinates. Slots 15 and 16 span the saturated kernel. -/
def row (i r : Nat) : E :=
  if i=0 ∨ i=2 then c (if r=3 then 5 else -3)
  else if i=1 then c (-3)
  else if i<15 then if r=3 then c 0 else wave (if i<9 then r else 2*r)
  else c (if r=3 then -1 else 3)
def col (i j : Nat) : E :=
  if i=1 then c (if j<3 then 1 else -1)
  else
    let n := if i=0 then 2 else if i=2 then 5 else if i=15 then 1 else if i=16 then 4 else (i-3)%6
    if n/3=j/3 then wave (n%3*(j%3)) else c 0

/-- Ordered sum over injections from the given list of slots into the available indices. -/
def injectSum (weight : Nat → Nat → E) : List Nat → List Nat → E
  | [], _ => c 1
  | i::tail, available => (available.map (fun j =>
      times (weight i j) (injectSum weight tail (available.erase j)))).foldl plus (c 0)

def contraction (modes : List Nat) : E :=
  times (injectSum row modes (List.range 4)) (injectSum col modes (List.range 6))
def samePair (i j a b : Nat) : Bool := (i==a && j==b) || (i==b && j==a)
/-- Ordered slots retain the factorial for the two identical kernel inputs. -/
def expectedQ (a b i j : Nat) : Int :=
  if a=15 ∧ b=15 then if samePair i j 4 12 || samePair i j 6 10 then 324 else 0
  else if a=16 ∧ b=16 then if samePair i j 3 13 || samePair i j 7 9 then 324 else 0
  else if samePair i j 0 2 then -17496
  else if samePair i j 5 14 || samePair i j 8 11 then 162
  else 0
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sliceVars : List Nat := [1,3,7,9,13]
def expectedSecond (i j : Nat) : Int :=
  if i=1 ∧ j=1 then -648 else if samePair i j 3 9 then -18 else 0
def expectedThird (i j k : Nat) : Int :=
  if i=j ∧ j=k ∧ i≠1 then 36
  else if (i=1 ∧ samePair j k 3 9) ∨ (j=1 ∧ samePair i k 3 9) ∨ (k=1 ∧ samePair i j 3 9) then -216 else 0
theorem q_15_15_0 : ((List.range 15).all (fun j => contraction [0,j,15,15] == c (expectedQ 15 15 0 j))) = true := by decide
theorem q_15_15_1 : ((List.range 15).all (fun j => contraction [1,j,15,15] == c (expectedQ 15 15 1 j))) = true := by decide
theorem q_15_15_2 : ((List.range 15).all (fun j => contraction [2,j,15,15] == c (expectedQ 15 15 2 j))) = true := by decide
theorem q_15_15_3 : ((List.range 15).all (fun j => contraction [3,j,15,15] == c (expectedQ 15 15 3 j))) = true := by decide
theorem q_15_15_4 : ((List.range 15).all (fun j => contraction [4,j,15,15] == c (expectedQ 15 15 4 j))) = true := by decide
theorem q_15_15_5 : ((List.range 15).all (fun j => contraction [5,j,15,15] == c (expectedQ 15 15 5 j))) = true := by decide
theorem q_15_15_6 : ((List.range 15).all (fun j => contraction [6,j,15,15] == c (expectedQ 15 15 6 j))) = true := by decide
theorem q_15_15_7 : ((List.range 15).all (fun j => contraction [7,j,15,15] == c (expectedQ 15 15 7 j))) = true := by decide
theorem q_15_15_8 : ((List.range 15).all (fun j => contraction [8,j,15,15] == c (expectedQ 15 15 8 j))) = true := by decide
theorem q_15_15_9 : ((List.range 15).all (fun j => contraction [9,j,15,15] == c (expectedQ 15 15 9 j))) = true := by decide
theorem q_15_15_10 : ((List.range 15).all (fun j => contraction [10,j,15,15] == c (expectedQ 15 15 10 j))) = true := by decide
theorem q_15_15_11 : ((List.range 15).all (fun j => contraction [11,j,15,15] == c (expectedQ 15 15 11 j))) = true := by decide
theorem q_15_15_12 : ((List.range 15).all (fun j => contraction [12,j,15,15] == c (expectedQ 15 15 12 j))) = true := by decide
theorem q_15_15_13 : ((List.range 15).all (fun j => contraction [13,j,15,15] == c (expectedQ 15 15 13 j))) = true := by decide
theorem q_15_15_14 : ((List.range 15).all (fun j => contraction [14,j,15,15] == c (expectedQ 15 15 14 j))) = true := by decide
theorem q_15_16_0 : ((List.range 15).all (fun j => contraction [0,j,15,16] == c (expectedQ 15 16 0 j))) = true := by decide
theorem q_15_16_1 : ((List.range 15).all (fun j => contraction [1,j,15,16] == c (expectedQ 15 16 1 j))) = true := by decide
theorem q_15_16_2 : ((List.range 15).all (fun j => contraction [2,j,15,16] == c (expectedQ 15 16 2 j))) = true := by decide
theorem q_15_16_3 : ((List.range 15).all (fun j => contraction [3,j,15,16] == c (expectedQ 15 16 3 j))) = true := by decide
theorem q_15_16_4 : ((List.range 15).all (fun j => contraction [4,j,15,16] == c (expectedQ 15 16 4 j))) = true := by decide
theorem q_15_16_5 : ((List.range 15).all (fun j => contraction [5,j,15,16] == c (expectedQ 15 16 5 j))) = true := by decide
theorem q_15_16_6 : ((List.range 15).all (fun j => contraction [6,j,15,16] == c (expectedQ 15 16 6 j))) = true := by decide
theorem q_15_16_7 : ((List.range 15).all (fun j => contraction [7,j,15,16] == c (expectedQ 15 16 7 j))) = true := by decide
theorem q_15_16_8 : ((List.range 15).all (fun j => contraction [8,j,15,16] == c (expectedQ 15 16 8 j))) = true := by decide
theorem q_15_16_9 : ((List.range 15).all (fun j => contraction [9,j,15,16] == c (expectedQ 15 16 9 j))) = true := by decide
theorem q_15_16_10 : ((List.range 15).all (fun j => contraction [10,j,15,16] == c (expectedQ 15 16 10 j))) = true := by decide
theorem q_15_16_11 : ((List.range 15).all (fun j => contraction [11,j,15,16] == c (expectedQ 15 16 11 j))) = true := by decide
theorem q_15_16_12 : ((List.range 15).all (fun j => contraction [12,j,15,16] == c (expectedQ 15 16 12 j))) = true := by decide
theorem q_15_16_13 : ((List.range 15).all (fun j => contraction [13,j,15,16] == c (expectedQ 15 16 13 j))) = true := by decide
theorem q_15_16_14 : ((List.range 15).all (fun j => contraction [14,j,15,16] == c (expectedQ 15 16 14 j))) = true := by decide
theorem q_16_16_0 : ((List.range 15).all (fun j => contraction [0,j,16,16] == c (expectedQ 16 16 0 j))) = true := by decide
theorem q_16_16_1 : ((List.range 15).all (fun j => contraction [1,j,16,16] == c (expectedQ 16 16 1 j))) = true := by decide
theorem q_16_16_2 : ((List.range 15).all (fun j => contraction [2,j,16,16] == c (expectedQ 16 16 2 j))) = true := by decide
theorem q_16_16_3 : ((List.range 15).all (fun j => contraction [3,j,16,16] == c (expectedQ 16 16 3 j))) = true := by decide
theorem q_16_16_4 : ((List.range 15).all (fun j => contraction [4,j,16,16] == c (expectedQ 16 16 4 j))) = true := by decide
theorem q_16_16_5 : ((List.range 15).all (fun j => contraction [5,j,16,16] == c (expectedQ 16 16 5 j))) = true := by decide
theorem q_16_16_6 : ((List.range 15).all (fun j => contraction [6,j,16,16] == c (expectedQ 16 16 6 j))) = true := by decide
theorem q_16_16_7 : ((List.range 15).all (fun j => contraction [7,j,16,16] == c (expectedQ 16 16 7 j))) = true := by decide
theorem q_16_16_8 : ((List.range 15).all (fun j => contraction [8,j,16,16] == c (expectedQ 16 16 8 j))) = true := by decide
theorem q_16_16_9 : ((List.range 15).all (fun j => contraction [9,j,16,16] == c (expectedQ 16 16 9 j))) = true := by decide
theorem q_16_16_10 : ((List.range 15).all (fun j => contraction [10,j,16,16] == c (expectedQ 16 16 10 j))) = true := by decide
theorem q_16_16_11 : ((List.range 15).all (fun j => contraction [11,j,16,16] == c (expectedQ 16 16 11 j))) = true := by decide
theorem q_16_16_12 : ((List.range 15).all (fun j => contraction [12,j,16,16] == c (expectedQ 16 16 12 j))) = true := by decide
theorem q_16_16_13 : ((List.range 15).all (fun j => contraction [13,j,16,16] == c (expectedQ 16 16 13 j))) = true := by decide
theorem q_16_16_14 : ((List.range 15).all (fun j => contraction [14,j,16,16] == c (expectedQ 16 16 14 j))) = true := by decide
theorem sliceSecond : (sliceVars.all (fun i => sliceVars.all (fun j => contraction [i,j] == c (expectedSecond i j)))) = true := by decide
theorem sliceMixed : (sliceVars.all (fun i => sliceVars.all (fun j => contraction [i,j,16] == c (if samePair i j 7 13 then -36 else 0)))) = true := by decide
theorem sliceThird : (sliceVars.all (fun i => sliceVars.all (fun j => sliceVars.all (fun k => contraction [i,j,k] == c (expectedThird i j k))))) = true := by decide
end PEqualNP.Gct.FourierTable
