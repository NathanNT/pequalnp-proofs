import PEqualNP.Gct.FourierTable
import PEqualNP.Gct.FourSixBound

open Module
namespace PEqualNP.Gct.FourierTable

def val (w : ℂ) (a : E) : ℂ := a.1+a.2*w
@[simp] theorem val_c (w : ℂ) (n : ℤ) : val w (c n)=(n : ℂ) := by simp [val,c]
noncomputable def integrate (x : Fin 15 → ℂ) (f : Fin 15 → ℂ) : ℂ := ∑ i, x i*f i
noncomputable def bil (w : ℂ) (x : Fin 15 → ℂ) (seed : List Nat) : ℂ :=
  integrate x (fun i => integrate x (fun j => val w (contraction (i.val :: j.val :: seed))))
noncomputable def cub (w : ℂ) (x : Fin 15 → ℂ) : ℂ :=
  integrate x (fun i => integrate x (fun j => integrate x (fun k => val w (contraction [i.val,j.val,k.val]))))

private lemma table_15_15 (i j : Fin 15) : contraction [i.val,j.val,15,15]=c (expectedQ 15 15 i.val j.val) := by
  have hi : ((List.range 15).all fun n => contraction [i.val,n,15,15] == c (expectedQ 15 15 i.val n))=true := by
    fin_cases i
    · exact q_15_15_0
    · exact q_15_15_1
    · exact q_15_15_2
    · exact q_15_15_3
    · exact q_15_15_4
    · exact q_15_15_5
    · exact q_15_15_6
    · exact q_15_15_7
    · exact q_15_15_8
    · exact q_15_15_9
    · exact q_15_15_10
    · exact q_15_15_11
    · exact q_15_15_12
    · exact q_15_15_13
    · exact q_15_15_14
  exact eq_of_beq (List.all_eq_true.mp hi j.val (List.mem_range.mpr j.isLt))
private lemma table_15_16 (i j : Fin 15) : contraction [i.val,j.val,15,16]=c (expectedQ 15 16 i.val j.val) := by
  have hi : ((List.range 15).all fun n => contraction [i.val,n,15,16] == c (expectedQ 15 16 i.val n))=true := by
    fin_cases i
    · exact q_15_16_0
    · exact q_15_16_1
    · exact q_15_16_2
    · exact q_15_16_3
    · exact q_15_16_4
    · exact q_15_16_5
    · exact q_15_16_6
    · exact q_15_16_7
    · exact q_15_16_8
    · exact q_15_16_9
    · exact q_15_16_10
    · exact q_15_16_11
    · exact q_15_16_12
    · exact q_15_16_13
    · exact q_15_16_14
  exact eq_of_beq (List.all_eq_true.mp hi j.val (List.mem_range.mpr j.isLt))
private lemma table_16_16 (i j : Fin 15) : contraction [i.val,j.val,16,16]=c (expectedQ 16 16 i.val j.val) := by
  have hi : ((List.range 15).all fun n => contraction [i.val,n,16,16] == c (expectedQ 16 16 i.val n))=true := by
    fin_cases i
    · exact q_16_16_0
    · exact q_16_16_1
    · exact q_16_16_2
    · exact q_16_16_3
    · exact q_16_16_4
    · exact q_16_16_5
    · exact q_16_16_6
    · exact q_16_16_7
    · exact q_16_16_8
    · exact q_16_16_9
    · exact q_16_16_10
    · exact q_16_16_11
    · exact q_16_16_12
    · exact q_16_16_13
    · exact q_16_16_14
  exact eq_of_beq (List.all_eq_true.mp hi j.val (List.mem_range.mpr j.isLt))
def sv : Fin 5 → Fin 15 := ![1,3,7,9,13]
private lemma smem (i : Fin 5) : (sv i).val ∈ sliceVars := by fin_cases i <;> decide
private lemma s2 (i j : Fin 5) : contraction [(sv i).val,(sv j).val]=c (expectedSecond (sv i).val (sv j).val) := by
  exact eq_of_beq (List.all_eq_true.mp (List.all_eq_true.mp sliceSecond _ (smem i)) _ (smem j))
private lemma sm (i j : Fin 5) : contraction [(sv i).val,(sv j).val,16]=c (if samePair (sv i).val (sv j).val 7 13 then -36 else 0) := by
  exact eq_of_beq (List.all_eq_true.mp (List.all_eq_true.mp sliceMixed _ (smem i)) _ (smem j))
private lemma s3 (i j k : Fin 5) : contraction [(sv i).val,(sv j).val,(sv k).val]=c (expectedThird (sv i).val (sv j).val (sv k).val) := by
  exact eq_of_beq (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp sliceThird _ (smem i)) _ (smem j)) _ (smem k))
private lemma small (x : Fin 15 → ℂ)
    (hz : ∀ j ∈ ([0,2,4,5,6,8,10,11,12,14] : List (Fin 15)), x j = 0)
    (f : Fin 15 → ℂ) : integrate x f = ∑ i : Fin 5, x (sv i)*f (sv i) := by
  norm_num at hz
  obtain ⟨h0,h2,h4,h5,h6,h8,h10,h11,h12,h14⟩ := hz
  simp [integrate,Fin.sum_univ_succ,sv,Matrix.cons_val,h0,h2,h4,h5,h6,h8,h10,h11,h12,h14]

end PEqualNP.Gct.FourierTable

open PEqualNP.Gct.FourierTable
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem PEqualNP.Gct.SaturatedTensorBound (w : ℂ) (W : Submodule ℂ (Fin 15 → ℂ))
    (h : ∀ x ∈ W, bil w x [15,15]=0 ∧ bil w x [15,16]=0 ∧ bil w x [16,16]=0 ∧
      bil w x []=0 ∧ bil w x [16]=0 ∧ cub w x=0) : finrank ℂ W ≤ 6 := by
  apply PEqualNP.Gct.FourSixBound W
  · intro x hx
    have hq := (h x hx).1
    simp only [bil,integrate,table_15_15,val_c] at hq
    norm_num [Fin.sum_univ_succ,expectedQ,samePair] at hq
    linear_combination hq/648
  · intro x hx
    have hq := (h x hx).2.1
    simp only [bil,integrate,table_15_16,val_c] at hq
    norm_num [Fin.sum_univ_succ,expectedQ,samePair] at hq
    linear_combination hq/324
  · intro x hx
    have hq := (h x hx).2.2.1
    simp only [bil,integrate,table_16_16,val_c] at hq
    norm_num [Fin.sum_univ_succ,expectedQ,samePair] at hq
    linear_combination hq/648
  · intro x hx hz
    obtain ⟨_,_,_,h₀,h₁,h₃⟩ := h x hx
    simp only [bil,cub,small x hz,s2,sm,s3,val_c] at h₀ h₁ h₃
    norm_num [Fin.sum_univ_succ,expectedSecond,expectedThird,samePair,sv,Matrix.cons_val] at h₀ h₁ h₃
    exact ⟨by linear_combination -h₀/36,by linear_combination -h₁/72,by linear_combination h₃/36⟩
