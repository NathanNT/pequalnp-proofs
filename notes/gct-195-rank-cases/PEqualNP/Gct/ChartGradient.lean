import PEqualNP.Gct.ChartSpan
namespace PEqualNP.Gct.FourierTable
open Finset
private lemma g0 (i : Fin 24) : grad (i.val::[])=c (gradRow0 i.val) :=
  eq_of_beq (List.all_eq_true.mp gradCert0 i.val (List.mem_range.mpr i.isLt))
private lemma g1 (i : Fin 24) : grad (i.val::[16])=c (gradRow1 i.val) :=
  eq_of_beq (List.all_eq_true.mp gradCert1 i.val (List.mem_range.mpr i.isLt))
private lemma g2 (i : Fin 24) : grad (i.val::[16,16])=c (gradRow2 i.val) :=
  eq_of_beq (List.all_eq_true.mp gradCert2 i.val (List.mem_range.mpr i.isLt))
private lemma g3 (i : Fin 24) : grad (i.val::[16,16,16])=c (gradRow3 i.val) :=
  eq_of_beq (List.all_eq_true.mp gradCert3 i.val (List.mem_range.mpr i.isLt))
private lemma g4 (i : Fin 24) : grad (i.val::[15])=c (gradRow4 i.val) :=
  eq_of_beq (List.all_eq_true.mp gradCert4 i.val (List.mem_range.mpr i.isLt))
private lemma g5 (i : Fin 24) : grad (i.val::[15,15])=c (gradRow5 i.val) :=
  eq_of_beq (List.all_eq_true.mp gradCert5 i.val (List.mem_range.mpr i.isLt))
private lemma g6 (i : Fin 24) : grad (i.val::[15,15,15])=c (gradRow6 i.val) :=
  eq_of_beq (List.all_eq_true.mp gradCert6 i.val (List.mem_range.mpr i.isLt))
theorem ext_small (w : ℂ) {i : Nat} (hi : i<17) : extAtom w i=atom w i := by
  funext r j
  simp [extAtom,atom,extRow,extCol,hi]

set_option maxHeartbeats 800000 in
theorem noComplement {w : ℂ} (hw : w^2+w+1=0) (z : Fin 24 → ℂ)
    (van : ∀ seeds ∈ ([[],[16],[16,16],[16,16,16],[15],[15,15],[15,15,15]] : List (List Nat)),
      mixed (chart w z :: seeds.map (extAtom w))=0) :
    z 17=0 ∧ z 18=0 ∧ z 19=0 ∧ z 20=0 ∧ z 21=0 ∧ z 22=0 ∧ z 23=0 := by
  have e0 := (firstSlot24 hw z []).symm.trans (van _ (by decide))
  simp only [g0,val_c] at e0
  norm_num [Fin.sum_univ_succ,gradRow0] at e0
  have e1 := (firstSlot24 hw z [16]).symm.trans (van _ (by decide))
  simp only [g1,val_c] at e1
  norm_num [Fin.sum_univ_succ,gradRow1] at e1
  have e2 := (firstSlot24 hw z [16,16]).symm.trans (van _ (by decide))
  simp only [g2,val_c] at e2
  norm_num [Fin.sum_univ_succ,gradRow2] at e2
  have e3 := (firstSlot24 hw z [16,16,16]).symm.trans (van _ (by decide))
  simp only [g3,val_c] at e3
  norm_num [Fin.sum_univ_succ,gradRow3] at e3
  have e4 := (firstSlot24 hw z [15]).symm.trans (van _ (by decide))
  simp only [g4,val_c] at e4
  norm_num [Fin.sum_univ_succ,gradRow4] at e4
  have e5 := (firstSlot24 hw z [15,15]).symm.trans (van _ (by decide))
  simp only [g5,val_c] at e5
  norm_num [Fin.sum_univ_succ,gradRow5] at e5
  have e6 := (firstSlot24 hw z [15,15,15]).symm.trans (van _ (by decide))
  simp only [g6,val_c] at e6
  norm_num [Fin.sum_univ_succ,gradRow6] at e6
  rw [e6] at e0
  exact ⟨by linear_combination e0/36-e3/34992,e4,e6,e1,by linear_combination e0/9+e3/4374,e5,e2⟩
def first15 (z : Fin 24 → ℂ) (i : Fin 15) := z (i.castLE (by decide))
set_option maxHeartbeats 1000000 in
theorem chart_split (w : ℂ) (z : Fin 24 → ℂ)
    (h : z 17=0 ∧ z 18=0 ∧ z 19=0 ∧ z 20=0 ∧ z 21=0 ∧ z 22=0 ∧ z 23=0) :
    chart w z = combo w (first15 z) + z 15 • atom w 15 + z 16 • atom w 16 := by
  obtain ⟨h17,h18,h19,h20,h21,h22,h23⟩ := h
  funext r j
  have e (i : Nat) (hi : i<17) : extAtom w i r j=atom w i r j := congrFun (congrFun (ext_small w hi) r) j
  simp only [chart,combo,Fin.sum_univ_succ,Pi.add_apply,Pi.smul_apply,smul_eq_mul,first15]
  norm_num [Fin.succ_mk,Fin.val_mk,Fin.castLE_mk] at *
  simp only [h17,h18,h19,h20,h21,h22,h23,zero_mul,add_zero,zero_add]
  simp only [e _ (by decide : 0<17)] -- remaining numerals reduce with the same bound
  rw [e 1 (by decide)]
  rw [e 2 (by decide)]
  rw [e 3 (by decide)]
  rw [e 4 (by decide)]
  rw [e 5 (by decide)]
  rw [e 6 (by decide)]
  rw [e 7 (by decide)]
  rw [e 8 (by decide)]
  rw [e 9 (by decide)]
  rw [e 10 (by decide)]
  rw [e 11 (by decide)]
  rw [e 12 (by decide)]
  rw [e 13 (by decide)]
  rw [e 14 (by decide)]
  rw [e 15 (by decide)]
  rw [e 16 (by decide)]
  ring
end PEqualNP.Gct.FourierTable
