import Blanc.Lift.Curve3Pool.CheckTries
import Blanc.Lift.ReachWalk

/-!
# Arm kernel facts for the quiet admin/getter lift

Checked-node facts for the dispatcher fall-through arms (`t_49aa_c0`, …), each
stated as a `checkNodeM` over the arm's body pc with empty frame and empty
memory map (the dispatcher hands the arm an empty stack), plus the exec-free
facts `xa_node_span` needs. Also `admRawClosedHalt`: a tree with no
`.ret`/`.callNext`/`.branchTo`/`.jump` node can only halt, which rules out the
returned branch of `xa_node_span` for these arms.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- A tree with no return-producing node: no `.ret`, `.callNext`, `.branchTo`
or `.jump`. The quiet arms satisfy this, so their runs halt. -/
def admRawClosedHalt : SFunc → Bool
  | .branch f g => admRawClosedHalt f && admRawClosedHalt g
  | .branchTo _ _ => false
  | .last _ => true
  | .next _ f => admRawClosedHalt f
  | .dest f => admRawClosedHalt f
  | .jump _ => false
  | .callNext _ _ => false
  | .ret => false
  | .pcAt _ f => admRawClosedHalt f
  | .undefined => true

/-- A closed-halt tree's run halts: no `.returned` outcome. -/
theorem admRawRun_halted {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc}
    {sevm : Sevm} {d : Devm} {f : SFunc} {o : Outcome}
    (h : admRawClosedHalt f = true) (run : SFunc.RunP P fs sevm d f o) :
    ∃ post, o = .halted post := by
  induction run with
  | zero d pop _ ih =>
    simp only [admRawClosedHalt, Bool.and_eq_true] at h
    exact ih h.1
  | succ d w hnz pop _ ih =>
    simp only [admRawClosedHalt, Bool.and_eq_true] at h
    exact ih h.2
  | toZero d pop _ ih => simp only [admRawClosedHalt, Bool.false_eq_true] at h
  | toSucc d w hnz lookup pop _ ih => simp only [admRawClosedHalt, Bool.false_eq_true] at h
  | last h => exact ⟨_, rfl⟩
  | next h _ ih => simpa only [admRawClosedHalt] using ih h
  | dest burn _ ih => simpa only [admRawClosedHalt] using ih h
  | jump d lookup pop _ ih => simp only [admRawClosedHalt, Bool.false_eq_true] at h
  | ret d pop => simp only [admRawClosedHalt, Bool.false_eq_true] at h
  | callHalt d lookup pop _ ih => simp only [admRawClosedHalt, Bool.false_eq_true] at h
  | callRet d lookup pop _ _ ihRun ihTail => simp only [admRawClosedHalt, Bool.false_eq_true] at h
  | pcAt h hpc _ ih => simpa only [admRawClosedHalt] using ih h

/-- The empty entry set is exec-free and closed. -/
theorem admRawExecFreeSet : ExecFreeSet cert.prog [] = true := by decide

theorem admRaw_check_commitNewFee :
    checkNodeM code (Cert.entries cert) mems true 0 0x49aa [] [] t_49aa_c0 = true := by
  rw [← checkNodeMT_eq codeTries]
  decide +kernel

theorem admRaw_free_commitNewFee : t_49aa_c0.execFreeIn [] = true := by decide

theorem admRaw_halt_commitNewFee : admRawClosedHalt t_49aa_c0 = true := by decide

theorem admRaw_check_feeGetter :
    checkNodeM code (Cert.entries cert) mems true 0 0x5103 [] [] t_5103_c0 = true := by
  rw [← checkNodeMT_eq codeTries]
  decide +kernel

theorem admRaw_free_feeGetter : t_5103_c0.execFreeIn [] = true := by decide

theorem admRaw_halt_feeGetter : admRawClosedHalt t_5103_c0 = true := by decide

theorem admRaw_check_coinsGetter :
    checkNodeM code (Cert.entries cert) mems true 0 0x5083 [] [] t_5083_c0 = true := by
  rw [← checkNodeMT_eq codeTries]
  decide +kernel

theorem admRaw_free_coinsGetter : t_5083_c0.execFreeIn [] = true := by decide

theorem admRaw_halt_coinsGetter : admRawClosedHalt t_5083_c0 = true := by decide

theorem admRaw_check_applyNewFee :
    checkNodeM code (Cert.entries cert) mems true 0 0x4a73 [] [] t_4a73_c0 = true := by
  rw [← checkNodeMT_eq codeTries]
  decide +kernel

theorem admRaw_free_applyNewFee : t_4a73_c0.execFreeIn [] = true := by decide

theorem admRaw_halt_applyNewFee : admRawClosedHalt t_4a73_c0 = true := by decide

theorem admRaw_check_revertNewParameters :
    checkNodeM code (Cert.entries cert) mems true 0 0x4b12 [] [] t_4b12_c0 = true := by
  rw [← checkNodeMT_eq codeTries]
  decide +kernel

theorem admRaw_free_revertNewParameters : t_4b12_c0.execFreeIn [] = true := by decide

theorem admRaw_halt_revertNewParameters : admRawClosedHalt t_4b12_c0 = true := by decide

theorem admRaw_check_commitTransferOwnership :
    checkNodeM code (Cert.entries cert) mems true 0 0x4b40 [] [] t_4b40_c0 = true := by
  rw [← checkNodeMT_eq codeTries]
  decide +kernel

theorem admRaw_free_commitTransferOwnership : t_4b40_c0.execFreeIn [] = true := by decide

theorem admRaw_halt_commitTransferOwnership : admRawClosedHalt t_4b40_c0 = true := by decide

theorem admRaw_check_applyTransferOwnership :
    checkNodeM code (Cert.entries cert) mems true 0 0x4be1 [] [] t_4be1_c0 = true := by
  rw [← checkNodeMT_eq codeTries]
  decide +kernel

theorem admRaw_free_applyTransferOwnership : t_4be1_c0.execFreeIn [] = true := by decide

theorem admRaw_halt_applyTransferOwnership : admRawClosedHalt t_4be1_c0 = true := by decide

theorem admRaw_check_revertTransferOwnership :
    checkNodeM code (Cert.entries cert) mems true 0 0x4c65 [] [] t_4c65_c0 = true := by
  rw [← checkNodeMT_eq codeTries]
  decide +kernel

theorem admRaw_free_revertTransferOwnership : t_4c65_c0.execFreeIn [] = true := by decide

theorem admRaw_halt_revertTransferOwnership : admRawClosedHalt t_4c65_c0 = true := by decide

theorem admRaw_check_killMe :
    checkNodeM code (Cert.entries cert) mems true 0 0x5019 [] [] t_5019_c0 = true := by
  rw [← checkNodeMT_eq codeTries]
  decide +kernel

theorem admRaw_free_killMe : t_5019_c0.execFreeIn [] = true := by decide

theorem admRaw_halt_killMe : admRawClosedHalt t_5019_c0 = true := by decide

theorem admRaw_check_unkillMe :
    checkNodeM code (Cert.entries cert) mems true 0 0x5055 [] [] t_5055_c0 = true := by
  rw [← checkNodeMT_eq codeTries]
  decide +kernel

theorem admRaw_free_unkillMe : t_5055_c0.execFreeIn [] = true := by decide

theorem admRaw_halt_unkillMe : admRawClosedHalt t_5055_c0 = true := by decide

theorem admRaw_check_balancesGetter :
    checkNodeM code (Cert.entries cert) mems true 0 0x50c3 [] [] t_50c3_c0 = true := by
  rw [← checkNodeMT_eq codeTries]
  decide +kernel

theorem admRaw_free_balancesGetter : t_50c3_c0.execFreeIn [] = true := by decide

theorem admRaw_halt_balancesGetter : admRawClosedHalt t_50c3_c0 = true := by decide

theorem admRaw_check_adminFeeGetter :
    checkNodeM code (Cert.entries cert) mems true 0 0x512a [] [] t_512a_c0 = true := by
  rw [← checkNodeMT_eq codeTries]
  decide +kernel

theorem admRaw_free_adminFeeGetter : t_512a_c0.execFreeIn [] = true := by decide

theorem admRaw_halt_adminFeeGetter : admRawClosedHalt t_512a_c0 = true := by decide

theorem admRaw_check_ownerGetter :
    checkNodeM code (Cert.entries cert) mems true 0 0x5151 [] [] t_5151_c0 = true := by
  rw [← checkNodeMT_eq codeTries]
  decide +kernel

theorem admRaw_free_ownerGetter : t_5151_c0.execFreeIn [] = true := by decide

theorem admRaw_halt_ownerGetter : admRawClosedHalt t_5151_c0 = true := by decide

theorem admRaw_check_initialAGetter :
    checkNodeM code (Cert.entries cert) mems true 0 0x5178 [] [] t_5178_c0 = true := by
  rw [← checkNodeMT_eq codeTries]
  decide +kernel

theorem admRaw_free_initialAGetter : t_5178_c0.execFreeIn [] = true := by decide

theorem admRaw_halt_initialAGetter : admRawClosedHalt t_5178_c0 = true := by decide

theorem admRaw_check_futureAGetter :
    checkNodeM code (Cert.entries cert) mems true 0 0x519f [] [] t_519f_c0 = true := by
  rw [← checkNodeMT_eq codeTries]
  decide +kernel

theorem admRaw_free_futureAGetter : t_519f_c0.execFreeIn [] = true := by decide

theorem admRaw_halt_futureAGetter : admRawClosedHalt t_519f_c0 = true := by decide

theorem admRaw_check_initialATimeGetter :
    checkNodeM code (Cert.entries cert) mems true 0 0x51c6 [] [] t_51c6_c0 = true := by
  rw [← checkNodeMT_eq codeTries]
  decide +kernel

theorem admRaw_free_initialATimeGetter : t_51c6_c0.execFreeIn [] = true := by decide

theorem admRaw_halt_initialATimeGetter : admRawClosedHalt t_51c6_c0 = true := by decide

theorem admRaw_check_futureATimeGetter :
    checkNodeM code (Cert.entries cert) mems true 0 0x51ed [] [] t_51ed_c0 = true := by
  rw [← checkNodeMT_eq codeTries]
  decide +kernel

theorem admRaw_free_futureATimeGetter : t_51ed_c0.execFreeIn [] = true := by decide

theorem admRaw_halt_futureATimeGetter : admRawClosedHalt t_51ed_c0 = true := by decide

theorem admRaw_check_adminActionsDeadlineGetter :
    checkNodeM code (Cert.entries cert) mems true 0 0x5214 [] [] t_5214_c0 = true := by
  rw [← checkNodeMT_eq codeTries]
  decide +kernel

theorem admRaw_free_adminActionsDeadlineGetter : t_5214_c0.execFreeIn [] = true := by decide

theorem admRaw_halt_adminActionsDeadlineGetter : admRawClosedHalt t_5214_c0 = true := by decide

theorem admRaw_check_transferOwnershipDeadlineGetter :
    checkNodeM code (Cert.entries cert) mems true 0 0x523b [] [] t_523b_c0 = true := by
  rw [← checkNodeMT_eq codeTries]
  decide +kernel

theorem admRaw_free_transferOwnershipDeadlineGetter : t_523b_c0.execFreeIn [] = true := by decide

theorem admRaw_halt_transferOwnershipDeadlineGetter :
    admRawClosedHalt t_523b_c0 = true := by decide

theorem admRaw_check_futureFeeGetter :
    checkNodeM code (Cert.entries cert) mems true 0 0x5262 [] [] t_5262_c0 = true := by
  rw [← checkNodeMT_eq codeTries]
  decide +kernel

theorem admRaw_free_futureFeeGetter : t_5262_c0.execFreeIn [] = true := by decide

theorem admRaw_halt_futureFeeGetter : admRawClosedHalt t_5262_c0 = true := by decide

theorem admRaw_check_futureAdminFeeGetter :
    checkNodeM code (Cert.entries cert) mems true 0 0x5289 [] [] t_5289_c0 = true := by
  rw [← checkNodeMT_eq codeTries]
  decide +kernel

theorem admRaw_free_futureAdminFeeGetter : t_5289_c0.execFreeIn [] = true := by decide

theorem admRaw_halt_futureAdminFeeGetter : admRawClosedHalt t_5289_c0 = true := by decide

theorem admRaw_check_futureOwnerGetter :
    checkNodeM code (Cert.entries cert) mems true 0 0x52b0 [] [] t_52b0_c0 = true := by
  rw [← checkNodeMT_eq codeTries]
  decide +kernel

theorem admRaw_free_futureOwnerGetter : t_52b0_c0.execFreeIn [] = true := by decide

theorem admRaw_halt_futureOwnerGetter : admRawClosedHalt t_52b0_c0 = true := by decide

end Blanc.Lift.Curve3Pool
