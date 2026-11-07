import Blanc.Lift.BuilderRequest.AmsterdamMsgProbeRevert
import Blanc.Lift.BuilderRequest.Exit.Frames

/-!
# Probe: a reverting deposit call through the message path, and the exit rejection with `REVERT` named

Disposable (goal `blanc-eip8282-builder-requests-v1`, O16).
-/

namespace Blanc.Lift.BuilderRequest.AmsterdamMsgProbe

open Jaune

def depositInhibit : InhibitBytes Deposit.code where
  sysDest := ⟨0x01, [0x1c], by decide⟩
  dest := ⟨0x02, [0x70], by decide⟩
  jumpiAt := 67
  revertAt := 0x273
  seg1 := by decide +kernel
  jumpi := by unfold Jinst.At; kernel_rfl
  jumpable := by decide +kernel
  seg2 := by decide +kernel
  rev := by unfold Linst.At; kernel_rfl

def exitInhibit : InhibitBytes Exit.code where
  sysDest := ⟨0xe1, [], by decide⟩
  dest := ⟨0x01, [0xc6], by decide⟩
  jumpiAt := 66
  revertAt := 0x1c9
  seg1 := by decide +kernel
  jumpi := by unfold Jinst.At; kernel_rfl
  jumpable := by decide +kernel
  seg2 := by decide +kernel
  rev := by unfold Linst.At; kernel_rfl

/-- **Exit rejection, with `REVERT` named.** On every fork with EIP-2929 access and `PUSH0`, covered or
Amsterdam: `Exit.exec_user_inhibited_fails` left open whether the failure is `REVERT` or out of gas. Given
the gas, it is `REVERT`, with its machine. -/
theorem exit_inhibited_reverts {s : Sevm} {b : Devm} {M : Mem} {G : Nat} (hcode : s.code = Exit.code)
    (hacc : s.benvStat.rules.access = .eip2929) (hp0 : s.benvStat.rules.op.push0 = true)
    (caller : s.caller ≠ systemAddress) (inhibited : b.getStorVal s.currentTarget 0 = B256.max) :
    Nonempty (Exec 0 s (St b [] M (G + inhibitFixed + sloadCost s b 0))
      (.error (.revert, (St (afterSloadA s b 0) [B256.max] M G).withOutput []))) :=
  exec_inhibited_reverts exitInhibit hcode hacc hp0 caller inhibited

/-- The settled revert's meter, generically: the reservoir back at its baseline, the spill back in
regular gas, no refund. This is the `handleErrorAmsterdam` arithmetic at the output. -/
theorem revertOutput_meter (M : Msg) (raw : Devm) :
    (revertOutput M raw).stateGasLeft = raw.stateGas.baseline ∧
      (revertOutput M raw).gasLeft = raw.gasLeft + raw.stateGas.spilled ∧
      (revertOutput M raw).refundCounter = 0 ∧ (revertOutput M raw).logs = [] ∧
      (revertOutput M raw).stateGasUsed =
        Int.ofNat M.stateGasGrant - Int.ofNat raw.stateGas.baseline + Int.ofNat 0 +
          Int.ofNat raw.stateGas.committedSpill :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **A deposit call that reverts under Amsterdam, through the top-level message path, at any storage
with slot 0 on the inhibitor.** The state returned is the pre-call state, value included. No log. No
state gas used. `raw` still holds the EIP-7708 log, so it is settlement that drops it. -/
theorem deposit_call_inhibited {M' : Msg} {benv : Benv} {G : Nat}
    (hfork : M'.benv.stat.fork = .amsterdam)
    (hauth : M'.tenv.stat.auths.isEmpty = true) (htarget : M'.target.isNone = false)
    (installed : M'.benv.state.getCode M'.currentTarget = Deposit.code)
    (hnew : (M'.value != 0 && decide (M'.benv.state.get M'.currentTarget).Empty) = false)
    (hprecomp : ¬ amsterdamRules.isPrecomp M'.currentTarget)
    (entry : M'.benvAfterTransfer = .ok benv) (hstat : benv.stat = M'.benv.stat)
    (caller : M'.caller ≠ systemAddress)
    (hgas : M'.gas = G + inhibitFixed +
      sloadCost (userSevm M' Deposit.code benv) (userEntry M' benv) 0)
    (inhibited : (userEntry M' benv).getStorVal M'.currentTarget 0 = B256.max) :
    let s := userSevm M' Deposit.code benv
    let e := userEntry M' benv
    let raw := (St (afterSloadA s e 0) [B256.max] .empty G).withOutput []
    processMessageCall M' = .ok (M'.benv.state, revertOutput M' raw) ∧
      raw.logs = (initDevm M').logs ∧
      (revertOutput M' raw).logs = [] ∧
      (revertOutput M' raw).error = some .revert ∧
      (revertOutput M' raw).gasLeft = G ∧
      (revertOutput M' raw).stateGasLeft = M'.stateGasGrant ∧
      (revertOutput M' raw).stateGasUsed = 0 ∧
      (revertOutput M' raw).returnData = [] := by
  intro s e raw
  have hsfork : s.benvStat.fork = .amsterdam := by
    show benv.stat.fork = _
    rw [hstat]
    exact hfork
  have hrun := exec_inhibited_reverts depositInhibit (s := s) (b := e) (M := .empty) (G := G) rfl
    (Blanc.amsterdam_access hsfork) (Blanc.amsterdam_push0 hsfork) caller inhibited
  have hSt : St e [] .empty (G + inhibitFixed + sloadCost s e 0) = e := by
    rw [← hgas]
    exact St.self rfl rfl
  rw [hSt] at hrun
  have hexec := (exec_iff_exec_eq _ _ _ _).mp hrun
  have hmeter : (afterSloadA s e 0).stateGas = e.stateGas := afterSloadA_stateGas
  have hlogs : raw.logs = (initDevm M').logs := by
    show (afterSloadA s e 0).logs = _
    rw [Deposit.afterSloadA_logs]
    show (userBase M').logs = _
    unfold userBase
    simp only [Deposit.balReadAccount_logs]
  have hs : raw.stateGas = e.stateGas := hmeter
  have hleft : e.stateGas.baseline = M'.stateGasGrant := rfl
  have hspill : e.stateGas.spilled = 0 := rfl
  have hcommit : e.stateGas.committedSpill = 0 := rfl
  refine ⟨processMessageCall_revert hfork hauth htarget installed Deposit.code_undelegated hnew hprecomp
    entry hstat hexec, hlogs, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · refine (revertOutput_meter M' raw).2.1.trans ?_
    rw [hs, hspill]
    rfl
  · refine (revertOutput_meter M' raw).1.trans ?_
    rw [hs, hleft]
  · refine (revertOutput_meter M' raw).2.2.2.2.trans ?_
    rw [hs, hleft, hcommit]
    simp only [Int.ofNat_eq_natCast, Int.natCast_zero, Int.add_zero, Int.sub_self]

end Blanc.Lift.BuilderRequest.AmsterdamMsgProbe
