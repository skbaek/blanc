import Blanc.Lift.Curve3Crv.Creation.HistoricalWalk
import Blanc.Lift.Curve3Crv.Creation.HistoricalTx
import Blanc.Lift.HistCreate

/-!
# The 3Crv CREATE message under Muir Glacier

`curve_create_muir_meta`: the recorded creation input, executed as a zero-value CREATE message
from the recorded deployer with empty call data under Muir Glacier rules, succeeds; it installs
exactly the certified runtime `Blanc.Lift.Curve3Crv.code`, leaves the storage
`deployedStor deployer`, no error, refund counter 0, the single log `Transfer(0, deployer, 0)`,
the inherited deletion set, and exactly `msg.gas - 580351` gas: the constructor's 125,151
(`ctorCost_muir`) plus the code deposit `200 · 2276 = 455200`. With the transaction's message gas
580,351 (`HistoricalTx.muir_message_gas`) the gas left is exactly 0; a smaller message gas fails
the gas premise.

The message and its pre-state are explicit premises; transaction validation, sender recovery,
settlement and block inclusion are not here.
-/

namespace Blanc.Lift.Curve3Crv.Creation

open Jaune Blanc.Lift Blanc.Lift.Curve3Crv

/-- **Real Muir Glacier CREATE-message execution of the 3Crv constructor**, with the
settlement metadata a transaction pipeline consumes. -/
theorem curve_create_muir_meta (msg : Msg) (hvalue : msg.value = 0)
    (hcodeAddress : msg.codeAddress = .none) (hcode : msg.code = code) (hdata : msg.data = [])
    (hcaller : msg.caller = deployer) (hgas : 580351 ≤ msg.gas)
    (hmuir : msg.benv.stat.rules = muirGlacierRules) (hstatic : msg.isStatic = false) :
    ∃ post, processCreateMessage msg = .ok post ∧
      (post.getCode msg.currentTarget).toList = Blanc.Lift.Curve3Crv.code.toList ∧
      Devm.getStor post msg.currentTarget = deployedStor deployer.toB256 ∧
      post.error = none ∧ post.refundCounter = 0 ∧
      post.logs = [transferLog msg.currentTarget deployer.toB256] ∧
      post.accountsToDelete = msg.inheritedDeletions ∧
      post.gasLeft = msg.gas - 580351 := by
  obtain ⟨benv, htransfer⟩ :=
    benvAfterTransfer_exists_zero (msg := processCreateMessage.msg msg) hvalue
  set sevm := initSevm (createSeed msg benv) with hsevm
  set b := initDevm (createSeed msg benv) with hb
  have hstat : sevm.benvStat = msg.benv.stat := by
    show benv.stat = (processCreateMessage.msg msg).benv.stat
    exact benvAfterTransfer_stat htransfer
  have hrules : sevm.benvStat.rules = muirGlacierRules := by rw [hstat]; exact hmuir
  have hsg : msg.benv.stat.rules.stateGas = none := by rw [hmuir]; rfl
  have hempty : Devm.getStor b sevm.currentTarget = Stor.empty := by
    show benv.state.getStor msg.currentTarget = _
    rw [benvAfterTransfer_ok_getStor htransfer msg.currentTarget (Or.inl hvalue),
      processCreateMessage_msg_getStor_currentTarget]
  have hcreated : sevm.currentTarget ∈ b.createdAccounts := by
    have heq := Msg.benvAfterTransfer_of_value_zero
      (msg := processCreateMessage.msg msg) hvalue
    have hbenv : benv = (processCreateMessage.msg msg).benv :=
      Except.ok.inj (htransfer.symm.trans heq)
    change msg.currentTarget ∈ benv.createdAccounts
    rw [hbenv]
    change msg.currentTarget ∈ msg.benv.createdAccounts.insert msg.currentTarget
    exact Std.HashSet.mem_insert_self
  have hlogs0 : b.logs = [] := initDevm_logs (by
    change sevm.benvStat.rules.stateGas = none
    rw [hrules]
    rfl)
  obtain ⟨raw, hrun, hout, herr, hst, hgasLeft, hrefund, hlogs, hdel⟩ :=
    ctor_run_muir hrules hstatic hcode hvalue hdata hcaller hcreated hempty
      (G := msg.gas - 125151) (by omega)
  have hpre0 : St b [] Mem.empty (msg.gas - 125151 + 125151) = b :=
    pre_eq_St rfl rfl (by show _ = msg.gas; omega)
  rw [hpre0] at hrun
  have hwin : raw.output = Blanc.Lift.Curve3Crv.code.toList := by
    rw [hout, runtimeWindow, ByteArray.sliceD_eq]
    exact runtime_window
  have hlen : raw.output.length = 2276 := by rw [hout]; exact runtimeWindow_length
  have hdep : raw.output.length * gasCodeDeposit ≤ raw.gasLeft := by
    rw [hlen, hgasLeft]; unfold gasCodeDeposit; omega
  have hmax : raw.output.length ≤ msg.benv.stat.rules.code.maxCodeSize := by
    rw [hlen, hmuir]; decide
  have herr' : raw.error = .none := by rw [herr]; rfl
  have hprefix : raw.output.head? ≠ some 0xEF := by rw [hwin]; exact runtime_head
  obtain ⟨post, hpost, hcodePost, hstorPost, herror⟩ := liftCreate_okH cert_check jumps_ok msg
    hcodeAddress hcode hsg htransfer hrun herr' hprefix hdep hmax
  have hexact := liftCreate_postH cert_check jumps_ok msg
    hcodeAddress hcode hsg htransfer hrun herr' hprefix hdep hmax
  have hpostEq : post = liftCreatePost msg.currentTarget
      (raw.recordTouch msg.benv.stat.rules true msg.currentTarget) :=
    Except.ok.inj (hpost.symm.trans hexact)
  have hnonempty : ¬ ({ raw.state.get msg.currentTarget with
      code := ⟨⟨raw.output⟩⟩ } : Acct).Empty := by
    intro empty
    have zero : raw.output.length = 0 := empty.1
    omega
  refine ⟨post, hpost, hcodePost.trans hwin, ?_, herror, ?_, ?_, ?_, ?_⟩
  · simp only [hstorPost, Acct.clearIfEmpty_stor, hnonempty, ↓reduceIte]
    show Devm.getStor raw sevm.currentTarget = _
    exact hst
  · rw [hpostEq]
    show raw.refundCounter = 0
    rw [hrefund]
    rfl
  · rw [hpostEq]
    show raw.logs = _
    rw [hlogs, hlogs0]
    rfl
  · rw [hpostEq]
    show raw.accountsToDelete = _
    rw [hdel]
    rfl
  · rw [hpostEq, (liftCreatePost_facts _ _).2.1, (recordTouch_meta _ _ _ _).2.2.2,
      Devm.recordTouch_output, hgasLeft, hlen]
    unfold gasCodeDeposit
    omega

end Blanc.Lift.Curve3Crv.Creation
