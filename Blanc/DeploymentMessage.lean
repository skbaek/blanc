-- DeploymentMessage.lean : contract-neutral CREATE message plumbing.
--
-- Constructor-specific execution remains in each contract.  This owner keeps
-- the shared bridge from fresh-account preparation and zero-value transfer to
-- an ordinary successful `processMessage` result.

import Blanc.ExecutionOccurrence

namespace Blanc

open Jaune

/-- Jaune's generic creation preparation clears the new account's storage
before incrementing its nonce. -/
theorem processCreateMessage_msg_getStor_currentTarget (msg : Msg) :
    (processCreateMessage.msg msg).benv.state.getStor msg.currentTarget =
      Stor.empty := by
  change (((msg.benv.state.setStor msg.currentTarget .empty).incrNonce
    msg.currentTarget).get msg.currentTarget).stor = .empty
  rw [State.incrNonce_get_stor]
  unfold State.setStor
  rw [State.get_set_self]

/-- A zero-value message can always cross its optional entry transfer. -/
theorem benvAfterTransfer_exists_zero
    {msg : Msg} (hvalue : msg.value = 0) :
    ∃ benv, msg.benvAfterTransfer = .ok benv := by
  have hnot : ¬ msg.benv.state.bal msg.caller < (0 : B256) := by
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_zero]
    omega
  unfold Msg.benvAfterTransfer
  rw [hvalue]
  by_cases htransfer : msg.shouldTransferValue = true
  · rw [if_pos htransfer]
    unfold Benv.subBal State.subBal
    rw [if_neg hnot]
    exact ⟨_, rfl⟩
  · rw [if_neg htransfer]
    exact ⟨_, rfl⟩

/-- Message-entry balance transfer preserves the static block environment. -/
theorem benvAfterTransfer_stat
    {msg : Msg} {benv : Benv}
    (h : msg.benvAfterTransfer = .ok benv) :
    benv.stat = msg.benv.stat := by
  by_cases htransfer : msg.shouldTransferValue = true
  · obtain ⟨middle, hsub, rfl⟩ := of_benvAfterTransfer htransfer h
    rfl
  · rw [of_benvAfterTransfer_no htransfer h]

/-- A successful raw `exec` with no frame error settles as the corresponding
ordinary message result. -/
theorem processMessage_ok_of_exec
    {msg : Msg} {benv : Benv} {post : Devm}
    (htransfer : msg.benvAfterTransfer = .ok benv)
    (hcodeAddress : msg.codeAddress = .none)
    (hexec : exec (initEvm (msg.withBenv benv)) = .ok post)
    (herror : post.error = .none) :
    processMessage msg = .ok post := by
  unfold processMessage runFrame Frame.enter Frame.ofCall
  rw [htransfer]
  unfold executeCode.enter
  simp only [Msg.withBenv, hcodeAddress]
  unfold Frame.settle Frame.settleMsg
  simp only [Msg.withBenv, hcodeAddress] at hexec
  rw [hexec]
  simp [executeCode.handleError, processMessage.settle, herror]

/-- Successful inner-message execution followed by successful code charging is
the successful CREATE settlement, with the charged output installed at the
new target. -/
theorem processCreateMessage_ok_of_processMessage_and_charge
    (msg : Msg) {raw charged : Devm}
    (hprocess : processMessage (processCreateMessage.msg msg) = .ok raw)
    (herror : raw.error = .none)
    (hcharge :
      processCreateMessage.chargeCodeGas msg.benv.stat.rules raw = .ok charged) :
    processCreateMessage msg =
      .ok (charged.setCode msg.currentTarget ⟨⟨charged.output⟩⟩) := by
  rw [processCreateMessage_eq, hprocess]
  unfold processCreateMessage.settle
  simp [herror, hcharge]

end Blanc
