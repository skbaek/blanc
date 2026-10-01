import Blanc.Lift.WithdrawalRequest.SubmissionLayout
import Blanc.Lift.WithdrawalRequest.SystemStorage
import Blanc.Lift.WithdrawalRequest.FeeGetter

/-! Complete raw successful-frame classification and its preserved fields. -/

namespace Blanc.Lift.WithdrawalRequest

open Jaune

/-- Exact raw effects; fee admission uses the executed word recurrence. -/
inductive FrameEffect (sevm : Sevm) (pre post : Devm) : Prop where
  | system (caller : sevm.caller = systemAddress) (dynamic : sevm.isStatic = false)
      (gas : Nat) (state : post = systemFramePost sevm pre pre.memory gas)
  | submission (caller : sevm.caller ≠ systemAddress) (dynamic : sevm.isStatic = false)
      (length : sevm.data.length = 56)
      (active : pre.getStorVal sevm.currentTarget 0 ≠ B256.max)
      (iterations : Nat) (finalOutput : B256)
      (fee : WordFakeExponential.Run (pre.getStorVal sevm.currentTarget 0)
        17 1 17 0 iterations finalOutput)
      (paid : (finalOutput / (17 : B256)).toNat ≤ sevm.value.toNat)
      (gas : Nat) (state : post = submissionPost sevm (afterSload sevm pre 0) pre.memory gas)
  | getter (caller : sevm.caller ≠ systemAddress) (empty : sevm.data = [])
      (value : sevm.value = 0) (active : pre.getStorVal sevm.currentTarget 0 ≠ B256.max)
      (iterations : Nat) (finalOutput : B256)
      (fee : WordFakeExponential.Run (pre.getStorVal sevm.currentTarget 0)
        17 1 17 0 iterations finalOutput)
      (gas : Nat) (state : post = feeGetterPost (afterSload sevm pre 0) pre.memory
        (finalOutput / 17) gas)
      (output : post.output = (finalOutput / (17 : B256)).toBytes)

/-- The entry calldata bound turns machine length guards into literal lengths. -/
theorem exec_frame_effect {sevm : Sevm} {pre post : Devm}
    (code : sevm.code = Blanc.withdrawalRequestCode)
    (fork : CoveredFork sevm.benvStat.fork) (stack : pre.stack = [])
    (aligned : pre.memory.size % 32 = 0) (wf : Mem.Wf pre.memory)
    (lengthBound : sevm.data.length < 2 ^ 256)
    (exec : Exec 0 sevm pre (.ok post)) : FrameEffect sevm pre post := by
  by_cases caller : sevm.caller = systemAddress
  · obtain ⟨dynamic, gas, state⟩ := exec_system_frame code fork stack caller exec
    exact .system caller dynamic gas state
  · obtain ⟨_, _, _, _, accepted⟩ := exec_user_fee_dispatch code fork stack caller exec
    rcases accepted with ⟨length, _, _⟩ | ⟨length, _, _⟩
    · have literal := congrArg B256.toNat length
      rw [B256.toNat_toB256_of_lt lengthBound] at literal
      change sevm.data.length = 56 at literal
      obtain ⟨dynamic, active, iterations, finalOutput, fee, paid, gas, state⟩ :=
        exec_submission code fork stack caller literal exec
      exact .submission caller dynamic literal active iterations finalOutput fee paid gas state
    · have literal := congrArg B256.toNat length
      rw [B256.toNat_toB256_of_lt lengthBound] at literal
      change sevm.data.length = 0 at literal
      have empty := List.eq_nil_of_length_eq_zero literal
      obtain ⟨value, active, iterations, finalOutput, fee, gas, state, output⟩ :=
        exec_fee_getter code fork stack aligned wf caller empty exec
      exact .getter caller empty value active iterations finalOutput fee gas state output

/-- Submission preserves raw balances even when its storage keys alias. -/
theorem submissionPost_balance (sevm : Sevm) (b : Devm) (M : Mem) (gas : Nat)
    (address : Adr) : (submissionPost sevm b M gas).getBal address = b.getBal address := by
  rw [submissionPost]
  rw [show (St (submissionBase sevm b M) [] (submissionMemory sevm M) gas).getBal address =
      (submissionBase sevm b M).getBal address from by
    generalize submissionBase sevm b M = finalBase
    rfl]
  rw [submissionBase, afterSstore_getBal, submissionLogged]
  rw [show ((submissionWordsStore sevm b).addLog (submissionLog sevm M)).getBal address =
      (submissionWordsStore sevm b).getBal address from by
    generalize submissionWordsStore sevm b = written
    rfl]
  rw [submissionWordsStore, afterSstore_getBal, submissionWord1Store, afterSstore_getBal,
    submissionCallerStore, afterSstore_getBal, submissionTailRead]
  simp only [Devm.getBal, afterSload_getAcct]
  change (submissionCountStore sevm b).getBal address = b.getBal address
  rw [submissionCountStore, afterSstore_getBal, submissionCountRead]
  simp only [Devm.getBal, afterSload_getAcct]

/-- STOP retains the inherited output and error fields. -/
theorem submissionPost_inherited (sevm : Sevm) (b : Devm) (M : Mem) (gas : Nat) :
    (submissionPost sevm b M gas).output = b.output ∧
    (submissionPost sevm b M gas).error = b.error := by
  have metaEq := (submissionPost_facts sevm b M gas).2.1
  exact ⟨(congrArg Meta.output metaEq).trans (submissionBase_inherited sevm b M).1,
    (congrArg Meta.error metaEq).trans (submissionBase_inherited sevm b M).2⟩

/-- The getter changes output and memory, retaining all raw storage and balances. -/
theorem feeGetterPost_preserves (b : Devm) (M : Mem) (fee : B256) (gas : Nat) :
    (∀ address, (feeGetterPost b M fee gas).getStor address = b.getStor address) ∧
    (∀ address, (feeGetterPost b M fee gas).getBal address = b.getBal address) ∧
    (feeGetterPost b M fee gas).logs = b.logs ∧
    (feeGetterPost b M fee gas).error = b.error := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro address
    rw [feeGetterPost, (returnPost_facts _ _ _ _).2.2.1 address, St_getStor]
  · intro address
    simp only [feeGetterPost, returnPost, Devm.getBal, Devm.getAcct,
      Devm.withOutput_state, Devm.memRead_state, Devm.setMach_state, St]
  · simp only [feeGetterPost, returnPost, Devm.withOutput_logs, Devm.memRead_logs,
      Devm.setMach_logs, St]
  · rw [feeGetterPost, (returnPost_facts _ _ _ _).2.1]
    rfl

/-- Raw balance/foreign-storage/error preservation follows exact post states. -/
theorem FrameEffect.preserves {sevm : Sevm} {pre post : Devm}
    (effect : FrameEffect sevm pre post) :
    (∀ address, post.getBal address = pre.getBal address) ∧
    (∀ address, address ≠ sevm.currentTarget → post.getStor address = pre.getStor address) ∧
    post.error = pre.error := by
  cases effect with
  | system caller dynamic gas state =>
    rw [state]
    exact ⟨systemFramePost_balance sevm pre pre.memory gas,
      fun address other => systemFramePost_other_storage sevm pre pre.memory gas address other.symm,
      systemFramePost_error sevm pre pre.memory gas⟩
  | submission caller dynamic length active iterations finalOutput fee paid gas state =>
    rw [state]
    refine ⟨?_, ?_, ?_⟩
    · intro address
      rw [submissionPost_balance]
      simp only [Devm.getBal, afterSload_getAcct]
    · intro address other
      rw [submissionPost_other_storage _ _ _ _ _ other, afterSload_getStor]
    · rw [(submissionPost_inherited _ _ _ _).2, afterSload_error]
  | getter caller empty value active iterations finalOutput fee gas state output =>
    rw [state]
    have preserved := feeGetterPost_preserves (afterSload sevm pre 0) pre.memory
      (finalOutput / 17) gas
    refine ⟨?_, ?_, ?_⟩
    · intro address
      rw [preserved.2.1 address]
      simp only [Devm.getBal, afterSload_getAcct]
    · intro address _
      rw [preserved.1 address, afterSload_getStor]
    · rw [preserved.2.2.2, afterSload_error]

/-- User success retains the inhibitor exclusion and the two literal input guards. -/
theorem FrameEffect.user_guards {sevm : Sevm} {pre post : Devm}
    (effect : FrameEffect sevm pre post) (user : sevm.caller ≠ systemAddress) :
    pre.getStorVal sevm.currentTarget 0 ≠ B256.max ∧
    (sevm.data.length = 56 ∨ (sevm.data = [] ∧ sevm.value = 0)) := by
  cases effect with
  | system caller _ _ _ => exact False.elim (user caller)
  | submission _ _ length active _ _ _ _ _ _ => exact ⟨active, Or.inl length⟩
  | getter _ empty value active _ _ _ _ _ _ => exact ⟨active, Or.inr ⟨empty, value⟩⟩

/-- Static success is exactly the getter branch of the successful effect relation. -/
theorem FrameEffect.static_getter {sevm : Sevm} {pre post : Devm}
    (effect : FrameEffect sevm pre post) (static : sevm.isStatic = true) :
    sevm.caller ≠ systemAddress ∧ sevm.data = [] ∧ sevm.value = 0 ∧
    pre.getStorVal sevm.currentTarget 0 ≠ B256.max ∧
    ∃ iterations finalOutput,
      WordFakeExponential.Run (pre.getStorVal sevm.currentTarget 0)
        17 1 17 0 iterations finalOutput ∧
      ∃ gas, post = feeGetterPost (afterSload sevm pre 0) pre.memory (finalOutput / 17) gas ∧
        post.output = (finalOutput / (17 : B256)).toBytes := by
  cases effect with
  | system _ dynamic _ _ => exact Bool.noConfusion (static.symm.trans dynamic)
  | submission _ dynamic _ _ _ _ _ _ _ _ => exact Bool.noConfusion (static.symm.trans dynamic)
  | getter caller empty value active iterations finalOutput fee gas state output =>
    exact ⟨caller, empty, value, active, iterations, finalOutput, fee, gas, state, output⟩

/-- Successful static effects preserve every storage cell, log and balance. -/
theorem FrameEffect.static_preserves {sevm : Sevm} {pre post : Devm}
    (effect : FrameEffect sevm pre post) (static : sevm.isStatic = true) :
    (∀ address, post.getStor address = pre.getStor address) ∧
    post.logs = pre.logs ∧ (∀ address, post.getBal address = pre.getBal address) := by
  obtain ⟨_, _, _, _, _, finalOutput, _, gas, state, _⟩ := effect.static_getter static
  rw [state]
  have preserved := feeGetterPost_preserves (afterSload sevm pre 0) pre.memory
    (finalOutput / 17) gas
  refine ⟨?_, ?_, ?_⟩
  · intro address
    rw [preserved.1 address, afterSload_getStor]
  · rw [preserved.2.2.1, afterSload_logs]
  · intro address
    rw [preserved.2.1 address]
    simp only [Devm.getBal, afterSload_getAcct]

/-- Every successful canonical frame preserves balances, foreign storage and inherited error. -/
theorem exec_frame_preserves {sevm : Sevm} {pre post : Devm}
    (code : sevm.code = Blanc.withdrawalRequestCode)
    (fork : CoveredFork sevm.benvStat.fork) (stack : pre.stack = [])
    (aligned : pre.memory.size % 32 = 0) (wf : Mem.Wf pre.memory)
    (lengthBound : sevm.data.length < 2 ^ 256) (exec : Exec 0 sevm pre (.ok post)) :
    (∀ address, post.getBal address = pre.getBal address) ∧
    (∀ address, address ≠ sevm.currentTarget → post.getStor address = pre.getStor address) ∧
    post.error = pre.error := by
  exact (exec_frame_effect code fork stack aligned wf lengthBound exec).preserves

/-- A successful static canonical frame is a zero-value, empty-calldata fee read. -/
theorem exec_static_frame {sevm : Sevm} {pre post : Devm}
    (code : sevm.code = Blanc.withdrawalRequestCode)
    (fork : CoveredFork sevm.benvStat.fork) (stack : pre.stack = [])
    (aligned : pre.memory.size % 32 = 0) (wf : Mem.Wf pre.memory)
    (lengthBound : sevm.data.length < 2 ^ 256) (static : sevm.isStatic = true)
    (exec : Exec 0 sevm pre (.ok post)) :
    sevm.caller ≠ systemAddress ∧ sevm.data = [] ∧ sevm.value = 0 ∧
    pre.getStorVal sevm.currentTarget 0 ≠ B256.max ∧
    (∃ iterations finalOutput,
      WordFakeExponential.Run (pre.getStorVal sevm.currentTarget 0)
        17 1 17 0 iterations finalOutput ∧
      ∃ gas, post = feeGetterPost (afterSload sevm pre 0) pre.memory (finalOutput / 17) gas ∧
        post.output = (finalOutput / (17 : B256)).toBytes) ∧
    (∀ address, post.getStor address = pre.getStor address) ∧ post.logs = pre.logs ∧
    (∀ address, post.getBal address = pre.getBal address) := by
  have effect := exec_frame_effect code fork stack aligned wf lengthBound exec
  obtain ⟨caller, empty, value, active, getter⟩ := effect.static_getter static
  exact ⟨caller, empty, value, active, getter, effect.static_preserves static⟩

/-- Invalid literal user length excludes success; this does not construct REVERT. -/
theorem exec_user_bad_length_no_ok {sevm : Sevm} {pre post : Devm}
    (code : sevm.code = Blanc.withdrawalRequestCode)
    (fork : CoveredFork sevm.benvStat.fork) (stack : pre.stack = [])
    (aligned : pre.memory.size % 32 = 0) (wf : Mem.Wf pre.memory)
    (lengthBound : sevm.data.length < 2 ^ 256) (user : sevm.caller ≠ systemAddress)
    (nonempty : sevm.data.length ≠ 0) (wrong : sevm.data.length ≠ 56)
    (exec : Exec 0 sevm pre (.ok post)) : False := by
  have effect := exec_frame_effect code fork stack aligned wf lengthBound exec
  rcases (effect.user_guards user).2 with length | ⟨empty, _⟩
  · exact wrong length
  · exact nonempty (congrArg List.length empty)

/-- Empty user input with value excludes success; no revert/gas construction is asserted. -/
theorem exec_user_value_no_ok {sevm : Sevm} {pre post : Devm}
    (code : sevm.code = Blanc.withdrawalRequestCode)
    (fork : CoveredFork sevm.benvStat.fork) (stack : pre.stack = [])
    (aligned : pre.memory.size % 32 = 0) (wf : Mem.Wf pre.memory)
    (lengthBound : sevm.data.length < 2 ^ 256) (user : sevm.caller ≠ systemAddress)
    (empty : sevm.data = []) (value : sevm.value ≠ 0)
    (exec : Exec 0 sevm pre (.ok post)) : False := by
  have effect := exec_frame_effect code fork stack aligned wf lengthBound exec
  rcases (effect.user_guards user).2 with length | ⟨_, zero⟩
  · simp only [empty, List.length_nil] at length
    exact (by decide : (0 : Nat) ≠ 56) length
  · exact value zero

/-- An inhibited user frame admits no successful execution. -/
theorem exec_user_inhibited_no_ok {sevm : Sevm} {pre post : Devm}
    (code : sevm.code = Blanc.withdrawalRequestCode)
    (fork : CoveredFork sevm.benvStat.fork) (stack : pre.stack = [])
    (aligned : pre.memory.size % 32 = 0) (wf : Mem.Wf pre.memory)
    (lengthBound : sevm.data.length < 2 ^ 256) (user : sevm.caller ≠ systemAddress)
    (inhibited : pre.getStorVal sevm.currentTarget 0 = B256.max)
    (exec : Exec 0 sevm pre (.ok post)) : False := by
  exact ((exec_frame_effect code fork stack aligned wf lengthBound exec).user_guards user).1 inhibited

/-- The literal submission branch ends in STOP with inherited output. -/
theorem exec_submission_output {sevm : Sevm} {pre post : Devm}
    (code : sevm.code = Blanc.withdrawalRequestCode)
    (fork : CoveredFork sevm.benvStat.fork) (stack : pre.stack = [])
    (user : sevm.caller ≠ systemAddress) (length : sevm.data.length = 56)
    (exec : Exec 0 sevm pre (.ok post)) : post.output = pre.output := by
  obtain ⟨_, _, _, _, _, _, gas, state⟩ := exec_submission code fork stack user length exec
  rw [state, (submissionPost_inherited _ _ _ gas).1, afterSload_output]

/-- The system branch returns its actual queue-memory slice. -/
theorem exec_system_output {sevm : Sevm} {pre post : Devm}
    (code : sevm.code = Blanc.withdrawalRequestCode)
    (fork : CoveredFork sevm.benvStat.fork) (stack : pre.stack = [])
    (caller : sevm.caller = systemAddress) (exec : Exec 0 sevm pre (.ok post)) :
    post.output = ((systemQueuePost sevm pre pre.memory).memory.read 0
      (76 * (systemCount sevm pre).toNat)).1 := by
  obtain ⟨_, gas, state⟩ := exec_system_frame code fork stack caller exec
  rw [state, systemFramePost_output]

end Blanc.Lift.WithdrawalRequest
