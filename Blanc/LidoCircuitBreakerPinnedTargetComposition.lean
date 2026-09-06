import Blanc.LidoCircuitBreakerPinnedTargetControl

/-!
# CircuitBreaker composition with a pinned pause target

This module discharges the two semantic seams left abstract by
`LidoCircuitBreakerPinnedTarget`: retained target-frame writes are replayed
through the actual CALL and STATICCALL spawns, and the successful observation
suffix is framed pointwise outside the caller's expiry slot.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune

private theorem replayCell_eq_of_none
    {owner : Adr} {key initial : B256}
    {writes : List Exec.StorageWrite}
    (none : ∀ write ∈ writes, write.matches owner key ≠ true) :
    Exec.StorageWrite.replayCell owner key initial writes = initial := by
  induction writes generalizing initial with
  | nil => rfl
  | cons head tail ih =>
      simp only [Exec.StorageWrite.replayCell, List.foldl_cons]
      rw [if_neg (none head (by simp))]
      exact ih (by
        intro write member
        exact none write (by simp [member]))

private theorem pinnedPause_cell_eq
    {sevm : Sevm} {target : Adr} {program : Prog} {duration : B256}
    {pausedUntil : Adr → Stor → B256} {surface : List B256}
    {callPre callPost : Devm} {key : B256}
    (bundle : LidoPinnedPauseTarget sevm.currentTarget sevm.caller target
      program pausedUntil surface)
    (pinned : PinnedPauseBoundaryExecutesProgram
      sevm target program duration callPre callPost)
    (member : key ∈
      [countSlot sevm.caller.toB256, heartbeatIntervalSlot]) :
    callPost.getStorVal sevm.currentTarget key =
      callPre.getStorVal sevm.currentTarget key := by
  rcases pinned with
    ⟨msg, xl, child, pc, nextPc, resume, exactCall, executes, time,
      spawn, filled, process, stepRun, childState, childOutput⟩
  rcases executes with ⟨uses, childEvm, raw, slotEq, rawNonempty⟩
  subst xl
  rcases rawNonempty with ⟨rawRun⟩
  have callSpawn : Xinst.step sevm callPre .call =
      .spawn (Jaune.Frame.ofCall msg) resume :=
    XStep.toStep_spawn (by
      simpa only [Ninst.call, Ninst.step_exec] using spawn)
  unfold Ninst.StepRun at stepRun
  rw [spawn] at stepRun
  obtain ⟨result, frameRun, resumeRun⟩ := stepRun
  have replay := Xinst.storageReplay_some_of_body callSpawn frameRun
    resumeRun.symm (fun committed =>
      Exec.storageReplay_committedPost rawRun committed)
  have noWrite := bundle.circuitBreaker_noninterference
    (Or.inl ⟨duration, exactCall⟩)
    ⟨uses, childEvm, raw, rfl, ⟨rawRun⟩⟩ process key member
  have noWriteRun :
      Exec.NoRetainedWriteTo rawRun sevm.currentTarget key :=
    noWrite rawRun
  change (Devm.getStor callPost sevm.currentTarget).get key =
    (Devm.getStor callPre sevm.currentTarget).get key
  rw [replay sevm.currentTarget key]
  split
  · exact replayCell_eq_of_none noWriteRun
  · rfl

private theorem pinnedStat_cell_eq
    {sevm : Sevm} {target : Adr} {program : Prog}
    {pausedUntil : Adr → Stor → B256} {surface : List B256}
    {statPre statPost : Devm} {key : B256}
    (bundle : LidoPinnedPauseTarget sevm.currentTarget sevm.caller target
      program pausedUntil surface)
    (pinned : PinnedStatBoundaryExecutesProgram
      sevm target program statPre statPost)
    (member : key ∈
      [countSlot sevm.caller.toB256, heartbeatIntervalSlot]) :
    statPost.getStorVal sevm.currentTarget key =
      statPre.getStorVal sevm.currentTarget key := by
  rcases pinned with
    ⟨msg, xl, child, pc, nextPc, resume, exactCall, executes, time,
      spawn, filled, process, stepRun, childState, childOutput⟩
  rcases executes with ⟨uses, childEvm, raw, slotEq, rawNonempty⟩
  subst xl
  rcases rawNonempty with ⟨rawRun⟩
  have statSpawn : Xinst.step sevm statPre .staticcall =
      .spawn (Jaune.Frame.ofCall msg) resume :=
    XStep.toStep_spawn (by
      simpa only [Ninst.staticcall, Ninst.step_exec] using spawn)
  unfold Ninst.StepRun at stepRun
  rw [spawn] at stepRun
  obtain ⟨result, frameRun, resumeRun⟩ := stepRun
  have replay := Xinst.storageReplay_some_of_body statSpawn frameRun
    resumeRun.symm (fun committed =>
      Exec.storageReplay_committedPost rawRun committed)
  have noWrite := bundle.circuitBreaker_noninterference
    (Or.inr exactCall)
    ⟨uses, childEvm, raw, rfl, ⟨rawRun⟩⟩ process key member
  have noWriteRun :
      Exec.NoRetainedWriteTo rawRun sevm.currentTarget key :=
    noWrite rawRun
  change (Devm.getStor statPost sevm.currentTarget).get key =
    (Devm.getStor statPre sevm.currentTarget).get key
  rw [replay sevm.currentTarget key]
  split
  · exact replayCell_eq_of_none noWriteRun
  · rfl

private theorem revertCall_not_ok
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {slot : Nat}
    (lookup : fs[slot]? = some Func.revert)
    (run : Func.RunCompiledTo fs sevm pre (Func.call slot) (.ok post)) :
    False := by
  obtain ⟨_, -, body⟩ := runCompiledTo_call_inv lookup run
  obtain ⟨_, hex, -⟩ := runCompiledTo_revert_inv body
  cases hex

private theorem bubbleCall_not_ok
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (lookup : fs[bubbleRevertSlot]? = some Func.revertReturnData)
    (run : Func.RunCompiledTo fs sevm pre
      (Func.call bubbleRevertSlot) (.ok post)) :
    False := by
  obtain ⟨_, -, body⟩ := runCompiledTo_call_inv lookup run
  rcases Func.runCompiledTo_revertReturnData_inv body with
    ⟨_, hex⟩ | ⟨_, hex, -⟩ <;> cases hex

private theorem failedCall_not_ok
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (lookup : fs[pauseFailedErrorSlot]? = some pauseFailedError)
    (run : Func.RunCompiledTo fs sevm pre
      (Func.call pauseFailedErrorSlot) (.ok post)) :
    False := by
  obtain ⟨_, -, body⟩ := runCompiledTo_call_inv lookup run
  rw [show pauseFailedError =
    Func.revertSelector (customErrorData "PauseFailed")
      (by simp [customErrorData, B256.length_toBytes]) from rfl] at body
  rcases runCompiledTo_revertSelector_inv body with
    ⟨_, hex⟩ | ⟨_, hex, -⟩ <;> cases hex

/-- A successful observation/decode/success suffix frames every persistent
cell other than the caller's expiry slot. -/
theorem observation_ok_getStorVal_eq_of_ne
    {fs : List Func} {sevm : Sevm} {statPost final : Devm}
    {owner : Adr} {key : B256}
    (h_empty : fs[emptyRevertSlot]? = some Func.revert)
    (h_bubble : fs[bubbleRevertSlot]? = some Func.revertReturnData)
    (h_failed : fs[pauseFailedErrorSlot]? = some pauseFailedError)
    (h_panic : fs[arithmeticPanicSlot]? =
      some (Func.revertData heartbeatArithmeticPanicData))
    (different : (owner, key) ≠
      (sevm.currentTarget, expirySlot sevm.caller.toB256))
    (run : Func.RunCompiledTo fs sevm statPost
      (Ninst.iszero :::
        ((Func.call bubbleRevertSlot) <?> decodePausedResult))
      (.ok final)) :
    final.getStorVal owner key = statPost.getStorVal owner key := by
  obtain ⟨branchPost, hiszero, run⟩ := runCompiledTo_next_inv run
  have hstorIszero : Devm.getStor statPost = Devm.getStor branchPost :=
    Ninst.Hinv.inv (f := Devm.getStor)
      (Ninst.Run.of_runCompiled hiszero)
  rcases runCompiledTo_branch_inv run with
    ⟨decodePre, -, hobservationPop, decodeRun⟩ |
      ⟨_, bubblePre, -, -, -, bubbleRun⟩
  · have hstorDecode : Devm.getStor statPost = Devm.getStor decodePre :=
      hstorIszero.trans
        (PopBurn.Inv.inv (Devm.PopBurn.of_popBurnBy hobservationPop))
    rw [decodePausedResult] at decodeRun
    obtain ⟨guardPost, hguard, decodeRun⟩ :=
      runCompiledTo_prepend_inv decodeRun
    have hstorGuard : Devm.getStor decodePre = Devm.getStor guardPost :=
      Line.of_inv Devm.getStor
        (by unfold returnDataShorterThan; line_inv) hguard
    rcases runCompiledTo_branch_inv decodeRun with
      ⟨loadPre, -, hguardPop, loadRun⟩ |
        ⟨_, emptyPre, -, -, -, emptyRun⟩
    · obtain ⟨loadPost, hload, loadRun⟩ :=
        runCompiledTo_prepend_inv loadRun
      obtain ⟨dupPost, hdup, loadRun⟩ := runCompiledTo_next_inv loadRun
      obtain ⟨zeroPost, hzero, loadRun⟩ := runCompiledTo_next_inv loadRun
      rcases runCompiledTo_branch_inv loadRun with
        ⟨canonicalPre, -, hzeroPop, canonicalRun⟩ |
          ⟨_, failedPre, -, -, -, failedRun⟩
      · obtain ⟨onePost, hone, canonicalRun⟩ :=
          runCompiledTo_next_inv canonicalRun
        obtain ⟨eqPost, heq, canonicalRun⟩ :=
          runCompiledTo_next_inv canonicalRun
        rcases runCompiledTo_branch_inv canonicalRun with
          ⟨emptyPre, -, -, emptyRun⟩ |
            ⟨_, successPre, -, -, hsuccessPop, successRun⟩
        · exact (revertCall_not_ok h_empty emptyRun).elim
        · have hprefix : Devm.getStor statPost =
              Devm.getStor successPre := by
            calc
              Devm.getStor statPost = Devm.getStor decodePre := hstorDecode
              _ = Devm.getStor guardPost := hstorGuard
              _ = Devm.getStor loadPre :=
                PopBurn.Inv.inv (Devm.PopBurn.of_popBurnBy hguardPop)
              _ = Devm.getStor loadPost :=
                Line.of_inv Devm.getStor
                  (by unfold loadWord; line_inv) hload
              _ = Devm.getStor dupPost :=
                Ninst.Hinv.inv (f := Devm.getStor)
                  (Ninst.Run.of_runCompiled hdup)
              _ = Devm.getStor zeroPost :=
                Ninst.Hinv.inv (f := Devm.getStor)
                  (Ninst.Run.of_runCompiled hzero)
              _ = Devm.getStor canonicalPre :=
                PopBurn.Inv.inv (Devm.PopBurn.of_popBurnBy hzeroPop)
              _ = Devm.getStor onePost :=
                Ninst.Hinv.inv (f := Devm.getStor)
                  (Ninst.Run.of_runCompiled hone)
              _ = Devm.getStor eqPost :=
                Ninst.Hinv.inv (f := Devm.getStor)
                  (Ninst.Run.of_runCompiled heq)
              _ = Devm.getStor successPre :=
                PopBurn.Inv.inv (Devm.PopBurn.of_popBurnBy hsuccessPop)
          exact (pauseSuccess_ok_getStorVal_eq_of_ne h_panic different
            successRun).trans
              (congrArg (fun stor => (stor owner).get key) hprefix).symm
      · exact (failedCall_not_ok h_failed failedRun).elim
    · exact (revertCall_not_ok h_empty emptyRun).elim
  · exact (bubbleCall_not_ok h_bubble bubbleRun).elim

/-- A successful observation/decode/success suffix preserves the complete
persistent-storage map of every account other than the CircuitBreaker. -/
theorem observation_ok_getStor_eq_of_owner_ne
    {fs : List Func} {sevm : Sevm} {statPost final : Devm} {owner : Adr}
    (h_empty : fs[emptyRevertSlot]? = some Func.revert)
    (h_bubble : fs[bubbleRevertSlot]? = some Func.revertReturnData)
    (h_failed : fs[pauseFailedErrorSlot]? = some pauseFailedError)
    (h_panic : fs[arithmeticPanicSlot]? =
      some (Func.revertData heartbeatArithmeticPanicData))
    (ownerNe : owner ≠ sevm.currentTarget)
    (run : Func.RunCompiledTo fs sevm statPost
      (Ninst.iszero :::
        ((Func.call bubbleRevertSlot) <?> decodePausedResult))
      (.ok final)) :
    Devm.getStor final owner = Devm.getStor statPost owner := by
  obtain ⟨branchPost, hiszero, run⟩ := runCompiledTo_next_inv run
  have hstorIszero : Devm.getStor statPost = Devm.getStor branchPost :=
    Ninst.Hinv.inv (f := Devm.getStor)
      (Ninst.Run.of_runCompiled hiszero)
  rcases runCompiledTo_branch_inv run with
    ⟨decodePre, -, hobservationPop, decodeRun⟩ |
      ⟨_, bubblePre, -, -, -, bubbleRun⟩
  · have hstorDecode : Devm.getStor statPost = Devm.getStor decodePre :=
      hstorIszero.trans
        (PopBurn.Inv.inv (Devm.PopBurn.of_popBurnBy hobservationPop))
    rw [decodePausedResult] at decodeRun
    obtain ⟨guardPost, hguard, decodeRun⟩ :=
      runCompiledTo_prepend_inv decodeRun
    have hstorGuard : Devm.getStor decodePre = Devm.getStor guardPost :=
      Line.of_inv Devm.getStor
        (by unfold returnDataShorterThan; line_inv) hguard
    rcases runCompiledTo_branch_inv decodeRun with
      ⟨loadPre, -, hguardPop, loadRun⟩ |
        ⟨_, emptyPre, -, -, -, emptyRun⟩
    · obtain ⟨loadPost, hload, loadRun⟩ :=
        runCompiledTo_prepend_inv loadRun
      obtain ⟨dupPost, hdup, loadRun⟩ := runCompiledTo_next_inv loadRun
      obtain ⟨zeroPost, hzero, loadRun⟩ := runCompiledTo_next_inv loadRun
      rcases runCompiledTo_branch_inv loadRun with
        ⟨canonicalPre, -, hzeroPop, canonicalRun⟩ |
          ⟨_, failedPre, -, -, -, failedRun⟩
      · obtain ⟨onePost, hone, canonicalRun⟩ :=
          runCompiledTo_next_inv canonicalRun
        obtain ⟨eqPost, heq, canonicalRun⟩ :=
          runCompiledTo_next_inv canonicalRun
        rcases runCompiledTo_branch_inv canonicalRun with
          ⟨emptyPre, -, -, emptyRun⟩ |
            ⟨_, successPre, -, -, hsuccessPop, successRun⟩
        · exact (revertCall_not_ok h_empty emptyRun).elim
        · have hprefix : Devm.getStor statPost =
              Devm.getStor successPre := by
            calc
              Devm.getStor statPost = Devm.getStor decodePre := hstorDecode
              _ = Devm.getStor guardPost := hstorGuard
              _ = Devm.getStor loadPre :=
                PopBurn.Inv.inv (Devm.PopBurn.of_popBurnBy hguardPop)
              _ = Devm.getStor loadPost :=
                Line.of_inv Devm.getStor
                  (by unfold loadWord; line_inv) hload
              _ = Devm.getStor dupPost :=
                Ninst.Hinv.inv (f := Devm.getStor)
                  (Ninst.Run.of_runCompiled hdup)
              _ = Devm.getStor zeroPost :=
                Ninst.Hinv.inv (f := Devm.getStor)
                  (Ninst.Run.of_runCompiled hzero)
              _ = Devm.getStor canonicalPre :=
                PopBurn.Inv.inv (Devm.PopBurn.of_popBurnBy hzeroPop)
              _ = Devm.getStor onePost :=
                Ninst.Hinv.inv (f := Devm.getStor)
                  (Ninst.Run.of_runCompiled hone)
              _ = Devm.getStor eqPost :=
                Ninst.Hinv.inv (f := Devm.getStor)
                  (Ninst.Run.of_runCompiled heq)
              _ = Devm.getStor successPre :=
                PopBurn.Inv.inv (Devm.PopBurn.of_popBurnBy hsuccessPop)
          exact (pauseSuccess_ok_getStor_eq_of_owner_ne h_panic ownerNe
            successRun).trans (congrFun hprefix owner).symm
      · exact (failedCall_not_ok h_failed failedRun).elim
    · exact (revertCall_not_ok h_empty emptyRun).elim
  · exact (bubbleCall_not_ok h_bubble bubbleRun).elim

private theorem pinnedTrace_final_cell_eq
    {fs : List Func} {sevm : Sevm} {entry final : Devm}
    {target : Adr} {program : Prog} {duration : B256}
    {pausedUntil : Adr → Stor → B256} {surface : List B256}
    {ex : Execution} {key : B256}
    (h_empty : fs[emptyRevertSlot]? = some Func.revert)
    (h_bubble : fs[bubbleRevertSlot]? = some Func.revertReturnData)
    (h_failed : fs[pauseFailedErrorSlot]? = some pauseFailedError)
    (h_panic : fs[arithmeticPanicSlot]? =
      some (Func.revertData heartbeatArithmeticPanicData))
    (bundle : LidoPinnedPauseTarget sevm.currentTarget sevm.caller target
      program pausedUntil surface)
    (hook : LidoPinnedBoundaryExecutions fs sevm entry target program
      duration ex)
    (hex : ex = .ok final)
    (member : key ∈
      [countSlot sevm.caller.toB256, heartbeatIntervalSlot])
    (different : (sevm.currentTarget, key) ≠
      (sevm.currentTarget, expirySlot sevm.caller.toB256)) :
    final.getStorVal sevm.currentTarget key =
      entry.getStorVal sevm.currentTarget key := by
  rcases hook with
    ⟨-, guardTestPost, guardPost, callPre, callPost, branchTestPost,
      armPre, statPre, statPost, guardRun, guardPop, callStaging,
      -, -, pinnedPause, -, callIszero, branchPop, statStaging,
      -, -, pinnedStat, observationRun⟩
  rw [hex] at observationRun
  let cell : Devm → B256 := fun state ↦
    state.getStorVal sevm.currentTarget key
  have guardEq : cell guardTestPost = cell entry :=
    congrArg (fun stor : Adr → Stor ↦ (stor sevm.currentTarget).get key)
      (Line.of_inv Devm.getStor
        (by unfold pauseCodeGuard loadWord; line_inv) guardRun).symm
  have guardPopEq : cell guardPost = cell guardTestPost :=
    congrArg (fun stor : Adr → Stor ↦ (stor sevm.currentTarget).get key)
      (PopBurn.Inv.inv (f := Devm.getStor)
        (Devm.PopBurn.of_popBurnBy guardPop)).symm
  have callStagingEq : cell callPre = cell guardPost :=
    congrArg (fun stor : Adr → Stor ↦ (stor sevm.currentTarget).get key)
      (pauseCallStaging_storInv callStaging).symm
  have callEq : cell callPost = cell callPre :=
    pinnedPause_cell_eq bundle pinnedPause member
  have branchTestEq : cell branchTestPost = cell callPost :=
    congrArg (fun stor : Adr → Stor ↦ (stor sevm.currentTarget).get key)
      (Ninst.Hinv.inv (f := Devm.getStor)
        (Ninst.Run.of_runCompiled callIszero)).symm
  have branchPopEq : cell armPre = cell branchTestPost :=
    congrArg (fun stor : Adr → Stor ↦ (stor sevm.currentTarget).get key)
      (PopBurn.Inv.inv (f := Devm.getStor)
        (Devm.PopBurn.of_popBurnBy branchPop)).symm
  have statStagingEq : cell statPre = cell armPre :=
    congrArg (fun stor : Adr → Stor ↦ (stor sevm.currentTarget).get key)
      (pauseStatStaging_storInv statStaging).symm
  have statEq : cell statPost = cell statPre :=
    pinnedStat_cell_eq bundle pinnedStat member
  have observationEq : cell final = cell statPost :=
    observation_ok_getStorVal_eq_of_ne h_empty h_bubble h_failed h_panic
      different observationRun
  exact observationEq.trans <| statEq.trans <| statStagingEq.trans <|
    branchPopEq.trans <| branchTestEq.trans <| callEq.trans <|
      callStagingEq.trans <| guardPopEq.trans guardEq

private theorem canonicalAddress_toB256_local (a : Adr) :
    canonicalAddress a.toB256 := by
  have wordNat : a.toB256.toNat = a.toNat := by
    simp [Adr.toB256, Adr.toNat, B256.toNat, B128.toNat]
  show a.toB256.toNat < 2 ^ 160
  rw [wordNat]
  exact Adr.toNat_lt_size a

private theorem pinnedTrace_noninterference
    {fs : List Func} {sevm : Sevm} {entry final : Devm}
    {target : Adr} {program : Prog} {duration : B256}
    {pausedUntil : Adr → Stor → B256} {surface : List B256}
    {ex : Execution}
    (h_empty : fs[emptyRevertSlot]? = some Func.revert)
    (h_bubble : fs[bubbleRevertSlot]? = some Func.revertReturnData)
    (h_failed : fs[pauseFailedErrorSlot]? = some pauseFailedError)
    (h_panic : fs[arithmeticPanicSlot]? =
      some (Func.revertData heartbeatArithmeticPanicData))
    (bundle : LidoPinnedPauseTarget sevm.currentTarget sevm.caller target
      program pausedUntil surface)
    (hook : LidoPinnedBoundaryExecutions fs sevm entry target program
      duration ex)
    (hex : ex = .ok final) :
    ∀ successPre,
      Func.RunCompiledTo fs sevm successPre pauseSuccess ex →
        PauseSuccessNoninterference sevm entry successPre := by
  intro successPre successRun
  rw [hex] at successRun
  have callerCanonical := canonicalAddress_toB256_local sevm.caller
  have countDifferent :
      (sevm.currentTarget, countSlot sevm.caller.toB256) ≠
        (sevm.currentTarget, expirySlot sevm.caller.toB256) := by
    intro equal
    exact (expirySlot_ne_registryAddressFamilies callerCanonical
      callerCanonical callerCanonical).2.2
        (congrArg Prod.snd equal).symm
  have intervalDifferent :
      (sevm.currentTarget, heartbeatIntervalSlot) ≠
        (sevm.currentTarget, expirySlot sevm.caller.toB256) := by
    intro equal
    exact expirySlot_ne_heartbeatIntervalSlot sevm.caller.toB256
      callerCanonical (congrArg Prod.snd equal).symm
  constructor
  · exact (pauseSuccess_ok_getStorVal_eq_of_ne h_panic countDifferent
      successRun).symm.trans
        (pinnedTrace_final_cell_eq h_empty h_bubble h_failed h_panic
          bundle hook hex (by simp) countDifferent)
  · exact (pauseSuccess_ok_getStorVal_eq_of_ne h_panic intervalDifferent
      successRun).symm.trans
        (pinnedTrace_final_cell_eq h_empty h_bubble h_failed h_panic
          bundle hook hex (by simp) intervalDifferent)

private theorem runFrame_result_unique
    {frame : Jaune.Frame} {xl : Xlot}
    {left right : TargetMessageResult}
    (leftRun : RunFrame frame xl left)
    (rightRun : RunFrame frame xl right) : left = right := by
  cases enter : frame.enter with
  | done result =>
    simp only [RunFrame, enter] at leftRun rightRun
    exact leftRun.2.trans rightRun.2.symm
  | run evm =>
    simp only [RunFrame, enter] at leftRun rightRun
    rcases leftRun with ⟨leftRaw, leftSlot, leftResult⟩
    rcases rightRun with ⟨rightRaw, rightSlot, rightResult⟩
    rw [leftSlot] at rightSlot
    injection rightSlot with pairEq
    have rawEq : leftRaw = rightRaw := congrArg Prod.snd pairEq
    subst rightRaw
    exact leftResult.trans rightResult.symm

private theorem stepCall_spawn_resume
    {sevm : Sevm} {pre : Devm} {msg : Msg} {resume : Resume}
    (spawn : Xinst.step sevm pre .call =
      .spawn (Jaune.Frame.ofCall msg) resume) :
    ∃ parent oi os, resume = .call parent oi os := by
  simp only [Xinst.step, Bind.bind, Except.bind] at spawn
  repeat' split at spawn
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at spawn
  all_goals first
    | cases spawn
    | exact ⟨_, _, _, (genericCall_step_spawn_exact spawn).2⟩

private theorem stepStaticcall_spawn_resume
    {sevm : Sevm} {pre : Devm} {msg : Msg} {resume : Resume}
    (spawn : Xinst.step sevm pre .staticcall =
      .spawn (Jaune.Frame.ofCall msg) resume) :
    ∃ parent oi os, resume = .call parent oi os := by
  simp only [Xinst.step, Bind.bind, Except.bind, Pure.pure, Except.pure] at spawn
  repeat' split at spawn
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at spawn
  all_goals first
    | cases spawn
    | exact ⟨_, _, _, (genericCall_step_spawn_exact spawn).2⟩

private theorem stubCode_nonempty :
    PinnedTargetControl.stubCode ≠ .empty := by
  decide +kernel

private theorem stubCode_not_delegation :
    ¬ isValidDelegation PinnedTargetControl.stubCode := by
  decide +kernel

private theorem stubProgram_compile_toList :
    Prog.compile PinnedTargetControl.stubProgram =
      some PinnedTargetControl.stubCode.toList := by
  rw [PinnedTargetControl.stubProgram_compile]
  simp [PinnedTargetControl.stubCode, PinnedTargetControl.stubBytes,
    ByteArray.toList_eq_toList_data]

private theorem stubCode_toList_nonempty :
    PinnedTargetControl.stubCode.toList ≠ [] := by
  decide +kernel

/-- Directly installed code is not a delegation designator, so at a state with
that code at `target` the resolved code address a spawned call carries is
`target` itself.

This is the *direct-installation* arm of the seam.  A later proxy revisit
replaces exactly this step — and nothing else in the crossing below — with a
proxy/implementation correspondence. -/
private theorem resolvedCodeAddress_of_direct
    {pre : Devm} {target : Adr} {code : ByteArray}
    (installed : pre.getCode target = code)
    (notDelegation : ¬ isValidDelegation code) :
    (getDelegatedCodeAddress (pre.getCode target)).getD target = target := by
  rw [installed]
  dsimp only [getDelegatedCodeAddress]
  rw [if_neg notDelegation]
  rfl

/-- An actual non-precompile spawn from a state with `program`'s compiled bytes
directly installed carries a retained execution of that program in its own
slot.

Nothing here is specific to a target: the message's code is derived from the
spawn source, and the three code facts are exactly what rules out the empty,
self and delegated sources.  The conclusion is the shared
`MessageExecutesProgram` predicate, so a caller obtains a real program
occurrence rather than a code-shaped assumption. -/
private theorem spawnedMessage_executesProgram
    {sevm : Sevm} {pre : Devm} {target : Adr}
    {code : ByteArray} {program : Prog}
    {msg : Msg} {xl : Xlot} {child : Devm} {resume : Resume} {x : Xinst}
    (compiled : Prog.compile program = some code.toList)
    (nonempty : code ≠ .empty)
    (notDelegation : ¬ isValidDelegation code)
    (targetNe : target ≠ sevm.currentTarget)
    (installed : pre.getCode target = code)
    (nonprecompile : sevm.benvStat.rules.isPrecomp target = false)
    (currentTarget : msg.currentTarget = target)
    (codeAddress : msg.codeAddress = some target)
    (valueZero : msg.value = 0)
    (transferValue : msg.shouldTransferValue = true)
    (sameRules : msg.benv.stat.rules = sevm.benvStat.rules)
    (spawn : Xinst.step sevm pre x =
      .spawn (Jaune.Frame.ofCall msg) resume)
    (filled : Xlot.Filled xl)
    (process : ProcessMessage msg xl (.ok child)) :
    MessageExecutesProgram msg xl program := by
  have codeEq : msg.code = code := by
    rcases Xinst.step_spawn_source spawn with empty | same | source
    · have impossible : code = .empty := by
        simpa only [Jaune.Frame.ofCall, currentTarget, installed] using empty
      exact (nonempty impossible).elim
    · have impossible : target = sevm.currentTarget := by
        simpa only [Jaune.Frame.ofCall, currentTarget] using same
      exact (targetNe impossible).elim
    · have direct := source (by
        change ¬ isValidDelegation (pre.getCode msg.currentTarget)
        rw [currentTarget, installed]
        exact notDelegation)
      simpa only [Jaune.Frame.ofCall, currentTarget, installed] using direct
  have uses : MessageUsesProgram msg program := by
    unfold MessageUsesProgram
    rw [codeEq]
    exact compiled.symm
  have affordable : ¬ msg.benv.state.bal msg.caller < msg.value := by
    rw [valueZero]
    rw [B256.lt_iff_toNat_lt_toNat]
    exact Nat.not_lt.mpr (Nat.zero_le _)
  obtain ⟨stmid, -, afterTransfer⟩ :=
    Msg.benvAfterTransfer_of_affordable msg transferValue affordable
  let benv := (msg.benv.withState stmid).addBal msg.currentTarget msg.value
  have enter : (Jaune.Frame.ofCall msg).enter =
      .run (initEvm (msg.withBenv benv)) := by
    apply Frame.enter_run_of_nonprecompile afterTransfer
    · exact codeAddress
    · change msg.benv.stat.rules.isPrecomp target = false
      rw [sameRules]
      exact nonprecompile
  unfold ProcessMessage RunFrame at process
  rw [enter] at process
  rcases process with ⟨raw, slotEq, -⟩
  subst xl
  exact ⟨uses, initEvm (msg.withBenv benv), raw, rfl, filled⟩

private theorem runCompiled_getCode_eq_of_nonempty
    {sevm : Sevm} {pre post : Devm} {n : Ninst} {owner : Adr}
    (run : Ninst.RunCompiled sevm pre n post)
    (nonempty : (pre.getCode owner).toList ≠ []) :
    post.getCode owner = pre.getCode owner := by
  rcases run with ⟨xl, filled, steps⟩
  have slotCode : Xlot.Rel Devm.CodePreserve xl := by
    rcases xl with _ | ⟨evm, raw⟩
    · trivial
    · rcases filled with ⟨childRun⟩
      cases raw <;> exact Exec.preserves_getCode childRun
  exact Ninst.codePreserve_effectRec n slotCode (steps 0) owner nonempty

/-- **The direct-installation crossing.**  A successful `pauseAfterSet` suffix,
run against an account carrying `program`'s exact compiled bytes directly,
itself supplies both actual program occurrences at the CALL and STATICCALL
boundaries.

The statement is target-neutral: it names the CircuitBreaker's own
`pauseAfterSet` route and its two boundary relations, but says nothing about
which program is installed beyond the four code facts below.  Nothing
callback-shaped is assumed — in particular neither `MessageExecutesProgram`
witness, no accepted query answer, and no final pausedness is a premise.  Both
occurrences are *derived* from the walk's own spawns.

**No** code-shape fact is asked of the caller. All three spawn sources
`Xinst.step_spawn_source` admits are ruled out from hypotheses the caller is
already supplying: `not_delegation_of_compile` and `Prog.compile_ne_nil` rule
out the delegated and empty sources from the compiler witness, and the
successful terminal polarity decides the `EXTCODESIZE` guard, whose zero arm
reverts. The depth fact is decided the same way: at the depth limit the `CALL`
answers `0` in-frame, the `ISZERO`-inverted branch selects the bubble, and the
bubble cannot end `.ok` — `pauseAfterCall_ok_depth_ne_zero` packages that
inversion, so `sevm.depth ≠ 0` is derived from the suffix rather than asked
for. A hypothesis implied by the ones beside it does not belong in a
signature -- it advertises a demand the theorem does not make. -/
theorem directBoundaryExecutions_of_afterSet_ok
    {fs : List Func} {sevm : Sevm} {entry final : Devm}
    {target : Adr} {duration : B256}
    {code : ByteArray} {program : Prog}
    (h_empty : fs[emptyRevertSlot]? = some Func.revert)
    (h_bubble : fs[bubbleRevertSlot]? = some Func.revertReturnData)
    (compiled : Prog.compile program = some code.toList)
    (targetNe : target ≠ sevm.currentTarget)
    (nonprecompile : sevm.benvStat.rules.isPrecomp target = false)
    (installed : entry.getCode target = code)
    (targetWindow : MemWordAt entry
      (targetWord * 32).toNat target.toB256)
    (durationWindow : MemWordAt entry
      (durationWord * 32).toNat duration)
    (dynamic : sevm.isStatic = false)
    (run : Func.RunCompiledTo fs sevm entry pauseAfterSet (.ok final)) :
    LidoPinnedBoundaryExecutions fs sevm entry target
      program duration (.ok final) := by
  have notDelegation : ¬ isValidDelegation code :=
    not_delegation_of_compile compiled.symm
  have toListNonempty : code.toList ≠ [] := fun isNil =>
    Prog.compile_ne_nil (isNil ▸ compiled)
  -- The successful terminal polarity already decides the CircuitBreaker's own
  -- `EXTCODESIZE` guard: its zero arm reverts, so a run that ends `.ok` is on
  -- the nonzero arm. Asking a caller for this would be asking it to re-supply
  -- what the run it is already handing us has settled.
  have installedNonzero : (entry.getCode target).size.toB256 ≠ 0 := by
    rcases pauseAfterSet_codeGuard_arms_windows h_empty targetWindow
        durationWindow run with ⟨_, _, reverted, _⟩ | ⟨nonzero, _⟩
    · exact absurd reverted (by simp)
    · exact nonzero
  have nonempty : code ≠ .empty := fun isEmpty =>
    installedNonzero (by rw [installed, isEmpty]; rfl)
  rw [pauseAfterSet_eq_afterCall] at run
  obtain ⟨guardTestPost, guardRun, guardBranch⟩ :=
    runCompiledTo_prepend_inv run
  rcases runCompiledTo_branch_inv guardBranch with
    ⟨guardPost, -, guardPop, liveRun⟩ |
      ⟨_, revertPre, -, -, -, revertRun⟩
  · have guardWalk := guardRun
    unfold pauseCodeGuard at guardWalk
    obtain ⟨s1, loadRun, guardWalk⟩ :=
      of_run_append (loadWord targetWord) guardWalk
    rcases Line.of_run_cons guardWalk with ⟨s2, dupRun, guardWalk⟩
    rcases Line.of_run_cons guardWalk with
      ⟨s3, codeSizeRun, guardWalk⟩
    rcases Line.of_run_cons guardWalk with
      ⟨_, iszeroRun, emptyRun⟩
    cases emptyRun
    have targetGuardTest :=
      (((targetWindow.acrossLoadWord loadRun).acrossNinst dupRun).acrossNinst
        codeSizeRun).acrossNinst iszeroRun
    have durationGuardTest :=
      (((durationWindow.acrossLoadWord loadRun).acrossNinst dupRun).acrossNinst
        codeSizeRun).acrossNinst iszeroRun
    have guardPopMemory :=
      (Devm.PopBurn.of_popBurnBy guardPop).memory
    have targetGuard :=
      MemWordAt.of_memory_eq guardPopMemory.symm targetGuardTest
    have durationGuard :=
      MemWordAt.of_memory_eq guardPopMemory.symm durationGuardTest
    obtain ⟨callPre, callStaging, liveRun⟩ :=
      runCompiledTo_prepend_inv liveRun
    obtain ⟨callPost, callRun, afterCall⟩ :=
      runCompiledTo_next_inv liveRun
    obtain ⟨gasWord, rest, callStack, targetCallPre⟩ :=
      pauseCallStaging_boundary_operands targetGuard callStaging
    have callData := pauseCallStaging_calldata durationGuard callStaging
    -- The last implied hypothesis, derived where it is decided: a successful
    -- suffix past the CALL is impossible at the depth limit, because the
    -- non-spawning arm's flag selects the bubble and the bubble cannot end
    -- `.ok`.  See `pauseAfterCall_ok_depth_ne_zero`.
    have depth : sevm.depth ≠ 0 :=
      pauseAfterCall_ok_depth_ne_zero h_bubble callStack callRun afterCall
    obtain ⟨callBoundary, callExecution⟩ :=
      pauseCall_boundary_with_execution callStack callData depth dynamic
        callRun
    have callPreInstalled : callPre.getCode target = code := by
      calc
        callPre.getCode target = guardPost.getCode target :=
          congrFun (pauseCallStaging_codeInv callStaging).symm target
        _ = guardTestPost.getCode target :=
          (congrArg (fun state : State => state.getCode target)
            guardPop.state).symm
        _ = entry.getCode target :=
          congrFun (Line.of_inv Devm.getCode
            (by unfold pauseCodeGuard loadWord; line_inv) guardRun).symm
            target
        _ = code := installed
    rcases callExecution with
      ⟨pauseMsg, pauseXl, pauseChild, pausePc, pauseNextPc, pauseResume,
        pauseCurrent, pauseTarget, pauseCodeAddress, pauseCaller, pauseValue,
        pauseTransfer, pauseStatic, pauseData, pauseTime, pauseRules,
        pauseSpawn, pauseFilled, pauseProcess, pauseStepRun, pauseState,
        pauseOutput⟩
    have callResolved := resolvedCodeAddress_of_direct callPreInstalled
      notDelegation
    rw [callResolved] at pauseCodeAddress
    have pauseXSpawn : Xinst.step sevm callPre .call =
        .spawn (Jaune.Frame.ofCall pauseMsg) pauseResume :=
      XStep.toStep_spawn (by
        simpa only [Ninst.call, Ninst.step_exec] using pauseSpawn)
    have pauseExecutes : MessageExecutesProgram pauseMsg pauseXl program :=
      spawnedMessage_executesProgram compiled nonempty notDelegation targetNe
        callPreInstalled nonprecompile pauseCurrent pauseCodeAddress pauseValue
        pauseTransfer pauseRules pauseXSpawn pauseFilled pauseProcess
    have pauseExact : ExactTargetCall sevm.currentTarget target
        (pauseForCalldata duration) false pauseMsg :=
      ⟨pauseCurrent, pauseTarget, pauseCodeAddress, pauseCaller, pauseValue,
        pauseTransfer, pauseStatic, pauseData⟩
    have pinnedPause : PinnedPauseBoundaryExecutesProgram sevm target
        program duration callPre callPost :=
      ⟨pauseMsg, pauseXl, pauseChild, pausePc, pauseNextPc, pauseResume,
        pauseExact, pauseExecutes, pauseTime, pauseSpawn, pauseFilled,
        pauseProcess, pauseStepRun, pauseState, pauseOutput⟩
    have afterCallContinuation := afterCall
    rw [pauseAfterCallBranch] at afterCall
    obtain ⟨branchTestPost, callIszero, callBranch⟩ :=
      runCompiledTo_next_inv afterCall
    rcases runCompiledTo_branch_inv callBranch with
      ⟨armPre, -, branchPop, statArmRun⟩ |
        ⟨_, bubblePre, -, -, -, bubbleRun⟩
    · rw [pauseStatArm] at statArmRun
      obtain ⟨statPre, statStaging, statArmRun⟩ :=
        runCompiledTo_prepend_inv statArmRun
      obtain ⟨statPost, statRun, observationRun⟩ :=
        runCompiledTo_next_inv statArmRun
      have targetCallPost :=
        pauseCall_targetWord_survives callBoundary targetCallPre
      have targetBranchTest := targetCallPost.acrossNinst
        (Ninst.Run.of_runCompiled callIszero)
      have targetArm := MemWordAt.of_memory_eq
        (Devm.PopBurn.of_popBurnBy branchPop).memory.symm targetBranchTest
      obtain ⟨statGasWord, statRest, statStack, -⟩ :=
        pauseStatStaging_boundary_operands targetArm statStaging
      have statData :=
        pauseStatStaging_boundary_calldata targetArm.memImage statStaging
      obtain ⟨statBoundary, statExecution⟩ :=
        pauseStat_boundary_with_execution statStack statData depth statRun
      have callPreNonempty : (callPre.getCode target).toList ≠ [] := by
        rw [callPreInstalled]
        exact toListNonempty
      have callCode :=
        runCompiled_getCode_eq_of_nonempty callRun callPreNonempty
      have statPreInstalled : statPre.getCode target = code := by
        calc
          statPre.getCode target = armPre.getCode target :=
            congrFun (pauseStatStaging_codeInv statStaging).symm target
          _ = branchTestPost.getCode target :=
            (congrArg (fun state : State => state.getCode target)
              branchPop.state).symm
          _ = callPost.getCode target :=
            congrFun (Ninst.Hinv.inv (f := Devm.getCode)
              (Ninst.Run.of_runCompiled callIszero)).symm target
          _ = callPre.getCode target := callCode
          _ = code := callPreInstalled
      rcases statExecution with
        ⟨statMsg, statXl, statChild, statPc, statNextPc, statResume,
          statCurrent, statTarget, statCodeAddress, staticCaller, statValue,
          statTransfer, statStatic, statDataEq, statTime, statRules,
          statSpawn, statFilled, statProcess, statStepRun, statState,
          statOutput⟩
      have statResolved := resolvedCodeAddress_of_direct statPreInstalled
        notDelegation
      rw [statResolved] at statCodeAddress
      have statXSpawn : Xinst.step sevm statPre .staticcall =
          .spawn (Jaune.Frame.ofCall statMsg) statResume :=
        XStep.toStep_spawn (by
          simpa only [Ninst.staticcall, Ninst.step_exec] using statSpawn)
      have statExecutes : MessageExecutesProgram statMsg statXl program :=
        spawnedMessage_executesProgram compiled nonempty notDelegation targetNe
          statPreInstalled nonprecompile statCurrent statCodeAddress statValue
          statTransfer statRules statXSpawn statFilled statProcess
      have statExact : ExactTargetCall sevm.currentTarget target
          isPausedCalldata true statMsg :=
        ⟨statCurrent, statTarget, statCodeAddress, staticCaller, statValue,
          statTransfer, statStatic, statDataEq⟩
      have pinnedStat : PinnedStatBoundaryExecutesProgram sevm target
          program statPre statPost :=
        ⟨statMsg, statXl, statChild, statPc, statNextPc, statResume,
          statExact, statExecutes, statTime, statSpawn, statFilled,
          statProcess, statStepRun, statState, statOutput⟩
      exact ⟨installedNonzero, guardTestPost, guardPost, callPre, callPost,
        branchTestPost, armPre, statPre, statPost, guardRun, guardPop,
        callStaging, callRun, callBoundary, pinnedPause,
        afterCallContinuation, callIszero, branchPop, statStaging, statRun,
        statBoundary, pinnedStat, observationRun⟩
    · exact (bubbleCall_not_ok h_bubble bubbleRun).elim
  · exact (revertCall_not_ok h_empty revertRun).elim

set_option linter.unusedVariables false in
/-- The compiled test stub is one instance of the direct-installation crossing.
Its statement is unchanged: the existing stub control consumes exactly this.
`depth` is retained for that byte-stable compatibility telescope even though
the crossing now derives the fact itself — see
`pauseAfterCall_ok_depth_ne_zero`; the linter is silenced for exactly that
retained binder. -/
theorem stubBoundaryExecutions_of_afterSet_ok
    {fs : List Func} {sevm : Sevm} {entry final : Devm}
    {target : Adr} {duration : B256}
    (h_empty : fs[emptyRevertSlot]? = some Func.revert)
    (h_bubble : fs[bubbleRevertSlot]? = some Func.revertReturnData)
    (targetNe : target ≠ sevm.currentTarget)
    (nonprecompile : sevm.benvStat.rules.isPrecomp target = false)
    (installed : entry.getCode target = PinnedTargetControl.stubCode)
    (targetWindow : MemWordAt entry
      (targetWord * 32).toNat target.toB256)
    (durationWindow : MemWordAt entry
      (durationWord * 32).toNat duration)
    (depth : sevm.depth ≠ 0)
    (dynamic : sevm.isStatic = false)
    (run : Func.RunCompiledTo fs sevm entry pauseAfterSet (.ok final)) :
    LidoPinnedBoundaryExecutions fs sevm entry target
      PinnedTargetControl.stubProgram duration (.ok final) :=
  directBoundaryExecutions_of_afterSet_ok h_empty h_bubble
    stubProgram_compile_toList targetNe nonprecompile
    installed targetWindow durationWindow dynamic run

private theorem spawnedChild_clean_of_zeroBranch
    {sevm : Sevm} {pre post testPost armPre : Devm}
    {instruction : Ninst} {msg : Msg} {xl : Xlot} {child : Devm}
    {pc nextPc : Nat} {resume : Resume}
    (spawn : Ninst.step ⟨pc, sevm, pre⟩ instruction =
      .spawn (Jaune.Frame.ofCall msg) resume nextPc)
    (process : ProcessMessage msg xl (.ok child))
    (stepRun : Ninst.StepRun pc sevm pre instruction xl (.ok post))
    (resumeCall : ∃ parent oi os, resume = .call parent oi os)
    (testRun : Ninst.RunCompiled sevm post Ninst.iszero testPost)
    (zeroPop : Devm.PopBurnBy [0] (gVerylow + gHigh) testPost armPre) :
    child.error.isSome = false := by
  unfold Ninst.StepRun at stepRun
  rw [spawn] at stepRun
  obtain ⟨result, frameRun, resumeRun⟩ := stepRun
  have resultEq : result = .ok child :=
    runFrame_result_unique frameRun process
  subst result
  rcases resumeCall with ⟨parent, oi, os, rfl⟩
  have postStack := Resume.call_stack_flag resumeRun.symm
  have testStack := (iszero_stack_inv testRun postStack).1
  have popped := zeroPop.stack
  change testPost.stack = 0 :: armPre.stack at popped
  rw [testStack] at popped
  have headEq := (List.cons.inj popped).1
  cases errorEq : child.error.isSome
  · rfl
  · exfalso
    simp only [errorEq, if_true] at headEq
    exact absurd headEq (by decide)

private theorem staticcallMessage_entry_getStor_eq
    {sevm : Sevm} {pre : Devm} {msg : Msg} {resume : Resume}
    {xl : Xlot} {program : Prog} {child : Devm} {owner : Adr}
    (spawn : Xinst.step sevm pre .staticcall =
      .spawn (Jaune.Frame.ofCall msg) resume)
    (executes : MessageExecutesProgram msg xl program)
    (process : ProcessMessage msg xl (.ok child)) :
    msg.benv.state.getStor owner = pre.state.getStor owner := by
  rcases executes with ⟨-, childEvm, raw, rfl, -⟩
  have actualEnter : (Jaune.Frame.ofCall msg).enter = .run childEvm :=
    (RunFrame.some_inv process).1
  have resumeCall := stepStaticcall_spawn_resume spawn
  rcases Xinst.step_shape sevm pre .staticcall with
    ⟨done, shape, -⟩ |
    ⟨d, endowment, newAddress, mi, ms, hprefix, shape⟩ |
    ⟨d, d₀, gas, value, caller, target, codeAddress, transferValue,
      isStatic, ii, isz, oi, osz, code, delegated, hprefix, -, -, -, shape⟩ <;>
      rw [shape] at spawn
  · cases spawn
  · rcases genericCreate_step_spawn_exact spawn with ⟨-, resumeCreate⟩
    rcases resumeCall with ⟨parent, outIndex, outSize, resumeCall⟩
    rw [resumeCall] at resumeCreate
    cases resumeCreate
  · have frameEq := (genericCall_step_spawn_exact spawn).1
    let generated := callMsg sevm (d.withReturnData []) gas value caller
      target codeAddress transferValue isStatic
      ((d.memory.read ii isz).1) code delegated
    have generatedEnter :
        (Jaune.Frame.ofCall generated).enter = .run childEvm := by
      rw [← frameEq]
      exact actualEnter
    rcases Frame.enter_run_inv actualEnter with
      ⟨actualBenv, actualTransfer, actualEvm⟩
    rcases Frame.enter_run_inv generatedEnter with
      ⟨generatedBenv, generatedTransfer, generatedEvm⟩
    change msg.benvAfterTransfer = .ok actualBenv at actualTransfer
    change generated.benvAfterTransfer = .ok generatedBenv at generatedTransfer
    have actualState : childEvm.dyna.state = actualBenv.state := by
      exact congrArg (fun evm : Evm ↦ evm.dyna.state) actualEvm
    have generatedState : childEvm.dyna.state = generatedBenv.state := by
      exact congrArg (fun evm : Evm ↦ evm.dyna.state) generatedEvm
    have actualStorage : childEvm.dyna.state.getStor owner =
        msg.benv.state.getStor owner := by
      rw [actualState, benvAfterTransfer_getStor_eq actualTransfer]
    have generatedStorage : childEvm.dyna.state.getStor owner =
        pre.state.getStor owner := by
      rw [generatedState, benvAfterTransfer_getStor_eq generatedTransfer]
      exact (hprefix.getStor owner).symm
    exact actualStorage.symm.trans generatedStorage

private theorem observation_zeroBranch
    {fs : List Func} {sevm : Sevm} {statPost final : Devm}
    (h_bubble : fs[bubbleRevertSlot]? = some Func.revertReturnData)
    (run : Func.RunCompiledTo fs sevm statPost
      (Ninst.iszero :::
        ((Func.call bubbleRevertSlot) <?> decodePausedResult))
      (.ok final)) :
    ∃ testPost armPre,
      Ninst.RunCompiled sevm statPost Ninst.iszero testPost ∧
      Devm.PopBurnBy [0] (gVerylow + gHigh) testPost armPre := by
  obtain ⟨testPost, testRun, branchRun⟩ := runCompiledTo_next_inv run
  rcases runCompiledTo_branch_inv branchRun with
    ⟨armPre, -, zeroPop, -⟩ | ⟨-, bubblePre, -, -, -, bubbleRun⟩
  · exact ⟨testPost, armPre, testRun, zeroPop⟩
  · exact (bubbleCall_not_ok h_bubble bubbleRun).elim

private theorem observation_success_answer_one
    {fs : List Func} {sevm : Sevm} {target : Adr}
    {statPre statPost final : Devm}
    (h_empty : fs[emptyRevertSlot]? = some Func.revert)
    (h_bubble : fs[bubbleRevertSlot]? = some Func.revertReturnData)
    (h_failed : fs[pauseFailedErrorSlot]? = some pauseFailedError)
    (boundary : PauseStatBoundary sevm target statPre statPost)
    (run : Func.RunCompiledTo fs sevm statPost
      (Ninst.iszero :::
        ((Func.call bubbleRevertSlot) <?> decodePausedResult))
      (.ok final)) :
    ∃ child : Devm,
      statPost.returnData = child.output ∧
      child.error.isSome = false ∧
      32 ≤ child.output.length ∧
      pausedAnswer child.output = 1 := by
  rcases pauseObservation_outcomes h_empty h_bubble h_failed boundary run with
    ⟨child, output, failed | short | falseAnswer | noncanonical | accepted⟩
  · exfalso
    rcases failed.2 with ⟨_, impossible⟩ | ⟨_, impossible, -⟩
    · cases impossible
    · cases impossible
  · exfalso
    rcases short with ⟨-, -, _, impossible, -⟩
    cases impossible
  · exfalso
    rcases falseAnswer with ⟨-, -, -, -, halted | reverted⟩
    · rcases halted with ⟨_, impossible⟩
      cases impossible
    · rcases reverted with ⟨_, impossible, -⟩
      cases impossible
  · exfalso
    rcases noncanonical with ⟨-, -, -, -, -, _, impossible, -⟩
    cases impossible
  · rcases accepted with ⟨clean, -, long, one, -⟩
    exact ⟨child, output, clean, long, one⟩

private theorem pinnedTarget_witness_and_paused
    {fs : List Func} {sevm : Sevm} {entry final : Devm}
    {target : Adr} {program : Prog} {duration : B256}
    {pausedUntil : Adr → Stor → B256} {surface : List B256}
    {ex : Execution}
    (h_empty : fs[emptyRevertSlot]? = some Func.revert)
    (h_bubble : fs[bubbleRevertSlot]? = some Func.revertReturnData)
    (h_failed : fs[pauseFailedErrorSlot]? = some pauseFailedError)
    (h_panic : fs[arithmeticPanicSlot]? =
      some (Func.revertData heartbeatArithmeticPanicData))
    (targetNe : target ≠ sevm.currentTarget)
    (bundle : LidoPinnedPauseTarget sevm.currentTarget sevm.caller target
      program pausedUntil surface)
    (hook : LidoPinnedBoundaryExecutions fs sevm entry target program
      duration ex)
    (hex : ex = .ok final) :
    ∃ callPre callPost,
      PinnedTargetPauseWitness sevm target program duration pausedUntil
          callPre callPost final ∧
        PausedAt pausedUntil final.state target sevm.benvStat.time := by
  rcases hook with
    ⟨-, guardTestPost, guardPost, callPre, callPost, branchTestPost,
      armPre, statPre, statPost, -, -, -, -, callBoundary, pinnedPause,
      -, callIszero, branchPop, statStaging, -, statBoundary, pinnedStat,
      observationRun⟩
  rw [hex] at observationRun
  rcases pinnedPause with
    ⟨pauseMsg, pauseXl, pauseChild, pausePc, pauseNextPc, pauseResume,
      pauseExact, pauseExecutes, pauseTime, pauseSpawn, pauseFilled,
      pauseProcess, pauseStepRun, pauseState, pauseOutput⟩
  have pauseXSpawn : Xinst.step sevm callPre .call =
      .spawn (Jaune.Frame.ofCall pauseMsg) pauseResume :=
    XStep.toStep_spawn (by
      simpa only [Ninst.call, Ninst.step_exec] using pauseSpawn)
  have pauseClean : pauseChild.error.isSome = false :=
    spawnedChild_clean_of_zeroBranch pauseSpawn pauseProcess pauseStepRun
      (stepCall_spawn_resume pauseXSpawn) callIszero branchPop
  have pauseEffect := bundle.pauseFor_effect pauseExact pauseExecutes
    pauseProcess pauseClean
  rw [pauseTime] at pauseEffect
  rcases pinnedStat with
    ⟨statMsg, statXl, statChild, statPc, statNextPc, statResume,
      statExact, statExecutes, statTime, statSpawn, statFilled,
      statProcess, statStepRun, statState, statOutput⟩
  have statXSpawn : Xinst.step sevm statPre .staticcall =
      .spawn (Jaune.Frame.ofCall statMsg) statResume :=
    XStep.toStep_spawn (by
      simpa only [Ninst.staticcall, Ninst.step_exec] using statSpawn)
  obtain ⟨statTestPost, statArmPre, statIszero, statZeroPop⟩ :=
    observation_zeroBranch h_bubble observationRun
  have statClean : statChild.error.isSome = false :=
    spawnedChild_clean_of_zeroBranch statSpawn statProcess statStepRun
      (stepStaticcall_spawn_resume statXSpawn) statIszero statZeroPop
  obtain ⟨observed, observedOutput, -, observedLong, observedOne⟩ :=
    observation_success_answer_one h_empty h_bubble h_failed statBoundary
      observationRun
  have statOutputEq : statChild.output = observed.output :=
    statOutput.symm.trans observedOutput
  have acceptedWord : AcceptedBoolWord statChild 1 := by
    refine ⟨statClean, ?_, ?_⟩
    · rw [statOutputEq]
      exact observedLong
    · rw [statOutputEq]
      simpa only [pausedAnswer] using observedOne
  have acceptedExecution : AcceptedBoolExecution (.ok statChild) 1 :=
    ⟨statChild, rfl, acceptedWord⟩
  rcases bundle.isPaused_truthful statExact statExecutes statProcess
      statChild rfl statClean with
    ⟨queryProjection, queryTruth, -⟩
  have pausedEntry : PausedAt pausedUntil statMsg.benv.state target
      statMsg.benv.stat.time := queryTruth.mp acceptedExecution
  have statEntryStor : statMsg.benv.state.getStor target =
      statPre.state.getStor target :=
    staticcallMessage_entry_getStor_eq statXSpawn statExecutes statProcess
  have callBranchStor : callPost.state.getStor target =
      branchTestPost.state.getStor target :=
    congrFun (Ninst.Hinv.inv (f := Devm.getStor)
      (Ninst.Run.of_runCompiled callIszero)) target
  have branchArmStor : branchTestPost.state.getStor target =
      armPre.state.getStor target :=
    congrFun (PopBurn.Inv.inv (f := Devm.getStor)
      (Devm.PopBurn.of_popBurnBy branchPop)) target
  have armStatStor : armPre.state.getStor target =
      statPre.state.getStor target :=
    congrFun (pauseStatStaging_storInv statStaging) target
  have callStatStor : callPost.state.getStor target =
      statPre.state.getStor target :=
    callBranchStor.trans (branchArmStor.trans armStatStor)
  have statChildCallProjection :
      pausedUntil target (statChild.state.getStor target) =
        pausedUntil target (pauseChild.state.getStor target) := by
    calc
      pausedUntil target (statChild.state.getStor target) =
          pausedUntil target (statMsg.benv.state.getStor target) :=
        queryProjection
      _ = pausedUntil target (statPre.state.getStor target) :=
        congrArg (pausedUntil target) statEntryStor
      _ = pausedUntil target (callPost.state.getStor target) :=
        congrArg (pausedUntil target) callStatStor.symm
      _ = pausedUntil target (pauseChild.state.getStor target) :=
        congrArg (pausedUntil target)
          (congrArg (fun state : State ↦ state.getStor target) pauseState)
  have finalTargetStor : final.state.getStor target =
      statPost.state.getStor target := by
    exact observation_ok_getStor_eq_of_owner_ne h_empty h_bubble h_failed
      h_panic targetNe observationRun
  have finalCallProjection :
      pausedUntil target (final.state.getStor target) =
        pausedUntil target (pauseChild.state.getStor target) := by
    calc
      pausedUntil target (final.state.getStor target) =
          pausedUntil target (statPost.state.getStor target) :=
        congrArg (pausedUntil target) finalTargetStor
      _ = pausedUntil target (statChild.state.getStor target) :=
        congrArg (pausedUntil target)
          (congrArg (fun state : State ↦ state.getStor target) statState)
      _ = pausedUntil target (pauseChild.state.getStor target) :=
        statChildCallProjection
  have pausedFinal :
      PausedAt pausedUntil final.state target sevm.benvStat.time := by
    unfold PausedAt at pausedEntry ⊢
    rw [finalTargetStor, statState, queryProjection, ← statTime]
    exact pausedEntry
  refine ⟨callPre, callPost, ⟨callBoundary, pauseMsg, pauseXl, pauseChild,
    pausePc, pauseNextPc, pauseResume, pauseExact, pauseExecutes, pauseTime,
    pauseSpawn, pauseProcess, pauseStepRun, pauseState, pauseOutput, pauseClean,
    pauseEffect, finalCallProjection⟩, pausedFinal⟩

/-- The production CircuitBreaker public pause composes with any pinned target
bundle whose actual CALL and STATICCALL occurrences execute the indexed
program.  Both T2 noninterference equalities are derived from those occurrences,
and the final pausedness claim names the same successful `final` state. -/
theorem publicPause_pinnedTarget
    {sevm : Sevm} {pre : Devm} {owner : Adr}
    {target duration idx0 len0 last0 : B256}
    {img : Bytes} {targetCode : ByteArray} {program : Prog}
    {pausedUntil : Adr → Stor → B256} {surface : List B256}
    {ex : Execution} :
    PublicPausePinnedTargetStatement sevm pre owner target duration idx0 len0
      last0 img targetCode program pausedUntil surface ex := by
  intro premises targetNe publicRun bundle entry reached hook final hex
  have reachedAt := reached
  rcases reached with
    ⟨targetWindow, durationWindow, targetCodeAt, countDecrement,
      afterSetRun⟩
  have canonicalTarget : target.toAdr.toB256 = target :=
    toB256_toAdr premises.targetCanonical
  have targetAdrWindow :
      MemWordAt entry (targetWord * 32).toNat target.toAdr.toB256 := by
    rw [canonicalTarget]
    exact targetWindow
  have noninterference := pinnedTrace_noninterference
    (fs := (runtime officialParams).main :: (runtime officialParams).aux)
    (by rfl) (by rfl) (by rfl) (by rfl) bundle hook hex
  have committedBoundary := pauseAfterSet_boundary_committed_outcomes
    (by rfl) (by rfl) (by rfl) (by rfl)
    targetAdrWindow durationWindow premises.entered premises.dynamic
    noninterference afterSetRun
  have committed : PublicPauseCommittedOutcomes sevm pre target duration
      targetCode ex := ⟨entry, reachedAt, committedBoundary⟩
  have witness := pinnedTarget_witness_and_paused
    (fs := (runtime officialParams).main :: (runtime officialParams).aux)
    (by rfl) (by rfl) (by rfl) (by rfl) targetNe bundle hook hex
  exact ⟨committed, witness⟩

/-- The compiled test stub specializes the generic composition without leaving
any account-behaviour clause as a premise.  The remaining argument is the
combined parent-trace and program-occurrence witness extracted from this public
run; only its two `MessageExecutesProgram` components are target-specific. -/
theorem publicPause_stubPinnedTarget
    {sevm : Sevm} {pre : Devm} {owner : Adr}
    {target duration idx0 len0 last0 : B256}
    {img : Bytes} {targetCode : ByteArray} {ex : Execution}
    (premises : PublicPauseEntryPremises sevm pre owner target duration
      idx0 len0 last0 img targetCode)
    (targetNe : target.toAdr ≠ sevm.currentTarget)
    (publicRun : Prog.RunCompiledTo sevm pre (runtime officialParams) ex) :
    ∀ entry,
      PublicPauseAfterSetAt
          ((runtime officialParams).main :: (runtime officialParams).aux)
          sevm pre target duration targetCode ex entry →
      LidoPinnedBoundaryExecutions
          ((runtime officialParams).main :: (runtime officialParams).aux)
          sevm entry target.toAdr PinnedTargetControl.stubProgram duration ex →
      ∀ final, ex = .ok final →
        PublicPausePinnedTargetConclusion sevm pre target duration targetCode
          PinnedTargetControl.stubProgram PinnedTargetControl.pausedUntil
          ex final := by
  intro entry reached hook final hex
  exact publicPause_pinnedTarget premises targetNe publicRun
    (PinnedTargetControl.stub_lidoPinnedPauseTarget sevm.currentTarget
      sevm.caller target.toAdr targetNe)
    entry reached hook final hex

/-- Full T2-family application for the compiled stub.  The callback
noninterference premise of `publicPause_committed_outcomes` is not assumed:
it is derived for every reached entry from that entry's two actual compiled
stub occurrences. -/
theorem publicPause_stub_committed_outcomes
    {sevm : Sevm} {pre final : Devm} {owner : Adr}
    {target duration idx0 len0 last0 : B256}
    {img : Bytes} {targetCode : ByteArray} {ex : Execution}
    (premises : PublicPauseEntryPremises sevm pre owner target duration
      idx0 len0 last0 img targetCode)
    (targetNe : target.toAdr ≠ sevm.currentTarget)
    (publicRun : Prog.RunCompiledTo sevm pre (runtime officialParams) ex)
    (success : ex = .ok final)
    (hooks : ∀ entry,
      PublicPauseAfterSetAt
          ((runtime officialParams).main :: (runtime officialParams).aux)
          sevm pre target duration targetCode ex entry →
      LidoPinnedBoundaryExecutions
          ((runtime officialParams).main :: (runtime officialParams).aux)
          sevm entry target.toAdr PinnedTargetControl.stubProgram duration ex) :
    PublicPauseCommittedOutcomes sevm pre target duration targetCode ex := by
  apply publicPause_committed_outcomes premises publicRun
  intro entry reached successPre successRun
  exact pinnedTrace_noninterference
    (fs := (runtime officialParams).main :: (runtime officialParams).aux)
    (by rfl) (by rfl) (by rfl) (by rfl)
    (PinnedTargetControl.stub_lidoPinnedPauseTarget sevm.currentTarget
      sevm.caller target.toAdr targetNe)
    (hooks entry reached) success successPre successRun

end Blanc.LidoCircuitBreaker
