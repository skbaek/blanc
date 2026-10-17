import Blanc.Lift.Curve3Pool.Walk.DispatchQuiet
import Blanc.Lift.Curve3Pool.Walk.ArmChecks
import Blanc.Lift.Curve3Pool.Walk.Admin
import Blanc.Lift.Curve3Pool.Walk.Getters
import Blanc.Lift.Curve3Pool.Bridge
import Blanc.Lift.Curve3Pool.Spec
import Blanc.Lift.FrameWalkNode

/-!
# Raw effects of the quiet admin/getter entries

For each admin entry and getter, `<entry>_raw` has the shape of
`removeLiquidity_raw`: dispatcher (`DispatchQuiet.lean`) hands the arm's body
pc with the exact `quietSt` state, `xa_node_span` crosses the checked
exec-free arm tree (the halted branch leaves no children; the returned branch
is impossible by `admRawRun_halted`), the existing `safe_*` proof gives the
model step and `QuietLands`, and `rawEffect_of_quietLands` turns it into Spec's
`RawEffect` for the childless frame.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- **The `commit_new_fee` raw effect.** -/
theorem commitNewFee_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selCommitNewFee)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨G1, hX⟩ := dq_to_3040 hcode hlen hcd hx
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
  obtain ⟨G2, hX⟩ := dq_to_499b hcode hX
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide)
  obtain ⟨G3, hX⟩ := dq_arm_commitNewFee hcode hsel hX
  have hst : (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G3).stack =
      [] ++ ([] : List B256) := rfl
  have hfr : FrameMatches (0 : B256) ([] : List AVal) ([] : List B256) := List.Forall₂.nil
  have hmm : MemMatches (0 : B256) ([] : MemMap)
      (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G3).memory :=
    memMatches_nil _ _
  rcases xa_node_span checkedM admRawExecFreeSet hcode hfork admRaw_check_commitNewFee
      admRaw_free_commitNewFee hst hfr hmm hX with
    ⟨run, hL⟩ | ⟨d', S', run, _hX', _hst', _hlen'⟩
  · obtain ⟨o, hstep, hlands⟩ := safe_commitNewFee hfork hck hsel hlen _ _ run
    exact ⟨quietEnv sevm, o, hstep, rawEffect_of_quietLands hL hlands⟩
  · obtain ⟨post', hcon⟩ := admRawRun_halted admRaw_halt_commitNewFee run
    cases hcon

/-- **The `apply_new_fee` raw effect.** -/
theorem applyNewFee_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selApplyNewFee)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨G1, hX⟩ := dq_to_3040 hcode hlen hcd hx
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
  obtain ⟨G2, hX⟩ := dq_to_499b hcode hX
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide)
  obtain ⟨G3, hX⟩ := dq_skip_5b5a1467 hcode hX (by rw [hsel]; decide)
  obtain ⟨G4, hX⟩ := dq_arm_applyNewFee hcode hsel hX
  have hst : (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G4).stack =
      [] ++ ([] : List B256) := rfl
  have hfr : FrameMatches (0 : B256) ([] : List AVal) ([] : List B256) := List.Forall₂.nil
  have hmm : MemMatches (0 : B256) ([] : MemMap)
      (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G4).memory :=
    memMatches_nil _ _
  rcases xa_node_span checkedM admRawExecFreeSet hcode hfork admRaw_check_applyNewFee
      admRaw_free_applyNewFee hst hfr hmm hX with
    ⟨run, hL⟩ | ⟨d', S', run, _hX', _hst', _hlen'⟩
  · obtain ⟨o, hstep, hlands⟩ := safe_applyNewFee hfork hck hsel hlen _ _ run
    exact ⟨quietEnv sevm, o, hstep, rawEffect_of_quietLands hL hlands⟩
  · obtain ⟨post', hcon⟩ := admRawRun_halted admRaw_halt_applyNewFee run
    cases hcon

/-- **The `revert_new_parameters` raw effect.** -/
theorem revertNewParameters_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRevertNewParameters)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨G1, hX⟩ := dq_to_3040 hcode hlen hcd hx
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
  obtain ⟨G2, hX⟩ := dq_to_499b hcode hX
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide)
  obtain ⟨G3, hX⟩ := dq_skip_5b5a1467 hcode hX (by rw [hsel]; decide)
  obtain ⟨G4, hX⟩ := dq_skip_4f12fe97 hcode hX (by rw [hsel]; decide)
  obtain ⟨G5, hX⟩ := dq_arm_revertNewParameters hcode hsel hX
  have hst : (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G5).stack =
      [] ++ ([] : List B256) := rfl
  have hfr : FrameMatches (0 : B256) ([] : List AVal) ([] : List B256) := List.Forall₂.nil
  have hmm : MemMatches (0 : B256) ([] : MemMap)
      (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G5).memory :=
    memMatches_nil _ _
  rcases xa_node_span checkedM admRawExecFreeSet hcode hfork admRaw_check_revertNewParameters
      admRaw_free_revertNewParameters hst hfr hmm hX with
    ⟨run, hL⟩ | ⟨d', S', run, _hX', _hst', _hlen'⟩
  · obtain ⟨o, hstep, hlands⟩ := safe_revertNewParameters hfork hck hsel hlen _ _ run
    exact ⟨quietEnv sevm, o, hstep, rawEffect_of_quietLands hL hlands⟩
  · obtain ⟨post', hcon⟩ := admRawRun_halted admRaw_halt_revertNewParameters run
    cases hcon

/-- **The `commit_transfer_ownership` raw effect.** -/
theorem commitTransferOwnership_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selCommitTransferOwnership)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨G1, hX⟩ := dq_to_3040 hcode hlen hcd hx
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
  obtain ⟨G2, hX⟩ := dq_to_499b hcode hX
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide)
  obtain ⟨G3, hX⟩ := dq_skip_5b5a1467 hcode hX (by rw [hsel]; decide)
  obtain ⟨G4, hX⟩ := dq_skip_4f12fe97 hcode hX (by rw [hsel]; decide)
  obtain ⟨G5, hX⟩ := dq_skip_226840fb hcode hX (by rw [hsel]; decide)
  obtain ⟨G6, hX⟩ := dq_arm_commitTransferOwnership hcode hsel hX
  have hst : (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G6).stack =
      [] ++ ([] : List B256) := rfl
  have hfr : FrameMatches (0 : B256) ([] : List AVal) ([] : List B256) := List.Forall₂.nil
  have hmm : MemMatches (0 : B256) ([] : MemMap)
      (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G6).memory :=
    memMatches_nil _ _
  rcases xa_node_span checkedM admRawExecFreeSet hcode hfork admRaw_check_commitTransferOwnership
      admRaw_free_commitTransferOwnership hst hfr hmm hX with
    ⟨run, hL⟩ | ⟨d', S', run, _hX', _hst', _hlen'⟩
  · obtain ⟨o, hstep, hlands⟩ := safe_commitTransferOwnership hfork hck hsel hlen _ _ run
    exact ⟨quietEnv sevm, o, hstep, rawEffect_of_quietLands hL hlands⟩
  · obtain ⟨post', hcon⟩ := admRawRun_halted admRaw_halt_commitTransferOwnership run
    cases hcon

/-- **The `apply_transfer_ownership` raw effect.** -/
theorem applyTransferOwnership_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selApplyTransferOwnership)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨G1, hX⟩ := dq_to_3040 hcode hlen hcd hx
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
  obtain ⟨G2, hX⟩ := dq_to_499b hcode hX
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide)
  obtain ⟨G3, hX⟩ := dq_skip_5b5a1467 hcode hX (by rw [hsel]; decide)
  obtain ⟨G4, hX⟩ := dq_skip_4f12fe97 hcode hX (by rw [hsel]; decide)
  obtain ⟨G5, hX⟩ := dq_skip_226840fb hcode hX (by rw [hsel]; decide)
  obtain ⟨G6, hX⟩ := dq_skip_6b441a40 hcode hX (by rw [hsel]; decide)
  obtain ⟨G7, hX⟩ := dq_arm_applyTransferOwnership hcode hsel hX
  have hst : (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G7).stack =
      [] ++ ([] : List B256) := rfl
  have hfr : FrameMatches (0 : B256) ([] : List AVal) ([] : List B256) := List.Forall₂.nil
  have hmm : MemMatches (0 : B256) ([] : MemMap)
      (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G7).memory :=
    memMatches_nil _ _
  rcases xa_node_span checkedM admRawExecFreeSet hcode hfork admRaw_check_applyTransferOwnership
      admRaw_free_applyTransferOwnership hst hfr hmm hX with
    ⟨run, hL⟩ | ⟨d', S', run, _hX', _hst', _hlen'⟩
  · obtain ⟨o, hstep, hlands⟩ := safe_applyTransferOwnership hfork hck hsel hlen _ _ run
    exact ⟨quietEnv sevm, o, hstep, rawEffect_of_quietLands hL hlands⟩
  · obtain ⟨post', hcon⟩ := admRawRun_halted admRaw_halt_applyTransferOwnership run
    cases hcon

/-- **The `revert_transfer_ownership` raw effect.** -/
theorem revertTransferOwnership_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRevertTransferOwnership)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨G1, hX⟩ := dq_to_3040 hcode hlen hcd hx
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
  obtain ⟨G2, hX⟩ := dq_to_499b hcode hX
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide)
  obtain ⟨G3, hX⟩ := dq_skip_5b5a1467 hcode hX (by rw [hsel]; decide)
  obtain ⟨G4, hX⟩ := dq_skip_4f12fe97 hcode hX (by rw [hsel]; decide)
  obtain ⟨G5, hX⟩ := dq_skip_226840fb hcode hX (by rw [hsel]; decide)
  obtain ⟨G6, hX⟩ := dq_skip_6b441a40 hcode hX (by rw [hsel]; decide)
  obtain ⟨G7, hX⟩ := dq_skip_6a1c05ae hcode hX (by rw [hsel]; decide)
  obtain ⟨G8, hX⟩ := dq_arm_revertTransferOwnership hcode hsel hX
  have hst : (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G8).stack =
      [] ++ ([] : List B256) := rfl
  have hfr : FrameMatches (0 : B256) ([] : List AVal) ([] : List B256) := List.Forall₂.nil
  have hmm : MemMatches (0 : B256) ([] : MemMap)
      (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G8).memory :=
    memMatches_nil _ _
  rcases xa_node_span checkedM admRawExecFreeSet hcode hfork admRaw_check_revertTransferOwnership
      admRaw_free_revertTransferOwnership hst hfr hmm hX with
    ⟨run, hL⟩ | ⟨d', S', run, _hX', _hst', _hlen'⟩
  · obtain ⟨o, hstep, hlands⟩ := safe_revertTransferOwnership hfork hck hsel hlen _ _ run
    exact ⟨quietEnv sevm, o, hstep, rawEffect_of_quietLands hL hlands⟩
  · obtain ⟨post', hcon⟩ := admRawRun_halted admRaw_halt_revertTransferOwnership run
    cases hcon

/-- **The `kill_me` raw effect.** -/
theorem killMe_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selKillMe)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨G1, hX⟩ := dq_to_3040 hcode hlen hcd hx
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
  obtain ⟨G2, hX⟩ := dq_to_499b hcode hX
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide)
  obtain ⟨G3, hX⟩ := dq_skip_5b5a1467 hcode hX (by rw [hsel]; decide)
  obtain ⟨G4, hX⟩ := dq_skip_4f12fe97 hcode hX (by rw [hsel]; decide)
  obtain ⟨G5, hX⟩ := dq_skip_226840fb hcode hX (by rw [hsel]; decide)
  obtain ⟨G6, hX⟩ := dq_skip_6b441a40 hcode hX (by rw [hsel]; decide)
  obtain ⟨G7, hX⟩ := dq_skip_6a1c05ae hcode hX (by rw [hsel]; decide)
  obtain ⟨G8, hX⟩ := dq_skip_86fbf193 hcode hX (by rw [hsel]; decide)
  obtain ⟨G9, hX⟩ := dq_skip_e2e7d264 hcode hX (by rw [hsel]; decide)
  obtain ⟨G10, hX⟩ := dq_skip_30c54085 hcode hX (by rw [hsel]; decide)
  obtain ⟨G11, hX⟩ := dq_skip_524c3901 hcode hX (by rw [hsel]; decide)
  obtain ⟨G12, hX⟩ := dq_arm_killMe hcode hsel hX
  have hst : (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G12).stack =
      [] ++ ([] : List B256) := rfl
  have hfr : FrameMatches (0 : B256) ([] : List AVal) ([] : List B256) := List.Forall₂.nil
  have hmm : MemMatches (0 : B256) ([] : MemMap)
      (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G12).memory :=
    memMatches_nil _ _
  rcases xa_node_span checkedM admRawExecFreeSet hcode hfork admRaw_check_killMe
      admRaw_free_killMe hst hfr hmm hX with
    ⟨run, hL⟩ | ⟨d', S', run, _hX', _hst', _hlen'⟩
  · obtain ⟨o, hstep, hlands⟩ := safe_killMe hfork hck hsel hlen _ _ run
    exact ⟨quietEnv sevm, o, hstep, rawEffect_of_quietLands hL hlands⟩
  · obtain ⟨post', hcon⟩ := admRawRun_halted admRaw_halt_killMe run
    cases hcon

/-- **The `unkill_me` raw effect.** -/
theorem unkillMe_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selUnkillMe)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨G1, hX⟩ := dq_to_3040 hcode hlen hcd hx
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
  obtain ⟨G2, hX⟩ := dq_to_499b hcode hX
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide)
  obtain ⟨G3, hX⟩ := dq_skip_5b5a1467 hcode hX (by rw [hsel]; decide)
  obtain ⟨G4, hX⟩ := dq_skip_4f12fe97 hcode hX (by rw [hsel]; decide)
  obtain ⟨G5, hX⟩ := dq_skip_226840fb hcode hX (by rw [hsel]; decide)
  obtain ⟨G6, hX⟩ := dq_skip_6b441a40 hcode hX (by rw [hsel]; decide)
  obtain ⟨G7, hX⟩ := dq_skip_6a1c05ae hcode hX (by rw [hsel]; decide)
  obtain ⟨G8, hX⟩ := dq_skip_86fbf193 hcode hX (by rw [hsel]; decide)
  obtain ⟨G9, hX⟩ := dq_skip_e2e7d264 hcode hX (by rw [hsel]; decide)
  obtain ⟨G10, hX⟩ := dq_skip_30c54085 hcode hX (by rw [hsel]; decide)
  obtain ⟨G11, hX⟩ := dq_skip_524c3901 hcode hX (by rw [hsel]; decide)
  obtain ⟨G12, hX⟩ := dq_skip_e3698853 hcode hX (by rw [hsel]; decide)
  obtain ⟨G13, hX⟩ := dq_arm_unkillMe hcode hsel hX
  have hst : (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G13).stack =
      [] ++ ([] : List B256) := rfl
  have hfr : FrameMatches (0 : B256) ([] : List AVal) ([] : List B256) := List.Forall₂.nil
  have hmm : MemMatches (0 : B256) ([] : MemMap)
      (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G13).memory :=
    memMatches_nil _ _
  rcases xa_node_span checkedM admRawExecFreeSet hcode hfork admRaw_check_unkillMe
      admRaw_free_unkillMe hst hfr hmm hX with
    ⟨run, hL⟩ | ⟨d', S', run, _hX', _hst', _hlen'⟩
  · obtain ⟨o, hstep, hlands⟩ := safe_unkillMe hfork hck hsel hlen _ _ run
    exact ⟨quietEnv sevm, o, hstep, rawEffect_of_quietLands hL hlands⟩
  · obtain ⟨post', hcon⟩ := admRawRun_halted admRaw_halt_unkillMe run
    cases hcon

/-- **The `coins` raw effect.** -/
theorem coins_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selCoins)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨G1, hX⟩ := dq_to_3040 hcode hlen hcd hx
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
  obtain ⟨G2, hX⟩ := dq_to_499b hcode hX
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide)
  obtain ⟨G3, hX⟩ := dq_skip_5b5a1467 hcode hX (by rw [hsel]; decide)
  obtain ⟨G4, hX⟩ := dq_skip_4f12fe97 hcode hX (by rw [hsel]; decide)
  obtain ⟨G5, hX⟩ := dq_skip_226840fb hcode hX (by rw [hsel]; decide)
  obtain ⟨G6, hX⟩ := dq_skip_6b441a40 hcode hX (by rw [hsel]; decide)
  obtain ⟨G7, hX⟩ := dq_skip_6a1c05ae hcode hX (by rw [hsel]; decide)
  obtain ⟨G8, hX⟩ := dq_skip_86fbf193 hcode hX (by rw [hsel]; decide)
  obtain ⟨G9, hX⟩ := dq_skip_e2e7d264 hcode hX (by rw [hsel]; decide)
  obtain ⟨G10, hX⟩ := dq_skip_30c54085 hcode hX (by rw [hsel]; decide)
  obtain ⟨G11, hX⟩ := dq_skip_524c3901 hcode hX (by rw [hsel]; decide)
  obtain ⟨G12, hX⟩ := dq_skip_e3698853 hcode hX (by rw [hsel]; decide)
  obtain ⟨G13, hX⟩ := dq_skip_3046f972 hcode hX (by rw [hsel]; decide)
  obtain ⟨G14, hX⟩ := dq_arm_coins hcode hsel hX
  have hst : (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G14).stack =
      [] ++ ([] : List B256) := rfl
  have hfr : FrameMatches (0 : B256) ([] : List AVal) ([] : List B256) := List.Forall₂.nil
  have hmm : MemMatches (0 : B256) ([] : MemMap)
      (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G14).memory :=
    memMatches_nil _ _
  rcases xa_node_span checkedM admRawExecFreeSet hcode hfork admRaw_check_coinsGetter
      admRaw_free_coinsGetter hst hfr hmm hX with
    ⟨run, hL⟩ | ⟨d', S', run, _hX', _hst', _hlen'⟩
  · obtain ⟨o, hstep, hlands⟩ := safe_coinsGetter hfork hck hsel hlen _ _ run
    exact ⟨quietEnv sevm, o, hstep, rawEffect_of_quietLands hL hlands⟩
  · obtain ⟨post', hcon⟩ := admRawRun_halted admRaw_halt_coinsGetter run
    cases hcon

/-- **The `balances` raw effect.** -/
theorem balances_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selBalances)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨G1, hX⟩ := dq_to_3040 hcode hlen hcd hx
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
  obtain ⟨G2, hX⟩ := dq_to_499b hcode hX
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide)
  obtain ⟨G3, hX⟩ := dq_skip_5b5a1467 hcode hX (by rw [hsel]; decide)
  obtain ⟨G4, hX⟩ := dq_skip_4f12fe97 hcode hX (by rw [hsel]; decide)
  obtain ⟨G5, hX⟩ := dq_skip_226840fb hcode hX (by rw [hsel]; decide)
  obtain ⟨G6, hX⟩ := dq_skip_6b441a40 hcode hX (by rw [hsel]; decide)
  obtain ⟨G7, hX⟩ := dq_skip_6a1c05ae hcode hX (by rw [hsel]; decide)
  obtain ⟨G8, hX⟩ := dq_skip_86fbf193 hcode hX (by rw [hsel]; decide)
  obtain ⟨G9, hX⟩ := dq_skip_e2e7d264 hcode hX (by rw [hsel]; decide)
  obtain ⟨G10, hX⟩ := dq_skip_30c54085 hcode hX (by rw [hsel]; decide)
  obtain ⟨G11, hX⟩ := dq_skip_524c3901 hcode hX (by rw [hsel]; decide)
  obtain ⟨G12, hX⟩ := dq_skip_e3698853 hcode hX (by rw [hsel]; decide)
  obtain ⟨G13, hX⟩ := dq_skip_3046f972 hcode hX (by rw [hsel]; decide)
  obtain ⟨G14, hX⟩ := dq_skip_c6610657 hcode hX (by rw [hsel]; decide)
  obtain ⟨G15, hX⟩ := dq_arm_balances hcode hsel hX
  have hst : (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G15).stack =
      [] ++ ([] : List B256) := rfl
  have hfr : FrameMatches (0 : B256) ([] : List AVal) ([] : List B256) := List.Forall₂.nil
  have hmm : MemMatches (0 : B256) ([] : MemMap)
      (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G15).memory :=
    memMatches_nil _ _
  rcases xa_node_span checkedM admRawExecFreeSet hcode hfork admRaw_check_balancesGetter
      admRaw_free_balancesGetter hst hfr hmm hX with
    ⟨run, hL⟩ | ⟨d', S', run, _hX', _hst', _hlen'⟩
  · obtain ⟨o, hstep, hlands⟩ := safe_balancesGetter hfork hck hsel hlen _ _ run
    exact ⟨quietEnv sevm, o, hstep, rawEffect_of_quietLands hL hlands⟩
  · obtain ⟨post', hcon⟩ := admRawRun_halted admRaw_halt_balancesGetter run
    cases hcon

/-- **The `fee` raw effect.** -/
theorem fee_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selFee)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨G1, hX⟩ := dq_to_3040 hcode hlen hcd hx
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
  obtain ⟨G2, hX⟩ := dq_to_499b hcode hX
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide)
  obtain ⟨G3, hX⟩ := dq_skip_5b5a1467 hcode hX (by rw [hsel]; decide)
  obtain ⟨G4, hX⟩ := dq_skip_4f12fe97 hcode hX (by rw [hsel]; decide)
  obtain ⟨G5, hX⟩ := dq_skip_226840fb hcode hX (by rw [hsel]; decide)
  obtain ⟨G6, hX⟩ := dq_skip_6b441a40 hcode hX (by rw [hsel]; decide)
  obtain ⟨G7, hX⟩ := dq_skip_6a1c05ae hcode hX (by rw [hsel]; decide)
  obtain ⟨G8, hX⟩ := dq_skip_86fbf193 hcode hX (by rw [hsel]; decide)
  obtain ⟨G9, hX⟩ := dq_skip_e2e7d264 hcode hX (by rw [hsel]; decide)
  obtain ⟨G10, hX⟩ := dq_skip_30c54085 hcode hX (by rw [hsel]; decide)
  obtain ⟨G11, hX⟩ := dq_skip_524c3901 hcode hX (by rw [hsel]; decide)
  obtain ⟨G12, hX⟩ := dq_skip_e3698853 hcode hX (by rw [hsel]; decide)
  obtain ⟨G13, hX⟩ := dq_skip_3046f972 hcode hX (by rw [hsel]; decide)
  obtain ⟨G14, hX⟩ := dq_skip_c6610657 hcode hX (by rw [hsel]; decide)
  obtain ⟨G15, hX⟩ := dq_skip_4903b0d1 hcode hX (by rw [hsel]; decide)
  obtain ⟨G16, hX⟩ := dq_arm_fee hcode hsel hX
  have hst : (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G16).stack =
      [] ++ ([] : List B256) := rfl
  have hfr : FrameMatches (0 : B256) ([] : List AVal) ([] : List B256) := List.Forall₂.nil
  have hmm : MemMatches (0 : B256) ([] : MemMap)
      (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G16).memory :=
    memMatches_nil _ _
  rcases xa_node_span checkedM admRawExecFreeSet hcode hfork admRaw_check_feeGetter
      admRaw_free_feeGetter hst hfr hmm hX with
    ⟨run, hL⟩ | ⟨d', S', run, _hX', _hst', _hlen'⟩
  · obtain ⟨o, hstep, hlands⟩ := safe_feeGetter hfork hck hsel hlen _ _ run
    exact ⟨quietEnv sevm, o, hstep, rawEffect_of_quietLands hL hlands⟩
  · obtain ⟨post', hcon⟩ := admRawRun_halted admRaw_halt_feeGetter run
    cases hcon

/-- **The `admin_fee` raw effect.** -/
theorem adminFee_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selAdminFee)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨G1, hX⟩ := dq_to_3040 hcode hlen hcd hx
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
  obtain ⟨G2, hX⟩ := dq_to_499b hcode hX
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide)
  obtain ⟨G3, hX⟩ := dq_skip_5b5a1467 hcode hX (by rw [hsel]; decide)
  obtain ⟨G4, hX⟩ := dq_skip_4f12fe97 hcode hX (by rw [hsel]; decide)
  obtain ⟨G5, hX⟩ := dq_skip_226840fb hcode hX (by rw [hsel]; decide)
  obtain ⟨G6, hX⟩ := dq_skip_6b441a40 hcode hX (by rw [hsel]; decide)
  obtain ⟨G7, hX⟩ := dq_skip_6a1c05ae hcode hX (by rw [hsel]; decide)
  obtain ⟨G8, hX⟩ := dq_skip_86fbf193 hcode hX (by rw [hsel]; decide)
  obtain ⟨G9, hX⟩ := dq_skip_e2e7d264 hcode hX (by rw [hsel]; decide)
  obtain ⟨G10, hX⟩ := dq_skip_30c54085 hcode hX (by rw [hsel]; decide)
  obtain ⟨G11, hX⟩ := dq_skip_524c3901 hcode hX (by rw [hsel]; decide)
  obtain ⟨G12, hX⟩ := dq_skip_e3698853 hcode hX (by rw [hsel]; decide)
  obtain ⟨G13, hX⟩ := dq_skip_3046f972 hcode hX (by rw [hsel]; decide)
  obtain ⟨G14, hX⟩ := dq_skip_c6610657 hcode hX (by rw [hsel]; decide)
  obtain ⟨G15, hX⟩ := dq_skip_4903b0d1 hcode hX (by rw [hsel]; decide)
  obtain ⟨G16, hX⟩ := dq_skip_ddca3f43 hcode hX (by rw [hsel]; decide)
  obtain ⟨G17, hX⟩ := dq_arm_adminFee hcode hsel hX
  have hst : (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G17).stack =
      [] ++ ([] : List B256) := rfl
  have hfr : FrameMatches (0 : B256) ([] : List AVal) ([] : List B256) := List.Forall₂.nil
  have hmm : MemMatches (0 : B256) ([] : MemMap)
      (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G17).memory :=
    memMatches_nil _ _
  rcases xa_node_span checkedM admRawExecFreeSet hcode hfork admRaw_check_adminFeeGetter
      admRaw_free_adminFeeGetter hst hfr hmm hX with
    ⟨run, hL⟩ | ⟨d', S', run, _hX', _hst', _hlen'⟩
  · obtain ⟨o, hstep, hlands⟩ := safe_adminFeeGetter hfork hck hsel hlen _ _ run
    exact ⟨quietEnv sevm, o, hstep, rawEffect_of_quietLands hL hlands⟩
  · obtain ⟨post', hcon⟩ := admRawRun_halted admRaw_halt_adminFeeGetter run
    cases hcon

/-- **The `owner` raw effect.** -/
theorem owner_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selOwner)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨G1, hX⟩ := dq_to_3040 hcode hlen hcd hx
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
  obtain ⟨G2, hX⟩ := dq_to_499b hcode hX
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide)
  obtain ⟨G3, hX⟩ := dq_skip_5b5a1467 hcode hX (by rw [hsel]; decide)
  obtain ⟨G4, hX⟩ := dq_skip_4f12fe97 hcode hX (by rw [hsel]; decide)
  obtain ⟨G5, hX⟩ := dq_skip_226840fb hcode hX (by rw [hsel]; decide)
  obtain ⟨G6, hX⟩ := dq_skip_6b441a40 hcode hX (by rw [hsel]; decide)
  obtain ⟨G7, hX⟩ := dq_skip_6a1c05ae hcode hX (by rw [hsel]; decide)
  obtain ⟨G8, hX⟩ := dq_skip_86fbf193 hcode hX (by rw [hsel]; decide)
  obtain ⟨G9, hX⟩ := dq_skip_e2e7d264 hcode hX (by rw [hsel]; decide)
  obtain ⟨G10, hX⟩ := dq_skip_30c54085 hcode hX (by rw [hsel]; decide)
  obtain ⟨G11, hX⟩ := dq_skip_524c3901 hcode hX (by rw [hsel]; decide)
  obtain ⟨G12, hX⟩ := dq_skip_e3698853 hcode hX (by rw [hsel]; decide)
  obtain ⟨G13, hX⟩ := dq_skip_3046f972 hcode hX (by rw [hsel]; decide)
  obtain ⟨G14, hX⟩ := dq_skip_c6610657 hcode hX (by rw [hsel]; decide)
  obtain ⟨G15, hX⟩ := dq_skip_4903b0d1 hcode hX (by rw [hsel]; decide)
  obtain ⟨G16, hX⟩ := dq_skip_ddca3f43 hcode hX (by rw [hsel]; decide)
  obtain ⟨G17, hX⟩ := dq_skip_fee3f7f9 hcode hX (by rw [hsel]; decide)
  obtain ⟨G18, hX⟩ := dq_arm_owner hcode hsel hX
  have hst : (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G18).stack =
      [] ++ ([] : List B256) := rfl
  have hfr : FrameMatches (0 : B256) ([] : List AVal) ([] : List B256) := List.Forall₂.nil
  have hmm : MemMatches (0 : B256) ([] : MemMap)
      (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G18).memory :=
    memMatches_nil _ _
  rcases xa_node_span checkedM admRawExecFreeSet hcode hfork admRaw_check_ownerGetter
      admRaw_free_ownerGetter hst hfr hmm hX with
    ⟨run, hL⟩ | ⟨d', S', run, _hX', _hst', _hlen'⟩
  · obtain ⟨o, hstep, hlands⟩ := safe_ownerGetter hfork hck hsel hlen _ _ run
    exact ⟨quietEnv sevm, o, hstep, rawEffect_of_quietLands hL hlands⟩
  · obtain ⟨post', hcon⟩ := admRawRun_halted admRaw_halt_ownerGetter run
    cases hcon

/-- **The `initial_A` raw effect.** -/
theorem initialA_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selInitialA)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨G1, hX⟩ := dq_to_3040 hcode hlen hcd hx
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
  obtain ⟨G2, hX⟩ := dq_to_499b hcode hX
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide)
  obtain ⟨G3, hX⟩ := dq_skip_5b5a1467 hcode hX (by rw [hsel]; decide)
  obtain ⟨G4, hX⟩ := dq_skip_4f12fe97 hcode hX (by rw [hsel]; decide)
  obtain ⟨G5, hX⟩ := dq_skip_226840fb hcode hX (by rw [hsel]; decide)
  obtain ⟨G6, hX⟩ := dq_skip_6b441a40 hcode hX (by rw [hsel]; decide)
  obtain ⟨G7, hX⟩ := dq_skip_6a1c05ae hcode hX (by rw [hsel]; decide)
  obtain ⟨G8, hX⟩ := dq_skip_86fbf193 hcode hX (by rw [hsel]; decide)
  obtain ⟨G9, hX⟩ := dq_skip_e2e7d264 hcode hX (by rw [hsel]; decide)
  obtain ⟨G10, hX⟩ := dq_skip_30c54085 hcode hX (by rw [hsel]; decide)
  obtain ⟨G11, hX⟩ := dq_skip_524c3901 hcode hX (by rw [hsel]; decide)
  obtain ⟨G12, hX⟩ := dq_skip_e3698853 hcode hX (by rw [hsel]; decide)
  obtain ⟨G13, hX⟩ := dq_skip_3046f972 hcode hX (by rw [hsel]; decide)
  obtain ⟨G14, hX⟩ := dq_skip_c6610657 hcode hX (by rw [hsel]; decide)
  obtain ⟨G15, hX⟩ := dq_skip_4903b0d1 hcode hX (by rw [hsel]; decide)
  obtain ⟨G16, hX⟩ := dq_skip_ddca3f43 hcode hX (by rw [hsel]; decide)
  obtain ⟨G17, hX⟩ := dq_skip_fee3f7f9 hcode hX (by rw [hsel]; decide)
  obtain ⟨G18, hX⟩ := dq_skip_8da5cb5b hcode hX (by rw [hsel]; decide)
  obtain ⟨G19, hX⟩ := dq_arm_initialA hcode hsel hX
  have hst : (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G19).stack =
      [] ++ ([] : List B256) := rfl
  have hfr : FrameMatches (0 : B256) ([] : List AVal) ([] : List B256) := List.Forall₂.nil
  have hmm : MemMatches (0 : B256) ([] : MemMap)
      (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G19).memory :=
    memMatches_nil _ _
  rcases xa_node_span checkedM admRawExecFreeSet hcode hfork admRaw_check_initialAGetter
      admRaw_free_initialAGetter hst hfr hmm hX with
    ⟨run, hL⟩ | ⟨d', S', run, _hX', _hst', _hlen'⟩
  · obtain ⟨o, hstep, hlands⟩ := safe_initialAGetter hfork hck hsel hlen _ _ run
    exact ⟨quietEnv sevm, o, hstep, rawEffect_of_quietLands hL hlands⟩
  · obtain ⟨post', hcon⟩ := admRawRun_halted admRaw_halt_initialAGetter run
    cases hcon

/-- **The `future_A` raw effect.** -/
theorem futureA_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selFutureA)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨G1, hX⟩ := dq_to_3040 hcode hlen hcd hx
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
  obtain ⟨G2, hX⟩ := dq_to_499b hcode hX
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide)
  obtain ⟨G3, hX⟩ := dq_skip_5b5a1467 hcode hX (by rw [hsel]; decide)
  obtain ⟨G4, hX⟩ := dq_skip_4f12fe97 hcode hX (by rw [hsel]; decide)
  obtain ⟨G5, hX⟩ := dq_skip_226840fb hcode hX (by rw [hsel]; decide)
  obtain ⟨G6, hX⟩ := dq_skip_6b441a40 hcode hX (by rw [hsel]; decide)
  obtain ⟨G7, hX⟩ := dq_skip_6a1c05ae hcode hX (by rw [hsel]; decide)
  obtain ⟨G8, hX⟩ := dq_skip_86fbf193 hcode hX (by rw [hsel]; decide)
  obtain ⟨G9, hX⟩ := dq_skip_e2e7d264 hcode hX (by rw [hsel]; decide)
  obtain ⟨G10, hX⟩ := dq_skip_30c54085 hcode hX (by rw [hsel]; decide)
  obtain ⟨G11, hX⟩ := dq_skip_524c3901 hcode hX (by rw [hsel]; decide)
  obtain ⟨G12, hX⟩ := dq_skip_e3698853 hcode hX (by rw [hsel]; decide)
  obtain ⟨G13, hX⟩ := dq_skip_3046f972 hcode hX (by rw [hsel]; decide)
  obtain ⟨G14, hX⟩ := dq_skip_c6610657 hcode hX (by rw [hsel]; decide)
  obtain ⟨G15, hX⟩ := dq_skip_4903b0d1 hcode hX (by rw [hsel]; decide)
  obtain ⟨G16, hX⟩ := dq_skip_ddca3f43 hcode hX (by rw [hsel]; decide)
  obtain ⟨G17, hX⟩ := dq_skip_fee3f7f9 hcode hX (by rw [hsel]; decide)
  obtain ⟨G18, hX⟩ := dq_skip_8da5cb5b hcode hX (by rw [hsel]; decide)
  obtain ⟨G19, hX⟩ := dq_skip_5409491a hcode hX (by rw [hsel]; decide)
  obtain ⟨G20, hX⟩ := dq_arm_futureA hcode hsel hX
  have hst : (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G20).stack =
      [] ++ ([] : List B256) := rfl
  have hfr : FrameMatches (0 : B256) ([] : List AVal) ([] : List B256) := List.Forall₂.nil
  have hmm : MemMatches (0 : B256) ([] : MemMap)
      (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G20).memory :=
    memMatches_nil _ _
  rcases xa_node_span checkedM admRawExecFreeSet hcode hfork admRaw_check_futureAGetter
      admRaw_free_futureAGetter hst hfr hmm hX with
    ⟨run, hL⟩ | ⟨d', S', run, _hX', _hst', _hlen'⟩
  · obtain ⟨o, hstep, hlands⟩ := safe_futureAGetter hfork hck hsel hlen _ _ run
    exact ⟨quietEnv sevm, o, hstep, rawEffect_of_quietLands hL hlands⟩
  · obtain ⟨post', hcon⟩ := admRawRun_halted admRaw_halt_futureAGetter run
    cases hcon

/-- **The `initial_A_time` raw effect.** -/
theorem initialATime_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selInitialATime)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨G1, hX⟩ := dq_to_3040 hcode hlen hcd hx
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
  obtain ⟨G2, hX⟩ := dq_to_499b hcode hX
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide)
  obtain ⟨G3, hX⟩ := dq_skip_5b5a1467 hcode hX (by rw [hsel]; decide)
  obtain ⟨G4, hX⟩ := dq_skip_4f12fe97 hcode hX (by rw [hsel]; decide)
  obtain ⟨G5, hX⟩ := dq_skip_226840fb hcode hX (by rw [hsel]; decide)
  obtain ⟨G6, hX⟩ := dq_skip_6b441a40 hcode hX (by rw [hsel]; decide)
  obtain ⟨G7, hX⟩ := dq_skip_6a1c05ae hcode hX (by rw [hsel]; decide)
  obtain ⟨G8, hX⟩ := dq_skip_86fbf193 hcode hX (by rw [hsel]; decide)
  obtain ⟨G9, hX⟩ := dq_skip_e2e7d264 hcode hX (by rw [hsel]; decide)
  obtain ⟨G10, hX⟩ := dq_skip_30c54085 hcode hX (by rw [hsel]; decide)
  obtain ⟨G11, hX⟩ := dq_skip_524c3901 hcode hX (by rw [hsel]; decide)
  obtain ⟨G12, hX⟩ := dq_skip_e3698853 hcode hX (by rw [hsel]; decide)
  obtain ⟨G13, hX⟩ := dq_skip_3046f972 hcode hX (by rw [hsel]; decide)
  obtain ⟨G14, hX⟩ := dq_skip_c6610657 hcode hX (by rw [hsel]; decide)
  obtain ⟨G15, hX⟩ := dq_skip_4903b0d1 hcode hX (by rw [hsel]; decide)
  obtain ⟨G16, hX⟩ := dq_skip_ddca3f43 hcode hX (by rw [hsel]; decide)
  obtain ⟨G17, hX⟩ := dq_skip_fee3f7f9 hcode hX (by rw [hsel]; decide)
  obtain ⟨G18, hX⟩ := dq_skip_8da5cb5b hcode hX (by rw [hsel]; decide)
  obtain ⟨G19, hX⟩ := dq_skip_5409491a hcode hX (by rw [hsel]; decide)
  obtain ⟨G20, hX⟩ := dq_skip_b4b577ad hcode hX (by rw [hsel]; decide)
  obtain ⟨G21, hX⟩ := dq_arm_initialATime hcode hsel hX
  have hst : (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G21).stack =
      [] ++ ([] : List B256) := rfl
  have hfr : FrameMatches (0 : B256) ([] : List AVal) ([] : List B256) := List.Forall₂.nil
  have hmm : MemMatches (0 : B256) ([] : MemMap)
      (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G21).memory :=
    memMatches_nil _ _
  rcases xa_node_span checkedM admRawExecFreeSet hcode hfork admRaw_check_initialATimeGetter
      admRaw_free_initialATimeGetter hst hfr hmm hX with
    ⟨run, hL⟩ | ⟨d', S', run, _hX', _hst', _hlen'⟩
  · obtain ⟨o, hstep, hlands⟩ := safe_initialATimeGetter hfork hck hsel hlen _ _ run
    exact ⟨quietEnv sevm, o, hstep, rawEffect_of_quietLands hL hlands⟩
  · obtain ⟨post', hcon⟩ := admRawRun_halted admRaw_halt_initialATimeGetter run
    cases hcon

/-- **The `future_A_time` raw effect.** -/
theorem futureATime_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selFutureATime)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨G1, hX⟩ := dq_to_3040 hcode hlen hcd hx
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
  obtain ⟨G2, hX⟩ := dq_to_499b hcode hX
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide)
  obtain ⟨G3, hX⟩ := dq_skip_5b5a1467 hcode hX (by rw [hsel]; decide)
  obtain ⟨G4, hX⟩ := dq_skip_4f12fe97 hcode hX (by rw [hsel]; decide)
  obtain ⟨G5, hX⟩ := dq_skip_226840fb hcode hX (by rw [hsel]; decide)
  obtain ⟨G6, hX⟩ := dq_skip_6b441a40 hcode hX (by rw [hsel]; decide)
  obtain ⟨G7, hX⟩ := dq_skip_6a1c05ae hcode hX (by rw [hsel]; decide)
  obtain ⟨G8, hX⟩ := dq_skip_86fbf193 hcode hX (by rw [hsel]; decide)
  obtain ⟨G9, hX⟩ := dq_skip_e2e7d264 hcode hX (by rw [hsel]; decide)
  obtain ⟨G10, hX⟩ := dq_skip_30c54085 hcode hX (by rw [hsel]; decide)
  obtain ⟨G11, hX⟩ := dq_skip_524c3901 hcode hX (by rw [hsel]; decide)
  obtain ⟨G12, hX⟩ := dq_skip_e3698853 hcode hX (by rw [hsel]; decide)
  obtain ⟨G13, hX⟩ := dq_skip_3046f972 hcode hX (by rw [hsel]; decide)
  obtain ⟨G14, hX⟩ := dq_skip_c6610657 hcode hX (by rw [hsel]; decide)
  obtain ⟨G15, hX⟩ := dq_skip_4903b0d1 hcode hX (by rw [hsel]; decide)
  obtain ⟨G16, hX⟩ := dq_skip_ddca3f43 hcode hX (by rw [hsel]; decide)
  obtain ⟨G17, hX⟩ := dq_skip_fee3f7f9 hcode hX (by rw [hsel]; decide)
  obtain ⟨G18, hX⟩ := dq_skip_8da5cb5b hcode hX (by rw [hsel]; decide)
  obtain ⟨G19, hX⟩ := dq_skip_5409491a hcode hX (by rw [hsel]; decide)
  obtain ⟨G20, hX⟩ := dq_skip_b4b577ad hcode hX (by rw [hsel]; decide)
  obtain ⟨G21, hX⟩ := dq_skip_2081066c hcode hX (by rw [hsel]; decide)
  obtain ⟨G22, hX⟩ := dq_arm_futureATime hcode hsel hX
  have hst : (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G22).stack =
      [] ++ ([] : List B256) := rfl
  have hfr : FrameMatches (0 : B256) ([] : List AVal) ([] : List B256) := List.Forall₂.nil
  have hmm : MemMatches (0 : B256) ([] : MemMap)
      (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G22).memory :=
    memMatches_nil _ _
  rcases xa_node_span checkedM admRawExecFreeSet hcode hfork admRaw_check_futureATimeGetter
      admRaw_free_futureATimeGetter hst hfr hmm hX with
    ⟨run, hL⟩ | ⟨d', S', run, _hX', _hst', _hlen'⟩
  · obtain ⟨o, hstep, hlands⟩ := safe_futureATimeGetter hfork hck hsel hlen _ _ run
    exact ⟨quietEnv sevm, o, hstep, rawEffect_of_quietLands hL hlands⟩
  · obtain ⟨post', hcon⟩ := admRawRun_halted admRaw_halt_futureATimeGetter run
    cases hcon

/-- **The `admin_actions_deadline` raw effect.** -/
theorem adminActionsDeadline_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selAdminActionsDeadline)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨G1, hX⟩ := dq_to_3040 hcode hlen hcd hx
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
  obtain ⟨G2, hX⟩ := dq_to_499b hcode hX
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide)
  obtain ⟨G3, hX⟩ := dq_skip_5b5a1467 hcode hX (by rw [hsel]; decide)
  obtain ⟨G4, hX⟩ := dq_skip_4f12fe97 hcode hX (by rw [hsel]; decide)
  obtain ⟨G5, hX⟩ := dq_skip_226840fb hcode hX (by rw [hsel]; decide)
  obtain ⟨G6, hX⟩ := dq_skip_6b441a40 hcode hX (by rw [hsel]; decide)
  obtain ⟨G7, hX⟩ := dq_skip_6a1c05ae hcode hX (by rw [hsel]; decide)
  obtain ⟨G8, hX⟩ := dq_skip_86fbf193 hcode hX (by rw [hsel]; decide)
  obtain ⟨G9, hX⟩ := dq_skip_e2e7d264 hcode hX (by rw [hsel]; decide)
  obtain ⟨G10, hX⟩ := dq_skip_30c54085 hcode hX (by rw [hsel]; decide)
  obtain ⟨G11, hX⟩ := dq_skip_524c3901 hcode hX (by rw [hsel]; decide)
  obtain ⟨G12, hX⟩ := dq_skip_e3698853 hcode hX (by rw [hsel]; decide)
  obtain ⟨G13, hX⟩ := dq_skip_3046f972 hcode hX (by rw [hsel]; decide)
  obtain ⟨G14, hX⟩ := dq_skip_c6610657 hcode hX (by rw [hsel]; decide)
  obtain ⟨G15, hX⟩ := dq_skip_4903b0d1 hcode hX (by rw [hsel]; decide)
  obtain ⟨G16, hX⟩ := dq_skip_ddca3f43 hcode hX (by rw [hsel]; decide)
  obtain ⟨G17, hX⟩ := dq_skip_fee3f7f9 hcode hX (by rw [hsel]; decide)
  obtain ⟨G18, hX⟩ := dq_skip_8da5cb5b hcode hX (by rw [hsel]; decide)
  obtain ⟨G19, hX⟩ := dq_skip_5409491a hcode hX (by rw [hsel]; decide)
  obtain ⟨G20, hX⟩ := dq_skip_b4b577ad hcode hX (by rw [hsel]; decide)
  obtain ⟨G21, hX⟩ := dq_skip_2081066c hcode hX (by rw [hsel]; decide)
  obtain ⟨G22, hX⟩ := dq_skip_14052288 hcode hX (by rw [hsel]; decide)
  obtain ⟨G23, hX⟩ := dq_arm_adminActionsDeadline hcode hsel hX
  have hst : (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G23).stack =
      [] ++ ([] : List B256) := rfl
  have hfr : FrameMatches (0 : B256) ([] : List AVal) ([] : List B256) := List.Forall₂.nil
  have hmm : MemMatches (0 : B256) ([] : MemMap)
      (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G23).memory :=
    memMatches_nil _ _
  rcases xa_node_span checkedM admRawExecFreeSet hcode hfork
      admRaw_check_adminActionsDeadlineGetter admRaw_free_adminActionsDeadlineGetter hst hfr hmm
      hX with
    ⟨run, hL⟩ | ⟨d', S', run, _hX', _hst', _hlen'⟩
  · obtain ⟨o, hstep, hlands⟩ := safe_adminActionsDeadlineGetter hfork hck hsel hlen _ _ run
    exact ⟨quietEnv sevm, o, hstep, rawEffect_of_quietLands hL hlands⟩
  · obtain ⟨post', hcon⟩ := admRawRun_halted admRaw_halt_adminActionsDeadlineGetter run
    cases hcon

/-- **The `transfer_ownership_deadline` raw effect.** -/
theorem transferOwnershipDeadline_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selTransferOwnershipDeadline)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨G1, hX⟩ := dq_to_3040 hcode hlen hcd hx
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
  obtain ⟨G2, hX⟩ := dq_to_499b hcode hX
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide)
  obtain ⟨G3, hX⟩ := dq_skip_5b5a1467 hcode hX (by rw [hsel]; decide)
  obtain ⟨G4, hX⟩ := dq_skip_4f12fe97 hcode hX (by rw [hsel]; decide)
  obtain ⟨G5, hX⟩ := dq_skip_226840fb hcode hX (by rw [hsel]; decide)
  obtain ⟨G6, hX⟩ := dq_skip_6b441a40 hcode hX (by rw [hsel]; decide)
  obtain ⟨G7, hX⟩ := dq_skip_6a1c05ae hcode hX (by rw [hsel]; decide)
  obtain ⟨G8, hX⟩ := dq_skip_86fbf193 hcode hX (by rw [hsel]; decide)
  obtain ⟨G9, hX⟩ := dq_skip_e2e7d264 hcode hX (by rw [hsel]; decide)
  obtain ⟨G10, hX⟩ := dq_skip_30c54085 hcode hX (by rw [hsel]; decide)
  obtain ⟨G11, hX⟩ := dq_skip_524c3901 hcode hX (by rw [hsel]; decide)
  obtain ⟨G12, hX⟩ := dq_skip_e3698853 hcode hX (by rw [hsel]; decide)
  obtain ⟨G13, hX⟩ := dq_skip_3046f972 hcode hX (by rw [hsel]; decide)
  obtain ⟨G14, hX⟩ := dq_skip_c6610657 hcode hX (by rw [hsel]; decide)
  obtain ⟨G15, hX⟩ := dq_skip_4903b0d1 hcode hX (by rw [hsel]; decide)
  obtain ⟨G16, hX⟩ := dq_skip_ddca3f43 hcode hX (by rw [hsel]; decide)
  obtain ⟨G17, hX⟩ := dq_skip_fee3f7f9 hcode hX (by rw [hsel]; decide)
  obtain ⟨G18, hX⟩ := dq_skip_8da5cb5b hcode hX (by rw [hsel]; decide)
  obtain ⟨G19, hX⟩ := dq_skip_5409491a hcode hX (by rw [hsel]; decide)
  obtain ⟨G20, hX⟩ := dq_skip_b4b577ad hcode hX (by rw [hsel]; decide)
  obtain ⟨G21, hX⟩ := dq_skip_2081066c hcode hX (by rw [hsel]; decide)
  obtain ⟨G22, hX⟩ := dq_skip_14052288 hcode hX (by rw [hsel]; decide)
  obtain ⟨G23, hX⟩ := dq_skip_405e28f8 hcode hX (by rw [hsel]; decide)
  obtain ⟨G24, hX⟩ := dq_arm_transferOwnershipDeadline hcode hsel hX
  have hst : (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G24).stack =
      [] ++ ([] : List B256) := rfl
  have hfr : FrameMatches (0 : B256) ([] : List AVal) ([] : List B256) := List.Forall₂.nil
  have hmm : MemMatches (0 : B256) ([] : MemMap)
      (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G24).memory :=
    memMatches_nil _ _
  rcases xa_node_span checkedM admRawExecFreeSet hcode hfork
      admRaw_check_transferOwnershipDeadlineGetter admRaw_free_transferOwnershipDeadlineGetter hst
      hfr hmm hX with
    ⟨run, hL⟩ | ⟨d', S', run, _hX', _hst', _hlen'⟩
  · obtain ⟨o, hstep, hlands⟩ := safe_transferOwnershipDeadlineGetter hfork hck hsel hlen _ _ run
    exact ⟨quietEnv sevm, o, hstep, rawEffect_of_quietLands hL hlands⟩
  · obtain ⟨post', hcon⟩ := admRawRun_halted admRaw_halt_transferOwnershipDeadlineGetter run
    cases hcon

/-- **The `future_fee` raw effect.** -/
theorem futureFee_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selFutureFee)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨G1, hX⟩ := dq_to_3040 hcode hlen hcd hx
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
  obtain ⟨G2, hX⟩ := dq_to_499b hcode hX
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide)
  obtain ⟨G3, hX⟩ := dq_skip_5b5a1467 hcode hX (by rw [hsel]; decide)
  obtain ⟨G4, hX⟩ := dq_skip_4f12fe97 hcode hX (by rw [hsel]; decide)
  obtain ⟨G5, hX⟩ := dq_skip_226840fb hcode hX (by rw [hsel]; decide)
  obtain ⟨G6, hX⟩ := dq_skip_6b441a40 hcode hX (by rw [hsel]; decide)
  obtain ⟨G7, hX⟩ := dq_skip_6a1c05ae hcode hX (by rw [hsel]; decide)
  obtain ⟨G8, hX⟩ := dq_skip_86fbf193 hcode hX (by rw [hsel]; decide)
  obtain ⟨G9, hX⟩ := dq_skip_e2e7d264 hcode hX (by rw [hsel]; decide)
  obtain ⟨G10, hX⟩ := dq_skip_30c54085 hcode hX (by rw [hsel]; decide)
  obtain ⟨G11, hX⟩ := dq_skip_524c3901 hcode hX (by rw [hsel]; decide)
  obtain ⟨G12, hX⟩ := dq_skip_e3698853 hcode hX (by rw [hsel]; decide)
  obtain ⟨G13, hX⟩ := dq_skip_3046f972 hcode hX (by rw [hsel]; decide)
  obtain ⟨G14, hX⟩ := dq_skip_c6610657 hcode hX (by rw [hsel]; decide)
  obtain ⟨G15, hX⟩ := dq_skip_4903b0d1 hcode hX (by rw [hsel]; decide)
  obtain ⟨G16, hX⟩ := dq_skip_ddca3f43 hcode hX (by rw [hsel]; decide)
  obtain ⟨G17, hX⟩ := dq_skip_fee3f7f9 hcode hX (by rw [hsel]; decide)
  obtain ⟨G18, hX⟩ := dq_skip_8da5cb5b hcode hX (by rw [hsel]; decide)
  obtain ⟨G19, hX⟩ := dq_skip_5409491a hcode hX (by rw [hsel]; decide)
  obtain ⟨G20, hX⟩ := dq_skip_b4b577ad hcode hX (by rw [hsel]; decide)
  obtain ⟨G21, hX⟩ := dq_skip_2081066c hcode hX (by rw [hsel]; decide)
  obtain ⟨G22, hX⟩ := dq_skip_14052288 hcode hX (by rw [hsel]; decide)
  obtain ⟨G23, hX⟩ := dq_skip_405e28f8 hcode hX (by rw [hsel]; decide)
  obtain ⟨G24, hX⟩ := dq_skip_e0a0b586 hcode hX (by rw [hsel]; decide)
  obtain ⟨G25, hX⟩ := dq_arm_futureFee hcode hsel hX
  have hst : (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G25).stack =
      [] ++ ([] : List B256) := rfl
  have hfr : FrameMatches (0 : B256) ([] : List AVal) ([] : List B256) := List.Forall₂.nil
  have hmm : MemMatches (0 : B256) ([] : MemMap)
      (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G25).memory :=
    memMatches_nil _ _
  rcases xa_node_span checkedM admRawExecFreeSet hcode hfork admRaw_check_futureFeeGetter
      admRaw_free_futureFeeGetter hst hfr hmm hX with
    ⟨run, hL⟩ | ⟨d', S', run, _hX', _hst', _hlen'⟩
  · obtain ⟨o, hstep, hlands⟩ := safe_futureFeeGetter hfork hck hsel hlen _ _ run
    exact ⟨quietEnv sevm, o, hstep, rawEffect_of_quietLands hL hlands⟩
  · obtain ⟨post', hcon⟩ := admRawRun_halted admRaw_halt_futureFeeGetter run
    cases hcon

/-- **The `future_admin_fee` raw effect.** -/
theorem futureAdminFee_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selFutureAdminFee)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨G1, hX⟩ := dq_to_3040 hcode hlen hcd hx
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
  obtain ⟨G2, hX⟩ := dq_to_499b hcode hX
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide)
  obtain ⟨G3, hX⟩ := dq_skip_5b5a1467 hcode hX (by rw [hsel]; decide)
  obtain ⟨G4, hX⟩ := dq_skip_4f12fe97 hcode hX (by rw [hsel]; decide)
  obtain ⟨G5, hX⟩ := dq_skip_226840fb hcode hX (by rw [hsel]; decide)
  obtain ⟨G6, hX⟩ := dq_skip_6b441a40 hcode hX (by rw [hsel]; decide)
  obtain ⟨G7, hX⟩ := dq_skip_6a1c05ae hcode hX (by rw [hsel]; decide)
  obtain ⟨G8, hX⟩ := dq_skip_86fbf193 hcode hX (by rw [hsel]; decide)
  obtain ⟨G9, hX⟩ := dq_skip_e2e7d264 hcode hX (by rw [hsel]; decide)
  obtain ⟨G10, hX⟩ := dq_skip_30c54085 hcode hX (by rw [hsel]; decide)
  obtain ⟨G11, hX⟩ := dq_skip_524c3901 hcode hX (by rw [hsel]; decide)
  obtain ⟨G12, hX⟩ := dq_skip_e3698853 hcode hX (by rw [hsel]; decide)
  obtain ⟨G13, hX⟩ := dq_skip_3046f972 hcode hX (by rw [hsel]; decide)
  obtain ⟨G14, hX⟩ := dq_skip_c6610657 hcode hX (by rw [hsel]; decide)
  obtain ⟨G15, hX⟩ := dq_skip_4903b0d1 hcode hX (by rw [hsel]; decide)
  obtain ⟨G16, hX⟩ := dq_skip_ddca3f43 hcode hX (by rw [hsel]; decide)
  obtain ⟨G17, hX⟩ := dq_skip_fee3f7f9 hcode hX (by rw [hsel]; decide)
  obtain ⟨G18, hX⟩ := dq_skip_8da5cb5b hcode hX (by rw [hsel]; decide)
  obtain ⟨G19, hX⟩ := dq_skip_5409491a hcode hX (by rw [hsel]; decide)
  obtain ⟨G20, hX⟩ := dq_skip_b4b577ad hcode hX (by rw [hsel]; decide)
  obtain ⟨G21, hX⟩ := dq_skip_2081066c hcode hX (by rw [hsel]; decide)
  obtain ⟨G22, hX⟩ := dq_skip_14052288 hcode hX (by rw [hsel]; decide)
  obtain ⟨G23, hX⟩ := dq_skip_405e28f8 hcode hX (by rw [hsel]; decide)
  obtain ⟨G24, hX⟩ := dq_skip_e0a0b586 hcode hX (by rw [hsel]; decide)
  obtain ⟨G25, hX⟩ := dq_skip_58680d0b hcode hX (by rw [hsel]; decide)
  obtain ⟨G26, hX⟩ := dq_arm_futureAdminFee hcode hsel hX
  have hst : (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G26).stack =
      [] ++ ([] : List B256) := rfl
  have hfr : FrameMatches (0 : B256) ([] : List AVal) ([] : List B256) := List.Forall₂.nil
  have hmm : MemMatches (0 : B256) ([] : MemMap)
      (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G26).memory :=
    memMatches_nil _ _
  rcases xa_node_span checkedM admRawExecFreeSet hcode hfork admRaw_check_futureAdminFeeGetter
      admRaw_free_futureAdminFeeGetter hst hfr hmm hX with
    ⟨run, hL⟩ | ⟨d', S', run, _hX', _hst', _hlen'⟩
  · obtain ⟨o, hstep, hlands⟩ := safe_futureAdminFeeGetter hfork hck hsel hlen _ _ run
    exact ⟨quietEnv sevm, o, hstep, rawEffect_of_quietLands hL hlands⟩
  · obtain ⟨post', hcon⟩ := admRawRun_halted admRaw_halt_futureAdminFeeGetter run
    cases hcon

/-- **The `future_owner` raw effect.** -/
theorem futureOwner_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selFutureOwner)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨G1, hX⟩ := dq_to_3040 hcode hlen hcd hx
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
  obtain ⟨G2, hX⟩ := dq_to_499b hcode hX
    (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide) (by rw [hsel]; decide)
    (by rw [hsel]; decide)
  obtain ⟨G3, hX⟩ := dq_skip_5b5a1467 hcode hX (by rw [hsel]; decide)
  obtain ⟨G4, hX⟩ := dq_skip_4f12fe97 hcode hX (by rw [hsel]; decide)
  obtain ⟨G5, hX⟩ := dq_skip_226840fb hcode hX (by rw [hsel]; decide)
  obtain ⟨G6, hX⟩ := dq_skip_6b441a40 hcode hX (by rw [hsel]; decide)
  obtain ⟨G7, hX⟩ := dq_skip_6a1c05ae hcode hX (by rw [hsel]; decide)
  obtain ⟨G8, hX⟩ := dq_skip_86fbf193 hcode hX (by rw [hsel]; decide)
  obtain ⟨G9, hX⟩ := dq_skip_e2e7d264 hcode hX (by rw [hsel]; decide)
  obtain ⟨G10, hX⟩ := dq_skip_30c54085 hcode hX (by rw [hsel]; decide)
  obtain ⟨G11, hX⟩ := dq_skip_524c3901 hcode hX (by rw [hsel]; decide)
  obtain ⟨G12, hX⟩ := dq_skip_e3698853 hcode hX (by rw [hsel]; decide)
  obtain ⟨G13, hX⟩ := dq_skip_3046f972 hcode hX (by rw [hsel]; decide)
  obtain ⟨G14, hX⟩ := dq_skip_c6610657 hcode hX (by rw [hsel]; decide)
  obtain ⟨G15, hX⟩ := dq_skip_4903b0d1 hcode hX (by rw [hsel]; decide)
  obtain ⟨G16, hX⟩ := dq_skip_ddca3f43 hcode hX (by rw [hsel]; decide)
  obtain ⟨G17, hX⟩ := dq_skip_fee3f7f9 hcode hX (by rw [hsel]; decide)
  obtain ⟨G18, hX⟩ := dq_skip_8da5cb5b hcode hX (by rw [hsel]; decide)
  obtain ⟨G19, hX⟩ := dq_skip_5409491a hcode hX (by rw [hsel]; decide)
  obtain ⟨G20, hX⟩ := dq_skip_b4b577ad hcode hX (by rw [hsel]; decide)
  obtain ⟨G21, hX⟩ := dq_skip_2081066c hcode hX (by rw [hsel]; decide)
  obtain ⟨G22, hX⟩ := dq_skip_14052288 hcode hX (by rw [hsel]; decide)
  obtain ⟨G23, hX⟩ := dq_skip_405e28f8 hcode hX (by rw [hsel]; decide)
  obtain ⟨G24, hX⟩ := dq_skip_e0a0b586 hcode hX (by rw [hsel]; decide)
  obtain ⟨G25, hX⟩ := dq_skip_58680d0b hcode hX (by rw [hsel]; decide)
  obtain ⟨G26, hX⟩ := dq_skip_e3824462 hcode hX (by rw [hsel]; decide)
  obtain ⟨G27, hX⟩ := dq_arm_futureOwner hcode hsel hX
  have hst : (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G27).stack =
      [] ++ ([] : List B256) := rfl
  have hfr : FrameMatches (0 : B256) ([] : List AVal) ([] : List B256) := List.Forall₂.nil
  have hmm : MemMatches (0 : B256) ([] : MemMap)
      (St pre [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G27).memory :=
    memMatches_nil _ _
  rcases xa_node_span checkedM admRawExecFreeSet hcode hfork admRaw_check_futureOwnerGetter
      admRaw_free_futureOwnerGetter hst hfr hmm hX with
    ⟨run, hL⟩ | ⟨d', S', run, _hX', _hst', _hlen'⟩
  · obtain ⟨o, hstep, hlands⟩ := safe_futureOwnerGetter hfork hck hsel hlen _ _ run
    exact ⟨quietEnv sevm, o, hstep, rawEffect_of_quietLands hL hlands⟩
  · obtain ⟨post', hcon⟩ := admRawRun_halted admRaw_halt_futureOwnerGetter run
    cases hcon

end Blanc.Lift.Curve3Pool
