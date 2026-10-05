import Blanc.Lift.UniswapV2Pair.HistoryWriters
import Blanc.Lift.UniswapV2Pair.HistoryWriterCheck
import Blanc.Lift.ReachDispatch
import Blanc.Lift.ReachChain

/-! Stateful literal dispatch excludes external instructions on each noncalling
writer's actual raw continuation chain. Thus its committed observation is its
own root exactly, with no recursively consumed child to replay again. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

private theorem noncalling_selector_noExecReach {D : Exec.Deriv} {sevm : Sevm}
    {b : Devm} {M : Mem} {G : Nat} {T : Conf} (writer : NoncallingWriter)
    (selector : Blanc.Sevm.selector sevm = writer.selector)
    (run : Reach (StepIn D) cert.prog sevm ⟨St b [] M G, t_001a_c0, []⟩ T)
    (target : AtExec T) : False := by
  have h := run
  unfold t_001a_c0 at h
  obtain ⟨d, hd, h⟩ := rr_next h target
  obtain ⟨_, rfl⟩ := ri_push hd.toRun
  obtain ⟨d, hd, h⟩ := rr_next h target
  obtain ⟨_, rfl⟩ := ri_calldataload hd.toRun
  obtain ⟨d, hd, h⟩ := rr_next h target
  obtain ⟨_, rfl⟩ := ri_push hd.toRun
  obtain ⟨d, hd, h⟩ := rr_next h target
  obtain ⟨_, hd⟩ := ri_shr hd.toRun
  simp only [show Bytes.toB256 [0] = (0 : B256) from rfl,
    show Bytes.toB256 [0xe0] = (224 : B256) from rfl,
    show (224 : B256).toNat = 224 from rfl,
    show Sevm.dataWord sevm 0 >>> 224 = writer.selector from selector] at hd
  subst d
  cases writer with
  | approve =>
    change Reach (StepIn D) cert.prog sevm ⟨St b [0x095ea7b3] M _, _, []⟩ T at h
    obtain ⟨_, h⟩ := rr_cmp_gt StepIn.toRun h target
    simp only [show B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42]) (0x095ea7b3 : B256)
      = (1 : B256) from by decide, show (1 : B256) ≠ 0 from by decide, ite_false] at h
    unfold t_00f9_c0 at h
    obtain ⟨_, h⟩ := rr_dest h target
    obtain ⟨_, h⟩ := rr_cmp_gt StepIn.toRun h target
    simp only [show B256.gtCheck (Bytes.toB256 [0x23, 0xb8, 0x72, 0xdd]) (0x095ea7b3 : B256)
      = (1 : B256) from by decide, show (1 : B256) ≠ 0 from by decide, ite_false] at h
    unfold t_0166_c0 at h
    obtain ⟨_, h⟩ := rr_dest h target
    obtain ⟨_, h⟩ := rr_cmp_gt StepIn.toRun h target
    simp only [show B256.gtCheck (Bytes.toB256 [0x09, 0x5e, 0xa7, 0xb3]) (0x095ea7b3 : B256)
      = (0 : B256) from by decide, ite_true] at h
    unfold t_0172_c0 at h
    obtain ⟨_, h⟩ := rr_cmp_eq StepIn.toRun (g := t_0315_c96) rfl h target
    simp only [show B256.eqCheck (Bytes.toB256 [0x09, 0x5e, 0xa7, 0xb3]) (0x095ea7b3 : B256)
      = (1 : B256) from by decide, show (1 : B256) ≠ 0 from by decide, ite_false] at h
    exact Reach.false_of_execFree historyWriterExecFreeEntries_set h target
      (NoncallingWriter.wrapper_execFree .approve) (by intro s hs; cases hs)
  | transfer =>
    change Reach (StepIn D) cert.prog sevm ⟨St b [0xa9059cbb] M _, _, []⟩ T at h
    obtain ⟨_, h⟩ := rr_cmp_gt StepIn.toRun h target
    simp only [show B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42]) (0xa9059cbb : B256)
      = (0 : B256) from by decide, ite_true] at h
    unfold t_002b_c0 at h
    obtain ⟨_, h⟩ := rr_cmp_gt StepIn.toRun h target
    simp only [show B256.gtCheck (Bytes.toB256 [0xba, 0x9a, 0x7a, 0x56]) (0xa9059cbb : B256)
      = (1 : B256) from by decide, show (1 : B256) ≠ 0 from by decide, ite_false] at h
    unfold t_0097_c0 at h
    obtain ⟨_, h⟩ := rr_dest h target
    obtain ⟨_, h⟩ := rr_cmp_gt StepIn.toRun h target
    simp only [show B256.gtCheck (Bytes.toB256 [0x7e, 0xce, 0xbe, 0x00]) (0xa9059cbb : B256)
      = (0 : B256) from by decide, ite_true] at h
    unfold t_00a3_c0 at h
    obtain ⟨_, h⟩ := rr_cmp_eq StepIn.toRun (g := t_04d7_c82) rfl h target
    simp only [show B256.eqCheck (Bytes.toB256 [0x7e, 0xce, 0xbe, 0x00]) (0xa9059cbb : B256)
      = (0 : B256) from by decide, ite_true] at h
    unfold t_00ae_c0 at h
    obtain ⟨_, h⟩ := rr_cmp_eq StepIn.toRun (g := t_050a_c83) rfl h target
    simp only [show B256.eqCheck (Bytes.toB256 [0x89, 0xaf, 0xcb, 0x44]) (0xa9059cbb : B256)
      = (0 : B256) from by decide, ite_true] at h
    unfold t_00b9_c0 at h
    obtain ⟨_, h⟩ := rr_cmp_eq StepIn.toRun (g := t_0556_c84) rfl h target
    simp only [show B256.eqCheck (Bytes.toB256 [0x95, 0xd8, 0x9b, 0x41]) (0xa9059cbb : B256)
      = (0 : B256) from by decide, ite_true] at h
    unfold t_00c4_c0 at h
    obtain ⟨_, h⟩ := rr_cmp_eq StepIn.toRun (g := t_055e_c85) rfl h target
    simp only [show B256.eqCheck (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb]) (0xa9059cbb : B256)
      = (1 : B256) from by decide, show (1 : B256) ≠ 0 from by decide, ite_false] at h
    exact Reach.false_of_execFree historyWriterExecFreeEntries_set h target
      (NoncallingWriter.wrapper_execFree .transfer) (by intro s hs; cases hs)
  | transferFrom =>
    change Reach (StepIn D) cert.prog sevm ⟨St b [0x23b872dd] M _, _, []⟩ T at h
    obtain ⟨_, h⟩ := rr_cmp_gt StepIn.toRun h target
    simp only [show B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42]) (0x23b872dd : B256)
      = (1 : B256) from by decide, show (1 : B256) ≠ 0 from by decide, ite_false] at h
    unfold t_00f9_c0 at h
    obtain ⟨_, h⟩ := rr_dest h target
    obtain ⟨_, h⟩ := rr_cmp_gt StepIn.toRun h target
    simp only [show B256.gtCheck (Bytes.toB256 [0x23, 0xb8, 0x72, 0xdd]) (0x23b872dd : B256)
      = (0 : B256) from by decide, ite_true] at h
    unfold t_0105_c0 at h
    obtain ⟨_, h⟩ := rr_cmp_gt StepIn.toRun h target
    simp only [show B256.gtCheck (Bytes.toB256 [0x36, 0x44, 0xe5, 0x15]) (0x23b872dd : B256)
      = (1 : B256) from by decide, show (1 : B256) ≠ 0 from by decide, ite_false] at h
    unfold t_0140_c0 at h
    obtain ⟨_, h⟩ := rr_dest h target
    obtain ⟨_, h⟩ := rr_cmp_eq StepIn.toRun (g := t_03ad_c93) rfl h target
    simp only [show B256.eqCheck (Bytes.toB256 [0x23, 0xb8, 0x72, 0xdd]) (0x23b872dd : B256)
      = (1 : B256) from by decide, show (1 : B256) ≠ 0 from by decide, ite_false] at h
    exact Reach.false_of_execFree historyWriterExecFreeEntries_set h target
      (NoncallingWriter.wrapper_execFree .transferFrom) (by intro s hs; cases hs)
  | «initialize» =>
    change Reach (StepIn D) cert.prog sevm ⟨St b [0x485cc955] M _, _, []⟩ T at h
    obtain ⟨_, h⟩ := rr_cmp_gt StepIn.toRun h target
    simp only [show B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42]) (0x485cc955 : B256)
      = (1 : B256) from by decide, show (1 : B256) ≠ 0 from by decide, ite_false] at h
    unfold t_00f9_c0 at h
    obtain ⟨_, h⟩ := rr_dest h target
    obtain ⟨_, h⟩ := rr_cmp_gt StepIn.toRun h target
    simp only [show B256.gtCheck (Bytes.toB256 [0x23, 0xb8, 0x72, 0xdd]) (0x485cc955 : B256)
      = (0 : B256) from by decide, ite_true] at h
    unfold t_0105_c0 at h
    obtain ⟨_, h⟩ := rr_cmp_gt StepIn.toRun h target
    simp only [show B256.gtCheck (Bytes.toB256 [0x36, 0x44, 0xe5, 0x15]) (0x485cc955 : B256)
      = (0 : B256) from by decide, ite_true] at h
    unfold t_0110_c0 at h
    obtain ⟨_, h⟩ := rr_cmp_eq StepIn.toRun (g := t_0416_c89) rfl h target
    simp only [show B256.eqCheck (Bytes.toB256 [0x36, 0x44, 0xe5, 0x15]) (0x485cc955 : B256)
      = (0 : B256) from by decide, ite_true] at h
    unfold t_011b_c0 at h
    obtain ⟨_, h⟩ := rr_cmp_eq StepIn.toRun (g := t_041e_c90) rfl h target
    simp only [show B256.eqCheck (Bytes.toB256 [0x48, 0x5c, 0xc9, 0x55]) (0x485cc955 : B256)
      = (1 : B256) from by decide, show (1 : B256) ≠ 0 from by decide, ite_false] at h
    exact Reach.false_of_execFree historyWriterExecFreeEntries_set h target
      (NoncallingWriter.wrapper_execFree .«initialize») (by intro s hs; cases hs)

private theorem noncalling_noExecReach {D : Exec.Deriv} {sevm : Sevm}
    {b : Devm} {G : Nat} {T : Conf} (writer : NoncallingWriter)
    (selector : Blanc.Sevm.selector sevm = writer.selector)
    (run : Reach (StepIn D) cert.prog sevm ⟨St b [] Mem.empty G, t_0000_c0, []⟩ T)
    (target : AtExec T) : False := by
  have h := run
  unfold t_0000_c0 at h
  obtain ⟨d, hd, h⟩ := rr_next h target; obtain ⟨_, rfl⟩ := ri_push hd.toRun
  obtain ⟨d, hd, h⟩ := rr_next h target; obtain ⟨_, rfl⟩ := ri_push hd.toRun
  obtain ⟨d, hd, h⟩ := rr_next h target
  obtain ⟨_, hd⟩ := ri_mstore hd.toRun
  simp only [show Bytes.toB256 [0x40] = (64 : B256) from rfl,
    show (64 : B256).toNat = 64 from rfl,
    show Bytes.toB256 [0x80] = (128 : B256) from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := rr_next h target; obtain ⟨_, rfl⟩ := ri_callvalue hd.toRun
  obtain ⟨d, hd, h⟩ := rr_next h target; obtain ⟨_, rfl⟩ := ri_dup rfl hd.toRun
  obtain ⟨d, hd, h⟩ := rr_next h target; obtain ⟨_, rfl⟩ := ri_iszero hd.toRun
  obtain ⟨d, hd, h⟩ := rr_next h target; obtain ⟨_, rfl⟩ := ri_push hd.toRun
  rcases rr_branch h target with ⟨_, _, rejected⟩ | ⟨_, _, h⟩
  · exact Reach.false_of_execFree historyWriterExecFreeEntries_set rejected target
      historyWriterRevert_execFree.1 (by intro s hs; cases hs)
  · unfold t_0010_c0 at h
    obtain ⟨_, h⟩ := rr_dest h target
    obtain ⟨d, hd, h⟩ := rr_next h target; obtain ⟨_, rfl⟩ := ri_pop hd.toRun
    obtain ⟨d, hd, h⟩ := rr_next h target; obtain ⟨_, rfl⟩ := ri_push hd.toRun
    obtain ⟨d, hd, h⟩ := rr_next h target; obtain ⟨_, rfl⟩ := ri_calldatasize hd.toRun
    obtain ⟨d, hd, h⟩ := rr_next h target; obtain ⟨_, rfl⟩ := ri_lt hd.toRun
    obtain ⟨d, hd, h⟩ := rr_next h target; obtain ⟨_, rfl⟩ := ri_push hd.toRun
    rcases rr_branch h target with ⟨_, _, h⟩ | ⟨_, _, rejected⟩
    · exact noncalling_selector_noExecReach writer selector h target
    · exact Reach.false_of_execFree historyWriterExecFreeEntries_set rejected target
        historyWriterRevert_execFree.2 (by intro s hs; cases hs)

/-- Actual raw same-frame nodes of these four literal selector routes cannot
decode an external instruction. This is derived from stateful reach, not an
assumption about the source transcript or its final storage. -/
theorem noncalling_no_exec {sevm : Sevm} {b : Devm} {G : Nat} {out : Execution}
    (run : Exec 0 sevm (St b [] Mem.empty G) out) (writer : NoncallingWriter)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = writer.selector) :
    ∀ node : Exec.Deriv, Exec.Deriv.ParentPrefix ⟨0, sevm, St b [] Mem.empty G, out, run⟩ node →
      ∀ x, ¬ Ninst.At node.sevm.code node.pc (.exec x) := by
  intro node chain x decoded
  obtain ⟨cursor, reach, ok⟩ := reach_of_parentPrefix cert_check rfl codeEq fork chain
  obtain ⟨tail, tree, _⟩ := ok.tree_of_exec decoded
  have target : AtExec (cursor.conf node.devm) := ⟨x, tail, tree⟩
  change Reach (StepIn _) cert.prog sevm ⟨St b [] Mem.empty G, t_0000_c0, []⟩ _ at reach
  exact noncalling_noExecReach writer selector reach target

theorem noncalling_descendants_nil {sevm : Sevm} {b : Devm} {G : Nat} {out : Execution}
    (run : Exec 0 sevm (St b [] Mem.empty G) out) (writer : NoncallingWriter)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = writer.selector) :
    Exec.descendantFrames run = [] :=
  Blanc.Exec.descendantFrames_eq_nil_of_noExec run (noncalling_no_exec run writer codeEq fork selector)

theorem noncalling_committed_frames {sevm : Sevm} {b : Devm} {G : Nat} {out : Execution}
    (run : Exec 0 sevm (St b [] Mem.empty G) out) (committed : Execution.commits out = true)
    (writer : NoncallingWriter) (codeEq : sevm.code = code)
    (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = writer.selector) :
    Exec.committedFrames run = [Exec.Frame.ofRun run committed] := by
  rw [Exec.committedFrames, dite_eq_left committed,
    noncalling_descendants_nil run writer codeEq fork selector]

def NoncallingWriter.touched (writer : NoncallingWriter) (sevm : Sevm) : List WriterKey :=
  match writer with
  | .approve => approveTouched sevm.caller (approveSpender sevm)
  | .transfer => transferTouched sevm.caller (transferRecipient sevm)
  | .transferFrom => transferFromTouched (transferFromOwner sevm) sevm.caller
      (transferFromRecipient sevm)
  | .initialize => []

def NoncallingWriter.step (writer : NoncallingWriter) (located : Exec.LocatedFrame) : HistoryStep :=
  { located := located, transcript := .done,
    entry := match writer with
      | .approve => approveDecodedEntry located.frame.sevm
      | .transfer => transferDecodedEntry located.frame.sevm
      | .transferFrom => transferFromDecodedEntry located.frame.sevm
      | .initialize => initializeDecodedEntry located.frame.sevm }

theorem noncalling_history_replay {U : WriterKey → Prop} {sevm : Sevm}
    {b post : Devm} {G : Nat} (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (committed : Execution.commits (.ok post) = true) (located : Exec.LocatedFrame)
    (original : located.frame = Exec.Frame.ofRun run committed) (writer : NoncallingWriter)
    (injective : WriterInj U) (apart : WriterApart U)
    (touched : ∀ k ∈ writer.touched sevm, U k)
    (representable : sevm.data.length < 2 ^ 256)
    (freshOutput : writer = .initialize → b.output = [])
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = writer.selector) :
    HistoryReplay U (b.getStor sevm.currentTarget)
      [writer.step located] (post.getStor sevm.currentTarget) := by
  cases writer with
  | approve =>
    exact approve_history_replay run committed located original injective apart touched
      representable codeEq fork selector
  | transfer =>
    exact transfer_history_replay run committed located original injective apart touched
      representable codeEq fork selector
  | transferFrom =>
    exact transferFrom_history_replay run committed located original injective apart touched
      representable codeEq fork selector
  | «initialize» =>
    exact initialize_history_replay run committed located original representable
      (freshOutput rfl) codeEq fork selector

theorem noncalling_success_nonstatic {sevm : Sevm} {b post : Devm} {G : Nat}
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) (writer : NoncallingWriter)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = writer.selector) : sevm.isStatic = false := by
  cases writer with
  | approve => exact (approve_bytecode_refines_raw codeEq fork selector run).2.2.2.1
  | transfer => exact (transfer_bytecode_refines_raw codeEq fork selector run).2.2.2.2.1
  | transferFrom => exact (transferFrom_bytecode_refines_raw codeEq fork selector run).2.2.2.2.2.1
  | «initialize» => exact (initialize_bytecode_refines_raw codeEq fork selector run).2.2.2.2.1

/-- The selected literal noncalling writer produces an exact storage replay and
exactly its own actual committed frame observation. Context and entering
occurrence remain anchored to the original outermost-target selection. -/
theorem selected_noncalling_history {U : WriterKey → Prop} {pair : Adr}
    {pc : Nat} {rootSevm : Sevm} {pre : Devm} {out : Execution}
    (root : Exec pc rootSevm pre out) (located : Exec.LocatedFrame)
    (selected : located ∈ (Exec.retainedTargetTurns pair root).filterMap Sum.getRight?)
    {sevm : Sevm} {b post : Devm} {G : Nat}
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (committed : Execution.commits (.ok post) = true)
    (original : located.frame = Exec.Frame.ofRun run committed) (writer : NoncallingWriter)
    (injective : WriterInj U) (apart : WriterApart U)
    (touched : ∀ k ∈ writer.touched sevm, U k)
    (representable : sevm.data.length < 2 ^ 256)
    (freshOutput : writer = .initialize → b.output = [])
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = writer.selector) :
    HistoryReplay U (b.getStor sevm.currentTarget) [writer.step located]
        (post.getStor sevm.currentTarget) ∧
      (writer.step located).source.context = writerContext sevm located.path ∧
      (writer.step located).transcript = .done ∧
      (historyObservation pair U).obs [writer.step located] = [located.frame] ∧
      (located.path ≠ [] → Nonempty (Exec.LocatedFrame.EnteringOccurrence root located)) := by
  refine ⟨noncalling_history_replay run committed located original writer injective apart touched
    representable freshOutput codeEq fork selector, ?_, rfl, ?_, ?_⟩
  · change writerContext located.frame.sevm located.path = _
    rw [original]
    rfl
  · obtain ⟨_, owned, _⟩ := Exec.retainedTargetTurns_spec pair root
    have targetEq : sevm.currentTarget = pair := by
      have targetEq := owned located selected
      rw [original] at targetEq
      exact targetEq
    have nonstatic := noncalling_success_nonstatic run writer codeEq fork selector
    have observes : pairFrameObservation pair (Exec.Frame.ofRun run committed) =
        [Exec.Frame.ofRun run committed] :=
      ite_eq_left ⟨targetEq, nonstatic⟩
    change (Exec.committedFrames located.frame.run).flatMap (pairFrameObservation pair) ++ [] = _
    rw [original]
    change (Exec.committedFrames run).flatMap (pairFrameObservation pair) ++ [] = _
    rw [noncalling_committed_frames run committed writer codeEq fork selector]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, observes]
  · intro nonroot
    exact (Exec.retainedTargetTurns_entering pair root located selected nonroot).2.2

end Blanc.Lift.UniswapV2Pair
