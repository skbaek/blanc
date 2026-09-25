-- DripTranscriptExec.lean : the DRIP core recursion, transcript-threaded
-- (DRIP completion unit T5), and the G4 coverage headline.
--
-- `Exec.coreDripAccounting` replays every committed execution as a realized
-- ledger.  Its transcript twin `Exec.coreDripTranscript` also pins the ledger's
-- call projection: the call kinds of the produced steps are exactly the
-- computed tags of the committed DRIP call frames of the execution, in
-- settled-frame order.  Each foreign handler identifies the arbitrary run with
-- the step's own derivation (`Exec.unique`, one named lemma per shape); the
-- target handler reads a DRIP frame's descendant frames off its actual exit
-- payout child (`ExitHandoffAt`, T4a) or proves there are none (T4b).  The
-- observed generic ladder (T3) then lifts the root law to configured
-- histories: `dripTraceRealizes_transcript`.

import Blanc.DripTranscript
import Blanc.DripFrameSpawns
import Blanc.ExecutionAccountingObserved
import Blanc.DripTraceRealizes
import Blanc.ExecIdentification

namespace Blanc

open Jaune

namespace Drip

/-- The transcript entry of one settled frame: its computed tag, if it is a
DRIP call. -/
noncomputable def frameCall (coalition : Finset Adr) (ca : Adr)
    (frame : Exec.Frame) : List Kind :=
  if frame.sevm.currentTarget = ca ∧
      (opTag coalition frame.sevm frame.pre).isCall = true
  then [opTag coalition frame.sevm frame.pre] else []

end Drip

/-- T1 with its exclusivity clause strengthened to the whole settled frame
list of the suffix. -/
def Exec.CoreDripTranscript (coalition : Finset Adr) (ca : Adr)
    (pc : Nat) (sevm : Sevm) (pre : Devm) (out : Execution) : Prop :=
  ∀ (run : Exec pc sevm pre out) (committed : Execution.commits out = true),
    CoveredFork sevm.benvStat.fork →
    Prog.At Drip.runtime ca pc sevm pre →
    Drip.dripEntrySpec.Pre ca sevm pre →
    (sevm.currentTarget = ca → sevm.codeAddress = some ca) →
    (sevm.currentTarget = ca → sevm.caller ≠ ca) →
    (sevm.currentTarget = ca → pre.memory = Mem.empty) →
    ∃ steps : List Drip.RealizedStep,
      Drip.RealizedChain (Drip.execEntrySnapshot coalition ca sevm pre.state) steps
        (Drip.snapshot coalition ca (Execution.committedPost out committed).state) ∧
      Drip.callKinds steps =
        (Exec.committedFrames run).flatMap (Drip.frameCall coalition ca)

namespace Drip

/-! ## The call projection of one step and one frame -/

theorem callKinds_cons (op : RealizedStep) (rest : List RealizedStep) :
    callKinds (op :: rest) =
      (if op.kind.isCall = true then [op.kind] else []) ++ callKinds rest := by
  unfold callKinds
  cases h : op.kind.isCall <;> simp [h]

/-- A frame not executing `ca` contributes no transcript entry. -/
theorem frameCall_of_target_ne {coalition : Finset Adr} {ca : Adr}
    {frame : Exec.Frame} (target_ne : frame.sevm.currentTarget ≠ ca) :
    frameCall coalition ca frame = [] := by
  unfold frameCall
  rw [if_neg fun both => target_ne both.1]

/-- A committed foreign root's transcript is that of its descendants. -/
theorem committedFrames_flatMap_of_target_ne {coalition : Finset Adr}
    {ca : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (target_ne : sevm.currentTarget ≠ ca) :
    (Exec.committedFrames run).flatMap (frameCall coalition ca) =
      (Exec.descendantFrames run).flatMap (frameCall coalition ca) := by
  simp only [Exec.committedFrames, dif_pos committed, List.flatMap_cons]
  rw [frameCall_of_target_ne (frame := Exec.Frame.ofRun run committed)
    target_ne, List.nil_append]

/-! ## Identifying the arbitrary run with the step's derivation

`Exec.CoreDripTranscript` quantifies over every derivation of its suffix; the
interpreter eliminator hands each handler the step's own pieces.  `Exec.unique`
identifies the two, one named lemma per step shape. -/

/-! ## The transcript observation -/

/-- DRIP's realized ledger observed through its call projection: a settled
frame contributes its `frameCall`, and an outside credit is observed as
nothing. -/
noncomputable def transcriptView (coalition : Finset Adr) (ca : Adr) :
    ExecutionAccountingReplay.ReplayObservation (carrier coalition ca) where
  O := Kind
  obs := callKinds
  obs_nil := rfl
  obs_append := callKinds_append
  frameObs := frameCall coalition ca
  credit := by
    intro _ pre post amount storage_eq balance_eq positive
    rcases externalCredit_chain (coalition := coalition) storage_eq balance_eq
        positive with ⟨op, kindEq, preEq, postEq⟩
    refine ⟨[op], Chain.cons preEq ?_, ?_⟩
    · rw [postEq]
      exact Chain.nil _
    · show callKinds ([op] : List RealizedStep) = []
      rw [callKinds_cons, kindEq]
      rfl

/-! ## The target frame, transcript-threaded -/

/-- The transcript replay of one successful DRIP frame: one head step carrying
the computed tag, then nested steps whose call projection is exactly the
frame's descendant frames' transcript. -/
def TargetTranscript (coalition : Finset Adr) (ca : Adr) {sevm : Sevm}
    {pre post : Devm} (exc : Exec 0 sevm pre (.ok post)) : Prop :=
  ∃ (op : RealizedStep) (nested : List RealizedStep),
    op.pre = execEntrySnapshot coalition ca sevm pre.state ∧
    op.kind = opTag coalition sevm pre ∧
    RealizedChain op.post nested (snapshot coalition ca post.state) ∧
    callKinds nested = (Exec.descendantFrames exc).flatMap (frameCall coalition ca)

/-- The actual-child twin of `exec_targetReplay`.  The exit callback's nested
replay is taken over the frame's actual payout slot, whose settled frames are
the frame's descendants (T4a); every other committed route has none (T4b). -/
theorem exec_targetReplayAt (coalition : Finset Adr) {sevm : Sevm}
    {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code.toList = code)
    (hcanon : pre.memory = Mem.empty)
    (precondition : dripEntrySpec.Pre sevm.currentTarget sevm pre)
    (caller_ne : sevm.caller ≠ sevm.currentTarget)
    (committed : Execution.commits (.ok post) = true)
    (hfork : CoveredFork sevm.benvStat.fork)
    (exitNested : ∀ handoff : ExitHandoffAt coalition exc,
      ∃ nested, RealizedChain
        (snapshot coalition sevm.currentTarget handoff.entry.state) nested
        (snapshot coalition sevm.currentTarget handoff.child.state) ∧
      callKinds nested =
        handoff.retained.settledFrames.flatMap
          (frameCall coalition sevm.currentTarget)) :
    TargetTranscript coalition sevm.currentTarget exc := by
  by_cases hexit : sevm.data.length.toB256 ≠ 0 ∧ Sevm.selector sevm = exitSelector
  · obtain ⟨hempty, hsel⟩ := hexit
    have exitDrip : exitSelector ≠ dripSelector := by decide +kernel
    have exitJoin : exitSelector ≠ joinSelector := by decide +kernel
    have hvalue := (exec_enters_exit exc hcode hsel hempty).1
    obtain ⟨handoff⟩ := exit_exec_handoffAt coalition exc hcode hsel hempty
      hcanon precondition caller_ne hfork
    rcases exitNested handoff with ⟨nested, chain, kinds⟩
    refine ⟨⟨_, _, _, handoff.effect⟩, nested, ?_, ?_, ?_, ?_⟩
    · exact (execEntrySnapshot_of_value_zero hvalue).symm
    · simp only [opTag, hempty, hsel, exitDrip, exitJoin, if_false, if_true]
    · rw [handoff.postSnapshot]
      exact chain
    · rw [handoff.frames]
      exact kinds
  · have hnotExit : sevm.data.length.toB256 = 0 ∨ Sevm.selector sevm ≠ exitSelector := by
      by_cases hnil : sevm.data.length.toB256 = 0
      · exact Or.inl hnil
      · exact Or.inr fun hsel => hexit ⟨hnil, hsel⟩
    rcases exec_nonexit_head coalition exc hcode hcanon precondition hnotExit with
      ⟨op, preEq, kindEq, postEq⟩
    refine ⟨op, [], preEq, kindEq, ?_, ?_⟩
    · rw [postEq]
      exact Chain.nil _
    · rw [nonexit_descendantFrames_nil exc hcode hcanon committed hnotExit hfork]
      rfl

end Drip

open Drip

/-! ## The interpreter recursion, transcript-threaded -/

/-- A failed raw execution cannot satisfy the committed replay premise. -/
theorem Exec.CoreDripTranscript.error
    {coalition : Finset Adr} {ca : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm}
    {error : EvmError × Devm} :
    Exec.CoreDripTranscript coalition ca pc sevm pre (.error error) := by
  intro _ committed
  simp [Execution.commits] at committed

/-- The compiled DRIP frame handler.  The head step's kind is the frame's
computed tag, so the frame's own transcript entry is the head step's call
projection; `exit` recurses into exactly its actual payout child. -/
theorem Exec.CoreDripTranscript.atTarget
    {coalition : Finset Adr} {ca : Adr} {sevm : Sevm} {pre post : Devm}
    (_programRun : Prog.Run sevm pre runtime post)
    (target : sevm.currentTarget = ca)
    (deeper : ForallDeeperAt sevm.depth ca runtime
      (fun pc childSevm childPre childOut _ =>
        Exec.CoreDripTranscript coalition ca pc childSevm childPre childOut)) :
    Exec.CoreDripTranscript coalition ca 0 sevm pre (.ok post) := by
  subst ca
  intro run committed hfork installed precondition _ caller canonical
  have hcode : sevm.code.toList = code := by
    have compiled := (installed.2 rfl).1
    rw [code_compile] at compiled
    exact Option.some.inj compiled
  have replay : TargetTranscript coalition sevm.currentTarget run := by
    apply exec_targetReplayAt coalition run hcode (canonical rfl) precondition
      (caller rfl) committed hfork
    rintro ⟨childMsg, hentry, child, xl, retained, process, childClean,
      entryTransfer, benvStat, targetNe, depth, childPreH, _, _, _⟩
    dsimp only
    cases retained with
    | none =>
        have childState :=
          _root_.Blanc.ProcessMessage.none_ok_state_eq_entry_of_clean
            process entryTransfer childClean
        refine ⟨[], ?_, rfl⟩
        rw [childState]
        exact Chain.nil _
    | @some childPc childSevm childPre childOut childRun =>
        obtain ⟨childCommitted, childTargetNe, childPrecondition, childAt,
            childDepth, startEq, childPost⟩ :=
          exitChild_facts coalition process childClean entryTransfer targetNe
            depth childPreH
        have childFork :=
          exitChild_covered process entryTransfer benvStat hfork
        rcases deeper childPc childSevm childPre childOut childRun
            childDepth childAt childRun childCommitted childFork childAt
            childPrecondition
            (fun childTarget => (childTargetNe childTarget).elim)
            (fun childTarget => (childTargetNe childTarget).elim)
            (fun childTarget => (childTargetNe childTarget).elim) with
          ⟨steps, chain, kinds⟩
        refine ⟨steps, ?_, kinds⟩
        rw [← startEq, childPost]
        exact chain
  rcases replay with ⟨op, nested, preEq, kindEq, tail, kinds⟩
  refine ⟨op :: nested, Chain.cons preEq tail, ?_⟩
  simp only [Exec.committedFrames, dif_pos committed, List.flatMap_cons]
  rw [callKinds_cons, kinds, kindEq]
  congr 1
  -- The frame's own transcript entry is its computed tag, since it runs `ca`.
  show _ = if sevm.currentTarget = sevm.currentTarget ∧
      (opTag coalition sevm pre).isCall = true
    then [opTag coalition sevm pre] else []
  by_cases call : (opTag coalition sevm pre).isCall = true
  · rw [if_pos call, if_pos ⟨rfl, call⟩]
  · rw [if_neg call, if_neg fun both => call both.2]

/-- Foreign nonrecursive execution contributes no call, so the suffix's
transcript is its continuation's. -/
theorem Exec.CoreDripTranscript.nextNone
    {coalition : Finset Adr} {ca : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm}
    {n : Ninst} {inter : Devm} {out : Execution}
    (hat : Ninst.At sevm.code pc n)
    (step : Ninst.StepRun pc sevm pre n .none (.ok inter))
    (next : Exec (pc + n.size) sevm inter out)
    (target_ne : sevm.currentTarget ≠ ca)
    (ih : Exec.CoreDripTranscript coalition ca (pc + n.size) sevm inter out) :
    Exec.CoreDripTranscript coalition ca pc sevm pre out := by
  intro run committed hfork _ precondition _ _ _
  have interPre : dripEntrySpec.Pre ca sevm inter :=
    _root_.Blanc.ContractSpec.Ninst.none_preserves_precond
      (c := dripEntrySpec) hfork step target_ne precondition
  have installedInter : Prog.At runtime ca (pc + n.size) sevm inter :=
    ⟨interPre.code, fun target => (target_ne target).elim⟩
  have sumNof : sum pre.state.bal < 2 ^ 256 := precondition.side
  rcases (carrier coalition ca).ofStorageEqBalanceMono_observed
      (transcriptView coalition ca) ()
      (_root_.Blanc.Ninst.foreignNone_getStor_eq hfork step target_ne)
      (_root_.Blanc.Ninst.targetBalanceMono_of_none hfork step target_ne sumNof) with
    ⟨headSteps, headReplay, headKinds⟩
  change List RealizedStep at headSteps
  rcases ih next committed hfork installedInter interPre
      (fun target => (target_ne target).elim)
      (fun target => (target_ne target).elim)
      (fun target => (target_ne target).elim) with
    ⟨tailSteps, tailReplay, tailKinds⟩
  rw [execEntrySnapshot_of_target_ne target_ne] at tailReplay ⊢
  refine ⟨@HAppend.hAppend (List RealizedStep) (List RealizedStep) _ _
    headSteps tailSteps, Chain.append headReplay tailReplay, ?_⟩
  have headNil : callKinds headSteps = [] := headKinds
  rw [callKinds_append, headNil, tailKinds, List.nil_append,
    committedFrames_flatMap_of_target_ne next committed target_ne,
    committedFrames_flatMap_of_target_ne run committed target_ne,
    Exec.descendantFrames_eq_of_nextNone hat step run next]

/-- A foreign terminal instruction contributes no call and no frame. -/
theorem Exec.CoreDripTranscript.last
    {coalition : Finset Adr} {ca : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm}
    {l : Linst} {out : Execution}
    (hat : Linst.At sevm.code pc l)
    (step : Linst.Run sevm pre l out)
    (target_ne : sevm.currentTarget ≠ ca) :
    Exec.CoreDripTranscript coalition ca pc sevm pre out := by
  intro run committed hfork _ precondition _ _ _
  cases out with
  | error error =>
      simp [Execution.commits] at committed
  | ok post =>
      have sumNof : sum pre.state.bal < 2 ^ 256 := precondition.side
      rcases (carrier coalition ca).ofStorageEqBalanceMono_observed
          (transcriptView coalition ca) ()
          (congrFun (_root_.Blanc.Linst.getStor_eq step) ca)
          (_root_.Blanc.Linst.targetBalanceMono_of_foreign step target_ne
            sumNof) with
        ⟨steps, replay, kinds⟩
      rw [execEntrySnapshot_of_target_ne target_ne]
      refine ⟨steps, replay, ?_⟩
      rw [committedFrames_flatMap_of_target_ne run committed target_ne,
        Exec.descendantFrames_eq_nil_of_last hat run]
      exact kinds

/-- Jump execution is world-state silent and enters no frame. -/
theorem Exec.CoreDripTranscript.jump
    {coalition : Finset Adr} {ca : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm}
    {j : Jinst} {pc' : Nat} {inter : Devm} {out : Execution}
    (hat : Jinst.At sevm.code pc j)
    (step : Jinst.Run ⟨pc, sevm, pre⟩ j (.ok ⟨pc', inter⟩))
    (next : Exec pc' sevm inter out)
    (target_ne : sevm.currentTarget ≠ ca)
    (ih : Exec.CoreDripTranscript coalition ca pc' sevm inter out) :
    Exec.CoreDripTranscript coalition ca pc sevm pre out := by
  intro run committed hfork _ precondition _ _ _
  have stateEq : inter.state = pre.state := Jinst.preserves_state step
  have interPre : dripEntrySpec.Pre ca sevm inter :=
    precondition.state_eq stateEq
  have installedInter : Prog.At runtime ca pc' sevm inter :=
    ⟨interPre.code, fun target => (target_ne target).elim⟩
  rcases ih next committed hfork installedInter interPre
      (fun target => (target_ne target).elim)
      (fun target => (target_ne target).elim)
      (fun target => (target_ne target).elim) with
    ⟨steps, replay, kinds⟩
  rw [execEntrySnapshot_of_target_ne target_ne, stateEq] at replay
  rw [execEntrySnapshot_of_target_ne target_ne]
  refine ⟨steps, replay, ?_⟩
  rw [kinds, committedFrames_flatMap_of_target_ne next committed target_ne,
    committedFrames_flatMap_of_target_ne run committed target_ne,
    Exec.descendantFrames_eq_of_jump hat step run next]

/-- A foreign filled child contributes exactly its settled transcript, then
the parent continuation's. -/
theorem Exec.CoreDripTranscript.nextSome
    {coalition : Finset Adr} {ca : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm}
    {n : Ninst} {cevm : Evm} {raw : Execution} {inter : Devm} {out : Execution}
    (hat : Ninst.At sevm.code pc n)
    (step : Ninst.StepRun pc sevm pre n (.some ⟨cevm, raw⟩) (.ok inter))
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (next : Exec (pc + n.size) sevm inter out)
    (target_ne : sevm.currentTarget ≠ ca)
    (ihChild : Exec.CoreDripTranscript coalition ca
      cevm.pc cevm.sta cevm.dyna raw)
    (ihNext : Exec.CoreDripTranscript coalition ca
      (pc + n.size) sevm inter out) :
    Exec.CoreDripTranscript coalition ca pc sevm pre out := by
  cases n with
  | reg r =>
      simp [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at step
  | push xs length =>
      simp [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at step
  | dupn imm =>
      cases (Step.run_ofExecution.mp step).1
  | swapn imm =>
      cases (Step.run_ofExecution.mp step).1
  | exchange imm =>
      cases (Step.run_ofExecution.mp step).1
  | exec x =>
      intro run committed hfork installed precondition _ _ _
      obtain ⟨frame, resume, settled, spawnEq, frameRun, resumeRun, childAt,
          childPrecondition, childDirect, childCaller, childCanonical,
          interPre, childFork⟩ :=
        foreignSpawn_facts hat step child target_ne installed precondition hfork
      have installedInter : Prog.At runtime ca (pc + 1) sevm inter :=
        ⟨interPre.code, fun target => (target_ne target).elim⟩
      have sumNof : sum pre.state.bal < 2 ^ 256 := precondition.side
      rcases (carrier coalition ca).xinstForeignSome_observed
          (transcriptView coalition ca) spawnEq frameRun resumeRun target_ne
          hfork sumNof child
          (fun childCommitted => ihChild child childCommitted childFork childAt
            childPrecondition childDirect childCaller childCanonical) with
        ⟨headSteps, headReplay, headKinds⟩
      change List RealizedStep at headSteps
      rcases ihNext next committed hfork installedInter interPre
          (fun target => (target_ne target).elim)
          (fun target => (target_ne target).elim)
          (fun target => (target_ne target).elim) with
        ⟨tailSteps, tailReplay, tailKinds⟩
      rw [execEntrySnapshot_of_target_ne target_ne] at tailReplay ⊢
      refine ⟨@HAppend.hAppend (List RealizedStep) (List RealizedStep) _ _
    headSteps tailSteps, Chain.append headReplay tailReplay, ?_⟩
      have headEq : callKinds headSteps =
          (if Frame.settlementCommits frame raw = true
            then (Exec.committedFrames child).flatMap (frameCall coalition ca)
            else []) := headKinds
      rw [callKinds_append, headEq, tailKinds,
        committedFrames_flatMap_of_target_ne next committed target_ne,
        committedFrames_flatMap_of_target_ne run committed target_ne,
        Exec.descendantFrames_flatMap_of_nextSome (frameCall coalition ca) hat
          spawnEq frameRun resumeRun run child next]
      rfl

/-- The complete interpreter recursion for the committed DRIP transcript. -/
theorem Exec.coreDripTranscript (coalition : Finset Adr) {ca : Adr} :
    Exec.Fa (Exec.Wkn ca Drip.runtime
      (fun pc sevm pre out _ => Exec.CoreDripTranscript coalition ca pc sevm pre out)) := by
  apply lift_core
    (ε := fun pc sevm pre out =>
      Exec.CoreDripTranscript coalition ca pc sevm pre out)
    (π := fun sevm pre post =>
      Exec.CoreDripTranscript coalition ca 0 sevm pre (.ok post))
    (analog := fun h => h)
    (ca := ca) (p := runtime)
  · intro sevm pre post run target deeper
    exact Exec.CoreDripTranscript.atTarget run target deeper
  · intro pc sevm pre error post target
    exact Exec.CoreDripTranscript.error
  · intro pc sevm pre noneAt targetNe
    exact Exec.CoreDripTranscript.error
  · intro pc sevm pre n error post hat step targetNe
    exact Exec.CoreDripTranscript.error
  · intro pc sevm pre n childEvm childOut error post
      hat step child targetNe ihChild
    exact Exec.CoreDripTranscript.error
  · intro pc sevm pre n inter out hat step next targetNe ihNext
    exact Exec.CoreDripTranscript.nextNone hat step next targetNe ihNext
  · intro pc sevm pre n childEvm childOut inter out
      hat step child next targetNe ihChild ihNext
    exact Exec.CoreDripTranscript.nextSome
      hat step child next targetNe ihChild ihNext
  · intro pc sevm pre j error post hat step targetNe
    exact Exec.CoreDripTranscript.error
  · intro pc sevm pre j pc' inter out hat step next targetNe ihNext
    exact Exec.CoreDripTranscript.jump hat step next targetNe ihNext
  · intro pc sevm pre l out hat step targetNe
    exact Exec.CoreDripTranscript.last hat step targetNe

theorem Exec.dripTranscriptChain_of_messageRoot
    (coalition : Finset Adr) {ca : Adr} {msg : Msg} {entry : Benv}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (transfer : msg.benvAfterTransfer = .ok entry)
    (evmEq : (⟨pc, sevm, pre⟩ : Evm) = initEvm (msg.withBenv entry))
    (committed : Execution.commits out = true)
    (ready : Drip.dripEntrySpec.MessageRunReady ca msg)
    (caller_ne : msg.currentTarget = ca → msg.caller ≠ ca)
    (hfork : CoveredFork sevm.benvStat.fork) :
    ∃ steps : List Drip.RealizedStep,
      Drip.RealizedChain (Drip.execEntrySnapshot coalition ca sevm pre.state) steps
        (Drip.snapshot coalition ca (Execution.committedPost out committed).state) ∧
      Drip.callKinds steps =
        (Exec.committedFrames run).flatMap (Drip.frameCall coalition ca) := by
  obtain ⟨installed, precondition, direct, caller, canonical⟩ :=
    messageRoot_facts transfer evmEq ready caller_ne
  exact Exec.coreDripTranscript coalition pc sevm pre out run installed run
    committed hfork installed precondition direct caller canonical

namespace Drip

/-- DRIP's ladder observed through its call projection: a committed message
root's ledger has exactly the root's committed DRIP calls. -/
noncomputable def ladderObserved (coalition : Finset Adr) (ca : Adr) :
    (ladder coalition ca).Observed where
  view := transcriptView coalition ca
  root := by
    intro _ _ msg entry pc sevm pre out run transfer evmEq committed runReady
      callerNe hfork sumNof
    exact Exec.dripTranscriptChain_of_messageRoot coalition run transfer evmEq
      committed (dripEntrySpec_messageRunReady runReady sumNof) callerNe hfork

/-- The DRIP transcript of a retained configured history: one entry per settled
DRIP call frame, in execution order. -/
noncomputable def _root_.Blanc.ExecutionTrace.ConfiguredHistoryTrace.dripCalls
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ExecutionTrace.ConfiguredHistoryTrace cfg checkpoint future)
    (coalition : Finset Adr) (ca : Adr) : List Kind :=
  history.settledFrames.flatMap (frameCall coalition ca)

/-- **G4 coverage.** Every configured history from the deployment root admits a
realized ledger whose call steps are exactly the history's settled DRIP calls,
once each, in execution order, each with its own computed kind. -/
theorem dripTraceRealizes_transcript
    {cfg : ChainConfig} {base deployed future : BlockChain} {ca : Adr}
    (root : DeploymentRoot cfg base deployed ca) (coalition : Finset Adr)
    (history : ExecutionTrace.ConfiguredHistoryTrace cfg deployed future)
    (hcov : ∀ timestamp fork,
      cfg.forkAt timestamp = .ok fork → CoveredFork fork) :
    ∃ steps, DripTraceRealizes root coalition steps future ∧
      callKinds steps = history.dripCalls coalition ca :=
  (ladderObserved coalition ca).traceRealizes_of_configuredHistoryTrace
    root.stateInv history hcov

end Drip

end Blanc
