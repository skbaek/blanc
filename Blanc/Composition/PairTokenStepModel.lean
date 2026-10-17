import Blanc.Composition.PairTokenStepOracle
import Blanc.Composition.PairTokenStepGhostStart
import Blanc.Composition.PairTokenJointAt
import Blanc.Lift.UniswapV2Pair.PairPositionalAdmission
import Blanc.Lift.Token.Holder

/-!
# The per-outer-step lemma of C3 (model side, U6c2)

One outer Pair step consumed by `PairAdmittedConsumes` from a state with the joint relation at its
entry: the recursion over `PositionalConsumes` carries the model ghost (`SegGhost`,
`PairTokenStepGhost.lean`) against the booked token ledger, moving the ledger across each observed
call with `pair_token_stepOracle`.  It concludes the step's `EntryNoShrinkSide` and the joint
relation after the step's subtree (`pair_token_step_model`).
-/

namespace Blanc.Composition.PairTokenJoint

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair

/-! ## Turns and the prior frame -/

/-- Exact turns keep the parent frame's context. -/
theorem exactTurns_context {frame : UniswapV2Pair.Frame} {request : Request} {turn : Nat}
    {turns : Transcript} {out : TurnsResult} (h : ExactTurns frame request turn turns out) :
    out.frame.context = frame.context := by
  refine ExactTurns.rec (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun frame _ _ _ out _ => out.frame.context = frame.context)
    (fun _ _ => trivial) (fun _ _ _ => trivial) (fun _ _ _ => trivial)
    (fun _ _ _ _ _ _ => trivial) ?_ ?_ ?_ h
  · intro frame request turn
    rfl
  · intro frame request turn emitter topics data tail out mutable rest ih
    exact ih
  · intro frame request turn sender value isStatic entry transcript tail child out selected rest
      _ ih
    exact ih

/-- **The prior frame of a resumption after exact turns**: same context; unchanged under a static
request; the economic core kept under a closed lock. -/
theorem exactTurns_priorOk {frame : UniswapV2Pair.Frame} {request : Request} {turns : Transcript}
    {executed : TurnsResult} {reply : ExternalResult}
    (during : ExactTurns frame request 0 turns executed) :
    PriorOk frame (if reply.success then executed.frame
      else { executed.frame with current := frame.current }) request where
  context := by
    split
    · exact exactTurns_context during
    · exact exactTurns_context during
  static := fun static => by
    have same := during.static_frame (Or.inl static)
    split
    · rw [same]
    · rfl
  core := fun locked => by
    have realized := during.realizes (turns.work + 1) (Nat.le_refl _)
    have core := driveTurns_locked_core (turns.work + 1) frame request 0 turns locked
    rw [realized] at core
    split
    · exact core
    · rfl

/-! ## The oracle as a balance step -/

theorem StepOracle.callBal {B : Book} {T pair : Adr} {frame : UniswapV2Pair.Frame}
    {request : Request} {reply : ExternalResult} {entered : Prop} {l l' : B.Ledger}
    (oracle : StepOracle B T pair frame request reply entered l l')
    (enteredAt : request.target = T → entered) :
    CallBal T pair frame request reply (B.bal l pair) (B.bal l' pair) where
  static := fun h => by rw [oracle.static h]
  read := fun target data success => (oracle.read target data success (enteredAt target)).2
  transfer := fun target data mutable => oracle.transfer target data mutable
  other := fun apart mutable => oracle.other apart mutable

/-- A consumption that succeeds does not start from a failure. -/
theorem notFailed_of_consumes {root start : Exec.Deriv} {index : Nat} {segment : SegmentResult}
    {transcript : Transcript} {out : RunResult} {bytes : Bytes}
    (consumed : PositionalConsumes root start index segment transcript out)
    (status : out.status = .success bytes) : NotFailed segment := by
  cases segment with
  | failed fr failure =>
    cases consumed
    cases status
  | finished fr output => trivial
  | suspended fr request cont => trivial

/-! ## The recursion -/

section Recursion

variable {pair T : Adr} {B : Book} (C : Core T B) {cfg : ChainConfig} {checkpoint future : BlockChain}
  (trace : ConfiguredHistoryTrace cfg checkpoint future)

/-- **The ghost along a positional consumption of a settled Pair frame.**  From a node whose
retained frames sit contiguously after `pre`, with the booked ledger `l` there and the ghost at
`l`'s balance, the consumption retains frames whose run reaches a ledger `l'` with a zero
allowance, and a successful step ends with its side reserve at most `l'`'s balance and its
obligation discharged. -/
theorem positional_ghost (laws : BookLaws B) (abi : Erc20Abi B) (self : SelfCaller C)
    (hist : C.Hist trace) (apart : pair ≠ T)
    (answerable : C.Answerable trace pair) {P : Exec.Frame} (settledP : P ∈ trace.settledFrames)
    (atPair : P.sevm.currentTarget = pair) {side : TokenSide} {t0 t1 : Adr}
    (hT : OnSide side (T = t0) (T = t1)) (distinct : t0 ≠ t1)
    (tokenEntered : ∀ {frame : UniswapV2Pair.Frame} {request : Request} {reply : ExternalResult}
      {index : Nat} (observed : SourceCallAt (Blanc.Exec.Frame.rootDeriv P) frame request reply index),
      request.target = T →
        getDelegatedCodeAddress (observed.call.occurrence.node.devm.getCode T) = none ∧
          ¬ observed.call.occurrence.node.sevm.benvStat.rules.isPrecomp T)
    {root start : Exec.Deriv} {index : Nat} {segment : SegmentResult} {transcript : Transcript}
    {out : RunResult} (consumed : PositionalConsumes root start index segment transcript out) :
    root = Blanc.Exec.Frame.rootDeriv P →
    ∀ (pre post : List Exec.Frame) (l : B.Ledger),
      trace.settledFrames = pre ++ Exec.descendantFrames start.exc ++ post →
      B.run (C.ledgerOf trace checkpoint.state) (entryAsks T pre) = some l →
      (∀ g, B.allow l pair g = 0) →
      LockedBelow pair (Exec.descendantFrames start.exc) →
      SegGhost side t0 t1 (B.bal l pair) segment →
      ∃ l', B.run l (entryAsks T (Exec.descendantFrames start.exc)) = some l' ∧
        (∀ g, B.allow l' pair g = 0) ∧
        ∀ bytes, out.status = .success bytes →
          out.frame.current.state.reserveOn side ≤ B.bal l' pair ∧
            SegObl side transcript segment := by
  -- one call: the oracle, the resumption, and the remaining consumption
  have step : ∀ {start : Exec.Deriv} {index : Nat} {frame : UniswapV2Pair.Frame}
      {request : Request} {continuation : Continuation} {reply : ExternalResult}
      {turns tail : Transcript} {executed : TurnsResult} {out out' : RunResult}
      (same : out'.status = out.status ∧ out'.frame = out.frame)
      (observed : SourceCallAt (Blanc.Exec.Frame.rootDeriv P) frame request reply index)
      (gap : Exec.Deriv.ExecFreeUntil start observed.call.occurrence.node)
      (during : ExactTurns frame request 0 turns executed)
      (rest : PositionalConsumes (Blanc.Exec.Frame.rootDeriv P) observed.call.returned (index + 1)
        (resumeSegment
          (if reply.success then executed.frame else {executed.frame with current := frame.current})
          request continuation reply) tail out)
      (ih : ∀ (pre post : List Exec.Frame) (l : B.Ledger),
        trace.settledFrames = pre ++ Exec.descendantFrames observed.call.returned.exc ++ post →
        B.run (C.ledgerOf trace checkpoint.state) (entryAsks T pre) = some l →
        (∀ g, B.allow l pair g = 0) →
        LockedBelow pair (Exec.descendantFrames observed.call.returned.exc) →
        SegGhost side t0 t1 (B.bal l pair) (resumeSegment
          (if reply.success then executed.frame else {executed.frame with current := frame.current})
          request continuation reply) →
        ∃ l', B.run l (entryAsks T (Exec.descendantFrames observed.call.returned.exc)) = some l' ∧
          (∀ g, B.allow l' pair g = 0) ∧
          ∀ bytes, out.status = .success bytes →
            out.frame.current.state.reserveOn side ≤ B.bal l' pair ∧
              SegObl side tail (resumeSegment
                (if reply.success then executed.frame
                  else {executed.frame with current := frame.current})
                request continuation reply))
      (pre post : List Exec.Frame) (l : B.Ledger),
      trace.settledFrames = pre ++ Exec.descendantFrames start.exc ++ post →
      B.run (C.ledgerOf trace checkpoint.state) (entryAsks T pre) = some l →
      (∀ g, B.allow l pair g = 0) →
      LockedBelow pair (Exec.descendantFrames start.exc) →
      SegGhost side t0 t1 (B.bal l pair) (.suspended frame request continuation) →
      ∃ l', B.run l (entryAsks T (Exec.descendantFrames start.exc)) = some l' ∧
        (∀ g, B.allow l' pair g = 0) ∧
        ∀ bytes, out'.status = .success bytes →
          out'.frame.current.state.reserveOn side ≤ B.bal l' pair ∧
            SegObl side (.next reply turns tail) (.suspended frame request continuation) := by
    intro start index frame request continuation reply turns tail executed out out' same observed gap
      during rest ih pre post l split atPre zero locked ghost
    have pairEq : frame.context.pair = pair := observed.pair_eq.trans atPair
    obtain ⟨mid, l1, eqMid, run1, oracle⟩ :=
      pair_token_stepOracle C laws abi self trace hist apart answerable settledP atPair observed gap
        locked (ContGhost.toT hT ghost) split atPre zero
    have bal := oracle.callBal fun target =>
      sourceCallAt_entered observed (by rw [target]; exact (tokenEntered observed target).1)
        (by rw [target]; exact (tokenEntered observed target).2)
    obtain ⟨ghost', discharge⟩ := resumeSegment_ghost (turns := turns) (tail := tail) hT distinct
      ghost pairEq bal (exactTurns_priorOk (reply := reply) during)
    have split' : trace.settledFrames =
        (pre ++ mid) ++ Exec.descendantFrames observed.call.returned.exc ++ post := by
      rw [split, eqMid]
      simp only [List.append_assoc]
    have atPre' : B.run (C.ledgerOf trace checkpoint.state) (entryAsks T (pre ++ mid)) = some l1 := by
      rw [entryAsks_append, Book.run_append, atPre, Option.bind_some]
      exact run1
    have locked' : LockedBelow pair (Exec.descendantFrames observed.call.returned.exc) :=
      fun D member => locked D (by rw [eqMid]; exact List.mem_append_right _ member)
    obtain ⟨l2, run2, zero2, final⟩ := ih (pre ++ mid) post l1 split' atPre' oracle.zero locked' ghost'
    refine ⟨l2, ?_, zero2, fun bytes status => ?_⟩
    · rw [eqMid, entryAsks_append, Book.run_append, run1, Option.bind_some]
      exact run2
    · rw [same.1] at status
      rw [same.2]
      obtain ⟨reserve, obligation⟩ := final bytes status
      exact ⟨reserve, discharge (notFailed_of_consumes rest status) obligation⟩
  refine PositionalConsumes.rec
    (motive_1 := fun root start _ segment transcript out _ =>
      root = Blanc.Exec.Frame.rootDeriv P →
      ∀ (pre post : List Exec.Frame) (l : B.Ledger),
        trace.settledFrames = pre ++ Exec.descendantFrames start.exc ++ post →
        B.run (C.ledgerOf trace checkpoint.state) (entryAsks T pre) = some l →
        (∀ g, B.allow l pair g = 0) →
        LockedBelow pair (Exec.descendantFrames start.exc) →
        SegGhost side t0 t1 (B.bal l pair) segment →
        ∃ l', B.run l (entryAsks T (Exec.descendantFrames start.exc)) = some l' ∧
          (∀ g, B.allow l' pair g = 0) ∧
          ∀ bytes, out.status = .success bytes →
            out.frame.current.state.reserveOn side ≤ B.bal l' pair ∧
              SegObl side transcript segment)
    (motive_2 := fun _ _ _ _ _ _ _ => True) ?_ ?_ ?_ ?_ ?_ ?_ ?_ consumed
  · -- finished
    intro root start index frame bytes free _ pre post l _ _ zero _ ghost
    have none := Exec.descendantFrames_eq_nil_of_no_sameFrame_xinstAt start.exc free
    refine ⟨l, by rw [none]; rfl, zero, fun _ _ => ⟨ghost, trivial⟩⟩
  · -- failed
    intro root start index frame failure genuine free _ pre post l _ _ zero _ _
    have none := Exec.descendantFrames_eq_nil_of_no_sameFrame_xinstAt start.exc free
    refine ⟨l, by rw [none]; rfl, zero, fun _ status => ?_⟩
    cases status
  · -- nextCall
    intro root start index frame request continuation reply turns tail executed out observed gap
      present noCodeTurns during rest ih rootEq
    subst rootEq
    exact step (out := out) ⟨rfl, rfl⟩ observed gap during.forget rest (ih rfl)
  · -- nextMutableCall
    intro root start index frame request continuation reply turns tail executed out events observed
      gap queue present noCodeTurns during rest _ ih rootEq
    subst rootEq
    exact step (out := out) ⟨rfl, rfl⟩ observed gap during.forget rest (ih rfl)
  · intro _ _ _
    trivial
  · intro _ _ _ _ _ _ _ _ _ _
    trivial
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _
    trivial

end Recursion

/-! ## The per-step lemma -/

/-- **The per-outer-step lemma of C3 (model side).**  A settled Pair frame `P` whose committed
subtree sits contiguously in the history, consumed as one outer step from an unlocked state with
the side's token `T` and distinct tokens, under H1 (`factoryQuiet`) and token entry
(`tokenEntered`: at every observed call of `P` to `T`, `T`'s code is undelegated and `T` is not a
precompile at the call), with the joint relation at `P`'s entry: the step's per-side token premise
holds, and after the subtree the booked ledger `l'` has the step's final side reserve at most the
Pair's balance and a zero Pair allowance. -/
theorem pair_token_step_model {pair T : Adr} {B : Book} (C : Core T B) (laws : BookLaws B)
    (abi : Erc20Abi B) (self : SelfCaller C) (side : TokenSide) {cfg : ChainConfig}
    {checkpoint future : BlockChain} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : C.Hist trace) (apart : pair ≠ T) (answerable : C.Answerable trace pair)
    {P : Exec.Frame} {pre post : List Exec.Frame}
    (split : trace.settledFrames = pre ++ Exec.committedFrames P.run ++ post)
    (atPair : P.sevm.currentTarget = pair)
    {current : Checkpoint} {entry : UniswapV2Pair.Entry} {transcript : Transcript} {out : RunResult}
    (consumed : PairAdmittedConsumes (Blanc.Exec.Frame.rootDeriv P)
      (startTyped current (writerContext P.sevm []) entry) transcript out)
    (token : current.state.tokenOn side = T) (distinct : current.state.token0 ≠ current.state.token1)
    (opened : current.state.unlocked = 1)
    (factoryQuiet : ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = pair →
      G.sevm.isStatic = false → G.sevm.caller ≠ current.state.factory)
    (tokenEntered : ∀ {frame : UniswapV2Pair.Frame} {request : Request} {reply : ExternalResult}
      {index : Nat} (observed : SourceCallAt (Blanc.Exec.Frame.rootDeriv P) frame request reply index),
      request.target = T →
        getDelegatedCodeAddress (observed.call.occurrence.node.devm.getCode T) = none ∧
          ¬ observed.call.occurrence.node.sevm.benvStat.rules.isPrecomp T)
    (joint : JointAt C trace pair side current.state P.pre.state)
    {bytes : Bytes} (successful : out.status = .success bytes) :
    EntryNoShrinkSide side current.state (writerContext P.sevm []) entry transcript ∧
      ∃ l', B.run (C.ledgerOf trace checkpoint.state)
          (entryAsks T (pre ++ Exec.committedFrames P.run)) = some l' ∧
        out.frame.current.state.reserveOn side ≤ B.bal l' pair ∧ ∀ g, B.allow l' pair g = 0 := by
  have frames := Exec.Frame.committedFrames_self P
  have settledP : P ∈ trace.settledFrames := by
    rw [split, frames]
    exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
  have inSettled : ∀ D ∈ Exec.descendantFrames P.run, D ∈ trace.settledFrames := by
    intro D member
    rw [split, frames]
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ member))
  have entryLedger := C.replayAt trace hist pre P (Exec.descendantFrames P.run ++ post) (by
    rw [split, frames]
    simp only [List.append_assoc, List.cons_append])
  have notEntry : entryAsks T [P] = [] := by
    have outside : ¬ (IsEntry T P ∧ P.sevm.isStatic = false) :=
      fun h => apart (atPair.symm.trans h.1.1)
    simp only [entryAsks, List.filter_cons, outside, decide_false, Bool.false_eq_true, ite_false,
      List.filter_nil, List.map_nil]
  have atPre : B.run (C.ledgerOf trace checkpoint.state) (entryAsks T (pre ++ [P])) =
      some (C.ledgerOf trace P.pre.state) := by
    rw [entryAsks_append, notEntry, List.append_nil]
    exact entryLedger
  have split0 : trace.settledFrames = (pre ++ [P]) ++
      Exec.descendantFrames (Blanc.Exec.Frame.rootDeriv P).exc ++ post := by
    rw [split, frames]
    simp only [List.append_assoc, List.cons_append]
    rfl
  have tokens : TokensFix current.state.token0 current.state.token1 current.state.factory
      current.state := ⟨rfl, rfl, rfl⟩
  obtain ⟨-, -, -, locked⟩ := consumed.positional.segInv
    (startTyped_segInv_outer tokens opened fun static => factoryQuiet P settledP atPair static)
    (fun D member atRoot mutable => factoryQuiet D (inSettled D member) (atRoot.trans atPair) mutable)
  have hT : OnSide side (T = current.state.token0) (T = current.state.token1) := by
    cases side
    · exact token.symm
    · exact token.symm
  have ghost := startTyped_ghost (side := side) (ctx := writerContext P.sevm []) (entry := entry)
    (rfl : current.state.token0 = _) (rfl : current.state.token1 = _) joint.1
  obtain ⟨l', run', zero', final⟩ := positional_ghost C trace laws abi self hist apart answerable
    settledP atPair hT distinct tokenEntered consumed.positional rfl (pre ++ [P]) post _ split0 atPre
    joint.2 (by rw [← atPair]; exact locked) ghost
  obtain ⟨reserve, obligation⟩ := final bytes successful
  refine ⟨entryNoShrinkSide_of_obl (notFailed_of_consumes consumed.positional successful)
    obligation, l', ?_, reserve, zero'⟩
  rw [frames, ← List.singleton_append, ← List.append_assoc, entryAsks_append, Book.run_append,
    atPre, Option.bind_some]
  exact run'

end Blanc.Composition.PairTokenJoint
