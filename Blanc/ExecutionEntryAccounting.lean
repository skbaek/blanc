import Blanc.ExecutionAccountingCore
import Blanc.ExecutionAccountingAdmission
import Blanc.ExecutionDirectCode
import Blanc.ExecutionNoninterference

/-!
# The carried invariant at the entry of every committed target frame

The accounting ladder (`Exec.coreAccounting`, `AccountingLadderAdmitted`) handles
foreign frames, message plumbing and settlement generically, but its target
handler must account for the target frame's own children.  Contracts whose
frames spawn only statically discharge that by the static-only restriction
(`Blanc/Lift/StaticOnlyFrames.lean`).  This module is the handler for a target
frame whose children may be non-static and may re-enter the contract.

It instantiates the ladder with the *entry carrier* of a storage invariant `I`:
a replay step is a committed frame, and the replay says only that `I` at the
start implies `I` at the end and `EntryGood` of every observed frame (it starts
at pc 0 on a covered fork, at the contract's code, admitted, with `I` at its
entry storage).  Every non-static committed target frame is observed.

The target handler `Exec.CoreAccounting.entryTarget` needs, per contract:

* `FramePreserves`: a successful target frame keeps `I` (the frame theorem);
* `SpawnKinds`: every same-frame node of a successful target frame that decodes
  an external instruction decodes `CALL` or `STATICCALL` (for a checked
  certificate, `CursorOK.exec_call_or_staticcall`);
* `SpawnEntry`: from `I` at the frame's entry, `I` at each such node — a prefix
  fact of the contract's own code (for a certified contract, a walk of
  `reach_of_parentPrefix`).

The child of such a node opens on the node's storage (`Evm.step_spawn_child_world`),
so the lower-depth hypothesis delivers `EntryGood` for every committed frame of a
settling child; children that do not settle contribute no frame.  The history
headline is `ConfiguredHistoryTrace.entryGood_settled`.
-/

namespace Blanc

open Jaune

/-- A spawned frame's message opens on the spawning world: every code-bearing
account keeps its storage, and no balance moves. -/
theorem Xinst.step_spawn_world {sevm : Sevm} {devm : Devm} {x : Xinst}
    {f : Frame} {rsm : Resume} (hfork : CoveredFork sevm.benvStat.fork)
    (hs : Xinst.step sevm devm x = .spawn f rsm) {a : Adr} (ha : devm.getCode a ≠ .empty) :
    f.inner.benv.state.getStor a = devm.state.getStor a ∧
      f.inner.benv.state.bal = devm.state.bal := by
  rcases Xinst.step_shapeCovered sevm devm x hfork with ⟨ex, hsh, -⟩ |
    ⟨d, e, na, mi, ms, hf, hsh⟩ |
    ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      hf, -, -, -, hsh⟩ <;> rw [hsh] at hs
  · cases hs
  · have hcode := (genericCreate.step_spawn_frame hs)
    simp only [genericCreate.step, Bind.bind, Except.bind, Except.assert,
      assertDynamic, Pure.pure, Except.pure] at hs
    repeat' split at hs
    all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
    all_goals obtain ⟨rfl, -⟩ := hs
    have hna : na ≠ a := by
      rintro rfl
      exact ha ((hf.getCode na).trans hcode.2.2)
    refine ⟨?_, ?_⟩
    · simp only [Frame.ofCreate]
      dsimp only [createMsg, processCreateMessage.msg, Msg.withBenv, Benv.setStor,
        addCreatedAccount, Benv.incrNonce, State.getStor]
      rw [State.incrNonce_get_stor, State.setStor_get_stor_ne hna, addAccessedAddress_state]
      show ((((d.withGasLeft (d.gasLeft - except64th d.gasLeft)).withReturnData []).state.incrNonce
        sevm.currentTarget).get a).stor = _
      rw [State.incrNonce_get_stor]
      exact congrArg (fun w : Jaune.State => (w.get a).stor) hf.state.symm
    · simp only [Frame.ofCreate]
      rw [Jaune.processCreateMessage_msg_bal_eq]
      show (addAccessedAddress _ na).state.bal = _
      rw [addAccessedAddress_state]
      show (((d.withGasLeft (d.gasLeft - except64th d.gasLeft)).withReturnData []).state.incrNonce
        sevm.currentTarget).bal = _
      rw [State.incrNonce_bal]
      exact congrArg Jaune.State.bal hf.state.symm
  · simp only [genericCall.step, Bind.bind, Except.bind, Pure.pure,
      Except.pure] at hs
    repeat' split at hs
    all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
    all_goals obtain ⟨rfl, -⟩ := hs
    all_goals exact ⟨(hf.getStor a).symm, congrArg Jaune.State.bal hf.state.symm⟩


/-- A spawned child opens on its parent's world: every code-bearing account keeps
its storage, and the world balance total does not grow. -/
theorem Evm.step_spawn_child_world {pc : Nat} {sevm : Sevm} {devm : Devm}
    {f : Frame} {rsm : Resume} {pc' : Nat} {cevm : Evm}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hs : Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc') (he : f.enter = .run cevm)
    {a : Adr} (ha : devm.getCode a ≠ .empty) :
    cevm.dyna.state.getStor a = devm.state.getStor a ∧
      sum cevm.dyna.state.bal ≤ sum devm.state.bal := by
  obtain ⟨x, -, hx, -⟩ := Evm.step_spawn_inv hs
  obtain ⟨hstor, hbal⟩ := Xinst.step_spawn_world hfork hx ha
  obtain ⟨benv, transfer, rfl⟩ := Frame.enter_run_inv he
  refine ⟨(congrFun (benvAfterTransfer_getStor_eq transfer) a).trans hstor, ?_⟩
  have h := Msg.benvAfterTransfer_balance_effect (out := .ok benv) transfer
  change State.balSum benv.state ≤ State.balSum f.inner.benv.state at h
  change sum benv.state.bal ≤ _
  rw [← hbal]
  exact h

/-- One same-frame edge does not grow the world balance total. -/
theorem Exec.Deriv.ParentStep.balSum_le {next node : Exec.Deriv}
    (edge : Exec.Deriv.ParentStep next node) :
    sum next.devm.state.bal ≤ sum node.devm.state.bal := by
  have h : Devm.BalNoninc node.devm next.devm := by
    cases edge with
    | cont hstep next =>
        exact Evm.step_effect balNoninc_refl_trans.2.1 Ninst.balance_effectRec
          Jinst.balance_effect Linst.balance_effect (xl := .none) (out := .ok _) trivial
          (by rw [hstep]; exact ⟨rfl, rfl⟩)
    | doneOk hstep henter hresume next =>
        exact Evm.step_effect balNoninc_refl_trans.2.1 Ninst.balance_effectRec
          Jinst.balance_effect Linst.balance_effect (xl := .none) (out := .ok _) trivial
          (by rw [hstep]; exact ⟨_, RunFrame.of_done henter, hresume.symm⟩)
    | runOk hstep henter child hresume next =>
        exact Evm.step_effect balNoninc_refl_trans.2.1 Ninst.balance_effectRec
          Jinst.balance_effect Linst.balance_effect (xl := .some ⟨_, _⟩) (out := .ok _)
          (Exec.balance_effect child)
          (by rw [hstep]; exact ⟨_, RunFrame.of_run henter, hresume.symm⟩)
  exact h

/-- Along a same-frame prefix the balance total does not grow and code-bearing
accounts keep their code. -/
theorem Exec.Deriv.ParentPrefix.balSum_le_getCode {root node : Exec.Deriv}
    (chain : Exec.Deriv.ParentPrefix root node) :
    sum node.devm.state.bal ≤ sum root.devm.state.bal ∧
      ∀ a, (root.devm.getCode a).toList ≠ [] → node.devm.getCode a = root.devm.getCode a := by
  induction chain with
  | refl => exact ⟨le_refl _, fun _ _ => rfl⟩
  | step head _ ih =>
      obtain ⟨hbal, hcode⟩ := ih
      refine ⟨hbal.trans (Blanc.Exec.Deriv.ParentStep.balSum_le head), fun a ha => ?_⟩
      have hstep := Blanc.Exec.Deriv.ParentStep.codePreserve head a ha
      rw [← hstep] at ha
      exact (hcode a ha).trans hstep

namespace ExecutionAccountingReplay

section Entry

variable (ca : Adr) (sem : CodeSem) (entry : Sevm → Devm → Prop) (I : Stor → Prop)

/-- An observed committed frame: it starts at pc `0` on a covered fork at the
contract's code, satisfies the admission, and `I` holds at its entry storage. -/
def EntryGood (f : Exec.Frame) : Prop :=
  f.pc = 0 ∧ CoveredFork f.sevm.benvStat.fork ∧ sem.At ca 0 f.sevm f.pre ∧
    entry f.sevm f.pre ∧ I (f.pre.state.getStor ca)

/-- The entry replay: `I` at the start gives `I` at the end and `EntryGood` of
every step. -/
def EntryReplay (a : Stor) (fs : List Exec.Frame) (b : Stor) : Prop :=
  I a → I b ∧ ∀ f ∈ fs, EntryGood ca sem entry I f

theorem EntryReplay.append {a b c : Stor} {xs ys : List Exec.Frame}
    (left : EntryReplay ca sem entry I a xs b) (right : EntryReplay ca sem entry I b ys c) :
    EntryReplay ca sem entry I a (xs ++ ys) c := by
  intro ha
  obtain ⟨hb, hxs⟩ := left ha
  obtain ⟨hc, hys⟩ := right hb
  refine ⟨hc, fun f hf => ?_⟩
  rcases List.mem_append.mp hf with hf | hf
  · exact hxs f hf
  · exact hys f hf

/-- The storage boundary at `ca`, with committed frames as steps. -/
def entryCarrier : ReplayCarrier ca where
  Snap := Stor
  Step := Exec.Frame
  Tag := Unit
  Replay := EntryReplay ca sem entry I
  ofState state := state.getStor ca
  frameEntry _ state := state.getStor ca
  nil := fun _ h => ⟨h, fun _ hf => absurd hf List.not_mem_nil⟩
  silent := fun storage _ => storage
  credit := by
    intro _ pre post _ storage _ _
    refine ⟨[], fun h => ⟨?_, fun _ hf => absurd hf List.not_mem_nil⟩⟩
    rw [storage]
    exact h
  entry_eq_ofState := by
    intro _ _ _ _ transfer _
    exact congrFun (benvAfterTransfer_getStor_eq transfer) ca

/-- Every non-static committed frame at `ca` is observed, as itself. -/
def entryObservation : ReplayObservation (entryCarrier ca sem entry I) where
  O := Exec.Frame
  obs := id
  obs_nil := rfl
  obs_append := fun _ _ => rfl
  frameObs f := if f.sevm.currentTarget = ca ∧ f.sevm.isStatic = false then [f] else []
  credit := by
    intro _ pre post _ storage _ _
    refine ⟨[], fun h => ⟨?_, fun _ hf => absurd hf List.not_mem_nil⟩, rfl⟩
    change I (post.getStor ca)
    rw [storage]
    exact h

end Entry

end ExecutionAccountingReplay

open ExecutionAccountingReplay

/-- A successful target frame keeps `I` (the contract's frame theorem). -/
def FramePreserves (ca : Adr) (sem : CodeSem) (entry : Sevm → Devm → Prop)
    (I : Stor → Prop) : Prop :=
  ∀ {sevm pre post} (run : Exec 0 sevm pre (.ok post)),
    sem.Run sevm pre post → sevm.currentTarget = ca → CoveredFork sevm.benvStat.fork →
    sem.At ca 0 sevm pre → Exec.FrameAdmitted ca entry run → sum pre.state.bal < 2 ^ 256 →
    I (pre.state.getStor ca) → I (post.state.getStor ca)

/-- Every external instruction a successful target frame decodes along its own
chain is `CALL` or `STATICCALL`. -/
def SpawnKinds (ca : Adr) (sem : CodeSem) : Prop :=
  ∀ {sevm pre post} (run : Exec 0 sevm pre (.ok post)),
    sem.Run sevm pre post → sevm.currentTarget = ca → CoveredFork sevm.benvStat.fork →
    sem.At ca 0 sevm pre →
    ∀ node, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ node →
      ∀ x, Ninst.At node.sevm.code node.pc (.exec x) → x = .call ∨ x = .staticcall

/-- **The spawn obligation.**  From `I` at a successful target frame's entry,
`I` at every node of its own chain that decodes an external instruction. -/
def SpawnEntry (ca : Adr) (sem : CodeSem) (entry : Sevm → Devm → Prop)
    (I : Stor → Prop) : Prop :=
  ∀ {sevm pre post} (run : Exec 0 sevm pre (.ok post)),
    sem.Run sevm pre post → sevm.currentTarget = ca → CoveredFork sevm.benvStat.fork →
    sem.At ca 0 sevm pre → Exec.FrameAdmitted ca entry run → sum pre.state.bal < 2 ^ 256 →
    I (pre.state.getStor ca) →
    ∀ node, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ node →
      ∀ x, Ninst.At node.sevm.code node.pc (.exec x) → I (node.devm.state.getStor ca)


namespace Exec.CoreAccounting

variable {ca : Adr} {sem : CodeSem} {entry : Sevm → Devm → Prop} {I : Stor → Prop}

/-- **The child of a spawning node of a successful target frame.**  What every consumer of the
target-parent chain needs at a `runOk` node: the node decodes an external instruction, its fork is
covered, the contract's code is installed there, the balance total only fell along the chain, the child's
fork is covered, a static frame spawns a static child, and the lower-depth hypothesis gives the child's
accounting (its code is at `ca`, a same-target child runs the same code, and it is admitted). -/
theorem spawnChild {C : ReplayCarrier ca} {V : ReplayObservation C}
    (kinds : SpawnKinds ca sem)
    {sevm₀ : Sevm} {pre₀ post₀ : Devm} (root : Exec 0 sevm₀ pre₀ (.ok post₀))
    (hrun : sem.Run sevm₀ pre₀ post₀) (target : sevm₀.currentTarget = ca)
    (fork : CoveredFork sevm₀.benvStat.fork) (installed : sem.At ca 0 sevm₀ pre₀)
    (admitted : Exec.FrameAdmitted ca entry root)
    (deeper : ForallDeeperAtSem sevm₀.depth ca sem
      (fun pc s d e _ => Exec.CoreAccounting ca sem entry C V pc s d e))
    {nodePc : Nat} {nodeSevm : Sevm} {nodePre : Devm} {out : Execution} {frame : Jaune.Frame}
    {rsm : Resume} {nextPc : Nat} {cevm : Evm} {raw : Execution} {inter : Devm}
    (step : Evm.step ⟨nodePc, nodeSevm, nodePre⟩ = .spawn frame rsm nextPc)
    (enter : frame.enter = .run cevm) (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (resume : rsm.run (frame.settle raw) = .ok inter) (next : Exec nextPc nodeSevm inter out)
    (chain : Exec.Deriv.ParentPrefix ⟨0, sevm₀, pre₀, .ok post₀, root⟩
      ⟨nodePc, nodeSevm, nodePre, out, .runOk step enter child resume next⟩) :
    ∃ x : Xinst, Ninst.At nodeSevm.code nodePc (.exec x) ∧
      CoveredFork nodeSevm.benvStat.fork ∧ nodePre.getCode ca ≠ .empty ∧
      sum nodePre.state.bal ≤ sum pre₀.state.bal ∧ CoveredFork cevm.sta.benvStat.fork ∧
      (nodeSevm.isStatic = true → cevm.sta.isStatic = true) ∧
      ∀ committed : Execution.commits raw = true,
        (cevm.sta.isStatic = true → (Exec.committedFrames child).flatMap V.frameObs = []) ∧
        (sum cevm.dyna.state.bal < 2 ^ 256 → ∃ steps,
          C.Replay (C.frameEntry cevm.sta cevm.dyna.state) steps
            (C.ofState (Execution.committedPost raw committed).state) ∧
          V.obs steps = (Exec.committedFrames child).flatMap V.frameObs) := by
  have sevmEq : nodeSevm = sevm₀ := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  obtain ⟨x, instruction, spawnStep, _⟩ := Evm.step_spawn_inv step
  have kind := kinds root hrun target fork installed _ chain x instruction
  obtain ⟨balLe, codeEq⟩ := Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode chain
  have codeNe : (pre₀.getCode ca).toList ≠ [] := fun empty =>
    sem.ne_nil (installed.1.symm.trans (congrArg some empty)) rfl
  have nodeInstalled : some (nodePre.getCode ca).toList = sem.image := by
    rw [show nodePre.getCode ca = pre₀.getCode ca from codeEq ca codeNe]
    exact installed.1
  have nodeCodeNe : nodePre.getCode ca ≠ .empty := fun empty => by
    rw [empty] at nodeInstalled
    exact sem.ne_nil nodeInstalled.symm (by simp only [ByteArray.toList_empty])
  have nodeFork : CoveredFork nodeSevm.benvStat.fork := by rw [sevmEq]; exact fork
  have childFork := Evm.step_spawn_child_fork step enter nodeFork
  have childDepth : cevm.sta.depth < sevm₀.depth := by
    rw [Frame.enter_run_depth enter, ← sevmEq]
    exact Step.spawn_depth_lt step
  have childAt : sem.At ca cevm.pc cevm.sta cevm.dyna := by
    obtain ⟨pcZero, getCode, _⟩ := Evm.step_spawn_child step enter
    refine ⟨?_, fun selected => ⟨?_, pcZero⟩⟩
    · rw [getCode ca]
      exact nodeInstalled
    · have sameTarget : frame.inner.currentTarget = nodeSevm.currentTarget := by
        rw [← Frame.enter_run_currentTarget enter, selected, sevmEq, target]
      have notDel : ¬ isValidDelegation (nodePre.getCode frame.inner.currentTarget) := by
        rw [← Frame.enter_run_currentTarget enter, selected]
        exact sem.not_delegation nodeInstalled
      have directCode : frame.inner.code = nodePre.getCode frame.inner.currentTarget := by
        rcases kind with rfl | rfl
        · exact Xinst.step_call_sameTarget_code spawnStep sameTarget notDel
        · exact Xinst.step_staticcall_sameTarget_code spawnStep sameTarget notDel
      rw [Frame.enter_run_code enter, directCode, ← Frame.enter_run_currentTarget enter,
        selected]
      exact nodeInstalled
  have childAdmitted : Exec.FrameAdmitted ca entry child := by
    intro childRoot member selected
    apply admitted childRoot _ selected
    apply List.mem_cons_of_mem
    apply Exec.mem_rawFrameDescendants_of_parentPrefix chain
    simp only [Exec.rawFrameDescendants, List.mem_cons, List.mem_append]
    simp only [Exec.rawFrameRoots, List.mem_cons] at member
    rcases member with rfl | member
    · exact Or.inl rfl
    · exact Or.inr (Or.inl member)
  have childCore := deeper cevm.pc cevm.sta cevm.dyna raw child childDepth childAt
  exact ⟨x, instruction, nodeFork, nodeCodeNe, balLe, childFork,
    fun static => (Frame.enter_run_isStatic enter).trans
      (Xinst.step_spawn_isStatic spawnStep static),
    fun committed => childCore child committed childFork childAt childAdmitted⟩

/-- The chain of a successful target frame: every committed descendant frame
observed below any of its same-frame nodes is `EntryGood`, and none is observed
when the frame is static. -/
private theorem entryChain (kinds : SpawnKinds ca sem) (spawn : SpawnEntry ca sem entry I)
    {sevm₀ : Sevm} {pre₀ post₀ : Devm} (root : Exec 0 sevm₀ pre₀ (.ok post₀))
    (hrun : sem.Run sevm₀ pre₀ post₀) (target : sevm₀.currentTarget = ca)
    (fork : CoveredFork sevm₀.benvStat.fork) (installed : sem.At ca 0 sevm₀ pre₀)
    (admitted : Exec.FrameAdmitted ca entry root)
    (deeper : ForallDeeperAtSem sevm₀.depth ca sem
      (fun pc s d e _ => Exec.CoreAccounting ca sem entry (entryCarrier ca sem entry I)
        (entryObservation ca sem entry I) pc s d e)) :
    ∀ {pc : Nat} {sevm : Sevm} {d : Devm} {out : Execution} (run : Exec pc sevm d out),
      Exec.Deriv.ParentPrefix ⟨0, sevm₀, pre₀, .ok post₀, root⟩ ⟨pc, sevm, d, out, run⟩ →
      (sevm.isStatic = true →
        (Exec.descendantFrames run).flatMap (entryObservation ca sem entry I).frameObs = []) ∧
      (sum pre₀.state.bal < 2 ^ 256 → I (pre₀.state.getStor ca) →
        ∀ f ∈ (Exec.descendantFrames run).flatMap (entryObservation ca sem entry I).frameObs,
          EntryGood ca sem entry I f) := by
  intro pc sevm d out run
  induction run with
  | halt step => intro _; simp only [descendantFrames, List.flatMap_nil, implies_true,
    Nat.reducePow, List.not_mem_nil, IsEmpty.forall_iff, and_self]
  | cont step next ih =>
    intro chain
    simpa only [Exec.descendantFrames] using ih (chain.snoc (.cont step next))
  | doneErr step enter resume => intro _; simp only [descendantFrames, List.flatMap_nil,
    implies_true, Nat.reducePow, List.not_mem_nil, IsEmpty.forall_iff, and_self]
  | doneOk step enter resume next ih =>
    intro chain
    simpa only [Exec.descendantFrames] using ih (chain.snoc (.doneOk step enter resume next))
  | runErr step enter child resume ih => intro _; simp only [descendantFrames, List.flatMap_nil,
    implies_true, Nat.reducePow, List.not_mem_nil, IsEmpty.forall_iff, and_self]
  | runOk step enter child resume next childIH nextIH =>
    rename_i nodePc nodeSevm nodePre frame rsm nextPc cevm raw inter final
    intro chain
    obtain ⟨x, instruction, nodeFork, nodeCodeNe, balLe, childFork, childStaticOf, childCore⟩ :=
      spawnChild kinds root hrun target fork installed admitted deeper step enter child resume
        next chain
    obtain ⟨nextStatic, nextGood⟩ := nextIH (chain.snoc (.runOk step enter child resume next))
    have split : (Exec.descendantFrames (Exec.runOk step enter child resume next)).flatMap
          (entryObservation ca sem entry I).frameObs =
        (if Frame.settlementCommits frame raw = true then
            (Exec.committedFrames child).flatMap (entryObservation ca sem entry I).frameObs
          else []) ++
          (Exec.descendantFrames next).flatMap (entryObservation ca sem entry I).frameObs := by
      by_cases settles : Frame.settlementCommits frame raw = true
      · rw [Exec.descendantFrames_runOk_of_settlementCommits step enter child resume next settles,
          Exec.committedFrames, dite_eq_left (Frame.raw_commits_of_settlementCommits settles)]
        simp only [settles, ↓reduceIte, List.flatMap_cons, List.flatMap_append,
          List.append_assoc]
      · rw [Exec.descendantFrames_runOk_of_not_settlementCommits step enter child resume next
          settles]
        simp only [settles, Bool.false_eq_true, ↓reduceIte, List.nil_append]
    rw [split]
    refine ⟨fun static => ?_, fun bound hI => ?_⟩
    · rw [nextStatic static, List.append_nil]
      split
      · rename_i settles
        exact (childCore (Frame.raw_commits_of_settlementCommits settles)).1
          (childStaticOf static)
      · rfl
    · intro f member
      rcases List.mem_append.mp member with member | member
      · split at member
        · rename_i settles
          obtain ⟨nodeI⟩ : Nonempty (I (nodePre.state.getStor ca)) :=
            ⟨spawn root hrun target fork installed admitted bound hI _ chain x instruction⟩
          obtain ⟨childStor, childBal⟩ :=
            Evm.step_spawn_child_world nodeFork step enter nodeCodeNe
          obtain ⟨steps, replay, observed⟩ :=
            (childCore (Frame.raw_commits_of_settlementCommits settles)).2
              (Nat.lt_of_le_of_lt (childBal.trans balLe) bound)
          have childI : I (cevm.dyna.state.getStor ca) := by
            rw [childStor]
            exact nodeI
          refine (replay childI).2 f ?_
          change f ∈ (entryObservation ca sem entry I).obs steps
          rw [observed]
          exact member
        · simp only [List.not_mem_nil] at member
      · exact nextGood bound hI f member

/-- **Target-parent spawn accounting.**  For the entry carrier of `I`, a
successful target frame satisfies `CoreAccounting` from the lower-depth
hypothesis, given the contract's frame theorem (`FramePreserves`), that its
frames spawn only by `CALL`/`STATICCALL` (`SpawnKinds`), and that `I` holds at
each of its spawning nodes (`SpawnEntry`).  Its children may be non-static and
may re-enter the contract. -/
theorem entryTarget (preserve : FramePreserves ca sem entry I) (kinds : SpawnKinds ca sem)
    (spawn : SpawnEntry ca sem entry I)
    {sevm : Sevm} {pre post : Devm} (hrun : sem.Run sevm pre post)
    (target : sevm.currentTarget = ca)
    (deeper : ForallDeeperAtSem sevm.depth ca sem
      (fun pc s d e _ => Exec.CoreAccounting ca sem entry (entryCarrier ca sem entry I)
        (entryObservation ca sem entry I) pc s d e)) :
    Exec.CoreAccounting ca sem entry (entryCarrier ca sem entry I)
      (entryObservation ca sem entry I) 0 sevm pre (.ok post) := by
  intro run committed fork installed admitted
  obtain ⟨descStatic, descGood⟩ :=
    entryChain kinds spawn run hrun target fork installed admitted deeper run (.refl _)
  have self : (Exec.committedFrames run).flatMap (entryObservation ca sem entry I).frameObs =
      (entryObservation ca sem entry I).frameObs (Exec.Frame.ofRun run committed) ++
        (Exec.descendantFrames run).flatMap (entryObservation ca sem entry I).frameObs := by
    rw [Exec.committedFrames, dite_eq_left committed, List.flatMap_cons]
  refine ⟨fun static => ?_, fun bound => ⟨_, fun hI => ⟨?_, fun f member => ?_⟩, rfl⟩⟩
  · rw [self, descStatic static, List.append_nil]
    simp only [entryObservation, Exec.Frame.ofRun, static, Bool.true_eq_false, and_false,
      ↓reduceIte]
  · exact preserve run hrun target fork installed admitted bound hI
  · change f ∈ (Exec.committedFrames run).flatMap (entryObservation ca sem entry I).frameObs
      at member
    rw [self] at member
    rcases List.mem_append.mp member with member | member
    · simp only [entryObservation, Exec.Frame.ofRun] at member
      split at member
      · rw [List.mem_singleton] at member
        subst member
        exact ⟨rfl, fork, installed, admitted.root target, hI⟩
      · simp only [List.not_mem_nil] at member
    · exact descGood bound hI f member

end Exec.CoreAccounting


namespace ExecutionAccountingReplay

variable {c : ContractSpecSem} {ca : Adr} {entry : Sevm → Devm → Prop} {I : Stor → Prop}

/-- The accounting ladder of the entry carrier, from the contract's frame theorem
and its spawn obligations. -/
def entryLadder (preserves : c.PreservesAdmitted ca entry)
    (preserve : FramePreserves ca c.sem entry I) (kinds : SpawnKinds ca c.sem)
    (spawn : SpawnEntry ca c.sem entry I) : AccountingLadderAdmitted c ca entry where
  carrier := entryCarrier ca c.sem entry I
  append := fun left right => EntryReplay.append ca c.sem entry I left right
  tag := fun _ _ => ()
  preserves := preserves
  view := entryObservation ca c.sem entry I
  root := by
    intro _ _ msg entryBenv pc sevm pre out run transfer evmEq committed admitted ready _ fork
      bound
    obtain ⟨installed, entryBound⟩ :=
      Exec.CoreAccounting.messageRoot_facts transfer evmEq ready bound
    have core := Exec.coreAccounting ca c.sem entry (entryCarrier ca c.sem entry I)
      (entryObservation ca c.sem entry I)
      (fun left right => EntryReplay.append ca c.sem entry I left right) (fun _ _ => ())
      (fun _ _ _ => rfl)
      (fun frame foreign => by
        change (if frame.sevm.currentTarget = ca ∧ frame.sevm.isStatic = false then [frame]
          else []) = []
        simp only [foreign, false_and, ↓reduceIte])
      (fun hrun target deeper =>
        Exec.CoreAccounting.entryTarget preserve kinds spawn hrun target deeper)
    exact (core pc sevm pre out run installed run committed fork installed admitted).2 entryBound

end ExecutionAccountingReplay

namespace ExecutionTrace

open ExecutionAccountingReplay

/-- **The carried invariant at the entry of every committed target frame.**  In a
configured history admitted at `ca`, from a checkpoint satisfying the contract's
state invariant and `I`, every settlement-committed non-static frame at `ca` —
including frames re-entered below the contract's own non-static calls — starts at
pc `0` on a covered fork at the contract's code, satisfies the admission, and has
`I` at its entry storage; `I` also holds at the end.  Per contract: its frame
theorem (`preserves`, `preserve`), `CALL`/`STATICCALL`-only spawning (`kinds`) and
`I` at its own spawning nodes (`spawn`).  Rolled-back frames are not claimed. -/
theorem ConfiguredHistoryTrace.entryGood_settled {c : ContractSpecSem} {ca : Adr}
    {entry : Sevm → Devm → Prop} {I : Stor → Prop}
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.StateInv ca checkpoint.state) (initial : I (checkpoint.state.getStor ca))
    (preserves : c.PreservesAdmitted ca entry)
    (preserve : FramePreserves ca c.sem entry I) (kinds : SpawnKinds ca c.sem)
    (spawn : SpawnEntry ca c.sem entry I) :
    I (future.state.getStor ca) ∧
      ∀ f ∈ trace.settledFrames, f.sevm.currentTarget = ca → f.sevm.isStatic = false →
        EntryGood ca c.sem entry I f := by
  obtain ⟨steps, replay, observed⟩ :=
    (entryLadder preserves preserve kinds spawn).configuredHistory trace admitted inv
  obtain ⟨final, good⟩ := replay initial
  change steps = trace.settledFrames.flatMap (fun f : Exec.Frame =>
    if f.sevm.currentTarget = ca ∧ f.sevm.isStatic = false then [f] else []) at observed
  refine ⟨final, fun f member target static => good f ?_⟩
  rw [observed]
  exact List.mem_flatMap.mpr ⟨f, member, by simp only [target, static, and_self, ↓reduceIte,
    List.mem_cons, List.not_mem_nil, or_false]⟩

end ExecutionTrace

end Blanc
