import Blanc.ExecutionEntryAccounting
import Blanc.StaticStorage
import Blanc.LockExclusion

/-!
# A model replay of a target frame's own steps and its re-entered children

`Blanc/ExecutionEntryAccounting.lean` carries a storage invariant through a target frame that spawns
children that may re-enter the contract; its replay only says "invariant in, invariant out".  A contract
whose history is the run of a pure model (Curve, WETH9) needs the target frame's *own model step to come
before the children's*: a frame that spawns an external call after its effect (WETH9's `withdraw` debits and
then sends ETH) is replayed as `own ++ (steps of the settled children)`.

This module is that target handler for an arbitrary account-local carrier whose boundary depends on the
target's storage only through its word at each key.  For a successful non-static target frame, the contract
supplies (`SpawnReplay`), in terms of its own frame theorem and its walk of the frame:

* its own steps `own`, which are exactly what the frame contributes to the observation;
* when the frame's chain has no external instruction, that `own` takes the entry to the post boundary;
* otherwise, at every node that decodes an external instruction, `own` takes the entry to that node's
  boundary, and after it (whatever the child did) nothing but silent steps reaches the post boundary, with
  no further external instruction.

The handler composes `own` with the children's replays, using the lower-depth hypothesis of the ladder for
each settled child and the storage transport of a call (`Xinst.storageReplay_some_of_body`) for its
opening and resumption; children that do not settle contribute nothing.  Static frames observe nothing and
keep their storage.  `modelLadder` turns the handler into an `AccountingLadderAdmitted`.

The per-frame bodies are child-provider lemmas, shared with the code-family handler
(`Blanc/ExecutionOwnerFamily.lean`): `staticFrame` (a static frame, given that nothing below it is
observed) and `modelFrame` (the model composition, given `ChildReplays`, the replays of the settled
children of the frame's spawning nodes).
-/

namespace Blanc

open Jaune
open ExecutionAccountingReplay

/-! ## The first external instruction of a chain -/

/-- `V` is the first node of the chain from `N` that decodes an external instruction. -/
inductive Exec.Deriv.FirstExec : Exec.Deriv → Exec.Deriv → Prop
  | here {N : Exec.Deriv} (x : Xinst) : Ninst.At N.sevm.code N.pc (.exec x) →
      Exec.Deriv.FirstExec N N
  | later {N N' V : Exec.Deriv} :
      (∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x)) → Exec.Deriv.ParentStep N' N →
      Exec.Deriv.FirstExec N' V → Exec.Deriv.FirstExec N V

theorem Exec.Deriv.FirstExec.parentPrefix {N V : Exec.Deriv} (h : Exec.Deriv.FirstExec N V) :
    Exec.Deriv.ParentPrefix N V := by
  induction h with
  | here _ _ => exact .refl _
  | later _ edge _ ih => exact .step edge ih

theorem Exec.Deriv.FirstExec.exec_at {N V : Exec.Deriv} (h : Exec.Deriv.FirstExec N V) :
    ∃ x, Ninst.At V.sevm.code V.pc (.exec x) := by
  induction h with
  | here x hx => exact ⟨x, hx⟩
  | later _ _ _ ih => exact ih

/-- The frames entered below a chain node are those entered below its first external instruction. -/
theorem Exec.Deriv.FirstExec.descendantFrames_eq {N V : Exec.Deriv}
    (h : Exec.Deriv.FirstExec N V) :
    Exec.descendantFrames N.exc = Exec.descendantFrames V.exc := by
  induction h with
  | here _ _ => rfl
  | @later N N' V hn edge _ ih =>
      cases edge with
      | cont step next => simpa only [Exec.descendantFrames] using ih
      | doneOk step enter resume next =>
          obtain ⟨x, instruction, -, -⟩ := Evm.step_spawn_inv step
          exact (hn x instruction).elim
      | runOk step enter child resume next =>
          obtain ⟨x, instruction, -, -⟩ := Evm.step_spawn_inv step
          exact (hn x instruction).elim

/-- Either no node of a frame's chain decodes an external instruction, or there is a first one. -/
theorem Exec.Deriv.exists_firstExec_or_none {pc : Nat} {sevm : Sevm} {d : Devm}
    {out : Execution} (run : Exec pc sevm d out) :
    (∀ N, Exec.Deriv.ParentPrefix ⟨pc, sevm, d, out, run⟩ N →
      ∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x)) ∨
    ∃ V, Exec.Deriv.FirstExec ⟨pc, sevm, d, out, run⟩ V := by
  induction run with
  | halt step =>
      rename_i pc sevm devm ex
      by_cases hx : ∃ x, Ninst.At sevm.code pc (.exec x)
      · obtain ⟨x, hx⟩ := hx
        exact .inr ⟨_, .here x hx⟩
      · have hx : ∀ x, ¬ Ninst.At sevm.code pc (.exec x) := fun x h => hx ⟨x, h⟩
        left
        intro N hN x
        cases hN with
        | refl => exact hx x
        | step head rest => cases head
  | cont step next ih =>
      rename_i pc sevm devm pc' devm' ex
      by_cases hx : ∃ x, Ninst.At sevm.code pc (.exec x)
      · obtain ⟨x, hx⟩ := hx
        exact .inr ⟨_, .here x hx⟩
      · have hx : ∀ x, ¬ Ninst.At sevm.code pc (.exec x) := fun x h => hx ⟨x, h⟩
        rcases ih with hnone | ⟨V, hV⟩
        · left
          intro N hN x
          cases hN with
          | refl => exact hx x
          | step head rest =>
              cases head
              exact hnone N rest x
        · exact .inr ⟨V, .later hx (.cont step next) hV⟩
  | doneErr step enter resume =>
      obtain ⟨x, instruction, -, -⟩ := Evm.step_spawn_inv step
      exact .inr ⟨_, .here x instruction⟩
  | doneOk step enter resume next ih =>
      obtain ⟨x, instruction, -, -⟩ := Evm.step_spawn_inv step
      exact .inr ⟨_, .here x instruction⟩
  | runErr step enter child resume ih =>
      obtain ⟨x, instruction, -, -⟩ := Evm.step_spawn_inv step
      exact .inr ⟨_, .here x instruction⟩
  | runOk step enter child resume next childIH nextIH =>
      obtain ⟨x, instruction, -, -⟩ := Evm.step_spawn_inv step
      exact .inr ⟨_, .here x instruction⟩


/-- Every node of a same-frame prefix shares the root's outcome. -/
theorem Exec.Deriv.ParentPrefix.exn_eq {root tail : Exec.Deriv}
    (h : Exec.Deriv.ParentPrefix root tail) : tail.exn = root.exn := by
  induction h with
  | refl => rfl
  | step head rest ih =>
      refine ih.trans ?_
      cases head <;> rfl

/-- A frame none of whose chain nodes decodes an external instruction enters no frame. -/
theorem Exec.descendantFrames_eq_nil_of_noExec {pc : Nat} {sevm : Sevm} {d : Devm}
    {out : Execution} (run : Exec pc sevm d out)
    (h : ∀ N, Exec.Deriv.ParentPrefix ⟨pc, sevm, d, out, run⟩ N →
      ∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x)) :
    Exec.descendantFrames run = [] := by
  induction run with
  | halt step => simp only [descendantFrames]
  | cont step next ih =>
      have := ih (fun N hN x => h N (.step (.cont step next) hN) x)
      simpa only [descendantFrames] using this
  | doneErr step enter resume =>
      obtain ⟨x, instruction, -, -⟩ := Evm.step_spawn_inv step
      exact (h _ (.refl _) x instruction).elim
  | doneOk step enter resume next ih =>
      obtain ⟨x, instruction, -, -⟩ := Evm.step_spawn_inv step
      exact (h _ (.refl _) x instruction).elim
  | runErr step enter child resume ih =>
      obtain ⟨x, instruction, -, -⟩ := Evm.step_spawn_inv step
      exact (h _ (.refl _) x instruction).elim
  | runOk step enter child resume next childIH nextIH =>
      obtain ⟨x, instruction, -, -⟩ := Evm.step_spawn_inv step
      exact (h _ (.refl _) x instruction).elim

/-- The frames of a spawning step: the settled child's, then the continuation's. -/
theorem Exec.descendantFrames_flatMap_runOk {O : Type} (f : Exec.Frame → List O)
    {pc pc' : Nat} {sevm : Sevm} {pre post : Devm} {frame : Jaune.Frame} {resume : Resume}
    {cevm : Evm} {raw out : Execution}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (enter : frame.enter = .run cevm) (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (hresume : resume.run (frame.settle raw) = .ok post) (next : Exec pc' sevm post out) :
    (Exec.descendantFrames (Exec.runOk step enter child hresume next)).flatMap f =
      (if Frame.settlementCommits frame raw = true then
          (Exec.committedFrames child).flatMap f else []) ++
        (Exec.descendantFrames next).flatMap f := by
  by_cases settles : Frame.settlementCommits frame raw = true
  · rw [Exec.descendantFrames_runOk_of_settlementCommits step enter child hresume next settles,
      Exec.committedFrames, dite_eq_left (Frame.raw_commits_of_settlementCommits settles)]
    simp only [settles, ↓reduceIte, List.flatMap_cons, List.flatMap_append, List.append_assoc]
  · rw [Exec.descendantFrames_runOk_of_not_settlementCommits step enter child hresume next
      settles]
    simp only [settles, Bool.false_eq_true, ↓reduceIte, List.nil_append]

/-- **The storage across a spawning step**, by words: a settled child hands its committed storage back to
the parent, and a child that does not settle leaves the parent's storage as it was. -/
theorem Exec.spawn_seam {pc pc' : Nat} {sevm : Sevm} {pre inter : Devm} {frame : Jaune.Frame}
    {resume : Resume} {cevm : Evm} {raw : Execution}
    (hfork : CoveredFork sevm.benvStat.fork)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (enter : frame.enter = .run cevm) (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (hresume : resume.run (frame.settle raw) = .ok inter) :
    (∀ h : Execution.commits raw = true, Frame.settlementCommits frame raw = true →
      ∀ a k, (Devm.getStor inter a).get k =
        (Devm.getStor (Execution.committedPost raw h) a).get k) ∧
    (Frame.settlementCommits frame raw ≠ true →
      ∀ a k, (Devm.getStor inter a).get k = (Devm.getStor pre a).get k) := by
  obtain ⟨x, -, spawn, -⟩ := Evm.step_spawn_inv step
  have childFork := Evm.step_spawn_child_fork step enter hfork
  refine ⟨?_, fun discarded a k => ?_⟩
  · intro committed settles a k
    rcases Xinst.step_shapeCovered sevm pre x hfork with
      ⟨execution, shape, -⟩ |
      ⟨d, endowment, newAddress, mi, ms, hprefix, shape⟩ |
      ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isStatic,
        ii, isz, oi, osz, code, disablePrecompiles, hprefix, _, _, _, shape⟩ <;>
      rw [shape] at spawn
    · cases spawn
    · have preparedUnprotected := genericCreate_step_spawn_prepared_target_unprotected spawn
      have preparedZero : ((d.state.incrNonce sevm.currentTarget).get newAddress).nonce = 0 :=
        not_ne_iff.mp (fun nonzero => preparedUnprotected (Or.inl nonzero))
      rcases genericCreate_step_spawn_exact spawn with ⟨rfl, rfl⟩
      let prepared := addAccessedAddress
        (((d.withGasLeft (d.gasLeft - except64th d.gasLeft)).withReturnData
          []).incrNonce sevm.currentTarget) newAddress
      let msg := createMsg sevm prepared (except64th d.gasLeft) endowment newAddress
        ((d.memory.read mi ms).1)
      change (Frame.ofCreate msg).enter = .run cevm at enter
      have seed : (cevm.dyna.state.get newAddress).nonce ≠ 0 := by
        rcases Frame.enter_run_inv enter with ⟨benv, transfer, evmEq⟩
        have preState := congrArg (fun evm : Evm => evm.dyna.state) evmEq
        rw [preState]
        change (benv.state.get newAddress).nonce ≠ 0
        rw [Msg.benvAfterTransfer_get_nonce transfer newAddress]
        change (((prepared.state.setStor newAddress .empty).incrNonce newAddress).get
          newAddress).nonce ≠ 0
        rw [State.incrNonce, State.setAccount_get_self, Acct.clearIfEmpty_nonce]
        dsimp only [State.setStor]
        rw [State.get_set_self]
        change ((d.state.incrNonce sevm.currentTarget).get newAddress).nonce + 1 ≠ 0
        rw [preparedZero]
        decide
      have retainedNonce := Exec.nonce_ne_zero_committedPost child committed childFork newAddress seed
      cases settledEq : (Frame.ofCreate msg).settle raw with
      | error error =>
          rw [settledEq] at hresume
          exact (Resume.create_run_error hresume).elim
      | ok settled =>
          have clean : settled.error.isSome = false := by
            change (Frame.ofCreate msg).settlementCommits raw = true at settles
            unfold Frame.settlementCommits at settles
            rw [settledEq] at settles
            change settled.error.isNone = true at settles
            cases h : settled.error with
            | none => rfl
            | some error => rw [h] at settles; cases settles
          have process := RunFrame.of_run (raw := raw) enter
          rw [settledEq] at process
          rcases ProcessCreateMessage.ok_setCode_state_of_clean process clean with
            ⟨inner, innerRun, _, deposited, stateEq⟩
          have rawEq := ProcessMessage.ok_state_eq_committedPost innerRun committed
          change (Resume.create prepared newAddress).run _ = .ok inter at hresume
          rw [settledEq] at hresume
          have resumedState := Resume.create_state hresume
          change ((inter.state.get a).stor).get k =
            (((Execution.committedPost raw committed).state.get a).stor).get k
          rw [resumedState, stateEq, rawEq]
          change (((Execution.committedPost raw committed).state.setCode newAddress deposited).get
            a).stor.get k = ((Execution.committedPost raw committed).state.get a).stor.get k
          by_cases equal : newAddress = a
          · subst a
            rw [State.setCode, State.setAccount_get_self, Acct.clearIfEmpty_stor,
              ite_eq_right (fun empty => retainedNonce empty.2.1)]
          · rw [State.setCode, State.setAccount_get_ne _ equal]
    · rcases genericCall_step_spawn_exact spawn with ⟨rfl, rfl⟩
      cases settledEq : (Frame.ofCall _).settle raw with
      | error error =>
          rw [settledEq] at hresume
          exact (Resume.call_run_error hresume).elim
      | ok settled =>
          have process := RunFrame.of_run (raw := raw) enter
          rw [settledEq] at process
          have stateEq := ProcessMessage.ok_state_eq_committedPost process committed
          rw [settledEq] at hresume
          have resumedState := Resume.call_state hresume
          change ((inter.state.get a).stor).get k =
            (((Execution.committedPost raw committed).state.get a).stor).get k
          rw [resumedState, stateEq]
  · exact congrArg (fun stor => stor.get k)
      (congrFun (Evm.step_spawn_rollback_getStor hfork step enter hresume discarded) a)



namespace Exec.CoreAccounting

variable {ca : Adr} {sem : CodeSem} {entry : Sevm → Devm → Prop} {C : ReplayCarrier ca}
  {V : ReplayObservation C}

/-- **Below a static frame no committed frame is observed.**  At any node of the chain of a successful
target frame that is static, the frames entered from that node on contribute no observation: every child
of a static frame is static, and the lower-depth hypothesis says a static committed run observes nothing. -/
theorem staticObservedNil (kinds : SpawnKinds ca sem)
    {sevm₀ : Sevm} {pre₀ post₀ : Devm} (root : Exec 0 sevm₀ pre₀ (.ok post₀))
    (hrun : sem.Run sevm₀ pre₀ post₀) (target : sevm₀.currentTarget = ca)
    (fork : CoveredFork sevm₀.benvStat.fork) (installed : sem.At ca 0 sevm₀ pre₀)
    (admitted : Exec.FrameAdmitted ca entry root)
    (deeper : ForallDeeperAtSem sevm₀.depth ca sem
      (fun pc s d e _ => Exec.CoreAccounting ca sem entry C V pc s d e)) :
    ∀ {pc : Nat} {sevm : Sevm} {d : Devm} {out : Execution} (run : Exec pc sevm d out),
      Exec.Deriv.ParentPrefix ⟨0, sevm₀, pre₀, .ok post₀, root⟩ ⟨pc, sevm, d, out, run⟩ →
      sevm.isStatic = true → (Exec.descendantFrames run).flatMap V.frameObs = [] := by
  intro pc sevm d out run
  induction run with
  | halt step => intro _ _; simp only [descendantFrames, List.flatMap_nil]
  | cont step next ih =>
      intro chain hs
      simpa only [Exec.descendantFrames] using ih (chain.snoc (.cont step next)) hs
  | doneErr step enter resume => intro _ _; simp only [descendantFrames, List.flatMap_nil]
  | doneOk step enter resume next ih =>
      intro chain hs
      simpa only [Exec.descendantFrames] using
        ih (chain.snoc (.doneOk step enter resume next)) hs
  | runErr step enter child resume ih => intro _ _; simp only [descendantFrames, List.flatMap_nil]
  | runOk step enter child resume next childIH nextIH =>
      rename_i nodePc nodeSevm nodePre frame rsm nextPc cevm raw inter final
      intro chain hs
      obtain ⟨x, instruction, nodeFork, nodeCodeNe, balLe, childFork, childStaticOf, childCore⟩ :=
        spawnChild kinds root hrun target fork installed admitted deeper step enter child resume
          next chain
      rw [Exec.descendantFrames_flatMap_runOk,
        nextIH (chain.snoc (.runOk step enter child resume next)) hs, List.append_nil]
      split
      · rename_i settles
        exact (childCore (Frame.raw_commits_of_settlementCommits settles)).1 (childStaticOf hs)
      · rfl

/-- **The contract's obligations for the model replay of a successful non-static target frame.**
Its own steps `own` contribute exactly the frame's own observation.  If no node of its chain decodes an
external instruction, `own` takes the entry boundary to the post boundary.  Otherwise, at every node that
decodes an external instruction, `own` takes the entry boundary to the node's boundary, and after such a
node (whatever its child did) only silent steps reach the post boundary and no later node decodes an
external instruction. -/
def SpawnReplay (ca : Adr) (sem : CodeSem) (entry : Sevm → Devm → Prop) (C : ReplayCarrier ca)
    (V : ReplayObservation C) : Prop :=
  ∀ {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (committed : Execution.commits (.ok post) = true),
    sem.Run sevm pre post → sevm.currentTarget = ca → CoveredFork sevm.benvStat.fork →
    sem.At ca 0 sevm pre → Exec.FrameAdmitted ca entry run → sum pre.state.bal < 2 ^ 256 →
    sevm.isStatic = false →
    ∃ own : List C.Step, V.obs own = V.frameObs (Exec.Frame.ofRun run committed) ∧
      ((∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
          ∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x)) →
        C.Replay (C.frameEntry sevm pre.state) own (C.ofState post.state)) ∧
      (∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
        ∀ x, Ninst.At N.sevm.code N.pc (.exec x) →
          C.Replay (C.frameEntry sevm pre.state) own (C.ofState N.devm.state) ∧
          ∀ N', Exec.Deriv.ParentStep N' N →
            C.Replay (C.ofState N'.devm.state) [] (C.ofState post.state) ∧
            ∀ M, Exec.Deriv.ParentPrefix N' M →
              ∀ y, ¬ Ninst.At M.sevm.code M.pc (.exec y))

/-- **The settled children of a frame's spawning nodes replay** (a child provider): at every
`runOk` node of the frame's own chain, a committed child entered under the world word bound replays,
from its entry boundary, with the observation of its committed frames.  The single-code handlers
supply it from the lower-depth hypothesis (`spawnChild`); a code family supplies it per spawn kind. -/
def ChildReplays (C : ReplayCarrier ca) (V : ReplayObservation C) {sevm₀ : Sevm}
    {pre₀ post₀ : Devm} (root : Exec 0 sevm₀ pre₀ (.ok post₀)) : Prop :=
  ∀ {nodePc : Nat} {nodeSevm : Sevm} {nodePre : Devm} {out : Execution} {frame : Jaune.Frame}
    {rsm : Resume} {nextPc : Nat} {cevm : Evm} {raw : Execution} {inter : Devm}
    (step : Evm.step ⟨nodePc, nodeSevm, nodePre⟩ = .spawn frame rsm nextPc)
    (enter : frame.enter = .run cevm) (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (resume : rsm.run (frame.settle raw) = .ok inter) (next : Exec nextPc nodeSevm inter out),
    Exec.Deriv.ParentPrefix ⟨0, sevm₀, pre₀, .ok post₀, root⟩
      ⟨nodePc, nodeSevm, nodePre, out, .runOk step enter child resume next⟩ →
    ∀ committed : Execution.commits raw = true, sum cevm.dyna.state.bal < 2 ^ 256 → ∃ steps,
      C.Replay (C.frameEntry cevm.sta cevm.dyna.state) steps
        (C.ofState (Execution.committedPost raw committed).state) ∧
      V.obs steps = (Exec.committedFrames child).flatMap V.frameObs

/-- **A static frame's accounting**, given that nothing below it is observed: it observes nothing and
keeps the owner's storage, so the empty replay takes its entry boundary to its post boundary. -/
theorem staticFrame
    (entryOfState : ∀ (sevm : Sevm) (state : State), C.frameEntry sevm state = C.ofState state)
    (ofStateGet : ∀ {s s' : State},
      (∀ k, (s.getStor ca).get k = (s'.getStor ca).get k) → C.ofState s = C.ofState s')
    (obsStatic : ∀ f : Exec.Frame, f.sevm.isStatic = true → V.frameObs f = [])
    {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (committed : Execution.commits (.ok post) = true) (fork : CoveredFork sevm.benvStat.fork)
    (codeNe : (pre.getCode ca).toList ≠ []) (hs : sevm.isStatic = true)
    (hdf : (Exec.descendantFrames run).flatMap V.frameObs = []) :
    (sevm.isStatic = true → (Exec.committedFrames run).flatMap V.frameObs = []) ∧
    (sum pre.state.bal < 2 ^ 256 → ∃ steps,
      C.Replay (C.frameEntry sevm pre.state) steps
        (C.ofState (Execution.committedPost (.ok post) committed).state) ∧
      V.obs steps = (Exec.committedFrames run).flatMap V.frameObs) := by
  have self : (Exec.committedFrames run).flatMap V.frameObs =
      V.frameObs (Exec.Frame.ofRun run committed) ++
        (Exec.descendantFrames run).flatMap V.frameObs := by
    rw [Exec.committedFrames, dite_eq_left committed, List.flatMap_cons]
  have hself : V.frameObs (Exec.Frame.ofRun run committed) = [] := obsStatic _ hs
  have hobs : (Exec.committedFrames run).flatMap V.frameObs = [] := by
    rw [self, hdf, hself]
    rfl
  refine ⟨fun _ => hobs, fun _ => ⟨[], ?_, ?_⟩⟩
  · have hview := Exec.getStor_committedPost_eq_of_static_protected run hs committed fork ca
      (State.Protected.of_code_ne_nil codeNe)
    have heq : C.ofState (Execution.committedPost (.ok post) committed).state =
        C.ofState pre.state := ofStateGet fun k => congrArg (fun stor => stor.get k) hview
    rw [heq, entryOfState]
    exact C.nil _
  · rw [hobs]
    exact V.obs_nil

/-- **The model replay of a successful frame from its own steps and its children's replays.**  If
`own` takes the boundary `a` to the post boundary when the frame's chain decodes no external
instruction, and otherwise to the boundary of every node that decodes one, after which only silent
steps follow and no external instruction, then `own`, the settled child's replay and the silent steps
take `a` to the post boundary, observing `own` and then the frame's committed descendants. -/
theorem modelFrame
    (entryOfState : ∀ (sevm : Sevm) (state : State), C.frameEntry sevm state = C.ofState state)
    (ofStateGet : ∀ {s s' : State},
      (∀ k, (s.getStor ca).get k = (s'.getStor ca).get k) → C.ofState s = C.ofState s')
    (append : ∀ {a b c xs ys}, C.Replay a xs b → C.Replay b ys c → C.Replay a (xs ++ ys) c)
    {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (fork : CoveredFork sevm.benvStat.fork)
    (rootNonempty : (pre.getCode ca).toList ≠ []) (bound : sum pre.state.bal < 2 ^ 256)
    (children : ChildReplays C V run) {a : C.Snap} (own : List C.Step)
    (c3 : (∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
        ∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x)) →
      C.Replay a own (C.ofState post.state))
    (c12 : ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
      ∀ x, Ninst.At N.sevm.code N.pc (.exec x) →
        C.Replay a own (C.ofState N.devm.state) ∧
        ∀ N', Exec.Deriv.ParentStep N' N →
          C.Replay (C.ofState N'.devm.state) [] (C.ofState post.state) ∧
          ∀ M, Exec.Deriv.ParentPrefix N' M →
            ∀ y, ¬ Ninst.At M.sevm.code M.pc (.exec y)) :
    ∃ steps, C.Replay a steps (C.ofState post.state) ∧
      V.obs steps = V.obs own ++ (Exec.descendantFrames run).flatMap V.frameObs := by
  rcases Exec.Deriv.exists_firstExec_or_none run with none | ⟨Vn, hV⟩
  · rw [Exec.descendantFrames_eq_nil_of_noExec run none]
    exact ⟨own, c3 none, by rw [List.flatMap_nil, List.append_nil]⟩
  · have hpV := hV.parentPrefix
    have dEq := hV.descendantFrames_eq
    obtain ⟨x, hx⟩ := hV.exec_at
    have hexn := Exec.Deriv.ParentPrefix.exn_eq hpV
    obtain ⟨vpc, vsevm, vd, vout, vrun⟩ := Vn
    dsimp only at hexn hx dEq
    subst hexn
    have nodeNonempty : (vd.getCode ca).toList ≠ [] := by
      rw [Blanc.Exec.Deriv.ParentPrefix.codePreserve hpV ca rootNonempty]
      exact rootNonempty
    cases vrun with
    | halt step =>
        rw [Evm.step_next hx] at step
        exact (Ninst.step_ne_halt_ok step).elim
    | cont step next =>
        rename_i pc' post'
        have nstep : Ninst.step ⟨vpc, vsevm, vd⟩ (.exec x) = .cont pc' post' := by
          rw [← Evm.step_next hx]
          exact step
        have nrun : Ninst.StepRun vpc vsevm vd (.exec x) .none (.ok post') := by
          unfold Ninst.StepRun
          rw [nstep]
          exact ⟨rfl, rfl⟩
        have hstor : Devm.getStor post' ca = Devm.getStor vd ca :=
          Ninst.none_getStor_eq_of_ne_sstore nrun (by intro h; cases h) ca
            (State.Protected.of_code_ne_nil nodeNonempty)
        obtain ⟨hc1, hc2⟩ := c12 _ hpV x hx
        obtain ⟨hrep2, hnoexec⟩ := hc2 _ (Exec.Deriv.ParentStep.cont step next)
        have hdf : Exec.descendantFrames next = [] :=
          Exec.descendantFrames_eq_nil_of_noExec next fun M hM y => hnoexec M hM y
        have hE : C.ofState vd.state = C.ofState post'.state :=
          ofStateGet fun k => by
            exact (congrArg (fun t => Stor.get t k) hstor).symm
        rw [dEq]
        simp only [Exec.descendantFrames, hdf, List.flatMap_nil, List.append_nil]
        refine ⟨own ++ [], append (hE ▸ hc1) hrep2, ?_⟩
        rw [V.obs_append, V.obs_nil, List.append_nil]
    | doneOk step enter resume next =>
        rename_i settled pc' post'
        have hstor : Devm.getStor post' ca = Devm.getStor vd ca :=
          Evm.step_doneOk_getStor_eq step enter resume ca
            (State.Protected.of_code_ne_nil nodeNonempty)
        obtain ⟨hc1, hc2⟩ := c12 _ hpV x hx
        obtain ⟨hrep2, hnoexec⟩ := hc2 _ (Exec.Deriv.ParentStep.doneOk step enter resume next)
        have hdf : Exec.descendantFrames next = [] :=
          Exec.descendantFrames_eq_nil_of_noExec next fun M hM y => hnoexec M hM y
        have hE : C.ofState vd.state = C.ofState post'.state :=
          ofStateGet fun k => by
            exact (congrArg (fun t => Stor.get t k) hstor).symm
        rw [dEq]
        simp only [Exec.descendantFrames, hdf, List.flatMap_nil, List.append_nil]
        refine ⟨own ++ [], append (hE ▸ hc1) hrep2, ?_⟩
        rw [V.obs_append, V.obs_nil, List.append_nil]
    | runOk step enter child resume next =>
        rename_i frame rsm pc' cevm raw inter
        have nodeFork : CoveredFork vsevm.benvStat.fork := by
          rw [show vsevm = sevm from Blanc.Exec.Deriv.ParentPrefix.sevm_eq hpV]
          exact fork
        have nodeCodeNe : vd.getCode ca ≠ .empty := fun empty =>
          nodeNonempty (by rw [empty]; simp only [ByteArray.toList_empty])
        obtain ⟨hc1, hc2⟩ := c12 _ hpV x hx
        obtain ⟨hrep2, hnoexec⟩ := hc2 _ (Exec.Deriv.ParentStep.runOk step enter child resume next)
        have hdf : Exec.descendantFrames next = [] :=
          Exec.descendantFrames_eq_nil_of_noExec next fun M hM y => hnoexec M hM y
        obtain ⟨seamA, seamB⟩ := Exec.spawn_seam nodeFork step enter child resume
        have hentry : Devm.getStor cevm.dyna ca = Devm.getStor vd ca :=
          Evm.step_spawn_enter_getStor nodeFork step enter ca
            (State.Protected.of_code_ne_nil nodeNonempty)
        rw [dEq, Exec.descendantFrames_flatMap_runOk, hdf, List.flatMap_nil, List.append_nil]
        by_cases settles : Frame.settlementCommits frame raw = true
        · have hcommit := Frame.raw_commits_of_settlementCommits settles
          have bound' : sum cevm.dyna.state.bal < 2 ^ 256 := by
            obtain ⟨-, childBal⟩ := Evm.step_spawn_child_world nodeFork step enter nodeCodeNe
            exact Nat.lt_of_le_of_lt
              (childBal.trans (Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode hpV).1) bound
          obtain ⟨csteps, creplay, cobs⟩ := children step enter child resume next hpV hcommit bound'
          have e1 : C.frameEntry cevm.sta cevm.dyna.state = C.ofState vd.state := by
            rw [entryOfState]
            exact ofStateGet fun k => by
              exact congrArg (fun t => Stor.get t k) hentry
          have e2 : C.ofState (Execution.committedPost raw hcommit).state =
              C.ofState inter.state := ofStateGet fun k => (seamA hcommit settles ca k).symm
          rw [e1, e2] at creplay
          refine ⟨own ++ csteps ++ [], append (append hc1 creplay) hrep2, ?_⟩
          rw [V.obs_append, V.obs_append, cobs, V.obs_nil]
          simp only [settles, ↓reduceIte, List.append_nil]
        · have e3 : C.ofState vd.state = C.ofState inter.state :=
            ofStateGet fun k => (seamB settles ca k).symm
          refine ⟨own ++ [], append (e3 ▸ hc1) hrep2, ?_⟩
          rw [V.obs_append, V.obs_nil]
          have hf : Frame.settlementCommits frame raw = false := by simpa only [Bool.not_eq_true] using
            settles
          simp only [hf, Bool.false_eq_true, ↓reduceIte, List.append_nil]

/-- **The target handler for a model replay.**  A successful target frame satisfies `CoreAccounting` for
a carrier whose boundary reads the target's storage only through its words (`ofStateGet`; the entry
boundary is the ordinary one), given the contract's `SpawnReplay` and that its frames spawn only by
`CALL`/`STATICCALL`.  Its children may be non-static and may re-enter the contract. -/
theorem spawnReplayTarget
    (entryOfState : ∀ (sevm : Sevm) (state : State), C.frameEntry sevm state = C.ofState state)
    (ofStateGet : ∀ {s s' : State},
      (∀ k, (s.getStor ca).get k = (s'.getStor ca).get k) → C.ofState s = C.ofState s')
    (obsStatic : ∀ f : Exec.Frame, f.sevm.isStatic = true → V.frameObs f = [])
    (append : ∀ {a b c xs ys}, C.Replay a xs b → C.Replay b ys c → C.Replay a (xs ++ ys) c)
    (kinds : SpawnKinds ca sem) (spawn : SpawnReplay ca sem entry C V)
    {sevm : Sevm} {pre post : Devm} (hrun : sem.Run sevm pre post)
    (target : sevm.currentTarget = ca)
    (deeper : ForallDeeperAtSem sevm.depth ca sem
      (fun pc s d e _ => Exec.CoreAccounting ca sem entry C V pc s d e)) :
    Exec.CoreAccounting ca sem entry C V 0 sevm pre (.ok post) := by
  intro run committed fork installed admitted
  have rootNonempty : (pre.getCode ca).toList ≠ [] := fun empty =>
    sem.ne_nil (installed.1.symm.trans (congrArg some empty)) rfl
  by_cases hs : sevm.isStatic = true
  · exact staticFrame entryOfState ofStateGet obsStatic run committed fork rootNonempty hs
      (staticObservedNil kinds run hrun target fork installed admitted deeper run (.refl _) hs)
  · have hs' : sevm.isStatic = false := by simpa only [Bool.not_eq_true] using hs
    refine ⟨fun h => absurd h hs, fun bound => ?_⟩
    obtain ⟨own, hown, c3, c12⟩ := spawn run committed hrun target fork installed admitted bound hs'
    obtain ⟨steps, replay, observed⟩ := modelFrame entryOfState ofStateGet append run fork
      rootNonempty bound
      (fun step enter child resume next chain childCommitted childBound => by
        obtain ⟨-, -, -, -, -, -, -, childCore⟩ := spawnChild kinds run hrun target fork installed
          admitted deeper step enter child resume next chain
        exact (childCore childCommitted).2 childBound)
      own c3 c12
    refine ⟨steps, replay, ?_⟩
    rw [observed, hown, Exec.committedFrames, dite_eq_left committed, List.flatMap_cons]

end Exec.CoreAccounting


namespace ExecutionAccountingReplay

/-- **The accounting ladder of a model replay.**  The contract's frame theorem (`preserves`) and its
`SpawnReplay` obligations, for a carrier whose boundary reads the target's storage through its words,
give the observed accounting ladder of the deployed code: foreign frames, messages, transactions, blocks
and rollback are the generic ladder's. -/
def modelLadder {c : ContractSpecSem} {ca : Adr} {entry : Sevm → Devm → Prop}
    (C : ReplayCarrier ca) (V : ReplayObservation C)
    (append : ∀ {a b c xs ys}, C.Replay a xs b → C.Replay b ys c → C.Replay a (xs ++ ys) c)
    (tag : Nat → Option Nat → C.Tag) (frameTag : Sevm → Devm → C.Tag)
    (entryOfState : ∀ (sevm : Sevm) (state : State), C.frameEntry sevm state = C.ofState state)
    (ofStateGet : ∀ {s s' : State},
      (∀ k, (s.getStor ca).get k = (s'.getStor ca).get k) → C.ofState s = C.ofState s')
    (obsStatic : ∀ f : Exec.Frame, f.sevm.isStatic = true → V.frameObs f = [])
    (obsForeign : ∀ f : Exec.Frame, f.sevm.currentTarget ≠ ca → V.frameObs f = [])
    (kinds : SpawnKinds ca c.sem) (spawn : Exec.CoreAccounting.SpawnReplay ca c.sem entry C V)
    (preserves : c.PreservesAdmitted ca entry) : AccountingLadderAdmitted c ca entry where
  carrier := C
  append := append
  tag := tag
  preserves := preserves
  view := V
  root := by
    intro _ _ msg entryBenv pc sevm pre out run transfer evmEq committed admitted ready _ fork
      bound
    obtain ⟨installed, entryBound⟩ :=
      Exec.CoreAccounting.messageRoot_facts transfer evmEq ready bound
    have core := Exec.coreAccounting ca c.sem entry C V append frameTag
      (fun sevm state _ => entryOfState sevm state) obsForeign
      (fun hrun target deeper =>
        Exec.CoreAccounting.spawnReplayTarget entryOfState ofStateGet obsStatic append kinds
          spawn hrun target deeper)
    exact (core pc sevm pre out run installed run committed fork installed admitted).2 entryBound

end ExecutionAccountingReplay

end Blanc
