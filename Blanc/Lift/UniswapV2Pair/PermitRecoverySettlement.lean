import Blanc.Lift.UniswapV2Pair.PermitPositional
import Blanc.Lift.UniswapV2Pair.SourceOccurrence
import Blanc.ExecutionPathLocator

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The actual instruction reads the recovery request from its own memory. -/
theorem PermitCallOccurrence.request_image {root : Exec.Deriv} {b : Devm}
    (actual : PermitCallOccurrence root b) :
    (actual.call.occurrence.node.devm.memory.read (482 : B256).toNat (128 : B256).toNat).1 =
      ExternalOperation.encode (.recover (permitPublicDigest root.sevm b)
        (permitV root.sevm) (permitR root.sevm) (permitS root.sevm)) := by
  rw [actual.beforeMemory]
  have request := (permitCallMemory_facts (sevm := root.sevm) (b := b)
    getterInitMemory_ptr (Mem.reads_data getterInitMemory) (permitOwner root.sevm)
    (permitSpender root.sevm) (permitValue root.sevm) (permitDeadline root.sevm)
    (permitV root.sevm) (permitR root.sevm) (permitS root.sevm)).2.1
  change ((permitPublicCallMemory root.sevm b).read 482 128).1 =
    ExternalOperation.encode (.recover (permitPublicDigest root.sevm b)
      (permitV root.sevm) (permitR root.sevm) (permitS root.sevm)) at request
  simpa only [show (482 : B256).toNat = 482 from rfl,
    show (128 : B256).toNat = 128 from rfl] using request

/-- A recovery reply and its complete located target-frame queue use the exact
slot that the original external instruction processed. -/
structure PermitRecoverySettlement {root : Exec.Deriv} {b : Devm}
    (actual : PermitCallOccurrence root b) where
  message : Msg
  parent : Devm
  child : Devm
  delegated : Bool
  codeAddress : Adr
  childCode : ByteArray
  availableGas : Nat
  messageEq : message = callMsg root.sevm parent
    (min actual.gasWord.toNat (except64th availableGas)) 0 root.sevm.currentTarget
    (1 : B256).toAdr codeAddress true true
    (ExternalOperation.encode (.recover (permitPublicDigest root.sevm b)
      (permitV root.sevm) (permitR root.sevm) (permitS root.sevm))) childCode delegated
  process : ProcessMessage message actual.call.occurrence.slot (.ok child)
  clean : child.error.isSome = false
  output : child.output = actual.out
  resumed : (Resume.call parent 450 32).run (.ok child) = .ok actual.call.returned.devm
  spawned : Evm.step ⟨actual.call.occurrence.node.pc, actual.call.occurrence.node.sevm,
    actual.call.occurrence.node.devm⟩ =
    .spawn (Jaune.Frame.ofCall message) (Resume.call parent 450 32)
      (actual.call.occurrence.node.pc + 1)
  entered : Bool
  enteredEq : entered = actual.call.occurrence.slot.isSome
  immediate : actual.call.occurrence.slot = .none →
    (Jaune.Frame.ofCall message).enter = .done (.ok child) ∧
      root.sevm.benvStat.rules.isPrecomp (1 : B256).toAdr
  paths : List Exec.LocatedFrame
  queue : SourceSlotQueue actual.call root.sevm.currentTarget 0 paths
  childFrames : List Exec.LocatedFrame
  partition : Exec.descendantFramePaths [] 0 actual.call.occurrence.node.exc =
    childFrames ++ Exec.descendantFramePaths [] 1 actual.call.returned.exc

/-- The actual successful recovery instruction supplies its exact processed slot,
immediate entry or original runOk child, located queue, and returned output. -/
theorem PermitCallOccurrence.settlement {root : Exec.Deriv} {b post : Devm}
    (actual : PermitCallOccurrence root b) (success : root.exn = .ok post)
    (fork : CoveredFork root.sevm.benvStat.fork) :
    Nonempty (PermitRecoverySettlement actual) := by
  have one := actual.flag_one success fork
  have operands : (actual.gasWord :: 1 :: 482 :: 128 :: 450 :: 32 ::
      permitPublicCallStack root.sevm b 0xd505accf) <<+ actual.call.occurrence.node.devm.stack := by
    rw [actual.beforeState]
    exact pref_append _ []
  have primitive : Ninst.StepRun actual.call.occurrence.node.pc root.sevm
      actual.call.occurrence.node.devm Ninst.staticcall actual.call.occurrence.slot
      (.ok actual.call.returned.devm) := by
    simpa only [actual.beforeSevm, actual.call.instruction, actual.call.result]
      using actual.call.occurrence.stepRun
  rcases of_step_staticcall_val_with_depth_frame_cause operands actual.call.occurrence.filled
      primitive fork with failed | called
  · have zero := failed.1
    rw [actual.post.stack, one] at zero
    exact (by decide : (0 : B256) ≠ 1)
      (pref_head_unique zero (pref_append [1] _)) |>.elim
  · obtain ⟨parent, child, delegated, name, childCode, avail, _, _, _, _, _, _,
      _, _, process, clean, resumed, _, returnedData, _, _, spawned⟩ := called
    let message := callMsg root.sevm parent (min actual.gasWord.toNat (except64th avail)) 0
      root.sevm.currentTarget (1 : B256).toAdr name true true
      (actual.call.occurrence.node.devm.memory.read (482 : B256).toNat (128 : B256).toNat).1
      childCode delegated
    have messageEq : message = callMsg root.sevm parent
        (min actual.gasWord.toNat (except64th avail)) 0 root.sevm.currentTarget
        (1 : B256).toAdr name true true
        (ExternalOperation.encode (.recover (permitPublicDigest root.sevm b)
          (permitV root.sevm) (permitR root.sevm) (permitS root.sevm))) childCode delegated := by
      exact congrArg (fun input => callMsg root.sevm parent
        (min actual.gasWord.toNat (except64th avail)) 0 root.sevm.currentTarget
        (1 : B256).toAdr name true true input childCode delegated) actual.request_image
    have decoded : Ninst.At root.sevm.code actual.call.occurrence.node.pc Ninst.staticcall := by
      simpa only [actual.beforeSevm, actual.call.instruction] using actual.call.occurrence.decoded
    have driverSpawn : Evm.step ⟨actual.call.occurrence.node.pc,
        actual.call.occurrence.node.sevm, actual.call.occurrence.node.devm⟩ =
        .spawn (Jaune.Frame.ofCall message) (Resume.call parent 450 32)
          (actual.call.occurrence.node.pc + 1) := by
      rw [actual.beforeSevm, Evm.step_next decoded]
      exact spawned
    have output : child.output = actual.out := returnedData.symm.trans actual.post.returnData
    have immediate : actual.call.occurrence.slot = .none →
        (Jaune.Frame.ofCall message).enter = .done (.ok child) ∧
          root.sevm.benvStat.rules.isPrecomp (1 : B256).toAdr := by
      intro slot
      have processNone : ProcessMessage message .none (.ok child) := slot ▸ process
      have entered : (Jaune.Frame.ofCall message).enter = .done (.ok child) := by
        cases entry : (Jaune.Frame.ofCall message).enter with
        | done result =>
          simp only [ProcessMessage, RunFrame, entry] at processNone
          exact congrArg FrameEntry.done processNone.2.symm
        | run evm =>
          simp only [ProcessMessage, RunFrame, entry] at processNone
          obtain ⟨raw, impossible, _⟩ := processNone
          cases impossible
      have xrun : Xinst.Run root.sevm actual.call.occurrence.node.devm .staticcall
          .none (.ok actual.call.returned.devm) := by
        have step := slot ▸ primitive
        simpa only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.Run] using step
      exact ⟨entered, Xinst.staticcall_none_precompile fork operands xrun
        ⟨1, _, by simpa only [one] using actual.post.stack, by decide⟩⟩
    obtain ⟨childFrames, partition⟩ := Blanc.Exec.Deriv.ParentStep.descendantFramePaths_spawn_suffix
      actual.call.edge driverSpawn [] 0
    suffices ∃ paths, SourceSlotQueue actual.call root.sevm.currentTarget 0 paths from by
      obtain ⟨paths, queue⟩ := this
      exact ⟨⟨message, parent, child, delegated, name, childCode, avail, messageEq, process,
        clean, output, resumed, driverSpawn, actual.call.occurrence.slot.isSome, rfl,
        immediate, paths, queue, childFrames, partition⟩⟩
    cases slotEq : actual.call.occurrence.slot with
    | none => exact ⟨[], Or.inl ⟨slotEq, rfl⟩⟩
    | some pair =>
      rcases pair with ⟨childEvm, raw⟩
      have processSome : ProcessMessage message (.some ⟨childEvm, raw⟩) (.ok child) :=
        slotEq ▸ process
      have filled := actual.call.occurrence.filled
      rw [slotEq] at filled
      obtain ⟨childRun⟩ := filled
      obtain ⟨entered, settled⟩ := RunFrame.some_inv processSome
      have commits := ProcessMessage.settlementCommits_of_some_ok_clean processSome clean
      have resumedRaw : (Resume.call parent 450 32).run
          ((Jaune.Frame.ofCall message).settle raw) = .ok actual.call.returned.devm := by
        rw [← settled]
        exact resumed
      obtain ⟨next, exactRun⟩ := Exec.exists_next_of_run_spawn actual.call.occurrence.node.exc
        driverSpawn entered childRun resumedRaw
      refine ⟨(Exec.retainedTargetTurnsAt root.sevm.currentTarget [0] childRun).filterMap
        Sum.getRight?, Or.inr ?_⟩
      refine ⟨childEvm, raw, Jaune.Frame.ofCall message, Resume.call parent 450 32,
        actual.call.occurrence.node.pc + 1, childRun, next, driverSpawn, entered,
        resumedRaw, slotEq, exactRun, ?_⟩
      simp only [commits, ite_true]


end Blanc.Lift.UniswapV2Pair
