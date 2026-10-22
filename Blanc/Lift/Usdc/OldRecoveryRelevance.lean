import Blanc.Lift.Usdc.OwnerQueriesV2
import Blanc.Lift.Usdc.PermitQueryV2_1
import Blanc.StaticcallObservation

/-! Local successful owner-query occurrences at their original fresh execution root.
This module does not enumerate historical invocations or define relevance by success. -/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift

/-- The registered V2/V2_1 owner routes produce one actual native answer at
its original fresh root. The source clause retains each exact input and real
owner comparison; this local successful producer is not a history census. -/
theorem old_owner_query_native {F : Exec.Deriv} {post : Devm}
    (pc : F.pc = 0) (stack : F.devm.stack = []) (memory : F.devm.memory = Mem.empty)
    (version : (F.sevm.code = ImplV2.code ∧ Sevm.selector F.sevm ∈ selV2.owners) ∨
      (F.sevm.code = ImplV2_1.code ∧ Sevm.selector F.sevm ∈ selV2_1.owners))
    (nodeleg : getDelegatedCodeAddress (F.devm.getCode 1) = none)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    ∃ (R : Exec.Deriv) (original : CallOccurrenceStep R .staticcall)
      (origin : Exec.Deriv.ExecFreeUntil F R) (call : CallOccurrenceStep F .staticcall)
      (parent child : Devm) (gas : Nat) (input : Bytes) (pointer : Nat)
      (Q : Exec.Deriv) (next : Cursor),
      let owner := (Sevm.dataWord F.sevm 4).toAdr
      let msg := callMsg call.occurrence.node.sevm parent gas 0
        call.occurrence.node.sevm.currentTarget 1 1 true true input
        (call.occurrence.node.devm.getCode 1) false
      call = original.reRoot origin.1 ∧
      call.occurrence.node = original.occurrence.node ∧
      call.occurrence.instruction = original.occurrence.instruction ∧
      call.occurrence.slot = original.occurrence.slot ∧
      call.occurrence.stepResult = original.occurrence.stepResult ∧
      call.returned = original.returned ∧ call.occurrence.node.sevm = F.sevm ∧
      Ninst.step ⟨call.occurrence.node.pc,call.occurrence.node.sevm,call.occurrence.node.devm⟩
        (.exec .staticcall) = .spawn (Frame.ofCall msg)
          (Resume.call parent pointer 32) (call.occurrence.node.pc + 1) ∧
      ProcessMessage msg call.occurrence.slot (.ok child) ∧ call.occurrence.slot = .none ∧
      msg.codeAddress = some 1 ∧ msg.disablePrecompiles = false ∧ gasEcrecover ≤ gas ∧
      child.error.isSome = false ∧ child.output = owner.toB256.toBytes ∧
      owner ≠ 0 ∧ call.returned.devm.returnData = owner.toB256.toBytes ∧
      StaticcallObservation call.occurrence.node.pc call.occurrence.node.sevm
        call.occurrence.node.devm call.occurrence.slot call.occurrence.stepResult ∧
      StaticcallRouting msg call.occurrence.slot (.ok child) ∧
      executeCode.enter msg = .inr (executePrecomp (initEvm msg) 1) ∧
      (Frame.ofCall msg).enter = .done ((Frame.ofCall msg).settle
        (executePrecomp (initEvm msg) 1)) ∧
      (.ok child : Except (EvmError × State × AdrSet × Tra) Devm) =
        (Frame.ofCall msg).settle (executePrecomp (initEvm msg) 1) ∧
      (Resume.call parent pointer 32).run (.ok child) = call.occurrence.stepResult ∧
      executeEcrecover (initEvm msg) = .ok gasEcrecover owner.toB256.toBytes ∧
      (Execution.commits F.exn = true → call.occurrence.Retained) ∧
      Exec.Deriv.ExecFreeUntil call.returned Q ∧
      (∃ S, Q.devm.stack = owner.toB256 :: owner.toB256 :: S) ∧
      ((F.sevm.code = ImplV2.code ∧ ∃ op : OwnerOpV2,
          Sevm.selector F.sevm = op.selector ∧
          input = (op.digest F).toBytes ++ (op.vWord F.sevm).toBytes ++
            (op.rWord F.sevm).toBytes ++ (op.sWord F.sevm).toBytes ∧
          pointer = op.recoveryPointer.toNat ∧ R.pc = 0x50a4 ∧
          call.occurrence.node.pc = 0x50ef ∧
          CursorOK ImplV2.code ImplV2.cert Q next ∧ next.f = op.comparison) ∨
        (F.sevm.code = ImplV2_1.code ∧
          input = (permitV2_1Digest F.sevm F.devm).toBytes ++
            (Sevm.dataWord F.sevm 132 &&& 255).toBytes ++
            (Sevm.dataWord F.sevm 164).toBytes ++ (Sevm.dataWord F.sevm 196).toBytes ∧
          pointer = 450 ∧ R.pc = 0x4a2d ∧ call.occurrence.node.pc = 0x4a78 ∧
          CursorOK ImplV2_1.code ImplV2_1.cert Q next ∧ next.f = ImplV2_1.t_421e_c71)) := by
  have produced : ∃ (R : Exec.Deriv) (call : CallOccurrenceStep R .staticcall)
      (origin : Exec.Deriv.ExecFreeUntil F R) (parent child : Devm) (gas : Nat)
      (input : Bytes) (pointer : Nat) (Q : Exec.Deriv) (next : Cursor),
      let owner := (Sevm.dataWord F.sevm 4).toAdr
      let msg := callMsg call.occurrence.node.sevm parent gas 0
        call.occurrence.node.sevm.currentTarget 1 1 true true input
        (call.occurrence.node.devm.getCode 1) false
      call.occurrence.node.sevm = F.sevm ∧
      Ninst.step ⟨call.occurrence.node.pc,call.occurrence.node.sevm,call.occurrence.node.devm⟩
        (.exec .staticcall) = .spawn (Frame.ofCall msg)
          (Resume.call parent pointer 32) (call.occurrence.node.pc + 1) ∧
      ProcessMessage msg call.occurrence.slot (.ok child) ∧ call.occurrence.slot = .none ∧
      (Frame.ofCall msg).enter = .done ((Frame.ofCall msg).settle
        (executePrecomp (initEvm (msg.withBenv msg.benv)) 1)) ∧
      gasEcrecover ≤ gas ∧ child.error.isSome = false ∧ child.output = owner.toB256.toBytes ∧
      ecrecoverOutput input = owner.toB256.toBytes ∧ owner ≠ 0 ∧
      call.returned.devm.returnData = owner.toB256.toBytes ∧
      Exec.Deriv.ExecFreeUntil call.returned Q ∧
      (∃ S, Q.devm.stack = owner.toB256 :: owner.toB256 :: S) ∧
      ((F.sevm.code = ImplV2.code ∧ ∃ op : OwnerOpV2,
          Sevm.selector F.sevm = op.selector ∧
          input = (op.digest F).toBytes ++ (op.vWord F.sevm).toBytes ++
            (op.rWord F.sevm).toBytes ++ (op.sWord F.sevm).toBytes ∧
          pointer = op.recoveryPointer.toNat ∧ R.pc = 0x50a4 ∧
          call.occurrence.node.pc = 0x50ef ∧
          CursorOK ImplV2.code ImplV2.cert Q next ∧ next.f = op.comparison) ∨
        (F.sevm.code = ImplV2_1.code ∧
          input = (permitV2_1Digest F.sevm F.devm).toBytes ++
            (Sevm.dataWord F.sevm 132 &&& 255).toBytes ++
            (Sevm.dataWord F.sevm 164).toBytes ++ (Sevm.dataWord F.sevm 196).toBytes ∧
          pointer = 450 ∧ R.pc = 0x4a2d ∧ call.occurrence.node.pc = 0x4a78 ∧
          CursorOK ImplV2_1.code ImplV2_1.cert Q next ∧ next.f = ImplV2_1.t_421e_c71)) := by
    rcases version with ⟨code,member⟩ | ⟨code,member⟩
    · obtain ⟨op,R,call,parent,child,gas,N,returned,Q,next,selector,entryPc,origin,
        sameEnv,sameExn,callPc,beforeSpan,callEnv,spawned,process,emptySlot,native,
        paid,clean,childOutput,output,nonzero,returnData,suffix,suffixExn,suffixEnv,
        placed,tree,continuations,registers,epilogue,comparisonEnv,comparisonExn,
        comparisonPlaced,comparisonTree,comparisonK,comparisonStack,total⟩ :=
        ownerV2_query_consumed pc code stack memory member nodeleg success fork
      refine ⟨R,call,origin,parent,child,gas,_,op.recoveryPointer.toNat,Q,next,
        callEnv,spawned,process,emptySlot,native,paid,clean,childOutput,output,nonzero,
        returnData,total,⟨_,comparisonStack⟩,Or.inl ?_⟩
      exact ⟨code,op,selector,rfl,rfl,entryPc,callPc,comparisonPlaced,comparisonTree⟩
    · have selector : Sevm.selector F.sevm = 0xd505accf := by
        simpa only [selV2_1, List.mem_cons, List.not_mem_nil, or_false] using member
      obtain ⟨R,call,parent,child,gas,Q,next,entryPc,origin,beforeSpan,callPc,callEnv,
        spawned,process,emptySlot,native,paid,clean,childOutput,output,nonzero,
        returnData,total,comparisonPlaced,comparisonTree,comparisonStack⟩ :=
        permitV2_1_query_consumed pc code stack memory selector nodeleg success fork
      refine ⟨R,call,origin,parent,child,gas,_,450,Q,next,
        callEnv,spawned,process,emptySlot,native,paid,clean,childOutput,output,nonzero,
        returnData,total,comparisonStack,Or.inr ?_⟩
      exact ⟨code,rfl,rfl,entryPc,callPc,comparisonPlaced,comparisonTree⟩
  obtain ⟨R,original,origin,parent,child,gas,input,pointer,Q,next,
    callEnv,spawned,process,emptySlot,native,paid,clean,childOutput,output,nonzero,
    returnData,total,comparisonStack,source⟩ := produced
  let call := original.reRoot origin.1
  let msg := callMsg call.occurrence.node.sevm parent gas 0
    call.occurrence.node.sevm.currentTarget 1 1 true true input
    (call.occurrence.node.devm.getCode 1) false
  have nativeActual : (Frame.ofCall msg).enter = .done
      ((Frame.ofCall msg).settle (executePrecomp (initEvm msg) 1)) := native
  have settlement : (.ok child : Except (EvmError × State × AdrSet × Tra) Devm) =
      (Frame.ofCall msg).settle (executePrecomp (initEvm msg) 1) := by
    have settled := process
    change RunFrame (Frame.ofCall msg) call.occurrence.slot (.ok child) at settled
    rw [RunFrame,nativeActual] at settled
    exact settled.2
  have resumed : (Resume.call parent pointer 32).run (.ok child) =
      call.occurrence.stepResult := by
    have actual := original.occurrence.stepRun
    rw [original.instruction,Ninst.StepRun,spawned] at actual
    obtain ⟨settled,frameRun,result⟩ := actual
    change RunFrame (Frame.ofCall msg) call.occurrence.slot settled at frameRun
    rw [RunFrame,nativeActual] at frameRun
    rw [frameRun.2,← settlement] at result
    exact result.symm
  have routing : StaticcallRouting msg call.occurrence.slot (.ok child) :=
    staticcall_routing_of_process (by rfl) call.occurrence.filled process
  have execution : executeCode.enter msg = .inr (executePrecomp (initEvm msg) 1) := by
    cases routing with
    | native address raw codeAddress enabled active entered rawNative entry slot settlement =>
        have addressOne : address = 1 := (Option.some.inj codeAddress).symm
        subst address
        rw [rawNative] at entered
        exact entered
    | vm evm raw entry slot run settlement =>
        have impossible : (none : Xlot) = some ⟨evm,raw⟩ := emptySlot.symm.trans slot
        cases impossible
  have answer : executeEcrecover (initEvm msg) =
      .ok gasEcrecover (Sevm.dataWord F.sevm 4).toAdr.toB256.toBytes := by
    rw [executeEcrecover_eq (evm := initEvm msg) paid]
    exact congrArg (PrecompResult.ok gasEcrecover) output
  exact ⟨R,original,origin,call,parent,child,gas,input,pointer,Q,next,
    rfl,rfl,rfl,rfl,rfl,rfl,callEnv,spawned,process,emptySlot,rfl,rfl,paid,clean,
    childOutput,nonzero,returnData,
    call.occurrence.staticcall_observation call.instruction,routing,execution,
    nativeActual,settlement,resumed,answer,call.retained,total,comparisonStack,source⟩

end Blanc.Lift.Usdc
