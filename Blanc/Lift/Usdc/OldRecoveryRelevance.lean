import Blanc.Lift.Usdc.OwnerQueriesV2
import Blanc.Lift.Usdc.PermitQueryV2_1
import Blanc.StaticcallObservation

/-! Local successful owner-query occurrences at their original fresh execution root.
This module does not enumerate historical invocations or define relevance by success. -/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift

/-- The registered V2/V2_1 owner routes produce one actual native answer at
its original fresh root, on any fork without state gas or block access lists
(`NeutralFork`, every historical fork). The source clause retains each exact
input and real owner comparison; this local successful producer is not a
history census. -/
private theorem old_owner_query_nativeH_effective {F : Exec.Deriv} {post : Devm}
    (pc : F.pc = 0) (stack : F.devm.stack = []) (memory : F.devm.memory = Mem.empty)
    (version : (F.sevm.code = ImplV2.code ∧ Sevm.selector F.sevm ∈ selV2.owners) ∨
      (F.sevm.code = ImplV2_1.code ∧ Sevm.selector F.sevm ∈ selV2_1.owners))
    (ready : F.sevm.benvStat.rules.delegatedCodeAddress (F.devm.getCode 1) = none)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
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
        ownerV2_query_consumed_effective pc code stack memory member ready success fork
      refine ⟨R,call,origin,parent,child,gas,_,op.recoveryPointer.toNat,Q,next,
        callEnv,spawned,process,emptySlot,native,paid,clean,childOutput,output,nonzero,
        returnData,total,⟨_,comparisonStack⟩,Or.inl ?_⟩
      exact ⟨code,op,selector,rfl,rfl,entryPc,callPc,comparisonPlaced,comparisonTree⟩
    · have selector : Sevm.selector F.sevm = 0xd505accf := by
        simpa only [selV2_1, List.mem_cons, List.not_mem_nil, or_false] using member
      obtain ⟨R,call,parent,child,gas,Q,next,entryPc,origin,beforeSpan,callPc,callEnv,
        spawned,process,emptySlot,native,paid,clean,childOutput,output,nonzero,
        returnData,total,comparisonPlaced,comparisonTree,comparisonStack⟩ :=
        permitV2_1_query_consumed_effective pc code stack memory selector ready success fork
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

/-- Pure nondelegation retains the original actual-query interface. -/
theorem old_owner_query_nativeH {F : Exec.Deriv} {post : Devm}
    (pc : F.pc = 0) (stack : F.devm.stack = []) (memory : F.devm.memory = Mem.empty)
    (version : (F.sevm.code = ImplV2.code ∧ Sevm.selector F.sevm ∈ selV2.owners) ∨
      (F.sevm.code = ImplV2_1.code ∧ Sevm.selector F.sevm ∈ selV2_1.owners))
    (nodeleg : getDelegatedCodeAddress (F.devm.getCode 1) = none)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
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
  have ready : F.sevm.benvStat.rules.delegatedCodeAddress (F.devm.getCode 1) = none := by
    simp only [ForkRules.delegatedCodeAddress, nodeleg, ite_self]
  exact old_owner_query_nativeH_effective pc stack memory version ready success fork


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
          CursorOK ImplV2_1.code ImplV2_1.cert Q next ∧ next.f = ImplV2_1.t_421e_c71)) :=
  old_owner_query_nativeH pc stack memory version nodeleg success fork.histFork.neutral

open Blanc.Lift.WriteSite

/-- A concrete successful old-USDC Pair-answer result at its original root.
This existential records the produced call; it is not a universe of relevant
queries and imposes no success restriction on the existing all-outcome observer. -/
def OldUsdcNativePairAnswer (F : Exec.Deriv) (pair : Adr) : Prop :=
  ∃ (call : CallOccurrenceStep F .staticcall) (parent child : Devm) (gas : Nat)
    (input : Bytes) (pointer : Nat) (Q : Exec.Deriv) (next : Cursor),
    let msg := callMsg call.occurrence.node.sevm parent gas 0
      call.occurrence.node.sevm.currentTarget 1 1 true true input
      (call.occurrence.node.devm.getCode 1) false
    (Sevm.dataWord F.sevm 4).toAdr = pair ∧
    ((F.sevm.code = ImplV2.code ∧ Sevm.selector F.sevm ∈ selV2.owners) ∨
      (F.sevm.code = ImplV2_1.code ∧ Sevm.selector F.sevm ∈ selV2_1.owners)) ∧
    call.occurrence.node.sevm = F.sevm ∧
    Ninst.step ⟨call.occurrence.node.pc,call.occurrence.node.sevm,call.occurrence.node.devm⟩
      (.exec .staticcall) = .spawn (Frame.ofCall msg)
        (Resume.call parent pointer 32) (call.occurrence.node.pc + 1) ∧
    ProcessMessage msg call.occurrence.slot (.ok child) ∧ call.occurrence.slot = .none ∧
    msg.codeAddress = some 1 ∧ msg.disablePrecompiles = false ∧ gasEcrecover ≤ gas ∧
    child.error.isSome = false ∧ child.output = pair.toB256.toBytes ∧ pair ≠ 0 ∧
    call.returned.devm.returnData = pair.toB256.toBytes ∧
    StaticcallObservation call.occurrence.node.pc call.occurrence.node.sevm
      call.occurrence.node.devm call.occurrence.slot call.occurrence.stepResult ∧
    StaticcallRouting msg call.occurrence.slot (.ok child) ∧
    executeCode.enter msg = .inr (executePrecomp (initEvm msg) 1) ∧
    (Frame.ofCall msg).enter = .done ((Frame.ofCall msg).settle
      (executePrecomp (initEvm msg) 1)) ∧
    (.ok child : Except (EvmError × State × AdrSet × Tra) Devm) =
      (Frame.ofCall msg).settle (executePrecomp (initEvm msg) 1) ∧
    (Resume.call parent pointer 32).run (.ok child) = call.occurrence.stepResult ∧
    executeEcrecover (initEvm msg) = .ok gasEcrecover pair.toB256.toBytes ∧
    (Execution.commits F.exn = true → call.occurrence.Retained) ∧
    Exec.Deriv.ExecFreeUntil call.returned Q ∧
    (∃ S, Q.devm.stack = pair.toB256 :: pair.toB256 :: S) ∧
    ((F.sevm.code = ImplV2.code ∧ ∃ op : OwnerOpV2,
        Sevm.selector F.sevm = op.selector ∧
        input = (op.digest F).toBytes ++ (op.vWord F.sevm).toBytes ++
          (op.rWord F.sevm).toBytes ++ (op.sWord F.sevm).toBytes ∧
        pointer = op.recoveryPointer.toNat ∧ call.occurrence.node.pc = 0x50ef ∧
        CursorOK ImplV2.code ImplV2.cert Q next ∧ next.f = op.comparison) ∨
      (F.sevm.code = ImplV2_1.code ∧
        input = (permitV2_1Digest F.sevm F.devm).toBytes ++
          (Sevm.dataWord F.sevm 132 &&& 255).toBytes ++
          (Sevm.dataWord F.sevm 164).toBytes ++ (Sevm.dataWord F.sevm 196).toBytes ∧
        pointer = 450 ∧ call.occurrence.node.pc = 0x4a78 ∧
        CursorOK ImplV2_1.code ImplV2_1.cert Q next ∧ next.f = ImplV2_1.t_421e_c71))

/-- Project the accepted actual query into the concrete Pair-answer API.
All native facts come from the unchanged original-root theorem. -/
theorem old_owner_pair_native_effective {F : Exec.Deriv} {post : Devm} {pair : Adr}
    (pc : F.pc = 0) (stack : F.devm.stack = []) (memory : F.devm.memory = Mem.empty)
    (version : (F.sevm.code = ImplV2.code ∧ Sevm.selector F.sevm ∈ selV2.owners) ∨
      (F.sevm.code = ImplV2_1.code ∧ Sevm.selector F.sevm ∈ selV2_1.owners))
    (ready : F.sevm.benvStat.rules.delegatedCodeAddress (F.devm.getCode 1) = none)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork)
    (owner : (Sevm.dataWord F.sevm 4).toAdr = pair) :
    OldUsdcNativePairAnswer F pair := by
  obtain ⟨R,original,origin,call,parent,child,gas,input,pointer,Q,next,
    identity,nodeIdentity,instructionIdentity,slotIdentity,resultIdentity,returnedIdentity,
    callEnv,spawned,process,emptySlot,address,enabled,paid,clean,childOutput,nonzero,
    returnData,observation,routing,execution,native,settlement,resumed,answer,retained,
    total,comparisonStack,source⟩ :=
    old_owner_query_nativeH_effective pc stack memory version ready success fork
  rw [owner] at childOutput nonzero returnData answer comparisonStack
  refine ⟨call,parent,child,gas,input,pointer,Q,next,owner,version,callEnv,spawned,
    process,emptySlot,address,enabled,paid,clean,childOutput,nonzero,returnData,
    observation,routing,execution,native,settlement,resumed,answer,retained,total,
    comparisonStack,?_⟩
  rcases source with ⟨code,op,selector,inputEq,pointerEq,entryPc,callPc,placed,tree⟩ |
    ⟨code,inputEq,pointerEq,entryPc,callPc,placed,tree⟩
  · exact Or.inl ⟨code,op,selector,inputEq,pointerEq,callPc,placed,tree⟩
  · exact Or.inr ⟨code,inputEq,pointerEq,callPc,placed,tree⟩

/-- Pure nondelegation retains the original actual-query interface. -/
theorem old_owner_pair_native {F : Exec.Deriv} {post : Devm} {pair : Adr}
    (pc : F.pc = 0) (stack : F.devm.stack = []) (memory : F.devm.memory = Mem.empty)
    (version : (F.sevm.code = ImplV2.code ∧ Sevm.selector F.sevm ∈ selV2.owners) ∨
      (F.sevm.code = ImplV2_1.code ∧ Sevm.selector F.sevm ∈ selV2_1.owners))
    (nodeleg : getDelegatedCodeAddress (F.devm.getCode 1) = none)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork)
    (owner : (Sevm.dataWord F.sevm 4).toAdr = pair) :
    OldUsdcNativePairAnswer F pair := by
  have ready : F.sevm.benvStat.rules.delegatedCodeAddress (F.devm.getCode 1) = none := by
    simp only [ForkRules.delegatedCodeAddress, nodeleg, ite_self]
  exact old_owner_pair_native_effective pc stack memory version ready success fork owner


/-- V1's same-run protected-write observations have only caller and initializer
exceptions. The existing empty owner table requires no native premise. -/
theorem implV1_allowLocality_observed
    {pair : Adr} {Tr : Adr → Prop} {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = ImplV1.code)
    (fork : CoveredFork sevm.benvStat.fork)
    (sep : RowSep 10 pair.toB256 (AllowKey Tr) (wsRoot ImplV1Ws.implWsAnn)
      (WriteSite.Env.root sevm)) :
    SProg.RunP (fun s d n d' => StepIn ⟨0,sevm,pre,.ok post,run⟩ s d n d' ∧
      GuardObs (fun x => ∃ g, Tr g ∧ allowSlot pair g = x)
        ((selV1T.eval (WriteSite.Env.root sevm) ∈ selV1.callers ∧ sevm.caller = pair) ∨
          selV1T.eval (WriteSite.Env.root sevm) ∈ selV1.inits) s d n)
      ImplV1.cert.prog sevm pre post := by
  refine SProg.RunP.mono ?_ (implV1_allowLocality run code fork sep)
  intro s d n d' h
  refine ⟨h.1,?_⟩
  intro store x v rest registers tracked
  rcases h.2 store x v rest registers tracked with allowed | nonInc
  · rcases allowed with ⟨caller,callerEq⟩ | ⟨owner,ownerEq⟩ | initializer
    · exact Or.inl (Or.inl ⟨caller,by simpa only [WriteSite.Env.root,toAdr_toB256] using callerEq⟩)
    · exact (List.not_mem_nil owner).elim
    · exact Or.inl (Or.inr initializer)
  · exact Or.inr nonInc

private theorem selV2T_root (sevm : Sevm) :
    selV2T.eval (WriteSite.Env.root sevm) = Sevm.selector sevm := by
  simp only [selV2T,Term.eval,Op2.eval,WriteSite.Env.root,Sevm.selector,Sevm.dataWord]
  rfl

/-- V2's local same-run write observations replace the owner-word exception
by the actual original-root native Pair answer, retaining caller and initializer
alternatives. This is a forward RunP result, not historical SSTORE completeness. -/
theorem implV2_allowLocality_observed
    {pair : Adr} {Tr : Adr → Prop} {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = ImplV2.code)
    (stack : pre.stack = []) (memory : pre.memory = Mem.empty)
    (nodeleg : getDelegatedCodeAddress (pre.getCode 1) = none)
    (fork : CoveredFork sevm.benvStat.fork)
    (sep : RowSep 10 pair.toB256 (AllowKey Tr) (wsRoot ImplV2Ws.implWsAnn)
      (WriteSite.Env.root sevm)) :
    SProg.RunP (fun s d n d' => StepIn ⟨0,sevm,pre,.ok post,run⟩ s d n d' ∧
      GuardObs (fun x => ∃ g, Tr g ∧ allowSlot pair g = x)
        ((Sevm.selector sevm ∈ selV2.callers ∧ sevm.caller = pair) ∨
          Sevm.selector sevm ∈ selV2.inits ∨
          OldUsdcNativePairAnswer ⟨0,sevm,pre,.ok post,run⟩ pair) s d n)
      ImplV2.cert.prog sevm pre post := by
  have allowed : AllowedFrame selV2 pair (WriteSite.Env.root sevm) →
      (Sevm.selector sevm ∈ selV2.callers ∧ sevm.caller = pair) ∨
        Sevm.selector sevm ∈ selV2.inits ∨
        OldUsdcNativePairAnswer ⟨0,sevm,pre,.ok post,run⟩ pair := by
    simp only [AllowedFrame,selV2]
    rw [selV2T_root]
    rintro (⟨caller,callerEq⟩ | ⟨owner,ownerEq⟩ | initializer)
    · exact Or.inl ⟨caller,by simpa only [WriteSite.Env.root,toAdr_toB256] using callerEq⟩
    · change (Sevm.dataWord sevm 4).toAdr = pair at ownerEq
      exact Or.inr (Or.inr (old_owner_pair_native (F := ⟨0,sevm,pre,.ok post,run⟩)
        rfl stack memory (Or.inl ⟨code,owner⟩) nodeleg rfl fork.histFork.neutral ownerEq))
    · exact Or.inr (Or.inl initializer)
  refine SProg.RunP.mono ?_ (implV2_allowLocality run code fork sep)
  intro s d n d' h
  refine ⟨h.1,?_⟩
  intro store x v rest registers tracked
  rcases h.2 store x v rest registers tracked with exception | nonInc
  · exact Or.inl (allowed exception)
  · exact Or.inr nonInc

/-- V2_1's local same-run write observations replace the owner-word exception
by the actual original-root native Pair answer, retaining caller and initializer
alternatives. This is a forward RunP result, not historical SSTORE completeness. -/
theorem implV2_1_allowLocality_observed
    {pair : Adr} {Tr : Adr → Prop} {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = ImplV2_1.code)
    (stack : pre.stack = []) (memory : pre.memory = Mem.empty)
    (nodeleg : getDelegatedCodeAddress (pre.getCode 1) = none)
    (fork : CoveredFork sevm.benvStat.fork)
    (sep : RowSep 10 pair.toB256 (AllowKey Tr) (wsRoot ImplV2_1Ws.implWsAnn)
      (WriteSite.Env.root sevm)) :
    SProg.RunP (fun s d n d' => StepIn ⟨0,sevm,pre,.ok post,run⟩ s d n d' ∧
      GuardObs (fun x => ∃ g, Tr g ∧ allowSlot pair g = x)
        ((Sevm.selector sevm ∈ selV2_1.callers ∧ sevm.caller = pair) ∨
          Sevm.selector sevm ∈ selV2_1.inits ∨
          OldUsdcNativePairAnswer ⟨0,sevm,pre,.ok post,run⟩ pair) s d n)
      ImplV2_1.cert.prog sevm pre post := by
  have allowed : AllowedFrame selV2_1 pair (WriteSite.Env.root sevm) →
      (Sevm.selector sevm ∈ selV2_1.callers ∧ sevm.caller = pair) ∨
        Sevm.selector sevm ∈ selV2_1.inits ∨
        OldUsdcNativePairAnswer ⟨0,sevm,pre,.ok post,run⟩ pair := by
    simp only [AllowedFrame,selV2_1]
    rw [selV2T_root]
    rintro (⟨caller,callerEq⟩ | ⟨owner,ownerEq⟩ | initializer)
    · exact Or.inl ⟨caller,by simpa only [WriteSite.Env.root,toAdr_toB256] using callerEq⟩
    · change (Sevm.dataWord sevm 4).toAdr = pair at ownerEq
      exact Or.inr (Or.inr (old_owner_pair_native (F := ⟨0,sevm,pre,.ok post,run⟩)
        rfl stack memory (Or.inr ⟨code,owner⟩) nodeleg rfl fork.histFork.neutral ownerEq))
    · exact Or.inr (Or.inl initializer)
  refine SProg.RunP.mono ?_ (implV2_1_allowLocality run code fork sep)
  intro s d n d' h
  refine ⟨h.1,?_⟩
  intro store x v rest registers tracked
  rcases h.2 store x v rest registers tracked with exception | nonInc
  · exact Or.inl (allowed exception)
  · exact Or.inr nonInc

end Blanc.Lift.Usdc
