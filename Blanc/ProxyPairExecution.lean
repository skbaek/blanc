import Blanc.ProxyPairProgram
import Blanc.ProxyPairImplementation
import Blanc.RootedExecution

/-!
# A concrete installed proxy/implementation pair

This module fixes one pair of accounts and runs the selector-free proxy at the
two 32-byte guard words.  Its contract-neutral frame-root bridge lives in
`Blanc.RootedExecution`; this file supplies only the proxy-pair predicate and
the concrete walks that establish it.
-/

namespace Blanc.ProxyPair

open Jaune
open Jaune.Ninst Blanc.Ninst

/-! ## Installed pair -/

def proxyAdr : Adr := 0x00000000000000000000000000000000000a0001

def implAdr : Adr := 0x00000000000000000000000000000000000b0002

def callerAdr : Adr := 0x00000000000000000000000000000000000c0003

/-- Five-argument wrapper used only by the local forward walk below. -/
private def proxyRootedRun
    (FS : List Func) (sevm : Sevm) (devm : Devm)
    (f : Func) (ex : Execution) : Prop :=
  ∃ run : Func.RunCompiledTo FS sevm devm f ex,
    rootedRunCompiledTo
      (fun root => root.exactInvocation implGuardedProg proxyAdr implAdr) run

private theorem proxyRootedRun_next
    {FS : List Func} {sevm : Sevm} {devm : Devm}
    {instruction : Ninst} {devm' : Devm} {f : Func} {ex : Execution}
    (step : Ninst.RunCompiled sevm devm instruction devm')
    (tail : proxyRootedRun FS sevm devm' f ex)
    [nonExec : NonExecInstruction instruction] :
    proxyRootedRun FS sevm devm (.next instruction f) ex := by
  rcases tail with ⟨tailRun, tailRooted⟩
  let run : Func.RunCompiledTo FS sevm devm (.next instruction f) ex :=
    .next step tailRun
  refine ⟨run, ?_⟩
  exact rootedRunCompiledTo.next (step := step) (tail := tailRun)
    (ninstAllChildRoots_of_not_exec nonExec.notExec) tailRooted

private theorem proxyRootedRun_branch_zero
    {FS : List Func} {sevm : Sevm} {devm : Devm}
    {f g : Func} {ex : Execution} {stack : List B256} {gas : Nat}
    (stackEq : devm.stack = 0 :: stack)
    (room : devm.stack.length < 1024)
    (gasEq : devm.gasLeft = gas + (gVerylow + gHigh))
    (arm : proxyRootedRun FS sevm
      (devm.setMach ⟨stack, devm.memory, gas⟩) f ex) :
    proxyRootedRun FS sevm devm (.branch f g) ex := by
  rcases arm with ⟨armRun, armRooted⟩
  let pop := Devm.popBurnBy_setMach stackEq gasEq
  let run : Func.RunCompiledTo FS sevm devm (.branch f g) ex :=
    .zero room pop armRun
  refine ⟨run, ?_⟩
  exact rootedRunCompiledTo.zero (g := g) (room := room)
    (pop := pop) (tail := armRun) armRooted

private theorem proxyRootedRun_branch_succ
    {FS : List Func} {sevm : Sevm} {devm : Devm}
    {f g : Func} {ex : Execution} {word : B256}
    {stack : List B256} {gas : Nat}
    (nonzero : word ≠ 0)
    (stackEq : devm.stack = word :: stack)
    (room : devm.stack.length < 1024)
    (gasEq : devm.gasLeft = gas + (gVerylow + gHigh + gJumpdest))
    (arm : proxyRootedRun FS sevm
      (devm.setMach ⟨stack, devm.memory, gas⟩) g ex) :
    proxyRootedRun FS sevm devm (.branch f g) ex := by
  rcases arm with ⟨armRun, armRooted⟩
  let pop := Devm.popBurnBy_setMach stackEq gasEq
  let run : Func.RunCompiledTo FS sevm devm (.branch f g) ex :=
    .succ nonzero room pop armRun
  refine ⟨run, ?_⟩
  exact rootedRunCompiledTo.succ (f := f) (hne := nonzero)
    (room := room) (pop := pop) (tail := armRun) armRooted

private theorem proxyRootedRun_call
    {FS : List Func} {sevm : Sevm} {devm : Devm}
    {index : Nat} {f : Func} {ex : Execution} {gas : Nat}
    (found : FS[index]? = some f)
    (room : devm.stack.length < 1024)
    (gasEq : devm.gasLeft = gas + (gVerylow + gMid + gJumpdest))
    (body : proxyRootedRun FS sevm
      (devm.setMach ⟨devm.stack, devm.memory, gas⟩) f ex) :
    proxyRootedRun FS sevm devm (.call index) ex := by
  rcases body with ⟨bodyRun, bodyRooted⟩
  let burn := Devm.burnBy_setMach_gas gasEq
  let run : Func.RunCompiledTo FS sevm devm (.call index) ex :=
    .call found room burn bodyRun
  refine ⟨run, ?_⟩
  exact rootedRunCompiledTo.call (found := found) (room := room)
    (burn := burn) (tail := bodyRun) bodyRooted

private def proxyRootedRunSpec : Blanc.Forward.RelSpec where
  head := ``proxyRootedRun
  next := ``proxyRootedRun_next
  branchZero := ``proxyRootedRun_branch_zero
  branchSucc := ``proxyRootedRun_branch_succ
  call := ``proxyRootedRun_call

local syntax (name := proxyRootedFuncRun) "proxy_rooted_run"
  (ppSpace "[" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| proxy_rooted_run $[[$hints,*]]?) => do
      let goal ← Lean.Elab.Tactic.getMainGoal
      let (_, context) ← (Blanc.Forward.funcWalk goal).run
        { rel := proxyRootedRunSpec
          hints := match hints with
            | some terms => terms.getElems.toList
            | none => []
          side := #[]
          step := 0
          budget := none }
      let proof ← Lean.instantiateMVars (Lean.mkMVar goal)
      for mvarId in ← Lean.Meta.getMVars proof do
        unless ← mvarId.isAssigned do
          let type ← mvarId.getType
          if (← Lean.Meta.isClass? type).isSome then
            mvarId.withContext do
              mvarId.assign (← Lean.Meta.synthInstance type)
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      if context.step == 0 then
        throwError "proxy_rooted_run: applied no rule"
      unless context.hints.isEmpty do
        throwError "proxy_rooted_run: unused hints"
      Lean.Elab.Tactic.replaceMainGoal context.side.toList

theorem proxyAdr_ne_implAdr : proxyAdr ≠ implAdr := by decide

def proxyAcct : Acct :=
  { Acct.nil with
    stor := Stor.empty.set implementationSlot implAdr.toB256
    code := proxyCode }

def implAcct : Acct := { Acct.nil with code := implGuardedCode }

def pairState : State :=
  State.set (State.set (.empty : State) implAdr implAcct) proxyAdr proxyAcct

theorem pairState_proxyAcct : pairState.get proxyAdr = proxyAcct := by
  rw [pairState, State.get_set_self]

theorem pairState_implAcct : pairState.get implAdr = implAcct := by
  rw [pairState, State.get_set_ne _ proxyAdr_ne_implAdr, State.get_set_self]

theorem pairState_proxyCode : (pairState.get proxyAdr).code = proxyCode := by
  rw [pairState_proxyAcct]
  rfl

theorem pairState_implCode : (pairState.get implAdr).code = implGuardedCode := by
  rw [pairState_implAcct]
  rfl

theorem pairState_proxySlot :
    (pairState.get proxyAdr).stor.get implementationSlot = implAdr.toB256 := by
  rw [pairState_proxyAcct]
  unfold proxyAcct
  rw [implementationSlot_val]
  rw [Stor.get_set_self]

theorem pairState_implSlot_zero :
    (pairState.get implAdr).stor.get implSlot = 0 := by
  rw [pairState_implAcct]
  rfl

theorem pairState_proxyImplSlot_zero :
    (pairState.get proxyAdr).stor.get implSlot = 0 := by
  rw [pairState_proxyAcct]
  unfold proxyAcct
  rw [Stor.get_set_ne _ implSlot_ne_implementationSlot.symm]
  simp [Stor.empty, Stor.get]

/-! ## The two fixed messages -/

def successData : Bytes := (1 : B256).toBytes

def revertData : Bytes := (0 : B256).toBytes

theorem successData_length : successData.length = 32 := by
  simp [successData, B256.length_toBytes]

theorem revertData_length : revertData.length = 32 := by
  simp [revertData, B256.length_toBytes]

def pairBenv : Benv :=
  { (default : Benv) with
    state := pairState
    stat := { (default : BenvStat) with origState := pairState } }

/-! ## The cold call split -/

theorem proxy_call_gas_split :
    calculateMsgCallGas 0 25095 25095 0 gasColdAccountAccess =
      (24744, 22144) := by
  decide

theorem pairBenv_impl_not_precompile :
    pairBenv.stat.rules.isPrecomp implAdr = false := by decide

/-! ## Entry and child messages -/

def proxyMsgSuccess : Msg :=
  { (default : Msg) with
    benv := pairBenv
    caller := callerAdr
    target := some proxyAdr
    currentTarget := proxyAdr
    gas := 27224
    value := 0
    data := successData
    codeAddress := some proxyAdr
    code := proxyCode
    shouldTransferValue := false
    isStatic := false
    accessedAddresses := .emptyWithCapacity
    accessedStorageKeys := .emptyWithCapacity
    disablePrecompiles := true }

def proxyMsgRevert : Msg :=
  { proxyMsgSuccess with data := revertData }

theorem proxyMsgSuccess_code : proxyMsgSuccess.code = proxyCode := rfl

theorem proxyMsgRevert_code : proxyMsgRevert.code = proxyCode := rfl

theorem proxyMsgSuccess_data : proxyMsgSuccess.data = successData := rfl

theorem proxyMsgRevert_data : proxyMsgRevert.data = revertData := rfl

theorem proxyMsgSuccess_gas : proxyMsgSuccess.gas = 27224 := rfl

theorem proxyMsgRevert_gas : proxyMsgRevert.gas = 27224 := rfl

theorem proxyMsgSuccess_target : proxyMsgSuccess.currentTarget = proxyAdr := rfl

theorem proxyMsgRevert_target : proxyMsgRevert.currentTarget = proxyAdr := rfl

theorem proxyMsgSuccess_caller : proxyMsgSuccess.caller = callerAdr := rfl

theorem proxyMsgRevert_caller : proxyMsgRevert.caller = callerAdr := rfl

/-! The continuation after the actual delegatecall.  Keeping this as a local
function lets the prefix walk be checked independently of the child resume. -/
def proxySuccessTail : Func :=
  proxyReturnTail

theorem proxyFallback_eq_prefix :
    proxyFallback =
      (calldatasize ::: pushB256 0 ::: pushB256 0 ::: calldatacopy :::
        pushB256 0 ::: pushB256 0 ::: calldatasize ::: pushB256 0 :::
        pushB256 implementationSlotLit ::: sload ::: gas ::: delcall :::
        proxySuccessTail) := by
  rfl

private lemma proxy_empty_extCost (S : List B256) (G : Nat) :
    ((initDevm proxyMsgSuccess).setMach
      ⟨S, (initDevm proxyMsgSuccess).memory, G⟩).extCost [⟨0, 32⟩] = gMemory := by
  rw [show (initDevm proxyMsgSuccess).memory = Mem.empty by rfl]
  simpa [initDevm, proxyMsgSuccess] using
    (Devm.extCost_empty_word (devm := initDevm proxyMsgSuccess) (S := S) (G := G))

private lemma proxy_copy_cost (S : List B256) (G : Nat) :
    gVerylow + gasCopy * ceilDiv 32 32 +
      ((initDevm proxyMsgSuccess).setMach
        ⟨S, (initDevm proxyMsgSuccess).memory, G⟩).extCost [⟨0, 32⟩] = 9 := by
  rw [proxy_empty_extCost]
  decide

private lemma proxy_empty_extCost' (S : List B256) (G : Nat) :
    ((initDevm proxyMsgSuccess).setMach
      ⟨S, Mem.empty, G⟩).extCost [⟨0, 32⟩] = gMemory := by
  exact Devm.extCost_empty_word

private def proxyCallPreSuccess : Devm :=
  let mem := (initDevm proxyMsgSuccess).memory.write (B256.toNat 0)
    ((initSevm proxyMsgSuccess).data.sliceD (B256.toNat 0)
      (Nat.toB256 (List.length (initSevm proxyMsgSuccess).data)).toNat 0)
  let entry := (initDevm proxyMsgSuccess).setMach ⟨[], Mem.empty, 27223⟩
  let beforeSload := entry.setMach
    ⟨[implementationSlotLit, 0,
        Nat.toB256 (List.length (initSevm proxyMsgSuccess).data), 0, 0], mem,
      27197⟩
  let afterSload :=
    (addAccessedStorageKey beforeSload
      (initSevm proxyMsgSuccess).currentTarget implementationSlotLit).setMach
      ⟨[beforeSload.getStorVal
          (initSevm proxyMsgSuccess).currentTarget implementationSlotLit,
        0, Nat.toB256 (List.length (initSevm proxyMsgSuccess).data), 0, 0], mem,
        27197 - gasColdSload⟩
  afterSload.setMach
      ⟨[Nat.toB256 25095,
        implAdr.toB256,
        0, Nat.toB256 (List.length (initSevm proxyMsgSuccess).data), 0, 0], mem,
      25095⟩

private def proxyCallBaseSuccess : Devm :=
  proxyCallPreSuccess.setMach
    ⟨[], proxyCallPreSuccess.memory, proxyCallPreSuccess.gasLeft⟩

private def proxySuccessD1 : Devm :=
  addAccessedAddress proxyCallBaseSuccess implAdr

private def proxySuccessParent : Devm :=
  callSpawnParent proxySuccessD1 24744 0 32 0 0

private def proxySuccessChild : Msg :=
  delcallSpawnMsg (initSevm proxyMsgSuccess) proxySuccessParent 22144
    implAdr 0 32 implGuardedCode false

private theorem proxy_success_child_enters :
    (Frame.ofCall proxySuccessChild).enter = .run (initEvm proxySuccessChild) := by
  apply Frame.enter_run_of_nonprecompile
    (f := Frame.ofCall proxySuccessChild) (adr := implAdr)
  · rfl
  · rfl
  · change pairBenv.stat.rules.isPrecomp implAdr = false
    exact pairBenv_impl_not_precompile

private theorem proxy_success_child_run :
    ∃ post,
      Prog.RunCompiledTo (initSevm proxySuccessChild)
        (initDevm proxySuccessChild) implGuardedProg (.ok post) ∧
      post.error = (initDevm proxySuccessChild).error ∧
      post.output = implReturnWord.toBytes ∧ post.gasLeft = 0 ∧
      post.state = pairState.setStorVal proxyAdr implSlot 1 ∧
      post.transientStorage = (initDevm proxySuccessChild).transientStorage ∧
      post.logs = (initDevm proxySuccessChild).logs := by
  have h_cold :
      (⟨(initSevm proxySuccessChild).currentTarget, implSlot⟩ : Adr × B256) ∉
        (initDevm proxySuccessChild).accessedStorageKeys := by
    change ((proxyAdr, implSlot) : Adr × B256) ∉
      (Std.HashSet.emptyWithCapacity : KeySet).insert
        (proxyAdr, implementationSlotLit)
    simpa [implementationSlotLit_eq_slot] using
      implSlot_ne_implementationSlot.symm
  have h_orig :
      getOrigStorVal (initSevm proxySuccessChild)
        (initSevm proxySuccessChild).currentTarget implSlot = 0 := by
    change (pairState.get proxyAdr).stor.get implSlot = 0
    exact pairState_proxyImplSlot_zero
  have h_cur :
      (initDevm proxySuccessChild).getStorVal
        (initSevm proxySuccessChild).currentTarget implSlot = 0 := by
    change (pairState.get proxyAdr).stor.get implSlot = 0
    exact pairState_proxyImplSlot_zero
  have h_data : Sevm.dataWord (initSevm proxySuccessChild) 0 ≠ 0 := by
    change Bytes.toB256 successData ≠ 0
    rw [show successData = (1 : B256).toBytes by rfl,
      B256.toB256_toBytes]
    decide
  obtain ⟨post, hrun, herr, hout, hgas, hstate, _, htra, hlogs⟩ :=
    implGuarded_runCompiledTo_nonzero [implGuarded]
      (initSevm proxySuccessChild) (initDevm proxySuccessChild) 0
      (by rfl) h_cold h_orig h_cur h_data
  refine ⟨post, ?_, herr, hout, hgas, hstate, htra, hlogs⟩
  refine Prog.runCompiledTo_intro (G := 22143)
    (mid := (initDevm proxySuccessChild).setMach
      ⟨(initDevm proxySuccessChild).stack,
        (initDevm proxySuccessChild).memory, 22143⟩) ?_ rfl hrun
  decide

private theorem proxy_success_child_exec :
    ∃ post,
      exec (initEvm proxySuccessChild) = .ok post ∧
      post.error = (initDevm proxySuccessChild).error ∧
      post.output = implReturnWord.toBytes ∧ post.gasLeft = 0 ∧
      post.state = pairState.setStorVal proxyAdr implSlot 1 ∧
      post.transientStorage = (initDevm proxySuccessChild).transientStorage ∧
      post.logs = (initDevm proxySuccessChild).logs := by
  obtain ⟨post, hrun, herr, hout, hgas, hstate, htra, hlogs⟩ :=
    proxy_success_child_run
  have h_code : some (initSevm proxySuccessChild).code.toList =
      Prog.compile implGuardedProg := by
    rw [show (initSevm proxySuccessChild).code = implGuardedCode by rfl]
    rw [show implGuardedCode.toList = implGuardedBytes by
      simp [implGuardedCode, ByteArray.toList_eq_toList_data]]
    exact implGuardedProg_compile.symm
  refine ⟨post, Prog.exec_of_runCompiledTo hrun h_code, herr, hout, hgas,
    hstate, htra, hlogs⟩

private theorem proxy_success_child_frame_roots
    {raw : Execution}
    (child : Exec (initEvm proxySuccessChild).pc
      (initEvm proxySuccessChild).sta
      (initEvm proxySuccessChild).dyna raw) :
    ∀ root ∈ Exec.rawFrameRoots child,
      root.exactInvocation implGuardedProg proxyAdr implAdr := by
  let childRoot : Exec.Deriv :=
    ⟨(initEvm proxySuccessChild).pc,
      (initEvm proxySuccessChild).sta,
      (initEvm proxySuccessChild).dyna, raw, child⟩
  have invocation :
      childRoot.exactInvocation implGuardedProg proxyAdr implAdr := by
    refine ⟨rfl, rfl, rfl, ?_⟩
    change some implGuardedCode.toList = Prog.compile implGuardedProg
    rw [show implGuardedCode.toList = implGuardedBytes by
      simp [implGuardedCode, ByteArray.toList_eq_toList_data]]
    exact implGuardedProg_compile.symm
  have noExecSource :
      ∀ site ∈ implGuardedProg.sourceSites, ∀ x : Xinst,
        site.instruction ≠ .exec x := by
    intro site member x
    simp [implGuardedProg, implGuarded, implSuccess, implRevert,
      Prog.sourceSites, table, cdl, mstoreAt, prepend,
      Func.sourceSites] at member
    aesop (add simp [Ninst.pushB256])
  have childless : Exec.rawFrameDescendants child = [] := by
    apply Exec.rawFrameDescendants_eq_nil_of_no_sameFrame_xinstAt child
    intro node sameFrame x instructionAt
    rcases childRoot.nonPush_sourceSite invocation sameFrame (by trivial)
        instructionAt with ⟨site, member, _, instructionEq⟩
    exact noExecSource site member x instructionEq
  intro root member
  rw [Exec.rawFrameRoots, childless, List.mem_singleton] at member
  exact member ▸ invocation

def proxySuccessChildMsg : Msg := proxySuccessChild

theorem proxySuccessChildMsg_exec :
    ∃ post,
      exec (initEvm proxySuccessChildMsg) = .ok post ∧
      Nonempty (Exec 0 (initSevm proxySuccessChildMsg)
        (initDevm proxySuccessChildMsg) (.ok post)) ∧
      post.error = (initDevm proxySuccessChildMsg).error ∧
      post.output = implReturnWord.toBytes ∧ post.gasLeft = 0 ∧
      post.state = pairState.setStorVal proxyAdr implSlot 1 ∧
      post.transientStorage = (initDevm proxySuccessChildMsg).transientStorage ∧
      post.logs = (initDevm proxySuccessChildMsg).logs := by
  obtain ⟨post, h_exec, herr, hout, hgas, hstate, htra, hlogs⟩ :=
    proxy_success_child_exec
  have hexec :
      exec ⟨0, initSevm proxySuccessChildMsg, initDevm proxySuccessChildMsg⟩ =
        .ok post := by
    simpa [proxySuccessChildMsg, initEvm] using h_exec
  have hderiv :
      Nonempty (Exec 0 (initSevm proxySuccessChildMsg)
        (initDevm proxySuccessChildMsg) (.ok post)) :=
    (exec_iff_exec_eq _ _ _ _).mpr hexec
  refine ⟨post, hexec, hderiv, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [proxySuccessChildMsg] using herr
  · exact hout
  · exact hgas
  · exact hstate
  · simpa [proxySuccessChildMsg] using htra
  · simpa [proxySuccessChildMsg] using hlogs

private theorem proxy_success_h_ext :
    (proxyCallBaseSuccess.setMach
      ⟨[], proxyCallBaseSuccess.memory, proxyCallBaseSuccess.gasLeft⟩).extCost
      [⟨0, 32⟩, ⟨0, 0⟩] = 0 := by
  apply Devm.extCost_covered
  decide

private theorem proxy_success_h_del :
    accessDelegation
      (addAccessedAddress
        (proxyCallPreSuccess.setMach
          ⟨[], proxyCallPreSuccess.memory, proxyCallPreSuccess.gasLeft⟩)
        implAdr) implAdr =
      ⟨false, implAdr, implGuardedCode, 0, proxySuccessD1⟩ := by
  change accessDelegation (addAccessedAddress proxyCallBaseSuccess implAdr) implAdr = _
  have hcode :
      (addAccessedAddress proxyCallBaseSuccess implAdr).state.getCode implAdr =
        implGuardedCode := by
    change (pairState.get implAdr).code = implGuardedCode
    exact pairState_implCode
  unfold accessDelegation
  simp only [hcode, implGuardedCode_notDelegation]
  rfl

private theorem proxy_success_h_acc :
    accessCost implAdr proxyCallBaseSuccess.accessedAddresses + 0 =
      gasColdAccountAccess := by
  have h : proxyCallBaseSuccess.accessedAddresses =
      (Std.HashSet.emptyWithCapacity : AdrSet) := by rfl
  rw [h]
  unfold accessCost
  simp

private theorem proxy_success_h_gas : 24744 + 0 ≤ proxySuccessD1.gasLeft := by
  decide

private theorem proxy_success_h_depth :
    (initSevm proxyMsgSuccess).depth ≠ 0 := by
  decide

private theorem proxy_success_delcall_spawn :
    Xinst.step (initSevm proxyMsgSuccess) proxyCallPreSuccess .delcall =
      .spawn (Frame.ofCall proxySuccessChild)
        (.call proxySuccessParent 0 0) := by
  have h_stk : proxyCallPreSuccess.stack =
      25095 :: implAdr.toB256 :: 0 :: 32 :: 0 :: 0 :: [] := by
    simp only [proxyCallPreSuccess, Devm.setMach_stack]
    decide
  have h_split :
      calculateMsgCallGas 0 25095 proxySuccessD1.gasLeft 0
          gasColdAccountAccess = (24744, 22144) := by
    change calculateMsgCallGas 0 25095 25095 0 gasColdAccountAccess =
      (24744, 22144)
    exact proxy_call_gas_split
  simpa [proxySuccessParent, proxySuccessChild,
    show (0 : B256).toNat = 0 by decide,
    show (32 : B256).toNat = 32 by decide] using
    (Xinst.step_delcall_spawn h_stk proxy_success_h_ext
      proxy_success_h_del proxy_success_h_acc h_split
      proxy_success_h_gas proxy_success_h_depth)

private theorem proxy_success_delcall_allChildRoots {post : Devm} :
    ninstAllChildRoots
      (fun root => root.exactInvocation implGuardedProg proxyAdr implAdr)
      (sevm := initSevm proxyMsgSuccess) (devm := proxyCallPreSuccess)
      (n := .exec .delcall) (devm' := post) := by
  exact ninstAllChildRoots_of_exec_spawn proxy_success_delcall_spawn
    proxy_success_child_enters (by
      intro raw child
      exact proxy_success_child_frame_roots child)

private theorem proxy_success_delcall :
    ∃ childPost post,
      childPost.output = implReturnWord.toBytes ∧
      childPost.gasLeft = 0 ∧
      childPost.state = pairState.setStorVal proxyAdr implSlot 1 ∧
      childPost.transientStorage = proxyCallPreSuccess.transientStorage ∧
      childPost.logs = proxyCallPreSuccess.logs ∧
      Ninst.RunCompiled (initSevm proxyMsgSuccess) proxyCallPreSuccess
        (.exec .delcall) post ∧
      post = (((incorporateChildOnSuccess proxySuccessParent childPost
        childPost.output).setMach
          ⟨1 :: proxySuccessParent.stack, proxySuccessParent.memory,
            proxySuccessParent.gasLeft + childPost.gasLeft⟩).memWrite
        0 (childPost.output.take 0)) ∧
      post.stack = [1] ∧
      post.memory = proxyCallPreSuccess.memory ∧
      post.gasLeft = 351 ∧
      post.returnData = implReturnWord.toBytes := by
  have h_stk : proxyCallPreSuccess.stack =
      25095 :: implAdr.toB256 :: 0 :: 32 :: 0 :: 0 :: [] := by
    simp only [proxyCallPreSuccess, Devm.setMach_stack]
    decide
  have h_del :
      accessDelegation
        (addAccessedAddress
          (proxyCallPreSuccess.setMach
            ⟨[], proxyCallPreSuccess.memory, proxyCallPreSuccess.gasLeft⟩)
          implAdr) implAdr =
        ⟨false, implAdr, implGuardedCode, 0, proxySuccessD1⟩ :=
    proxy_success_h_del
  obtain ⟨childPost, hchild, herr, hout, hgas, hstate, htra, hlogs⟩ :=
    proxy_success_child_exec
  have h_ok : childPost.error.isSome = false := by
    rw [herr]
    rfl
  have hsettle :
      (Frame.ofCall proxySuccessChild).settle
        (exec (initEvm proxySuccessChild)) = .ok childPost := by
    rw [hchild]
    simp [Frame.ofCall, Frame.settle, Frame.settleMsg, processMessage.settle,
      executeCode.handleError, h_ok]
  let post := (((incorporateChildOnSuccess proxySuccessParent childPost
      childPost.output).setMach
        ⟨1 :: proxySuccessParent.stack, proxySuccessParent.memory,
          proxySuccessParent.gasLeft + childPost.gasLeft⟩).memWrite 0
      (childPost.output.take 0))
  have hres :
      Resume.run (.call proxySuccessParent 0 0)
        ((Frame.ofCall proxySuccessChild).settle
          (exec (initEvm proxySuccessChild))) = .ok post := by
    have hpstack : proxySuccessParent.stack.length < 1024 := by
      change [].length < 1024
      decide
    rw [hsettle, Resume.run_call_ok h_ok hpstack]
  refine ⟨childPost, post, ?_⟩
  constructor
  · exact hout
  · constructor
    · exact hgas
    · constructor
      · exact hstate
      · constructor
        · exact htra
        · constructor
          · unfold proxyCallPreSuccess
            simp only [Devm.setMach_logs]
            rw [hlogs]
            rfl
          · constructor
            · apply Ninst.runCompiled_delcall h_stk
              · exact proxy_success_h_ext
              · exact h_del
              · exact proxy_success_h_acc
              · change calculateMsgCallGas 0 25095 25095 0 gasColdAccountAccess =
                  (24744, 22144)
                exact proxy_call_gas_split
              · exact proxy_success_h_gas
              · exact proxy_success_h_depth
              · change (Frame.ofCall proxySuccessChild).enter = .run (initEvm proxySuccessChild)
                exact proxy_success_child_enters
              · have h0 : (0 : B256).toNat = 0 := by decide
                have h32 : (32 : B256).toNat = 32 := by decide
                simpa [post, proxySuccessParent, proxySuccessChild, h0, h32] using hres
            · constructor
              · dsimp only [post]
              · constructor
                · dsimp only [post]
                  rfl
                · constructor
                  · dsimp only [post]
                    change proxySuccessParent.memory = proxyCallPreSuccess.memory
                    change proxyCallBaseSuccess.memory.extends
                        [⟨0, 32⟩, ⟨0, 0⟩] = proxyCallPreSuccess.memory
                    rw [Mem.extends_covered (by decide)]
                    rfl
                  · constructor
                    · dsimp only [post]
                      rw [hgas]
                      change proxySuccessParent.gasLeft + 0 = 351
                      decide
                    · dsimp only [post]
                      change childPost.output = implReturnWord.toBytes
                      exact hout

private theorem proxy_success_tail (childPost : Devm)
    (hout : childPost.output = implReturnWord.toBytes)
    (hstate : childPost.state = pairState.setStorVal proxyAdr implSlot 1)
    (htra : childPost.transientStorage = proxyCallPreSuccess.transientStorage)
    (hlogs : childPost.logs = proxyCallPreSuccess.logs) :
    ∃ final,
      Func.RunCompiledTo (proxyFallback :: [])
        (initSevm proxyMsgSuccess)
        (((incorporateChildOnSuccess proxySuccessParent childPost childPost.output).setMach
          ⟨1 :: proxySuccessParent.stack, proxySuccessParent.memory, 351⟩).memWrite
            0 (childPost.output.take 0))
        proxySuccessTail (.ok final) ∧
      final.output = implReturnWord.toBytes ∧
      final.gasLeft = 318 ∧
      final.state = pairState.setStorVal proxyAdr implSlot 1 ∧
      final.transientStorage = proxyCallPreSuccess.transientStorage ∧
      final.logs = proxyCallPreSuccess.logs := by
  have hbound : (0 : Nat) + 32 ≤ implReturnWord.toBytes.length := by
    simp [B256.length_toBytes]
  let base := incorporateChildOnSuccess proxySuccessParent childPost childPost.output
  let final :=
    (((base.setMach ⟨[], proxySuccessParent.memory.write 0
        implReturnWord.toBytes, 318⟩).memRead 0 32).2.withOutput
      implReturnWord.toBytes)
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hstart :
        (((incorporateChildOnSuccess proxySuccessParent childPost childPost.output).setMach
            ⟨1 :: proxySuccessParent.stack, proxySuccessParent.memory, 351⟩).memWrite
          0 (childPost.output.take 0)) =
        base.setMach ⟨[1], proxySuccessParent.memory, 351⟩ := by
      simp [base, Devm.memWrite, Mach.memWrite, liftMachPure,
        Mem.write, hout]
      rw [Devm.setMach_setMach]
      rfl
    rw [hstart]
    have hbase_returnData : base.returnData = implReturnWord.toBytes := by
      dsimp [base]
      rw [incorporateChildOnSuccess_returnData, hout]
    have hpmem : proxySuccessParent.memory.size = 32 := by
      decide
    have hext :
        (base.setMach ⟨[0, 0, 32, 0, 1], proxySuccessParent.memory, 343⟩).extCost
          [⟨0, 32⟩] = 0 := by
      apply Devm.extCost_covered
      rw [hpmem]
      decide
    have hslice :
        List.sliceD implReturnWord.toBytes 0 32 0 = implReturnWord.toBytes := by
      decide +kernel
    func_run [6]
    all_goals simp_all [Devm.returnData_setMach, B256.length_toBytes]
    all_goals try decide
    case h_cost =>
      simp only [show Nat.toB256 32 = (32 : B256) by decide,
        show (B256.toNat (32 : B256)) = 32 by decide,
        show ((0 : B256).toNat) = 0 by decide]
      rw [hext]
      decide
    case h_arm =>
      dsimp [final]
      rw [show Nat.toB256 32 = (32 : B256) by decide,
        show (B256.toNat (0 : B256)) = 0 by decide,
        show (B256.toNat (32 : B256)) = 32 by decide,
        show (OfNat.ofNat 0 : UInt8) = 0 by decide,
        hslice]
      have hne : implReturnWord.toBytes ≠ [] := by
        intro h
        have := B256.length_toBytes implReturnWord
        rw [h] at this
        simp at this
      have hread :
          ((proxySuccessParent.memory.write 0 implReturnWord.toBytes).read 0 32).1 =
            implReturnWord.toBytes := by
        simpa only [B256.length_toBytes] using
          (Mem.read_write_zero proxySuccessParent.memory hne)
      have hfinalext :
          (base.setMach ⟨[0, 32], proxySuccessParent.memory.write 0
            implReturnWord.toBytes, 318⟩).extCost [⟨0, 32⟩] = 0 := by
        apply Devm.extCost_covered
        have hm : (proxySuccessParent.memory.write 0 implReturnWord.toBytes).size = 32 := by
          decide
        rw [hm]
        decide
      have hrun := Func.runCompiledTo_ret_word
        (fs := [proxyFallback]) (sevm := initSevm proxyMsgSuccess)
        (devm := base.setMach ⟨[0, 32], proxySuccessParent.memory.write 0
          implReturnWord.toBytes, 318⟩)
        (i := 0) (sz := 32) (s := []) (e := 0) (G := 318)
        (out := implReturnWord.toBytes) rfl hfinalext rfl hread
      simpa only [Devm.setMach_setMach, Devm.memory_setMach,
        Devm.gasLeft_setMach,
        show (B256.toNat (0 : B256)) = 0 by decide,
        show (B256.toNat (32 : B256)) = 32 by decide] using hrun
  · rfl
  · rfl
  · simp only [final, Devm.withOutput_state, Devm.memRead_state,
      Devm.setMach_state]
    change childPost.state = pairState.setStorVal proxyAdr implSlot 1
    exact hstate
  · simp only [final, Devm.withOutput_transientStorage]
    change childPost.transientStorage = proxyCallPreSuccess.transientStorage
    exact htra
  · simp only [final, Devm.withOutput_logs, Devm.memRead_logs,
      Devm.setMach_logs]
    unfold base incorporateChildOnSuccess
    simp only [Devm.setWorld_logs, Devm.setMeta_logs, Devm.setMach_logs]
    rw [hlogs]
    rfl

private theorem proxy_success_func_run :
  ∃ final,
      proxyRootedRun [proxyFallback] (initSevm proxyMsgSuccess)
        ((initDevm proxyMsgSuccess).setMach
          ⟨[], Mem.empty, 27223⟩) proxyFallback (.ok final) ∧
      final.output = implReturnWord.toBytes ∧
      final.gasLeft = 318 ∧
      final.state = pairState.setStorVal proxyAdr implSlot 1 ∧
      final.transientStorage = proxyCallPreSuccess.transientStorage ∧
      final.logs = proxyCallPreSuccess.logs := by
  obtain ⟨childPost, post, hout, hgas, hstate, htra, hlogs, hcall, hpost,
      _hstack, _hmemory, _hcallgas, _hreturnData⟩ := proxy_success_delcall
  obtain ⟨final, htail, hfout, hfgas, hfstate, hftra, hflogs⟩ :=
    proxy_success_tail childPost hout hstate htra hlogs
  rw [hpost] at hcall
  have rooted : proxyRootedRun [proxyFallback] (initSevm proxyMsgSuccess)
      ((initDevm proxyMsgSuccess).setMach ⟨[], Mem.empty, 27223⟩)
      proxyFallback (.ok final) := by
    change proxyRootedRun [proxyFallback] (initSevm proxyMsgSuccess)
      ((initDevm proxyMsgSuccess).setMach ⟨[], Mem.empty, 27223⟩)
      (calldatasize ::: pushB256 0 ::: pushB256 0 ::: calldatacopy :::
        pushB256 0 ::: pushB256 0 ::: calldatasize ::: pushB256 0 :::
        pushB256 implementationSlotLit ::: sload ::: gas ::: delcall :::
        proxySuccessTail) (.ok final)
    proxy_rooted_run [9]
    all_goals simp_all
    all_goals try decide
    case h_cold =>
      change ((proxyAdr, implementationSlotLit) : Adr × B256) ∉
        (Std.HashSet.emptyWithCapacity : KeySet)
      simp
    case tail =>
      have h_stk : proxyCallPreSuccess.stack =
          25095 :: implAdr.toB256 :: 0 :: 32 :: 0 :: 0 :: [] := by
        simp only [proxyCallPreSuccess, Devm.setMach_stack]
        decide
      have hslot :
          (initDevm proxyMsgSuccess).getStorVal
              (initSevm proxyMsgSuccess).currentTarget implementationSlotLit =
            implAdr.toB256 := by
        change (pairState.get proxyAdr).stor.get implementationSlotLit = implAdr.toB256
        rw [implementationSlotLit_eq_slot, pairState_proxySlot]
      have hmem : (initDevm proxyMsgSuccess).memory = Mem.empty := by rfl
      have tailRooted : rootedRunCompiledTo
          (fun root => root.exactInvocation implGuardedProg proxyAdr implAdr)
          htail :=
        rootedRunCompiledTo_of_execFree (run := htail) (by
          simp [proxySuccessTail, proxyReturnTail, funcExecFree, Ninst.pushB256])
      have known : proxyRootedRun [proxyFallback]
          (initSevm proxyMsgSuccess) proxyCallPreSuccess
          (delcall ::: proxySuccessTail) (.ok final) := by
        refine ⟨Func.RunCompiledTo.next hcall htail, ?_⟩
        exact rootedRunCompiledTo.next (step := hcall) (tail := htail)
          proxy_success_delcall_allChildRoots tailRooted
      simpa only [proxyCallPreSuccess, Devm.setMach_setMach,
        Devm.addAccessedStorageKey_setMach_setMach, Devm.getStorVal_setMach,
        Devm.memory_setMach, h_stk, hslot, hmem] using known
  exact ⟨final, rooted, hfout, hfgas, hfstate, hftra, hflogs⟩

theorem proxyProg_success_runCompiledTo :
    ∃ (final : Devm) (outer : Exec 0 (initSevm proxyMsgSuccess)
        (initDevm proxyMsgSuccess) (.ok final)),
      Prog.RunCompiledTo (initSevm proxyMsgSuccess)
        (initDevm proxyMsgSuccess) proxyProg (.ok final) ∧
      exec ⟨0, initSevm proxyMsgSuccess, initDevm proxyMsgSuccess⟩ =
        .ok final ∧
      (∀ root ∈ Exec.rawFrameRoots outer,
        root = (⟨0, initSevm proxyMsgSuccess, initDevm proxyMsgSuccess,
          .ok final, outer⟩ : Exec.Deriv) ∨
        root.exactInvocation implGuardedProg proxyAdr implAdr) ∧
      final.output = implReturnWord.toBytes ∧
      final.gasLeft = 318 ∧
      final.state = pairState.setStorVal proxyAdr implSlot 1 ∧
      final.transientStorage = (initDevm proxyMsgSuccess).transientStorage ∧
      final.logs = (initDevm proxyMsgSuccess).logs := by
  obtain ⟨final, ⟨hrun, rooted⟩, hout, hgas, hstate, hftra, hflogs⟩ :=
    proxy_success_func_run
  have hprog :
      Prog.RunCompiledTo (initSevm proxyMsgSuccess)
        (initDevm proxyMsgSuccess) proxyProg (.ok final) := by
    refine Prog.runCompiledTo_intro (G := 27223)
      (mid := (initDevm proxyMsgSuccess).setMach
        ⟨[], Mem.empty, 27223⟩) ?_ rfl hrun
    decide
  have hcode :
      some (initSevm proxyMsgSuccess).code.toList = Prog.compile proxyProg := by
    rw [show (initSevm proxyMsgSuccess).code = proxyCode by rfl]
    rw [show proxyCode.toList = proxyBytes by
      simp [proxyCode, proxyBytes, ByteArray.toList_eq_toList_data]]
    exact proxyProg_compile
  have htra0 :
      proxyCallPreSuccess.transientStorage =
        (initDevm proxyMsgSuccess).transientStorage := by rfl
  have hlogs0 :
      proxyCallPreSuccess.logs = (initDevm proxyMsgSuccess).logs := by rfl
  have hburn : Devm.BurnBy gJumpdest (initDevm proxyMsgSuccess)
      ((initDevm proxyMsgSuccess).setMach
        ⟨[], Mem.empty, 27223⟩) := by
    apply Devm.burnBy_setMach_gas
    decide
  obtain ⟨outer, descendantRoots⟩ :=
    Prog.exec_of_rootedRunCompiledTo hburn rooted hcode
  have hexec :
      exec ⟨0, initSevm proxyMsgSuccess, initDevm proxyMsgSuccess⟩ =
        .ok final :=
    (exec_iff_exec_eq _ _ _ _).mp ⟨outer⟩
  have rootCases :
      ∀ root ∈ Exec.rawFrameRoots outer,
        root = (⟨0, initSevm proxyMsgSuccess, initDevm proxyMsgSuccess,
          .ok final, outer⟩ : Exec.Deriv) ∨
        root.exactInvocation implGuardedProg proxyAdr implAdr := by
    intro root member
    simp only [Exec.rawFrameRoots, List.mem_cons] at member
    rcases member with rfl | member
    · exact Or.inl rfl
    · exact Or.inr (descendantRoots root member)
  refine ⟨final, outer, hprog, hexec, rootCases, hout, hgas, hstate, ?_, ?_⟩
  · exact hftra.trans htra0
  · exact hflogs.trans hlogs0

/-! ## Reverting guard branch -/

private def proxyCallPreRevert : Devm :=
  let mem := (initDevm proxyMsgRevert).memory.write (B256.toNat 0)
    ((initSevm proxyMsgRevert).data.sliceD (B256.toNat 0)
      (Nat.toB256 (List.length (initSevm proxyMsgRevert).data)).toNat 0)
  let entry := (initDevm proxyMsgRevert).setMach ⟨[], Mem.empty, 27223⟩
  let beforeSload := entry.setMach
    ⟨[implementationSlotLit, 0,
        Nat.toB256 (List.length (initSevm proxyMsgRevert).data), 0, 0], mem,
      27197⟩
  let afterSload :=
    (addAccessedStorageKey beforeSload
      (initSevm proxyMsgRevert).currentTarget implementationSlotLit).setMach
      ⟨[beforeSload.getStorVal
          (initSevm proxyMsgRevert).currentTarget implementationSlotLit,
        0, Nat.toB256 (List.length (initSevm proxyMsgRevert).data), 0, 0], mem,
        27197 - gasColdSload⟩
  afterSload.setMach
      ⟨[Nat.toB256 25095,
        implAdr.toB256,
        0, Nat.toB256 (List.length (initSevm proxyMsgRevert).data), 0, 0], mem,
      25095⟩

private def proxyCallBaseRevert : Devm :=
  proxyCallPreRevert.setMach
    ⟨[], proxyCallPreRevert.memory, proxyCallPreRevert.gasLeft⟩

private def proxyRevertD1 : Devm :=
  addAccessedAddress proxyCallBaseRevert implAdr

private def proxyRevertParent : Devm :=
  callSpawnParent proxyRevertD1 24744 0 32 0 0

private def proxyRevertChild : Msg :=
  delcallSpawnMsg (initSevm proxyMsgRevert) proxyRevertParent 22144
    implAdr 0 32 implGuardedCode false

private theorem proxy_revert_child_enters :
    (Frame.ofCall proxyRevertChild).enter = .run (initEvm proxyRevertChild) := by
  apply Frame.enter_run_of_nonprecompile
    (f := Frame.ofCall proxyRevertChild) (adr := implAdr)
  · rfl
  · rfl
  · change pairBenv.stat.rules.isPrecomp implAdr = false
    exact pairBenv_impl_not_precompile

private theorem proxy_revert_child_run :
    ∃ post,
      Prog.RunCompiledTo (initSevm proxyRevertChild)
        (initDevm proxyRevertChild) implGuardedProg
          (.error (.revert, post)) ∧
      post.error = (initDevm proxyRevertChild).error ∧
      post.output = [] ∧ post.gasLeft = 22117 ∧
      post.state = pairState ∧
      post.transientStorage = (initDevm proxyRevertChild).transientStorage ∧
      post.logs = (initDevm proxyRevertChild).logs := by
  have h_cold :
      (⟨(initSevm proxyRevertChild).currentTarget, implSlot⟩ : Adr × B256) ∉
        (initDevm proxyRevertChild).accessedStorageKeys := by
    change ((proxyAdr, implSlot) : Adr × B256) ∉
      (Std.HashSet.emptyWithCapacity : KeySet).insert
        (proxyAdr, implementationSlotLit)
    simpa [implementationSlotLit_eq_slot] using
      implSlot_ne_implementationSlot.symm
  have h_data : Sevm.dataWord (initSevm proxyRevertChild) 0 = 0 := by
    change Bytes.toB256 revertData = 0
    rw [show revertData = (0 : B256).toBytes by rfl,
      B256.toB256_toBytes]
  obtain ⟨post, hrun, herr, hout, hgas, hstate, htra, hlogs⟩ :=
    implGuarded_runCompiledTo_zero [implGuarded]
      (initSevm proxyRevertChild) (initDevm proxyRevertChild) 22117 h_data
  refine ⟨post, ?_, herr, hout, hgas, ?_, htra, hlogs⟩
  · refine Prog.runCompiledTo_intro (G := 22143)
      (mid := (initDevm proxyRevertChild).setMach
        ⟨(initDevm proxyRevertChild).stack,
          (initDevm proxyRevertChild).memory, 22143⟩) ?_ rfl hrun
    decide
  · change post.state = pairState at hstate
    exact hstate

private theorem proxy_revert_child_exec :
    ∃ raw,
      exec (initEvm proxyRevertChild) = .error (.revert, raw) ∧
      raw.error = (initDevm proxyRevertChild).error ∧
      raw.output = [] ∧ raw.gasLeft = 22117 ∧
      raw.state = pairState ∧
      raw.transientStorage = (initDevm proxyRevertChild).transientStorage ∧
      raw.logs = (initDevm proxyRevertChild).logs := by
  obtain ⟨raw, hrun, herr, hout, hgas, hstate, htra, hlogs⟩ :=
    proxy_revert_child_run
  have h_code : some (initSevm proxyRevertChild).code.toList =
      Prog.compile implGuardedProg := by
    rw [show (initSevm proxyRevertChild).code = implGuardedCode by rfl]
    rw [show implGuardedCode.toList = implGuardedBytes by
      simp [implGuardedCode, ByteArray.toList_eq_toList_data]]
    exact implGuardedProg_compile.symm
  refine ⟨raw, ?_, herr, hout, hgas, hstate, htra, hlogs⟩
  simpa [initEvm] using Prog.exec_of_runCompiledTo hrun h_code

private theorem proxy_revert_child_frame_roots
    {raw : Execution}
    (child : Exec (initEvm proxyRevertChild).pc
      (initEvm proxyRevertChild).sta
      (initEvm proxyRevertChild).dyna raw) :
    ∀ root ∈ Exec.rawFrameRoots child,
      root.exactInvocation implGuardedProg proxyAdr implAdr := by
  let childRoot : Exec.Deriv :=
    ⟨(initEvm proxyRevertChild).pc,
      (initEvm proxyRevertChild).sta,
      (initEvm proxyRevertChild).dyna, raw, child⟩
  have invocation :
      childRoot.exactInvocation implGuardedProg proxyAdr implAdr := by
    refine ⟨rfl, rfl, rfl, ?_⟩
    change some implGuardedCode.toList = Prog.compile implGuardedProg
    rw [show implGuardedCode.toList = implGuardedBytes by
      simp [implGuardedCode, ByteArray.toList_eq_toList_data]]
    exact implGuardedProg_compile.symm
  have noExecSource :
      ∀ site ∈ implGuardedProg.sourceSites, ∀ x : Xinst,
        site.instruction ≠ .exec x := by
    intro site member x
    simp [implGuardedProg, implGuarded, implSuccess, implRevert,
      Prog.sourceSites, table, cdl, mstoreAt, prepend,
      Func.sourceSites] at member
    aesop (add simp [Ninst.pushB256])
  have childless : Exec.rawFrameDescendants child = [] := by
    apply Exec.rawFrameDescendants_eq_nil_of_no_sameFrame_xinstAt child
    intro node sameFrame x instructionAt
    rcases childRoot.nonPush_sourceSite invocation sameFrame (by trivial)
        instructionAt with ⟨site, member, _, instructionEq⟩
    exact noExecSource site member x instructionEq
  intro root member
  rw [Exec.rawFrameRoots, childless, List.mem_singleton] at member
  exact member ▸ invocation

def proxyRevertChildMsg : Msg := proxyRevertChild

theorem proxyRevertChildMsg_exec :
    ∃ raw,
      Prog.RunCompiledTo (initSevm proxyRevertChildMsg)
        (initDevm proxyRevertChildMsg) implGuardedProg
          (.error (.revert, raw)) ∧
      exec (initEvm proxyRevertChildMsg) = .error (.revert, raw) ∧
      Nonempty (Exec 0 (initSevm proxyRevertChildMsg)
        (initDevm proxyRevertChildMsg) (.error (.revert, raw))) ∧
      raw.error = (initDevm proxyRevertChildMsg).error ∧
      raw.output = [] ∧ raw.gasLeft = 22117 ∧
      raw.state = pairState ∧
      raw.transientStorage = (initDevm proxyRevertChildMsg).transientStorage ∧
      raw.logs = (initDevm proxyRevertChildMsg).logs := by
  obtain ⟨raw, hrun, herr, hout, hgas, hstate, htra, hlogs⟩ :=
    proxy_revert_child_run
  have h_code : some (initSevm proxyRevertChild).code.toList =
      Prog.compile implGuardedProg := by
    rw [show (initSevm proxyRevertChild).code = implGuardedCode by rfl]
    rw [show implGuardedCode.toList = implGuardedBytes by
      simp [implGuardedCode, ByteArray.toList_eq_toList_data]]
    exact implGuardedProg_compile.symm
  have hexec :
      exec (initEvm proxyRevertChildMsg) = .error (.revert, raw) :=
    by
      simpa [proxyRevertChildMsg, initEvm] using
        (Prog.exec_of_runCompiledTo hrun h_code)
  have hderiv :
      Nonempty (Exec 0 (initSevm proxyRevertChildMsg)
        (initDevm proxyRevertChildMsg) (.error (.revert, raw))) := by
    have h_eq :
        exec ⟨0, initSevm proxyRevertChildMsg,
          initDevm proxyRevertChildMsg⟩ = .error (.revert, raw) := by
      simpa [proxyRevertChildMsg, initEvm] using hexec
    exact (exec_iff_exec_eq _ _ _ _).mpr h_eq
  refine ⟨raw, hrun, hexec, hderiv, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [proxyRevertChildMsg] using herr
  · exact hout
  · exact hgas
  · exact hstate
  · simpa [proxyRevertChildMsg] using htra
  · simpa [proxyRevertChildMsg] using hlogs

private theorem proxy_revert_h_ext :
    (proxyCallBaseRevert.setMach
      ⟨[], proxyCallBaseRevert.memory, proxyCallBaseRevert.gasLeft⟩).extCost
      [⟨0, 32⟩, ⟨0, 0⟩] = 0 := by
  apply Devm.extCost_covered
  decide

private theorem proxy_revert_h_del :
    accessDelegation
      (addAccessedAddress
        (proxyCallPreRevert.setMach
          ⟨[], proxyCallPreRevert.memory, proxyCallPreRevert.gasLeft⟩)
        implAdr) implAdr =
      ⟨false, implAdr, implGuardedCode, 0, proxyRevertD1⟩ := by
  change accessDelegation (addAccessedAddress proxyCallBaseRevert implAdr) implAdr = _
  have hcode :
      (addAccessedAddress proxyCallBaseRevert implAdr).state.getCode implAdr =
        implGuardedCode := by
    change (pairState.get implAdr).code = implGuardedCode
    exact pairState_implCode
  unfold accessDelegation
  simp only [hcode, implGuardedCode_notDelegation]
  rfl

private theorem proxy_revert_h_acc :
    accessCost implAdr proxyCallBaseRevert.accessedAddresses + 0 =
      gasColdAccountAccess := by
  have h : proxyCallBaseRevert.accessedAddresses =
      (Std.HashSet.emptyWithCapacity : AdrSet) := by rfl
  rw [h]
  unfold accessCost
  simp

private theorem proxy_revert_h_gas :
    24744 + 0 ≤ proxyRevertD1.gasLeft := by
  decide

private theorem proxy_revert_h_depth :
    (initSevm proxyMsgRevert).depth ≠ 0 := by
  decide

private theorem proxy_revert_delcall_spawn :
    Xinst.step (initSevm proxyMsgRevert) proxyCallPreRevert .delcall =
      .spawn (Frame.ofCall proxyRevertChild)
        (.call proxyRevertParent 0 0) := by
  have h_stk : proxyCallPreRevert.stack =
      25095 :: implAdr.toB256 :: 0 :: 32 :: 0 :: 0 :: [] := by
    simp only [proxyCallPreRevert, Devm.setMach_stack]
    decide
  have h_split :
      calculateMsgCallGas 0 25095 proxyRevertD1.gasLeft 0
          gasColdAccountAccess = (24744, 22144) := by
    change calculateMsgCallGas 0 25095 25095 0 gasColdAccountAccess =
      (24744, 22144)
    exact proxy_call_gas_split
  simpa [proxyRevertParent, proxyRevertChild,
    show (0 : B256).toNat = 0 by decide,
    show (32 : B256).toNat = 32 by decide] using
    (Xinst.step_delcall_spawn h_stk proxy_revert_h_ext
      proxy_revert_h_del proxy_revert_h_acc h_split
      proxy_revert_h_gas proxy_revert_h_depth)

private theorem proxy_revert_delcall_allChildRoots {post : Devm} :
    ninstAllChildRoots
      (fun root => root.exactInvocation implGuardedProg proxyAdr implAdr)
      (sevm := initSevm proxyMsgRevert) (devm := proxyCallPreRevert)
      (n := .exec .delcall) (devm' := post) := by
  exact ninstAllChildRoots_of_exec_spawn proxy_revert_delcall_spawn
    proxy_revert_child_enters (by
      intro raw child
      exact proxy_revert_child_frame_roots child)

private theorem proxy_revert_delcall :
    ∃ childPost post,
      childPost.error.isSome = true ∧
      childPost.output = [] ∧ childPost.gasLeft = 22117 ∧
      childPost.state = pairState ∧
      childPost.transientStorage = proxyCallPreRevert.transientStorage ∧
      childPost.logs = proxyCallPreRevert.logs ∧
      Ninst.RunCompiled (initSevm proxyMsgRevert) proxyCallPreRevert
        (.exec .delcall) post ∧
      post = (((incorporateChildOnError proxyRevertParent childPost
        childPost.output).setMach
          ⟨0 :: proxyRevertParent.stack, proxyRevertParent.memory,
            proxyRevertParent.gasLeft + childPost.gasLeft⟩).memWrite
        0 (childPost.output.take 0)) ∧
      post.stack = [0] ∧
      post.memory = proxyCallPreRevert.memory ∧
      post.gasLeft = 22468 ∧
      post.returnData = [] := by
  have h_stk : proxyCallPreRevert.stack =
      25095 :: implAdr.toB256 :: 0 :: 32 :: 0 :: 0 :: [] := by
    simp only [proxyCallPreRevert, Devm.setMach_stack]
    decide
  have h_del :
      accessDelegation
        (addAccessedAddress
          (proxyCallPreRevert.setMach
            ⟨[], proxyCallPreRevert.memory, proxyCallPreRevert.gasLeft⟩)
          implAdr) implAdr =
        ⟨false, implAdr, implGuardedCode, 0, proxyRevertD1⟩ :=
    proxy_revert_h_del
  obtain ⟨raw, hchild, herr, hout, hgas, hstate, htra, hlogs⟩ :=
    proxy_revert_child_exec
  let childPost := raw.withError (some .revert)
  have hrawerr : (raw.withError (some .revert)).error.isSome = true := by
    rfl
  have hsettle :
      (Frame.ofCall proxyRevertChild).settle
        (exec (initEvm proxyRevertChild)) = .ok childPost := by
    rw [hchild]
    simp [childPost, Frame.ofCall, Frame.settle, Frame.settleMsg,
      processMessage.settle, executeCode.handleError, hrawerr]
    unfold Devm.rollback
    apply Devm.ext
    · rfl
    · rfl
    · apply World.ext
      · change proxyRevertChild.benv.state = raw.state
        rw [hstate]
        rfl
      · change proxyRevertChild.tenv.transientStorage = raw.transientStorage
        rw [htra]
        rfl
  have hce : childPost.error.isSome = true := by
    exact hrawerr
  have hchildgas : childPost.gasLeft = 22117 := by
    change raw.gasLeft = 22117
    exact hgas
  have hchildout : childPost.output = [] := by
    change raw.output = []
    exact hout
  let post := (((incorporateChildOnError proxyRevertParent childPost
      childPost.output).setMach
        ⟨0 :: proxyRevertParent.stack, proxyRevertParent.memory,
          proxyRevertParent.gasLeft + childPost.gasLeft⟩).memWrite 0
      (childPost.output.take 0))
  have hres :
      Resume.run (.call proxyRevertParent 0 0)
        ((Frame.ofCall proxyRevertChild).settle
          (exec (initEvm proxyRevertChild))) = .ok post := by
    rw [hsettle, Resume.run_call_err hce (by decide)]
  refine ⟨childPost, post, ?_⟩
  constructor
  · exact hce
  · constructor
    · change raw.output = []
      exact hout
    · constructor
      · change raw.gasLeft = 22117
        exact hgas
      · constructor
        · change raw.state = pairState
          exact hstate
        · constructor
          · change raw.transientStorage = proxyCallPreRevert.transientStorage
            rw [htra]
            rfl
          · constructor
            · change raw.logs = proxyCallPreRevert.logs
              rw [hlogs]
              rfl
            · constructor
              · apply Ninst.runCompiled_delcall h_stk
                · exact proxy_revert_h_ext
                · exact h_del
                · exact proxy_revert_h_acc
                · change calculateMsgCallGas 0 25095 25095 0 gasColdAccountAccess =
                    (24744, 22144)
                  exact proxy_call_gas_split
                · exact proxy_revert_h_gas
                · exact proxy_revert_h_depth
                · change (Frame.ofCall proxyRevertChild).enter =
                    .run (initEvm proxyRevertChild)
                  exact proxy_revert_child_enters
                · have h0 : (0 : B256).toNat = 0 := by decide
                  have h32 : (32 : B256).toNat = 32 := by decide
                  simpa [post, proxyRevertParent, proxyRevertChild, h0, h32]
                    using hres
              · constructor
                · dsimp only [post]
                · constructor
                  · dsimp only [post]
                    rfl
                  · constructor
                    · dsimp only [post]
                      change proxyRevertParent.memory = proxyCallPreRevert.memory
                      change proxyCallBaseRevert.memory.extends
                          [⟨0, 32⟩, ⟨0, 0⟩] = proxyCallPreRevert.memory
                      rw [Mem.extends_covered (by decide)]
                      rfl
                    · constructor
                      · dsimp only [post]
                        rw [hchildgas]
                        change proxyRevertParent.gasLeft + 22117 = 22468
                        decide
                      · dsimp only [post]
                        change childPost.output = []
                        exact hchildout

private theorem proxy_revert_tail (childPost : Devm)
    (hout : childPost.output = [])
    (hstate : childPost.state = pairState)
    (htra : childPost.transientStorage = proxyCallPreRevert.transientStorage) :
    ∃ final,
      Func.RunCompiledTo [proxyFallback] (initSevm proxyMsgRevert)
        (((incorporateChildOnError proxyRevertParent childPost childPost.output).setMach
          ⟨0 :: proxyRevertParent.stack, proxyRevertParent.memory, 22468⟩).memWrite
            0 (childPost.output.take 0))
        proxySuccessTail (.error (.revert, final)) ∧
      final.output = [] ∧
      final.gasLeft = 22439 ∧
      final.state = pairState ∧
      final.transientStorage = proxyCallPreRevert.transientStorage ∧
      final.logs = proxyCallPreRevert.logs := by
  let base := incorporateChildOnError proxyRevertParent childPost childPost.output
  let final := (base.setMach ⟨[], proxyRevertParent.memory, 22439⟩).withOutput []
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hstart :
        (((incorporateChildOnError proxyRevertParent childPost childPost.output).setMach
          ⟨0 :: proxyRevertParent.stack, proxyRevertParent.memory, 22468⟩).memWrite
            0 (childPost.output.take 0)) =
        base.setMach ⟨[0], proxyRevertParent.memory, 22468⟩ := by
      simp [base, Devm.memWrite, Mach.memWrite, liftMachPure, Mem.write, hout]
      rw [Devm.setMach_setMach]
      rfl
    rw [hstart]
    have hbase_returnData : base.returnData = [] := by
      dsimp [base]
      rw [incorporateChildOnError_returnData, hout]
    func_run [3]
    all_goals simp_all [Devm.returnData_setMach]
    all_goals try decide
    case h_cost =>
      simp only [show (Nat.toB256 0).toNat = 0 by decide]
      rw [Devm.extCost_empty_window]
      decide
    case h_arm =>
      dsimp [final]
      have hrun := Func.runCompiledTo_rev
        (fs := [proxyFallback]) (sevm := initSevm proxyMsgRevert)
        (devm := base.setMach ⟨[0, 0], proxyRevertParent.memory, 22439⟩)
        (i := 0) (sz := 0) (s := []) (out := []) (G := 22439)
        (d' := base.setMach ⟨[], proxyRevertParent.memory, 22439⟩)
        (by rfl) (by
          change (22439 : Nat) = 22439 +
            (base.setMach ⟨[0, 0], proxyRevertParent.memory, 22439⟩).extCost
              [⟨0, 0⟩]
          rw [Devm.extCost_empty_window]) (by exact Devm.memRead_zero)
      have hslice :
          List.sliceD ([] : Bytes) (B256.toNat 0) (B256.toNat 0) 0 = [] := by
        rfl
      have hmemzero :
          proxyRevertParent.memory.write (B256.toNat 0)
            (List.sliceD ([] : Bytes) (B256.toNat 0)
                (B256.toNat 0) 0) = proxyRevertParent.memory := by
        rw [hslice]
        rfl
      simpa [hmemzero, show Nat.toB256 0 = (0 : B256) by decide] using hrun
  · rfl
  · rfl
  · simp only [final, Devm.withOutput_state, Devm.setMach_state]
    change childPost.state = pairState
    exact hstate
  · simp only [final, Devm.withOutput_transientStorage]
    unfold base incorporateChildOnError
    simp only [Devm.setWorld_transientStorage, Devm.setMach_transientStorage]
    exact htra
  · simp only [final, Devm.withOutput_logs, Devm.setMach_logs]
    change (incorporateChildOnError proxyRevertParent childPost
      childPost.output).logs = proxyCallPreRevert.logs
    rw [incorporateChildOnError_logs]
    rfl

private theorem proxy_revert_func_run :
    ∃ final,
      proxyRootedRun [proxyFallback] (initSevm proxyMsgRevert)
        ((initDevm proxyMsgRevert).setMach
          ⟨[], Mem.empty, 27223⟩) proxyFallback
          (.error (.revert, final)) ∧
      final.output = [] ∧
      final.gasLeft = 22439 ∧
      final.state = pairState ∧
      final.transientStorage = proxyCallPreRevert.transientStorage ∧
      final.logs = proxyCallPreRevert.logs := by
  obtain ⟨childPost, post, hce, hout, hgas, hstate, htra, hlogs, hcall, hpost,
      _hstack, _hmemory, _hcallgas, _hreturnData⟩ := proxy_revert_delcall
  obtain ⟨final, htail, hfout, hfgas, hfstate, hftra, hflogs⟩ :=
    proxy_revert_tail childPost hout hstate htra
  rw [hpost] at hcall
  have rooted : proxyRootedRun [proxyFallback] (initSevm proxyMsgRevert)
      ((initDevm proxyMsgRevert).setMach ⟨[], Mem.empty, 27223⟩)
      proxyFallback (.error (.revert, final)) := by
    change proxyRootedRun [proxyFallback] (initSevm proxyMsgRevert)
      ((initDevm proxyMsgRevert).setMach ⟨[], Mem.empty, 27223⟩)
      (calldatasize ::: pushB256 0 ::: pushB256 0 ::: calldatacopy :::
        pushB256 0 ::: pushB256 0 ::: calldatasize ::: pushB256 0 :::
        pushB256 implementationSlotLit ::: sload ::: gas ::: delcall :::
        proxySuccessTail) (.error (.revert, final))
    proxy_rooted_run [9]
    all_goals simp_all
    all_goals try decide
    case h_cold =>
      change ((proxyAdr, implementationSlotLit) : Adr × B256) ∉
        (Std.HashSet.emptyWithCapacity : KeySet)
      simp
    case tail =>
      have h_stk : proxyCallPreRevert.stack =
          25095 :: implAdr.toB256 :: 0 :: 32 :: 0 :: 0 :: [] := by
        simp only [proxyCallPreRevert, Devm.setMach_stack]
        decide
      have hslot :
          (initDevm proxyMsgRevert).getStorVal
              (initSevm proxyMsgRevert).currentTarget implementationSlotLit =
            implAdr.toB256 := by
        change (pairState.get proxyAdr).stor.get implementationSlotLit = implAdr.toB256
        rw [implementationSlotLit_eq_slot, pairState_proxySlot]
      have hmem : (initDevm proxyMsgRevert).memory = Mem.empty := by rfl
      have tailRooted : rootedRunCompiledTo
          (fun root => root.exactInvocation implGuardedProg proxyAdr implAdr)
          htail :=
        rootedRunCompiledTo_of_execFree (run := htail) (by
          simp [proxySuccessTail, proxyReturnTail, funcExecFree, Ninst.pushB256])
      have known : proxyRootedRun [proxyFallback]
          (initSevm proxyMsgRevert) proxyCallPreRevert
          (delcall ::: proxySuccessTail) (.error (.revert, final)) := by
        refine ⟨Func.RunCompiledTo.next hcall htail, ?_⟩
        exact rootedRunCompiledTo.next (step := hcall) (tail := htail)
          proxy_revert_delcall_allChildRoots tailRooted
      simpa only [proxyCallPreRevert, Devm.setMach_setMach,
        Devm.addAccessedStorageKey_setMach_setMach, Devm.getStorVal_setMach,
        Devm.memory_setMach, h_stk, hslot, hmem] using known
  exact ⟨final, rooted, hfout, hfgas, hfstate, hftra, hflogs⟩

theorem proxyProg_revert_runCompiledTo :
    ∃ (final : Devm) (outer : Exec 0 (initSevm proxyMsgRevert)
        (initDevm proxyMsgRevert) (.error (.revert, final))),
      Prog.RunCompiledTo (initSevm proxyMsgRevert)
        (initDevm proxyMsgRevert) proxyProg
          (.error (.revert, final)) ∧
      exec ⟨0, initSevm proxyMsgRevert, initDevm proxyMsgRevert⟩ =
        .error (.revert, final) ∧
      (∀ root ∈ Exec.rawFrameRoots outer,
        root = (⟨0, initSevm proxyMsgRevert, initDevm proxyMsgRevert,
          .error (.revert, final), outer⟩ : Exec.Deriv) ∨
        root.exactInvocation implGuardedProg proxyAdr implAdr) ∧
      final.output = [] ∧
      final.gasLeft = 22439 ∧
      final.state = pairState ∧
      final.transientStorage = (initDevm proxyMsgRevert).transientStorage ∧
      final.logs = (initDevm proxyMsgRevert).logs := by
  obtain ⟨final, ⟨hrun, rooted⟩, hout, hgas, hstate, hftra, hflogs⟩ :=
    proxy_revert_func_run
  have hprog :
      Prog.RunCompiledTo (initSevm proxyMsgRevert)
        (initDevm proxyMsgRevert) proxyProg (.error (.revert, final)) := by
    refine Prog.runCompiledTo_intro (G := 27223)
      (mid := (initDevm proxyMsgRevert).setMach
        ⟨[], Mem.empty, 27223⟩) ?_ rfl hrun
    decide
  have hcode :
      some (initSevm proxyMsgRevert).code.toList = Prog.compile proxyProg := by
    rw [show (initSevm proxyMsgRevert).code = proxyCode by rfl]
    rw [show proxyCode.toList = proxyBytes by
      simp [proxyCode, proxyBytes, ByteArray.toList_eq_toList_data]]
    exact proxyProg_compile
  have hburn : Devm.BurnBy gJumpdest (initDevm proxyMsgRevert)
      ((initDevm proxyMsgRevert).setMach
        ⟨[], Mem.empty, 27223⟩) := by
    apply Devm.burnBy_setMach_gas
    decide
  obtain ⟨outer, descendantRoots⟩ :=
    Prog.exec_of_rootedRunCompiledTo hburn rooted hcode
  have hexec :
      exec ⟨0, initSevm proxyMsgRevert, initDevm proxyMsgRevert⟩ =
        .error (.revert, final) :=
    (exec_iff_exec_eq _ _ _ _).mp ⟨outer⟩
  have rootCases :
      ∀ root ∈ Exec.rawFrameRoots outer,
        root = (⟨0, initSevm proxyMsgRevert, initDevm proxyMsgRevert,
          .error (.revert, final), outer⟩ : Exec.Deriv) ∨
        root.exactInvocation implGuardedProg proxyAdr implAdr := by
    intro root member
    simp only [Exec.rawFrameRoots, List.mem_cons] at member
    rcases member with rfl | member
    · exact Or.inl rfl
    · exact Or.inr (descendantRoots root member)
  refine ⟨final, outer, hprog, hexec, rootCases, hout, hgas, hstate, ?_, ?_⟩
  · exact hftra
  · exact hflogs

end Blanc.ProxyPair
