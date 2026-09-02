import Blanc.MessageExecutionInversion
import Blanc.PinnedPauseTarget
import Blanc.ProrataWethVaultCode
import Blanc.TransientSettlement
import Blanc.WethCode

/-!
# The PRORATA vault's exact WETH boundary

This is the first inhabitant of Blanc's composition stratum.  It owns facts
that name both the PRORATA WETH vault and the inherited WETH program; neither
contract family imports this module.

The cut in this file is deliberately below the ERC-4626 laws.  It fixes the
configured account, independent calldata encoders, direct-code conditions and
the shape of an actually spawned WETH child.  Contract effects are attached in
the sibling composition module, never accepted as a premise here.
-/

namespace Blanc.Composition.ProrataWethVault

open Jaune

/-! ## Configured accounts and direct code -/

/-- The account selected by the vault's compiled `assetAddress` constant. -/
def wethAccount : Adr :=
  Blanc.ProrataWethVault.assetAddress.toAdr

/-- The configured word is already a canonical address word. -/
theorem wethAccount_toB256 :
    wethAccount.toB256 = Blanc.ProrataWethVault.assetAddress := by
  decide +kernel

/-- The direct-code assumptions at one vault call edge.

The byte equality is exposed rather than replaced by a behavioural token
interface.  Together with `wethCode_compile` it identifies the exact inherited
Blanc program. -/
structure DirectWethConfiguration
    (vault : Adr) (sevm : Sevm) (pre : Devm) : Prop where
  distinct : wethAccount ≠ vault
  nonprecompile : sevm.benvStat.rules.isPrecomp wethAccount = false
  code : (pre.getCode wethAccount).toList = Blanc.wethCode

theorem DirectWethConfiguration.installed
    {vault : Adr} {sevm : Sevm} {pre : Devm}
    (config : DirectWethConfiguration vault sevm pre) :
    ProgramInstalledAt pre.state wethAccount Blanc.weth := by
  unfold ProgramInstalledAt
  rw [show pre.state.getCode wethAccount = pre.getCode wethAccount from rfl,
    config.code, Blanc.wethCode_compile]

theorem DirectWethConfiguration.notDelegated
    {vault : Adr} {sevm : Sevm} {pre : Devm}
    (config : DirectWethConfiguration vault sevm pre) :
    ¬ isValidDelegation (pre.getCode wethAccount) := by
  apply not_delegation_of_compile (p := Blanc.weth)
  rw [config.code, Blanc.wethCode_compile]

theorem DirectWethConfiguration.resolvedCodeAddress
    {vault : Adr} {sevm : Sevm} {pre : Devm}
    (config : DirectWethConfiguration vault sevm pre) :
    (getDelegatedCodeAddress (pre.getCode wethAccount)).getD wethAccount =
      wethAccount := by
  unfold getDelegatedCodeAddress
  rw [if_neg config.notDelegated]
  rfl

/-! ## Independent calldata encoders -/

/-- Canonical `balanceOf(vault)` calldata, 36 bytes. -/
def balanceOfCalldata (vault : Adr) : Bytes :=
  abiSelectorBytes (selector "balanceOf" [.address]) ++ vault.toB256.toBytes

/-- Canonical `transferFrom(owner,vault,assets)` calldata, 100 bytes. -/
def transferFromCalldata (owner vault : Adr) (assets : B256) : Bytes :=
  abiSelectorBytes
      (selector "transferFrom" [.address, .address, .uint256]) ++
    owner.toB256.toBytes ++ vault.toB256.toBytes ++ assets.toBytes

/-- Canonical `transfer(receiver,assets)` calldata, 68 bytes. -/
def transferCalldata (receiver : Adr) (assets : B256) : Bytes :=
  abiSelectorBytes (selector "transfer" [.address, .uint256]) ++
    receiver.toB256.toBytes ++ assets.toBytes

@[simp] theorem balanceOfCalldata_length (vault : Adr) :
    (balanceOfCalldata vault).length = 36 := by
  simp [balanceOfCalldata, abiSelectorBytes_length, B256.length_toBytes]

@[simp] theorem transferFromCalldata_length
    (owner vault : Adr) (assets : B256) :
    (transferFromCalldata owner vault assets).length = 100 := by
  simp [transferFromCalldata, abiSelectorBytes_length,
    B256.length_toBytes]

@[simp] theorem transferCalldata_length (receiver : Adr) (assets : B256) :
    (transferCalldata receiver assets).length = 68 := by
  simp [transferCalldata, abiSelectorBytes_length, B256.length_toBytes]

/-- Selector and argument facts for the canonical asset query. -/
theorem balanceOfCalldata_facts {sevm : Sevm} {vault : Adr}
    (hdata : sevm.data = balanceOfCalldata vault) :
    Sevm.selector sevm = selector "balanceOf" [.address] ∧
      Sevm.dataWord sevm 4 = vault.toB256 := by
  constructor
  · apply selector_eq_of_data_eq_abiSelectorBytes_append
      (selected := selector "balanceOf" [.address])
      (tail := vault.toB256.toBytes)
    · have hsel : selector "balanceOf" [.address] =
          (0x70a08231 : B256) := by decide +kernel
      rw [hsel]
      rfl
    · simpa [balanceOfCalldata] using hdata
  · apply dataWord_of_append
      (pre := abiSelectorBytes (selector "balanceOf" [.address]))
      (post := [])
    · rw [abiSelectorBytes_length]
      rfl
    · simpa [balanceOfCalldata] using hdata

/-- Selector and all three raw ABI words of the canonical delegated transfer. -/
theorem transferFromCalldata_facts
    {sevm : Sevm} {owner vault : Adr} {assets : B256}
    (hdata : sevm.data = transferFromCalldata owner vault assets) :
    Sevm.selector sevm =
        selector "transferFrom" [.address, .address, .uint256] ∧
      Sevm.dataWord sevm 4 = owner.toB256 ∧
      Sevm.dataWord sevm 36 = vault.toB256 ∧
      Sevm.dataWord sevm 68 = assets := by
  have dataShape : sevm.data =
      abiSelectorBytes
          (selector "transferFrom" [.address, .address, .uint256]) ++
        (owner.toB256.toBytes ++
          (vault.toB256.toBytes ++ assets.toBytes)) := by
    simpa [transferFromCalldata, List.append_assoc] using hdata
  constructor
  · apply selector_eq_of_data_eq_abiSelectorBytes_append
      (selected :=
        selector "transferFrom" [.address, .address, .uint256])
      (tail := owner.toB256.toBytes ++
        vault.toB256.toBytes ++ assets.toBytes)
    · have hsel :
          selector "transferFrom" [.address, .address, .uint256] =
            (0x23b872dd : B256) := by decide +kernel
      rw [hsel]
      rfl
    · simpa [List.append_assoc] using dataShape
  · constructor
    · apply dataWord_of_append
        (pre := abiSelectorBytes
          (selector "transferFrom" [.address, .address, .uint256]))
        (post := vault.toB256.toBytes ++ assets.toBytes)
      · rw [abiSelectorBytes_length]
        rfl
      · exact dataShape
    · constructor
      · refine dataWord_of_append
          (idx := (36 : B256))
          (pre := abiSelectorBytes
              (selector "transferFrom" [.address, .address, .uint256]) ++
            owner.toB256.toBytes)
          (w := vault.toB256)
          (post := assets.toBytes) ?_ ?_
        · simp [abiSelectorBytes_length, B256.length_toBytes,
            show (36 : B256).toNat = 36 by decide +kernel]
        · simpa [List.append_assoc] using dataShape
      · refine dataWord_of_append
          (idx := (68 : B256))
          (pre := abiSelectorBytes
              (selector "transferFrom" [.address, .address, .uint256]) ++
            owner.toB256.toBytes ++ vault.toB256.toBytes)
          (w := assets)
          (post := []) ?_ ?_
        · simp [abiSelectorBytes_length, B256.length_toBytes,
            show (68 : B256).toNat = 68 by decide +kernel]
        · simpa [List.append_assoc] using dataShape

/-- Selector and both raw ABI words of the canonical outbound transfer. -/
theorem transferCalldata_facts
    {sevm : Sevm} {receiver : Adr} {assets : B256}
    (hdata : sevm.data = transferCalldata receiver assets) :
    Sevm.selector sevm = selector "transfer" [.address, .uint256] ∧
      Sevm.dataWord sevm 4 = receiver.toB256 ∧
      Sevm.dataWord sevm 36 = assets := by
  have dataShape : sevm.data =
      abiSelectorBytes (selector "transfer" [.address, .uint256]) ++
        (receiver.toB256.toBytes ++ assets.toBytes) := by
    simpa [transferCalldata, List.append_assoc] using hdata
  constructor
  · apply selector_eq_of_data_eq_abiSelectorBytes_append
      (selected := selector "transfer" [.address, .uint256])
      (tail := receiver.toB256.toBytes ++ assets.toBytes)
    · have hsel : selector "transfer" [.address, .uint256] =
          (0xa9059cbb : B256) := by decide +kernel
      rw [hsel]
      rfl
    · exact dataShape
  · constructor
    · apply dataWord_of_append
        (pre := abiSelectorBytes
          (selector "transfer" [.address, .uint256]))
        (post := assets.toBytes)
      · rw [abiSelectorBytes_length]
        rfl
      · exact dataShape
    · refine dataWord_of_append
        (idx := (36 : B256))
        (pre := abiSelectorBytes
            (selector "transfer" [.address, .uint256]) ++
          receiver.toB256.toBytes)
        (w := assets)
        (post := []) ?_ ?_
      · simp [abiSelectorBytes_length, B256.length_toBytes,
          show (36 : B256).toNat = 36 by decide +kernel]
      · simpa [List.append_assoc] using dataShape

/-! ## Actual child occurrences -/

/-- One exact retained WETH child, tied to the parent instruction that spawned
it and the child execution slot that the same compiled step consumed.

This structure is a conclusion of the boundary adapters below.  In particular,
`executes` is not supplied by a caller as a token-behaviour hypothesis: it is
derived from the direct code, non-precompile and retained `ProcessMessage`
facts of the actual step. -/
def ExactWethChildExecution
    (sevm : Sevm) (pre post : Devm) (instruction : Ninst)
    (calldata : Bytes) (static : Bool) (result : Devm → Prop) : Prop :=
  ∃ (msg : Msg) (xl : Xlot) (child : Devm)
      (pc nextPc : Nat) (resume : Resume),
    ExactTargetCall sevm.currentTarget wethAccount calldata static msg ∧
    MessageExecutesProgram msg xl Blanc.weth ∧
    msg.benv.state = pre.state ∧
    msg.benv.stat.rules = sevm.benvStat.rules ∧
    Ninst.step ⟨pc, sevm, pre⟩ instruction =
      .spawn (Jaune.Frame.ofCall msg) resume nextPc ∧
    Xlot.Filled xl ∧
    ProcessMessage msg xl (.ok child) ∧
    Ninst.StepRun pc sevm pre instruction xl (.ok post) ∧
    post.state = child.state ∧
    post.returnData = child.output ∧
    ∃ tail, post.stack =
      (if child.error.isSome then (0 : B256) else 1) :: tail ∧
    result child

/-- The unrefined occurrence: the child may have succeeded or rolled back. -/
def ExactWethChildOccurrence
    (sevm : Sevm) (pre post : Devm) (instruction : Ninst)
    (calldata : Bytes) (static : Bool) : Prop :=
  ExactWethChildExecution sevm pre post instruction calldata static
    (fun _ => True)

/-- A clean occurrence with one exact child output. -/
def ExactWethChildSuccess
    (sevm : Sevm) (pre post : Devm) (instruction : Ninst)
    (calldata output : Bytes) (static : Bool) : Prop :=
  ExactWethChildExecution sevm pre post instruction calldata static
    (fun child => child.error = none ∧ child.output = output)

/-- The raw status word and returndata of the actual CALL refine its retained
child, without introducing a semantic success token. -/
theorem ExactWethChildOccurrence.success_of_post
    {sevm : Sevm} {pre post : Devm} {instruction : Ninst}
    {calldata output : Bytes} {static : Bool}
    (occurrence : ExactWethChildOccurrence sevm pre post instruction
      calldata static)
    (successFlag : ∃ tail, post.stack = (1 : B256) :: tail)
    (returnData : post.returnData = output) :
    ExactWethChildSuccess sevm pre post instruction calldata output static := by
  unfold ExactWethChildOccurrence ExactWethChildExecution at occurrence
  rcases occurrence with ⟨msg, xl, child, pc, nextPc, resume,
    target, executes, childWorld, childRules, spawn, filled, process, stepRun,
    state, childOutput, actualTail, actualStack, -⟩
  obtain ⟨expectedTail, expectedStack⟩ := successFlag
  have headEq : (if child.error.isSome then (0 : B256) else 1) = 1 := by
    have listEq := actualStack.symm.trans expectedStack
    injection listEq with headEq
  have errorSomeFalse : child.error.isSome = false := by
    by_cases h : child.error.isSome = true
    · simp only [h, if_pos] at headEq
      exact (B256.zero_ne_one headEq).elim
    · exact Bool.eq_false_of_not_eq_true h
  have errorNone : child.error = none := by
    cases herror : child.error with
    | none => rfl
    | some error =>
        simp only [herror, Option.isSome_some] at errorSomeFalse
        cases errorSomeFalse
  refine ⟨msg, xl, child, pc, nextPc, resume, target, executes, childWorld,
    childRules, spawn, filled, process, stepRun, state, childOutput, actualTail,
    actualStack, errorNone, ?_⟩
  rw [← childOutput]
  exact returnData

/-- A status-zero result from the actual retained child is an error settlement,
so the child and the caught parent step both expose the call-entry world.  This
is frame-relative rollback: parent work performed before the CALL remains in
`pre`, while no partial WETH write escapes the failed child. -/
theorem ExactWethChildOccurrence.rollback_of_post
    {sevm : Sevm} {pre post : Devm} {instruction : Ninst}
    {calldata : Bytes} {static : Bool}
    (occurrence : ExactWethChildOccurrence sevm pre post instruction
      calldata static)
    (failureFlag : ∃ tail, post.stack = (0 : B256) :: tail) :
    post.state = pre.state := by
  unfold ExactWethChildOccurrence ExactWethChildExecution at occurrence
  rcases occurrence with ⟨msg, xl, child, pc, nextPc, resume,
    target, executes, childWorld, childRules, spawn, filled, process, stepRun,
    postState, postReturnData, actualTail, actualStack, -⟩
  obtain ⟨failureTail, failureStack⟩ := failureFlag
  have headEq :
      (if child.error.isSome then (0 : B256) else 1) = 0 := by
    have stackEq := actualStack.symm.trans failureStack
    injection stackEq with headEq
  have childError : child.error.isSome := by
    by_cases childError : child.error.isSome
    · exact childError
    · rw [if_neg childError] at headEq
      exact (B256.zero_ne_one headEq.symm).elim
  have rollback := ProcessMessage.rollback_of_error process childError
  exact postState.trans (rollback.1.trans childWorld)

private theorem wethCode_nonempty : Blanc.wethCode ≠ [] := by
  decide +kernel

/-- An actual non-precompile spawn from the configured account carries a
retained execution of the inherited WETH program.

The proof obtains the child's code from the opcode's spawn itself.  Direct
installation is used only to identify those bytes; neither a program-use
token nor a callee effect is accepted as a premise. -/
private theorem spawnedMessage_executes_weth
    {sevm : Sevm} {pre : Devm}
    {msg : Msg} {xl : Xlot} {child : Devm} {resume : Resume} {x : Xinst}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (currentTarget : msg.currentTarget = wethAccount)
    (codeAddress : msg.codeAddress = some wethAccount)
    (valueZero : msg.value = 0)
    (transferValue : msg.shouldTransferValue = true)
    (sameRules : msg.benv.stat.rules = sevm.benvStat.rules)
    (spawn : Xinst.step sevm pre x =
      .spawn (Jaune.Frame.ofCall msg) resume)
    (filled : Xlot.Filled xl)
    (process : ProcessMessage msg xl (.ok child)) :
    MessageExecutesProgram msg xl Blanc.weth := by
  have codeEq : msg.code.toList = Blanc.wethCode := by
    rcases Xinst.step_spawn_source spawn with empty | same | source
    · have empty' : pre.getCode wethAccount = .empty := by
        simpa only [Jaune.Frame.ofCall, currentTarget] using empty
      have impossible : Blanc.wethCode = [] := by
        rw [← config.code]
        simp only [empty', ByteArray.toList_empty]
      exact (wethCode_nonempty impossible).elim
    · have impossible : wethAccount = sevm.currentTarget := by
        simpa only [Jaune.Frame.ofCall, currentTarget] using same
      exact (config.distinct impossible).elim
    · have direct := source (by
        change ¬ isValidDelegation (pre.getCode msg.currentTarget)
        rw [currentTarget]
        exact config.notDelegated)
      have codeBytes : msg.code = pre.getCode wethAccount := by
        simpa only [Jaune.Frame.ofCall, currentTarget] using direct
      exact (congrArg ByteArray.toList codeBytes).trans config.code
  have uses : MessageUsesProgram msg Blanc.weth := by
    unfold MessageUsesProgram
    rw [Blanc.wethCode_compile]
    exact congrArg some codeEq
  have affordable : ¬ msg.benv.state.bal msg.caller < msg.value := by
    rw [valueZero, B256.lt_iff_toNat_lt_toNat]
    exact Nat.not_lt.mpr (Nat.zero_le _)
  obtain ⟨stmid, -, afterTransfer⟩ :=
    Msg.benvAfterTransfer_of_affordable msg transferValue affordable
  let benv := (msg.benv.withState stmid).addBal msg.currentTarget msg.value
  have enter : (Jaune.Frame.ofCall msg).enter =
      .run (initEvm (msg.withBenv benv)) := by
    apply Frame.enter_run_of_nonprecompile afterTransfer
    · exact codeAddress
    · change msg.benv.stat.rules.isPrecomp wethAccount = false
      rw [sameRules]
      exact config.nonprecompile
  unfold ProcessMessage RunFrame at process
  rw [enter] at process
  rcases process with ⟨raw, slotEq, -⟩
  subst xl
  exact ⟨uses, initEvm (msg.withBenv benv), raw, rfl, filled⟩

/-! ## CALL and STATICCALL boundary adapters -/

/-- A successful raw CALL edge with the vault's canonical target and a pinned
input window yields one exact retained WETH occurrence.

The explicit affordability premise is a resource fact about this opcode, not
a callee-behaviour assumption.  It keeps this composition-local adapter on the
existing public forward CALL seam and makes no universal gas claim. -/
theorem exactWethCallOccurrence_of_runCompiled
    {sevm : Sevm} {pre post : Devm}
    {gasWord inputOffset inputSize outputOffset outputSize : B256}
    {rest : List B256} {calldata : Bytes}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (h_stk : pre.stack =
      gasWord :: wethAccount.toB256 :: 0 :: inputOffset :: inputSize ::
        outputOffset :: outputSize :: rest)
    (h_window :
      (pre.memory.read inputOffset.toNat inputSize.toNat).1 = calldata)
    (h_depth : sevm.depth ≠ 0)
    (h_dynamic : sevm.isStatic = false)
    (h_gas :
      let base := addAccessedAddress
        (pre.setMach ⟨rest, pre.memory, pre.gasLeft⟩) wethAccount
      let ext := (pre.setMach ⟨rest, pre.memory, pre.gasLeft⟩).extCost
        [⟨inputOffset.toNat, inputSize.toNat⟩,
          ⟨outputOffset.toNat, outputSize.toNat⟩]
      let acc := accessCost wethAccount
        (pre.setMach ⟨rest, pre.memory, pre.gasLeft⟩).accessedAddresses
      (calculateMsgCallGas 0 gasWord.toNat base.gasLeft ext acc).1 + ext ≤
        base.gasLeft)
    (run : Ninst.RunCompiled sevm pre Ninst.call post) :
    ExactWethChildOccurrence sevm pre post Ninst.call calldata false := by
  obtain ⟨xl, hfill, hrun⟩ := run
  have hx := hrun 0
  rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep] at hx
  have hta : wethAccount.toB256.toAdr = wethAccount := toAdr_toB256 wethAccount
  let popped := pre.setMach ⟨rest, pre.memory, pre.gasLeft⟩
  let base := addAccessedAddress popped wethAccount
  have hcode : base.state.getCode wethAccount = pre.getCode wethAccount := by
    rfl
  have hnone : getDelegatedCodeAddress (pre.getCode wethAccount) = none := by
    unfold getDelegatedCodeAddress
    rw [if_neg config.notDelegated]
  have hdel : accessDelegation base wethAccount =
      ⟨false, wethAccount, pre.getCode wethAccount, 0, base⟩ := by
    simp only [accessDelegation, hcode, hnone]
  let ext := popped.extCost
    [⟨inputOffset.toNat, inputSize.toNat⟩,
      ⟨outputOffset.toNat, outputSize.toNat⟩]
  let acc := accessCost wethAccount popped.accessedAddresses
  rcases hsplit : calculateMsgCallGas 0 gasWord.toNat base.gasLeft ext acc with
    ⟨mcc, mcs⟩
  have hga : mcc + ext ≤ base.gasLeft := by
    simpa only [popped, base, ext, acc, hsplit] using h_gas
  have hdel' : accessDelegation
      (addAccessedAddress
        (pre.setMach ⟨rest, pre.memory, pre.gasLeft⟩)
          wethAccount.toB256.toAdr) wethAccount.toB256.toAdr =
      ⟨false, wethAccount, pre.getCode wethAccount, 0, base⟩ := by
    simpa only [hta, popped, base] using hdel
  obtain ⟨hstep, -, -, -, -, -, -, -⟩ :=
    directCall_zero_spawn h_stk (ext := ext) (acc := acc) (mcc := mcc)
      (mcs := mcs) (d1 := base) (dp := false) (dadr := wethAccount)
      (code := pre.getCode wethAccount) (dgc := 0)
      (by rfl) hdel' (by rfl) hsplit hga h_depth
  rw [hta] at hstep
  let parent := callSpawnParent base (mcc + ext)
    inputOffset.toNat inputSize.toNat outputOffset.toNat outputSize.toNat
  have hpmem : parent.memory = pre.memory.extends
      [⟨inputOffset.toNat, inputSize.toNat⟩,
        ⟨outputOffset.toNat, outputSize.toNat⟩] := by
    rfl
  have hdata : parent.memory.data.sliceD inputOffset.toNat
      inputSize.toNat 0 = calldata := by
    rw [hpmem]
    exact h_window
  have hmsgeq : callSpawnMsg sevm parent mcs wethAccount wethAccount
      inputOffset.toNat inputSize.toNat (pre.getCode wethAccount) false =
      callMsg sevm parent mcs 0 sevm.currentTarget wethAccount wethAccount
        true false calldata (pre.getCode wethAccount) false := by
    show callMsg sevm parent mcs 0 sevm.currentTarget wethAccount wethAccount
      true false
      (parent.memory.data.sliceD inputOffset.toNat inputSize.toNat 0)
      (pre.getCode wethAccount) false = _
    rw [hdata]
  rw [hstep] at hx
  obtain ⟨r, hframe, hres⟩ := hx
  rcases r with ⟨e, st, ca, tra⟩ | child
  · rw [Resume.run_call_fatal] at hres
    cases hres
  rw [hmsgeq] at hframe
  have hres' :
      (Resume.call parent outputOffset.toNat outputSize.toNat).run
        (.ok child) = .ok post := hres.symm
  let msg := callMsg sevm parent mcs 0 sevm.currentTarget wethAccount
    wethAccount true false calldata (pre.getCode wethAccount) false
  have hxspawn : Xinst.step sevm pre .call =
      .spawn (Jaune.Frame.ofCall msg)
        (.call parent outputOffset.toNat outputSize.toNat) := by
    rw [hstep, hmsgeq]
  have executes : MessageExecutesProgram msg xl Blanc.weth := by
    apply spawnedMessage_executes_weth config (msg := msg) (child := child)
      (resume := .call parent outputOffset.toNat outputSize.toNat)
      (x := .call)
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact hxspawn
    · exact hfill
    · exact hframe
  have hspawn : Ninst.step ⟨0, sevm, pre⟩ Ninst.call =
      .spawn (Jaune.Frame.ofCall msg)
        (.call parent outputOffset.toNat outputSize.toNat) 1 := by
    simp only [Ninst.call, Ninst.step_exec]
    change XStep.toStep 1 (Xinst.step sevm pre .call) = _
    rw [hxspawn]
    rfl
  refine ⟨msg, xl, child, 0, 1,
    .call parent outputOffset.toNat outputSize.toNat, ?_, executes, rfl, rfl,
    hspawn, hfill, hframe, hrun 0, Resume.call_state hres',
    Resume.call_returnData hres', parent.stack,
    Resume.call_stack_flag hres', trivial⟩
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
  show sevm.isStatic = false
  exact h_dynamic

/-- The STATICCALL sibling used by `totalAssets`: the exact input window is
read by an actual retained child whose code is the configured WETH runtime. -/
theorem exactWethStatcallOccurrence_of_runCompiled
    {sevm : Sevm} {pre post : Devm}
    {gasWord inputOffset inputSize outputOffset outputSize : B256}
    {rest : List B256} {calldata : Bytes}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (h_stk : pre.stack =
      gasWord :: wethAccount.toB256 :: inputOffset :: inputSize ::
        outputOffset :: outputSize :: rest)
    (h_window :
      (pre.memory.read inputOffset.toNat inputSize.toNat).1 = calldata)
    (h_depth : sevm.depth ≠ 0)
    (h_gas :
      let base := addAccessedAddress
        (pre.setMach ⟨rest, pre.memory, pre.gasLeft⟩) wethAccount
      let ext := (pre.setMach ⟨rest, pre.memory, pre.gasLeft⟩).extCost
        [⟨inputOffset.toNat, inputSize.toNat⟩,
          ⟨outputOffset.toNat, outputSize.toNat⟩]
      let acc := accessCost wethAccount
        (pre.setMach ⟨rest, pre.memory, pre.gasLeft⟩).accessedAddresses
      (calculateMsgCallGas 0 gasWord.toNat base.gasLeft ext acc).1 + ext ≤
        base.gasLeft)
    (run : Ninst.RunCompiled sevm pre Ninst.statcall post) :
    ExactWethChildOccurrence sevm pre post Ninst.statcall calldata true := by
  obtain ⟨xl, hfill, hrun⟩ := run
  have hx := hrun 0
  rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep] at hx
  have hta : wethAccount.toB256.toAdr = wethAccount := toAdr_toB256 wethAccount
  let popped := pre.setMach ⟨rest, pre.memory, pre.gasLeft⟩
  let base := addAccessedAddress popped wethAccount
  have hcode : base.state.getCode wethAccount = pre.getCode wethAccount := by
    rfl
  have hnone : getDelegatedCodeAddress (pre.getCode wethAccount) = none := by
    unfold getDelegatedCodeAddress
    rw [if_neg config.notDelegated]
  have hdel : accessDelegation base wethAccount =
      ⟨false, wethAccount, pre.getCode wethAccount, 0, base⟩ := by
    simp only [accessDelegation, hcode, hnone]
  let ext := popped.extCost
    [⟨inputOffset.toNat, inputSize.toNat⟩,
      ⟨outputOffset.toNat, outputSize.toNat⟩]
  let acc := accessCost wethAccount popped.accessedAddresses
  rcases hsplit : calculateMsgCallGas 0 gasWord.toNat base.gasLeft ext acc with
    ⟨mcc, mcs⟩
  have hga : mcc + ext ≤ base.gasLeft := by
    simpa only [popped, base, ext, acc, hsplit] using h_gas
  have hdel' : accessDelegation
      (addAccessedAddress
        (pre.setMach ⟨rest, pre.memory, pre.gasLeft⟩)
          wethAccount.toB256.toAdr) wethAccount.toB256.toAdr =
      ⟨false, wethAccount, pre.getCode wethAccount, 0, base⟩ := by
    simpa only [hta, popped, base] using hdel
  obtain ⟨hstep, -, -, -, -, -, -, -⟩ :=
    directStatcall_spawn h_stk (ext := ext) (acc := acc) (mcc := mcc)
      (mcs := mcs) (d1 := base) (dp := false) (dadr := wethAccount)
      (code := pre.getCode wethAccount) (dgc := 0)
      (by rfl) hdel' (by rfl) hsplit hga h_depth
  rw [hta] at hstep
  let parent := callSpawnParent base (mcc + ext)
    inputOffset.toNat inputSize.toNat outputOffset.toNat outputSize.toNat
  have hpmem : parent.memory = pre.memory.extends
      [⟨inputOffset.toNat, inputSize.toNat⟩,
        ⟨outputOffset.toNat, outputSize.toNat⟩] := by
    rfl
  have hdata : parent.memory.data.sliceD inputOffset.toNat
      inputSize.toNat 0 = calldata := by
    rw [hpmem]
    exact h_window
  have hmsgeq : statcallSpawnMsg sevm parent mcs wethAccount wethAccount
      inputOffset.toNat inputSize.toNat (pre.getCode wethAccount) false =
      callMsg sevm parent mcs 0 sevm.currentTarget wethAccount wethAccount
        true true calldata (pre.getCode wethAccount) false := by
    show callMsg sevm parent mcs 0 sevm.currentTarget wethAccount wethAccount
      true true
      (parent.memory.data.sliceD inputOffset.toNat inputSize.toNat 0)
      (pre.getCode wethAccount) false = _
    rw [hdata]
  rw [hstep] at hx
  obtain ⟨r, hframe, hres⟩ := hx
  rcases r with ⟨e, st, ca, tra⟩ | child
  · rw [Resume.run_call_fatal] at hres
    cases hres
  rw [hmsgeq] at hframe
  have hres' :
      (Resume.call parent outputOffset.toNat outputSize.toNat).run
        (.ok child) = .ok post := hres.symm
  let msg := callMsg sevm parent mcs 0 sevm.currentTarget wethAccount
    wethAccount true true calldata (pre.getCode wethAccount) false
  have hxspawn : Xinst.step sevm pre .statcall =
      .spawn (Jaune.Frame.ofCall msg)
        (.call parent outputOffset.toNat outputSize.toNat) := by
    rw [hstep, hmsgeq]
  have executes : MessageExecutesProgram msg xl Blanc.weth := by
    apply spawnedMessage_executes_weth config (msg := msg) (child := child)
      (resume := .call parent outputOffset.toNat outputSize.toNat)
      (x := .statcall)
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact hxspawn
    · exact hfill
    · exact hframe
  have hspawn : Ninst.step ⟨0, sevm, pre⟩ Ninst.statcall =
      .spawn (Jaune.Frame.ofCall msg)
        (.call parent outputOffset.toNat outputSize.toNat) 1 := by
    simp only [Ninst.statcall, Ninst.step_exec]
    change XStep.toStep 1 (Xinst.step sevm pre .statcall) = _
    rw [hxspawn]
    rfl
  refine ⟨msg, xl, child, 0, 1,
    .call parent outputOffset.toNat outputSize.toNat, ?_, executes, rfl, rfl,
    hspawn, hfill, hframe, hrun 0, Resume.call_state hres',
    Resume.call_returnData hres', parent.stack,
    Resume.call_stack_flag hres', trivial⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Selector exclusion at the WETH boundary -/

/-- The three outbound selector words the vault is allowed to stage. -/
def allowedWethSelectors : List B256 :=
  [ selector "balanceOf" [.address],
    selector "transferFrom" [.address, .address, .uint256],
    selector "transfer" [.address, .uint256] ]

theorem approveSelector_not_allowed :
    selector "approve" [.address, .uint256] ∉ allowedWethSelectors := by
  decide +kernel

theorem withdrawSelector_not_allowed :
    selector "withdraw" [.uint256] ∉ allowedWethSelectors := by
  decide +kernel

end Blanc.Composition.ProrataWethVault
