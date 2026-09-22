-- ProrataWethVaultRevertSteps.lean : the vault's revert-cause vocabulary and
-- the revert-aware entry, guard and WETH-child adapters the nonrevert cores use.

import Blanc.RevertCause
import Blanc.ProrataWethVaultArithmeticRevert
import Blanc.Composition.ProrataWethVaultStaging

namespace Blanc.Composition.ProrataWethVault

open Jaune
open Jaune.Ninst Ninst
open Source

/-- A compiled step that is a `CALL` or `STATICCALL` to the configured WETH
account whose pushed status word is zero: the child reverted or halted, or the
call was refused at the call-depth limit.  Nothing else about the child is
assumed, and nothing about the parent is concluded here. -/
def WethChildRefused (_sevm : Sevm) (callPre : Devm) (instruction : Ninst)
    (callPost : Devm) : Prop :=
  (instruction = Ninst.call ∨ instruction = Ninst.staticcall) ∧
    callPre.stack[1]? = some wethAccount.toB256 ∧
    callPost.stack.head? = some (0 : B256)

/-! ## Entry and guards along an avoiding walk

The vault's selector entry, its two endpoint wrappers and its canonical
address guard, each passed on the strength of the headline's own premise
rather than of a successful outcome. -/

section

variable {P : Sevm → Devm → Ninst → Devm → Prop}
  {fs : List Func} {sevm : Sevm}

/-- The static-head guard passes when the calldata covers the head. -/
theorem requireStaticArgs_avoiding {pre : Devm} {out : Execution}
    {words : Nat} {body : Func}
    (argsPresent : B256.ltCheck sevm.data.length.toB256
      (Nat.toB256 (4 + 32 * words)) = 0)
    (run : Func.RunCompiledToAvoiding P fs sevm pre
      (Blanc.ProrataWethVault.requireStaticArgs words body) out) :
    ∃ bodyPre,
      pre.state = bodyPre.state ∧ pre.memory = bodyPre.memory ∧
      Func.RunCompiledToAvoiding P fs sevm bodyPre body out := by
  unfold Blanc.ProrataWethVault.requireStaticArgs at run
  change Func.RunCompiledToAvoiding P fs sevm pre
    ([pushB256 (Nat.toB256 (4 + 32 * words)), calldatasize, lt] +++
      (Func.revert <?> body)) out at run
  obtain ⟨testPre, testRun, branchRun⟩ :=
    Func.RunCompiledToAvoiding.prepend_inv run
  rcases Line.of_run_cons testRun with ⟨afterWord, qword, rest⟩
  rcases Line.of_run_cons rest with ⟨afterSize, qsize, rest⟩
  rcases Line.of_run_cons rest with ⟨afterTest, qlt, hnil⟩
  cases hnil
  have p1 : [Nat.toB256 (4 + 32 * words)] <<+ afterWord.stack :=
    prefix_of_push (of_run_pushB256 qword) nil_pref
  have p2 : [sevm.data.length.toB256,
      Nat.toB256 (4 + 32 * words)] <<+ afterSize.stack :=
    prefix_of_push (of_run_calldatasize qsize) p1
  have p3 : (0 : B256) :: [] <<+ testPre.stack := by
    have compared := prefix_of_lt qlt p2
    rw [argsPresent] at compared
    exact compared
  obtain ⟨bodyPre, hpop, bodyRun, -⟩ :=
    Func.RunCompiledToAvoiding.zero_branch_of_prefix p3 branchRun
  have hpop' := Devm.PopBurn.of_popBurnBy hpop
  have line := Line.Run.cons qword (Line.Run.cons qsize
    (Line.Run.cons qlt Line.Run.nil))
  exact ⟨bodyPre,
    (Line.of_inv Devm.state (by line_inv) line).trans hpop'.state,
    (Line.of_inv Devm.memory (by line_inv) line).trans hpop'.memory, bodyRun⟩

/-- The canonical-address guard passes on a canonical argument word. -/
theorem canonicalAddressArg_avoiding {pre : Devm} {out : Execution}
    {index : B256} {body : Func} {tail : Stack}
    (argValid : ValidAdr (Sevm.argWord sevm index))
    (hp : tail <<+ pre.stack)
    (run : Func.RunCompiledToAvoiding P fs sevm pre
      (Blanc.ProrataWethVault.canonicalAddressArg index body) out) :
    ∃ bodyPre,
      tail <<+ bodyPre.stack ∧
      pre.state = bodyPre.state ∧ pre.memory = bodyPre.memory ∧
      Func.RunCompiledToAvoiding P fs sevm bodyPre body out := by
  unfold Blanc.ProrataWethVault.canonicalAddressArg at run
  obtain ⟨afterArg, argLine, run⟩ :=
    Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨guardPost, guardLine, branchRun⟩ :=
    Func.RunCompiledToAvoiding.prepend_inv run
  have argPrefix : Sevm.argWord sevm index :: tail <<+ afterArg.stack :=
    prefix_of_arg hp argLine
  obtain ⟨guardWord, guardPrefix, guardValid⟩ :=
    of_check_non_address argPrefix guardLine
  have zeroPrefix : (0 : B256) :: tail <<+ guardPost.stack := by
    rw [← guardValid.mpr argValid]
    exact guardPrefix
  obtain ⟨bodyPre, hpop, bodyRun, bodyPrefix⟩ :=
    Func.RunCompiledToAvoiding.zero_branch_of_prefix zeroPrefix branchRun
  have hpop' := Devm.PopBurn.of_popBurnBy hpop
  exact ⟨bodyPre, bodyPrefix,
    (Line.of_inv Devm.state (by line_inv) argLine).trans
      ((Line.of_inv Devm.state (by line_inv) guardLine).trans hpop'.state),
    (Line.of_inv Devm.memory (by line_inv) argLine).trans
      ((Line.of_inv Devm.memory (by line_inv) guardLine).trans
        hpop'.memory),
    bodyRun⟩

end

/-- **Vault entry along an avoiding walk.**  With the selector of a routed
endpoint, zero call value and a covering static head, an avoiding walk of the
vault's main function reaches the endpoint body with the entry state and
memory. -/
theorem vault_endpoint_avoiding
    {P : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {entry : Devm}
    {out : Execution} {sig : B256} {words : Nat} {body : Func}
    (selectorEq : Sevm.selector sevm = sig)
    (member : (sig, Blanc.ProrataWethVault.routed words body) ∈
      Blanc.ProrataWethVault.vaultFuncs)
    (valueZero : sevm.value = 0)
    (argsPresent : B256.ltCheck sevm.data.length.toB256
      (Nat.toB256 (4 + 32 * words)) = 0)
    (run : Func.RunCompiledToAvoiding P
      (Blanc.ProrataWethVault.vault.main :: Blanc.ProrataWethVault.vault.aux)
      sevm entry Blanc.ProrataWethVault.vault.main out) :
    ∃ bodyPre,
      entry.state = bodyPre.state ∧ entry.memory = bodyPre.memory ∧
      Func.RunCompiledToAvoiding P
        (Blanc.ProrataWethVault.vault.main :: Blanc.ProrataWethVault.vault.aux)
        sevm bodyPre body out := by
  change Func.RunCompiledToAvoiding P _ sevm entry
    (fsig +++ dispatchWith Blanc.ProrataWethVault.revertSlot
      Blanc.ProrataWethVault.vaultTree) out at run
  obtain ⟨dispatchPre, fsigRun, dispatchRun⟩ :=
    Func.RunCompiledToAvoiding.prepend_inv run
  have selectorPrefix : sig :: [] <<+ dispatchPre.stack := by
    rw [← selectorEq]
    exact prefix_of_fsig nil_pref fsigRun
  obtain ⟨endpointPre, -, dispatchState, dispatchMemory, endpointRun⟩ :=
    Func.RunCompiledToAvoiding.reach_of_dispatchWith
      Blanc.ProrataWethVault.vaultFuncs_sorted member selectorPrefix
      dispatchRun
  change Func.RunCompiledToAvoiding P _ sevm endpointPre
    (nonpayable (Blanc.ProrataWethVault.requireStaticArgs words body)) out
    at endpointRun
  obtain ⟨staticPre, staticRun, -, wrapperState, wrapperMemory⟩ :=
    Func.RunCompiledToAvoiding.nonpayable_body_of_value_zero valueZero
      nil_pref endpointRun
  obtain ⟨bodyPre, staticState, staticMemory, bodyRun⟩ :=
    requireStaticArgs_avoiding argsPresent staticRun
  exact ⟨bodyPre,
    (Line.of_inv Devm.state (by line_inv) fsigRun).trans
      (dispatchState.trans (wrapperState.trans staticState)),
    (Line.of_inv Devm.memory (by line_inv) fsigRun).trans
      (dispatchMemory.trans (wrapperMemory.trans staticMemory)),
    bodyRun⟩

/-- **Program entry.**  A reverting program walk of the vault visits a
refused WETH child as soon as every avoiding walk of the selected endpoint
body is impossible. -/
theorem vault_revert_visits_of_body
    {sevm : Sevm} {pre d : Devm} {sig : B256} {words : Nat} {body : Func}
    (selectorEq : Sevm.selector sevm = sig)
    (member : (sig, Blanc.ProrataWethVault.routed words body) ∈
      Blanc.ProrataWethVault.vaultFuncs)
    (valueZero : sevm.value = 0)
    (argsPresent : B256.ltCheck sevm.data.length.toB256
      (Nat.toB256 (4 + 32 * words)) = 0)
    (walk : Prog.RunCompiledTo sevm pre Blanc.ProrataWethVault.vault
      (.error (.revert, d)))
    (impossible : ∀ bodyPre, pre.state = bodyPre.state →
      pre.memory = bodyPre.memory →
      Func.RunCompiledToAvoiding WethChildRefused
        (Blanc.ProrataWethVault.vault.main :: Blanc.ProrataWethVault.vault.aux)
        sevm bodyPre body (.error (.revert, d)) → False) :
    Prog.RunCompiledToVisiting WethChildRefused sevm pre
      Blanc.ProrataWethVault.vault (.error (.revert, d)) := by
  refine Prog.RunCompiledToVisiting.of_not_avoiding walk ?_
  intro entry burn run
  obtain ⟨bodyPre, entryState, entryMemory, bodyRun⟩ :=
    vault_endpoint_avoiding selectorEq member valueZero argsPresent run
  have burn' := Devm.Burn.of_burnBy burn
  exact impossible bodyPre (burn'.state.trans entryState)
    (burn'.memory.trans entryMemory) bodyRun

/-! ## The WETH `balanceOf` child along an avoiding walk

A walk that avoids `WethChildRefused` crossed the `STATICCALL` with a nonzero
status word.  The actual child is then the exact configured WETH program, which
returns one 32-byte word, so both of `readTotalAssets`' checks pass and the
walk reaches the continuation with the balance word on the stack. -/

/-- `readTotalAssets` along a walk that visits no refused WETH child: the
continuation is reached with one word on the stack, well-formed memory, and
every operation word at or above byte 64 preserved. -/
theorem readTotalAssets_avoiding {fs : List Func} {sevm : Sevm}
    {entry : Devm} {out : Execution} {body : Func}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf entry.memory)
    (run : Func.RunCompiledToAvoiding WethChildRefused fs sevm entry
      (Blanc.ProrataWethVault.readTotalAssets body) out) :
    ∃ (word : B256) (bodyPre : Devm),
      word :: [] <<+ bodyPre.stack ∧
      Mem.Wf bodyPre.memory ∧
      (∀ {offset : Nat} {w : B256}, 64 ≤ offset →
        MemWordAt entry offset w → MemWordAt bodyPre offset w) ∧
      Func.RunCompiledToAvoiding WethChildRefused fs sevm bodyPre body out := by
  have memory : MemoryImage entry entry.memory.data.toList := by
    refine ⟨memoryWf, ?_⟩
    intro index
    simp
  rw [readTotalAssets_sourceShape] at run
  obtain ⟨callPre, staging, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨callPost, crossing, notRefused, run⟩ :=
    Func.RunCompiledToAvoiding.next_inv run
  obtain ⟨gasWord, rest, stack, -, callPreWf⟩ :=
    balanceOfStaging_boundary memory staging
  have operandPrefix :
      gasWord :: wethAccount.toB256 :: 28 :: 36 :: 0 :: 32 :: rest <<+
        callPre.stack := by
    rw [stack]
    exact ⟨[], by simp [Split]⟩
  have crossingSource := Ninst.Run.of_runCompiled crossing
  -- A status-zero crossing is exactly the refused child this walk avoids.
  have depth : sevm.depth ≠ 0 := by
    rcases of_run_staticcall_val_with_depth operandPrefix crossingSource hfork with
      failure | success
    · obtain ⟨zeroPrefix, -, -⟩ := failure
      exfalso
      apply notRefused
      refine ⟨Or.inr rfl, by rw [stack]; rfl, ?_⟩
      obtain ⟨suffix, zeroStack⟩ := zeroPrefix
      simp only [Split] at zeroStack
      rw [zeroStack]
      rfl
    · obtain ⟨_, _, _, _, _, _, _, positiveDepth, _⟩ := success
      exact Nat.ne_of_gt positiveDepth
  have stagingCode : Devm.getCode entry = Devm.getCode callPre :=
    Line.of_inv Devm.getCode (by
      unfold balanceOfStaging mstoreAt pushList
      simp only [List.map, List.cons_append, List.nil_append]
      line_inv) staging
  have callConfig :
      DirectWethConfiguration sevm.currentTarget sevm callPre := by
    refine ⟨config.distinct, config.nonprecompile, ?_⟩
    rw [← congrFun stagingCode wethAccount]
    exact config.code
  have occurrence := balanceOfStaging_occurrence callConfig hfork memory staging
    depth (staticGasAvailable_of_runCompiled callConfig hfork crossing) crossing
  -- The status word is nonzero, so the retained child succeeded.
  have successFlag : ∃ tail, callPost.stack = (1 : B256) :: tail := by
    have shape := occurrence
    unfold ExactWethChildOccurrence ExactWethChildExecution at shape
    obtain ⟨-, -, child, -, -, -, -, -, -, -, -, -, -, -, -, -, -, statusTail,
      statusStack, -⟩ := shape
    have statusNonzero :
        (if child.error.isSome then (0 : B256) else 1) ≠ 0 := by
      intro statusZero
      apply notRefused
      refine ⟨Or.inr rfl, by rw [stack]; rfl, ?_⟩
      rw [statusStack, statusZero]
      rfl
    exact ExactWethChildOccurrence.successFlag_of_nonzero occurrence
      statusStack statusNonzero
  have success :
      ExactWethChildSuccess sevm callPre callPost staticcall
        (balanceOfCalldata sevm.currentTarget) callPost.returnData true :=
    ExactWethChildOccurrence.success_of_post occurrence successFlag rfl
  obtain ⟨-, -, output⟩ := SuccessfulWethWorldProgramRun.balanceOf_effect
    (ExactWethChildSuccess.worldProgramRun hfork success)
  have returnDataLength : callPost.returnData.length = 32 := by
    rw [output, B256.length_toBytes]
  have callPostWf : Mem.Wf callPost.memory := by
    rcases of_run_staticcall_val_with_depth operandPrefix crossingSource hfork with
      failure | success
    · obtain ⟨zeroPrefix, -, -⟩ := failure
      obtain ⟨tail, oneStack⟩ := successFlag
      have onePrefix : (1 : B256) :: [] <<+ callPost.stack := by
        rw [oneStack]
        exact pref_append [1] tail
      exact (B256.zero_ne_one (pref_head_unique zeroPrefix onePrefix)).elim
    · rcases success with
        ⟨parent, child, _, _, _, _, _, -, -, -, parentMemory, -, -, -, -,
          -, -, -, finalMemory, -⟩
      rw [finalMemory, parentMemory]
      exact (Mem.Wf.extends _ callPreWf).write _ _
  -- The zero-status guard falls through.
  obtain ⟨statusPre, statusZeroRun, -, statusBranch⟩ :=
    Func.RunCompiledToAvoiding.next_inv run
  have statusZeroSource := Ninst.Run.of_runCompiled statusZeroRun
  have statusPrefix : (0 : B256) :: [] <<+ statusPre.stack := by
    obtain ⟨tail, oneStack⟩ := successFlag
    have onePrefix : (1 : B256) :: [] <<+ callPost.stack := by
      rw [oneStack]
      exact pref_append [1] tail
    have oneNonzero : (1 : B256) ≠ 0 := by decide
    simpa [B256.eqCheck, oneNonzero] using
      prefix_of_iszero statusZeroSource onePrefix
  obtain ⟨sizePre, statusPop, sizeRun, -⟩ :=
    Func.RunCompiledToAvoiding.zero_branch_of_prefix statusPrefix statusBranch
  have statusPop' := Devm.PopBurn.of_popBurnBy statusPop
  -- The exact-size guard falls through: the child returned one word.
  obtain ⟨s1, q1, -, sizeRun⟩ := Func.RunCompiledToAvoiding.next_inv sizeRun
  obtain ⟨s2, q2, -, sizeRun⟩ := Func.RunCompiledToAvoiding.next_inv sizeRun
  obtain ⟨s3, q3, -, sizeRun⟩ := Func.RunCompiledToAvoiding.next_inv sizeRun
  obtain ⟨sizeBranchPre, q4, -, sizeBranch⟩ :=
    Func.RunCompiledToAvoiding.next_inv sizeRun
  have r1 := Ninst.Run.of_runCompiled q1
  have r2 := Ninst.Run.of_runCompiled q2
  have r3 := Ninst.Run.of_runCompiled q3
  have r4 := Ninst.Run.of_runCompiled q4
  have push32 := of_run_pushB256 r1
  have returnSize := of_run_returndatasize_val r2
  have statusReturnData : statusPre.returnData = callPost.returnData := by
    obtain ⟨tail, oneStack⟩ := successFlag
    exact (iszero_stack_inv statusZeroRun oneStack).2.2
  have sizeReturnData : s1.returnData = callPost.returnData :=
    push32.returnData.symm.trans
      (statusPop'.returnData.symm.trans statusReturnData)
  have p1 : (32 : B256) :: [] <<+ s1.stack := prefix_of_push push32 nil_pref
  have p2 : s1.returnData.length.toB256 :: 32 :: [] <<+ s2.stack :=
    prefix_of_push returnSize p1
  rw [sizeReturnData, returnDataLength] at p2
  have p3 := prefix_of_eq r3 p2
  have p4 := prefix_of_iszero r4 p3
  have sizeZeroPrefix : (0 : B256) :: [] <<+ sizeBranchPre.stack := by
    have size32 : Nat.toB256 32 = (32 : B256) := by decide +kernel
    have oneNonzero : (1 : B256) ≠ 0 := by decide
    simpa [B256.eqCheck, size32, oneNonzero] using p4
  obtain ⟨decodePre, sizePop, decodeRun, -⟩ :=
    Func.RunCompiledToAvoiding.zero_branch_of_prefix sizeZeroPrefix sizeBranch
  have sizePop' := Devm.PopBurn.of_popBurnBy sizePop
  -- Decode the returned word.
  obtain ⟨mloadPre, q5, -, decodeRun⟩ :=
    Func.RunCompiledToAvoiding.next_inv decodeRun
  obtain ⟨bodyPre, q6, -, bodyRun⟩ :=
    Func.RunCompiledToAvoiding.next_inv decodeRun
  have r5 := Ninst.Run.of_runCompiled q5
  have r6 := Ninst.Run.of_runCompiled q6
  obtain ⟨loadedOffset, loadStack, loadMemory, -⟩ := of_run_mload_val r6
  obtain ⟨loadTail, -, pushed⟩ := loadStack
  have mloadMemory : mloadPre.memory = callPost.memory := by
    rw [← (of_run_pushB256 r5).memory, ← sizePop'.memory,
      ← Ninst.Hinv.inv (f := Devm.memory) r4,
      ← Ninst.Hinv.inv (f := Devm.memory) r3, ← returnSize.memory,
      ← push32.memory, ← statusPop'.memory,
      ← Ninst.Hinv.inv (f := Devm.memory) statusZeroSource]
  refine ⟨_, bodyPre, ⟨loadTail, by simpa [Stack.Push, Split] using pushed⟩, ?_, ?_, bodyRun⟩
  · rw [loadMemory, mloadMemory]
    exact callPostWf.extend _ _
  · intro offset w afterCalldata window
    have callPreWindow := window.acrossBalanceOfStaging afterCalldata staging
    have callPostWindow := callPreWindow.acrossStaticcall
      (by
        change 32 ≤ offset
        omega)
      operandPrefix crossingSource hfork
    apply MemWordAt.extend loadMemory
    exact MemWordAt.of_memory_eq mloadMemory callPostWindow


/-! ## Flow adapters

The pieces the `deposit`/`mint`/`withdraw`/`redeem` walk cores share: the WETH
configuration carried along a walk, the balance read with its exact value, the
successful-child output window, and the vault's staged-word guards passed on
the headline's own premises. -/

/-- The WETH configuration depends only on the installed code, so it travels
to any state that keeps the WETH account's code. -/
theorem DirectWethConfiguration.of_code_eq {sevm : Sevm} {a b : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm a)
    (code : b.getCode wethAccount = a.getCode wethAccount) :
    DirectWethConfiguration sevm.currentTarget sevm b := by
  refine ⟨config.distinct, config.nonprecompile, ?_⟩
  rw [code]
  exact config.code

/-- The WETH configuration survives any single compiled step. -/
theorem DirectWethConfiguration.of_runCompiled {sevm : Sevm} {a b : Devm}
    {n : Ninst}
    (config : DirectWethConfiguration sevm.currentTarget sevm a)
    (run : Ninst.RunCompiled sevm a n b) :
    DirectWethConfiguration sevm.currentTarget sevm b :=
  config.of_code_eq (Ninst.runCompiled_preserves_getCode run (by
    rw [config.code]
    exact wethCode_nonempty))

/-- The WETH configuration survives any state-preserving stretch. -/
theorem DirectWethConfiguration.of_state_eq' {sevm : Sevm} {a b : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm a)
    (state : a.state = b.state) :
    DirectWethConfiguration sevm.currentTarget sevm b :=
  config.of_code_eq (getCode_eq_of_state_eq state wethAccount).symm

/-- A successful STATICCALL whose child returned one word copied it to memory
word zero. -/
theorem staticcallOutputWindow {sevm : Sevm} {pre post : Devm}
    {gasWord target inputSize : B256} {rest : List B256}
    (stack : pre.stack =
      gasWord :: target :: 28 :: inputSize :: 0 :: 32 :: rest)
    (crossing : Ninst.RunCompiled sevm pre staticcall post)
    (hfork : CoveredFork sevm.benvStat.fork)
    (successFlag : ∃ tail, post.stack = (1 : B256) :: tail)
    (returnDataLength : post.returnData.length = 32) :
    (post.memory.read 0 32).1 = post.returnData := by
  have operandPrefix :
      gasWord :: target :: 28 :: inputSize :: 0 :: 32 :: rest <<+
        pre.stack := by
    rw [stack]
    exact ⟨[], by simp [Split]⟩
  rcases of_run_staticcall_val_with_depth operandPrefix
      (Ninst.Run.of_runCompiled crossing) hfork with failure | success
  · obtain ⟨zeroPrefix, -, -⟩ := failure
    obtain ⟨tail, successStack⟩ := successFlag
    have onePrefix : (1 : B256) :: [] <<+ post.stack := by
      rw [successStack]
      exact pref_append [1] tail
    exact (B256.zero_ne_one (pref_head_unique zeroPrefix onePrefix)).elim
  · rcases success with
      ⟨parent, child, _, _, _, _, _, -, -, -, parentMemory, -, -, -, -, -,
        -, childReturnData, finalMemory, -⟩
    have childLength : child.output.length = 32 := by
      rw [← childReturnData]
      exact returnDataLength
    have childNonempty : child.output ≠ [] := by
      intro empty
      rw [empty] at childLength
      cases childLength
    have takeAll : child.output.take (32 : B256).toNat = child.output := by
      apply (List.take_eq_self_iff child.output).2
      rw [show (32 : B256).toNat = 32 from rfl, childLength]
    rw [finalMemory, childReturnData, takeAll]
    change ((parent.memory.write 0 child.output).read 0 32).1 = child.output
    simpa only [childLength] using
      Mem.read_write_zero parent.memory childNonempty

/-- A successful CALL whose child returned one word copied it to memory word
zero. -/
theorem callOutputWindow {sevm : Sevm} {pre post : Devm}
    {gasWord target inputSize : B256} {rest : List B256}
    (stack : pre.stack =
      gasWord :: target :: 0 :: 28 :: inputSize :: 0 :: 32 :: rest)
    (crossing : Ninst.RunCompiled sevm pre call post)
    (hfork : CoveredFork sevm.benvStat.fork)
    (successFlag : ∃ tail, post.stack = (1 : B256) :: tail)
    (returnDataLength : post.returnData.length = 32) :
    (post.memory.read 0 32).1 = post.returnData := by
  have operandPrefix :
      gasWord :: target :: 0 :: 28 :: inputSize :: 0 :: 32 :: rest <<+
        pre.stack := by
    rw [stack]
    exact ⟨[], by simp [Split]⟩
  rcases of_run_call_val_with_depth operandPrefix
      (Ninst.Run.of_runCompiled crossing) hfork with failure | success
  · obtain ⟨zeroPrefix, -⟩ := failure
    obtain ⟨tail, successStack⟩ := successFlag
    have onePrefix : (1 : B256) :: [] <<+ post.stack := by
      rw [successStack]
      exact pref_append [1] tail
    exact (B256.zero_ne_one (pref_head_unique zeroPrefix onePrefix)).elim
  · rcases success with
      ⟨parent, child, _, _, _, _, _, -, -, -, parentMemory, -, -, -, -, -,
        -, childReturnData, finalMemory, -⟩
    have childLength : child.output.length = 32 := by
      rw [← childReturnData]
      exact returnDataLength
    have childNonempty : child.output ≠ [] := by
      intro empty
      rw [empty] at childLength
      cases childLength
    have takeAll : child.output.take (32 : B256).toNat = child.output := by
      apply (List.take_eq_self_iff child.output).2
      rw [show (32 : B256).toNat = 32 from rfl, childLength]
    rw [finalMemory, childReturnData, takeAll]
    change ((parent.memory.write 0 child.output).read 0 32).1 = child.output
    simpa only [childLength] using
      Mem.read_write_zero parent.memory childNonempty

/-- The checked suffix after a WETH crossing whose status word is one and
whose return data is one word: both guards fall through, and the loaded
return word reaches the continuation. -/
theorem checkedWordSuffix_avoiding {fs : List Func} {sevm : Sevm}
    {callPost : Devm} {out : Execution} {body : Func} {tail : Stack}
    {word : B256}
    (statusOne : (1 : B256) :: tail <<+ callPost.stack)
    (returnDataLength : callPost.returnData.length = 32)
    (window : (callPost.memory.read 0 32).1 = word.toBytes)
    (run : Func.RunCompiledToAvoiding WethChildRefused fs sevm callPost
      (iszero :::
        (Func.revert <?>
          (pushB256 32 ::: returndatasize ::: eq ::: iszero :::
            (Func.revert <?> (pushB256 0 ::: mload ::: body))))) out) :
    ∃ bodyPre,
      word :: tail <<+ bodyPre.stack ∧
      bodyPre.state = callPost.state ∧
      bodyPre.memory = callPost.memory.extend 0 32 ∧
      Func.RunCompiledToAvoiding WethChildRefused fs sevm bodyPre body out := by
  obtain ⟨statusPre, statusZeroRun, -, statusBranch⟩ :=
    Func.RunCompiledToAvoiding.next_inv run
  have statusZeroSource := Ninst.Run.of_runCompiled statusZeroRun
  have statusPrefix : (0 : B256) :: tail <<+ statusPre.stack := by
    have oneNonzero : (1 : B256) ≠ 0 := by decide
    simpa [B256.eqCheck, oneNonzero] using
      prefix_of_iszero statusZeroSource statusOne
  obtain ⟨sizePre, statusPop, sizeRun, sizeTail⟩ :=
    Func.RunCompiledToAvoiding.zero_branch_of_prefix statusPrefix statusBranch
  have statusPop' := Devm.PopBurn.of_popBurnBy statusPop
  obtain ⟨s1, q1, -, sizeRun⟩ := Func.RunCompiledToAvoiding.next_inv sizeRun
  obtain ⟨s2, q2, -, sizeRun⟩ := Func.RunCompiledToAvoiding.next_inv sizeRun
  obtain ⟨s3, q3, -, sizeRun⟩ := Func.RunCompiledToAvoiding.next_inv sizeRun
  obtain ⟨sizeBranchPre, q4, -, sizeBranch⟩ :=
    Func.RunCompiledToAvoiding.next_inv sizeRun
  have r1 := Ninst.Run.of_runCompiled q1
  have r2 := Ninst.Run.of_runCompiled q2
  have r3 := Ninst.Run.of_runCompiled q3
  have r4 := Ninst.Run.of_runCompiled q4
  have push32 := of_run_pushB256 r1
  have returnSize := of_run_returndatasize_val r2
  have statusReturnData : statusPre.returnData = callPost.returnData := by
    obtain ⟨t, ht⟩ := statusOne
    simp only [Split] at ht
    exact (iszero_stack_inv statusZeroRun (ht.trans (List.cons_append ..))).2.2
  have sizeReturnData : s1.returnData = callPost.returnData :=
    push32.returnData.symm.trans
      (statusPop'.returnData.symm.trans statusReturnData)
  have p1 : (32 : B256) :: tail <<+ s1.stack := prefix_of_push push32 sizeTail
  have p2 : s1.returnData.length.toB256 :: 32 :: tail <<+ s2.stack :=
    prefix_of_push returnSize p1
  rw [sizeReturnData, returnDataLength] at p2
  have p4 := prefix_of_iszero r4 (prefix_of_eq r3 p2)
  have sizeZeroPrefix : (0 : B256) :: tail <<+ sizeBranchPre.stack := by
    have size32 : Nat.toB256 32 = (32 : B256) := by decide +kernel
    have oneNonzero : (1 : B256) ≠ 0 := by decide
    simpa [B256.eqCheck, size32, oneNonzero] using p4
  obtain ⟨decodePre, sizePop, decodeRun, decodeTail⟩ :=
    Func.RunCompiledToAvoiding.zero_branch_of_prefix sizeZeroPrefix sizeBranch
  have sizePop' := Devm.PopBurn.of_popBurnBy sizePop
  obtain ⟨mloadPre, q5, -, decodeRun⟩ :=
    Func.RunCompiledToAvoiding.next_inv decodeRun
  obtain ⟨bodyPre, q6, -, bodyRun⟩ :=
    Func.RunCompiledToAvoiding.next_inv decodeRun
  have r5 := Ninst.Run.of_runCompiled q5
  have r6 := Ninst.Run.of_runCompiled q6
  have mloadMemory : mloadPre.memory = callPost.memory := by
    rw [← (of_run_pushB256 r5).memory, ← sizePop'.memory,
      ← Ninst.Hinv.inv (f := Devm.memory) r4,
      ← Ninst.Hinv.inv (f := Devm.memory) r3, ← returnSize.memory,
      ← push32.memory, ← statusPop'.memory,
      ← Ninst.Hinv.inv (f := Devm.memory) statusZeroSource]
  have mloadState : callPost.state = mloadPre.state := by
    rw [← (of_run_pushB256 r5).state, ← sizePop'.state,
      ← Ninst.Hinv.inv (f := Devm.state) r4,
      ← Ninst.Hinv.inv (f := Devm.state) r3, ← returnSize.state,
      ← push32.state, ← statusPop'.state,
      ← Ninst.Hinv.inv (f := Devm.state) statusZeroSource]
  have selfReads : Mem.Reads mloadPre.memory mloadPre.memory.data.toList := by
    intro index
    simp
  obtain ⟨loaded, loadMemory, -⟩ :=
    prefix_of_mload_val r6 (prefix_of_push (of_run_pushB256 r5) decodeTail)
      selfReads
  have loadedWord : Bytes.toB256
      (mloadPre.memory.data.toList.sliceD (0 : B256).toNat 32 0) = word := by
    rw [← Mem.Reads.read selfReads, mloadMemory,
      show (0 : B256).toNat = 0 from rfl, window, B256.toB256_toBytes]
  refine ⟨bodyPre, ?_, ?_, ?_, bodyRun⟩
  · rw [loadedWord] at loaded
    exact loaded
  · exact (Ninst.Hinv.inv (f := Devm.state) r6).symm.trans mloadState.symm
  · rw [loadMemory, mloadMemory]
    rfl

/-- `readTotalAssets` along a walk that visits no refused WETH child, with the
word it hands on: the configured vault's WETH balance at entry.  Every storage
row and the WETH configuration survive, and so does every operation word at
or above byte 64. -/
theorem readTotalAssets_exact_avoiding {fs : List Func} {sevm : Sevm}
    {entry : Devm} {out : Execution} {body : Func}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf entry.memory)
    (run : Func.RunCompiledToAvoiding WethChildRefused fs sevm entry
      (Blanc.ProrataWethVault.readTotalAssets body) out) :
    ∃ bodyPre : Devm,
      (entry.state.getStor wethAccount).get sevm.currentTarget.toB256 :: [] <<+
        bodyPre.stack ∧
      Mem.Wf bodyPre.memory ∧
      (∀ {offset : Nat} {w : B256}, 64 ≤ offset →
        MemWordAt entry offset w → MemWordAt bodyPre offset w) ∧
      Devm.getStor bodyPre = Devm.getStor entry ∧
      DirectWethConfiguration sevm.currentTarget sevm bodyPre ∧
      Func.RunCompiledToAvoiding WethChildRefused fs sevm bodyPre body out := by
  have memory : MemoryImage entry entry.memory.data.toList := by
    refine ⟨memoryWf, ?_⟩
    intro index
    simp
  rw [readTotalAssets_sourceShape] at run
  obtain ⟨callPre, staging, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨callPost, crossing, notRefused, run⟩ :=
    Func.RunCompiledToAvoiding.next_inv run
  obtain ⟨gasWord, rest, stack, -, callPreWf⟩ :=
    balanceOfStaging_boundary memory staging
  have operandPrefix :
      gasWord :: wethAccount.toB256 :: 28 :: 36 :: 0 :: 32 :: rest <<+
        callPre.stack := by
    rw [stack]
    exact ⟨[], by simp [Split]⟩
  have crossingSource := Ninst.Run.of_runCompiled crossing
  have depth : sevm.depth ≠ 0 := by
    rcases of_run_staticcall_val_with_depth operandPrefix crossingSource hfork with
      failure | success
    · obtain ⟨zeroPrefix, -, -⟩ := failure
      exfalso
      apply notRefused
      refine ⟨Or.inr rfl, by rw [stack]; rfl, ?_⟩
      obtain ⟨suffix, zeroStack⟩ := zeroPrefix
      simp only [Split] at zeroStack
      rw [zeroStack]
      rfl
    · obtain ⟨_, _, _, _, _, _, _, positiveDepth, _⟩ := success
      exact Nat.ne_of_gt positiveDepth
  have stagingCode : Devm.getCode entry = Devm.getCode callPre :=
    Line.of_inv Devm.getCode (by
      unfold balanceOfStaging mstoreAt pushList
      simp only [List.map, List.cons_append, List.nil_append]
      line_inv) staging
  have stagingStorage : Devm.getStor entry = Devm.getStor callPre :=
    Line.of_inv Devm.getStor (by
      unfold balanceOfStaging mstoreAt pushList
      simp only [List.map, List.cons_append, List.nil_append]
      line_inv) staging
  have callConfig :
      DirectWethConfiguration sevm.currentTarget sevm callPre :=
    config.of_code_eq (congrFun stagingCode wethAccount).symm
  have occurrence := balanceOfStaging_occurrence callConfig hfork memory staging
    depth (staticGasAvailable_of_runCompiled callConfig hfork crossing) crossing
  have successFlag : ∃ tail, callPost.stack = (1 : B256) :: tail := by
    have shape := occurrence
    unfold ExactWethChildOccurrence ExactWethChildExecution at shape
    obtain ⟨-, -, child, -, -, -, -, -, -, -, -, -, -, -, -, -, -, statusTail,
      statusStack, -⟩ := shape
    have statusNonzero :
        (if child.error.isSome then (0 : B256) else 1) ≠ 0 := by
      intro statusZero
      apply notRefused
      refine ⟨Or.inr rfl, by rw [stack]; rfl, ?_⟩
      rw [statusStack, statusZero]
      rfl
    exact ExactWethChildOccurrence.successFlag_of_nonzero occurrence
      statusStack statusNonzero
  have success :
      ExactWethChildSuccess sevm callPre callPost staticcall
        (balanceOfCalldata sevm.currentTarget) callPost.returnData true :=
    ExactWethChildOccurrence.success_of_post occurrence successFlag rfl
  obtain ⟨storage, -, output⟩ := SuccessfulWethWorldProgramRun.balanceOf_effect
    (ExactWethChildSuccess.worldProgramRun hfork success)
  have returnDataLength : callPost.returnData.length = 32 := by
    rw [output, B256.length_toBytes]
  have window := staticcallOutputWindow stack crossing hfork successFlag
    returnDataLength
  rw [output] at window
  obtain ⟨statusTail, statusStack⟩ := successFlag
  obtain ⟨bodyPre, wordPrefix, bodyState, bodyMemory, bodyRun⟩ :=
    checkedWordSuffix_avoiding (tail := [])
      (by rw [statusStack]; exact ⟨statusTail, by simp [Split]⟩)
      returnDataLength window run
  have callPostWf : Mem.Wf callPost.memory := by
    rcases of_run_staticcall_val_with_depth operandPrefix crossingSource hfork with
      failure | success
    · obtain ⟨zeroPrefix, -, -⟩ := failure
      have onePrefix : (1 : B256) :: [] <<+ callPost.stack := by
        rw [statusStack]
        exact pref_append [1] statusTail
      exact (B256.zero_ne_one (pref_head_unique zeroPrefix onePrefix)).elim
    · rcases success with
        ⟨parent, child, _, _, _, _, _, -, -, -, parentMemory, -, -, -, -,
          -, -, -, finalMemory, -⟩
      rw [finalMemory, parentMemory]
      exact (Mem.Wf.extends _ callPreWf).write _ _
  have bodyStorage : Devm.getStor bodyPre = Devm.getStor entry :=
    (funext (getStor_eq_of_state_eq bodyState)).trans
      (storage.trans stagingStorage.symm)
  refine ⟨bodyPre, ?_, ?_, ?_, bodyStorage, ?_, bodyRun⟩
  · have balanceEq : (callPre.state.getStor wethAccount).get
        sevm.currentTarget.toB256 =
        (entry.state.getStor wethAccount).get sevm.currentTarget.toB256 :=
      (congrArg (fun storage : Stor => storage.get sevm.currentTarget.toB256)
        (congrFun stagingStorage wethAccount)).symm
    change (Devm.getStor callPre wethAccount).get sevm.currentTarget.toB256
      :: [] <<+ bodyPre.stack at wordPrefix
    exact balanceEq ▸ wordPrefix
  · rw [bodyMemory]
    exact callPostWf.extend _ _
  · intro offset w afterCalldata entryWindow
    have callPreWindow := entryWindow.acrossBalanceOfStaging afterCalldata staging
    have callPostWindow := callPreWindow.acrossStaticcall
      (by
        change 32 ≤ offset
        omega)
      operandPrefix crossingSource hfork
    exact MemWordAt.extend bodyMemory callPostWindow
  · exact (callConfig.of_runCompiled crossing).of_state_eq' bodyState.symm


/-- The canonical-`true` check after a WETH mutation, along an avoiding walk,
when the child returned the one-word `true`. -/
theorem canonicalTrueSuffix_avoiding {fs : List Func} {sevm : Sevm}
    {callPost : Devm} {out : Execution} {body : Func} {tail : Stack}
    (statusOne : (1 : B256) :: tail <<+ callPost.stack)
    (returnDataLength : callPost.returnData.length = 32)
    (window : (callPost.memory.read 0 32).1 = (1 : B256).toBytes)
    (run : Func.RunCompiledToAvoiding WethChildRefused fs sevm callPost
      (iszero :::
        (Func.revert <?>
          Blanc.ProrataWethVault.requireCanonicalWethTrue body)) out) :
    ∃ bodyPre,
      tail <<+ bodyPre.stack ∧
      bodyPre.state = callPost.state ∧
      bodyPre.memory = callPost.memory.extend 0 32 ∧
      Func.RunCompiledToAvoiding WethChildRefused fs sevm bodyPre body out := by
  unfold Blanc.ProrataWethVault.requireCanonicalWethTrue at run
  obtain ⟨checkPre, wordPrefix, checkState, checkMemory, checkRun⟩ :=
    checkedWordSuffix_avoiding statusOne returnDataLength window run
  obtain ⟨s1, q1, -, checkRun⟩ := Func.RunCompiledToAvoiding.next_inv checkRun
  obtain ⟨s2, q2, -, checkRun⟩ := Func.RunCompiledToAvoiding.next_inv checkRun
  obtain ⟨s3, q3, -, branchRun⟩ := Func.RunCompiledToAvoiding.next_inv checkRun
  have r1 := Ninst.Run.of_runCompiled q1
  have r2 := Ninst.Run.of_runCompiled q2
  have r3 := Ninst.Run.of_runCompiled q3
  have flag := prefix_of_iszero r3
    (prefix_of_eq r2 (prefix_of_push (of_run_pushB256 r1) wordPrefix))
  have zeroPrefix : (0 : B256) :: tail <<+ s3.stack := by
    have oneNonzero : (1 : B256) ≠ 0 := by decide
    simpa [B256.eqCheck, oneNonzero] using flag
  obtain ⟨bodyPre, pop, bodyRun, bodyTail⟩ :=
    Func.RunCompiledToAvoiding.zero_branch_of_prefix zeroPrefix branchRun
  have pop' := Devm.PopBurn.of_popBurnBy pop
  refine ⟨bodyPre, bodyTail, ?_, ?_, bodyRun⟩
  · rw [← pop'.state, ← Ninst.Hinv.inv (f := Devm.state) r3,
      ← Ninst.Hinv.inv (f := Devm.state) r2, ← (of_run_pushB256 r1).state]
    exact checkState
  · rw [← pop'.memory, ← Ninst.Hinv.inv (f := Devm.memory) r3,
      ← Ninst.Hinv.inv (f := Devm.memory) r2, ← (of_run_pushB256 r1).memory]
    exact checkMemory

/-- A checked WETH mutation along an avoiding walk: the crossing did not
refuse, so the exact child ran and returned canonical `true`, and the walk
reaches the continuation.  Every account but WETH keeps its storage, and
every operation word at or above byte 32 survives. -/
theorem wethMutationCall_avoiding {fs : List Func} {sevm : Sevm}
    {callPre : Devm} {out : Execution} {body : Func}
    {gasWord inputSize : B256} {rest : List B256} {calldata : Bytes}
    (config : DirectWethConfiguration sevm.currentTarget sevm callPre)
    (hfork : CoveredFork sevm.benvStat.fork)
    (callPreWf : Mem.Wf callPre.memory)
    (stack : callPre.stack =
      gasWord :: wethAccount.toB256 :: 0 :: 28 :: inputSize :: 0 :: 32 :: rest)
    (window : (callPre.memory.read 28 inputSize.toNat).1 = calldata)
    (returnsTrue : ∀ {callPost : Devm},
      ExactWethChildSuccess sevm callPre callPost call calldata
          callPost.returnData sevm.isStatic →
        callPost.returnData = (1 : B256).toBytes ∧
        ∀ account, wethAccount ≠ account →
          Devm.getStor callPost account = Devm.getStor callPre account)
    (run : Func.RunCompiledToAvoiding WethChildRefused fs sevm callPre
      (call ::: iszero :::
        (Func.revert <?>
          Blanc.ProrataWethVault.requireCanonicalWethTrue body)) out) :
    ∃ bodyPre,
      Mem.Wf bodyPre.memory ∧
      (∀ {offset : Nat} {w : B256}, 32 ≤ offset →
        MemWordAt callPre offset w → MemWordAt bodyPre offset w) ∧
      (∀ account, wethAccount ≠ account →
        Devm.getStor bodyPre account = Devm.getStor callPre account) ∧
      DirectWethConfiguration sevm.currentTarget sevm bodyPre ∧
      Func.RunCompiledToAvoiding WethChildRefused fs sevm bodyPre body out := by
  obtain ⟨callPost, crossing, notRefused, run⟩ :=
    Func.RunCompiledToAvoiding.next_inv run
  have operandPrefix :
      gasWord :: wethAccount.toB256 :: 0 :: 28 :: inputSize :: 0 :: 32 :: rest
        <<+ callPre.stack := by
    rw [stack]
    exact ⟨[], by simp [Split]⟩
  have crossingSource := Ninst.Run.of_runCompiled crossing
  have depth : sevm.depth ≠ 0 := by
    rcases of_run_call_val_with_depth operandPrefix crossingSource hfork with
      failure | success
    · obtain ⟨zeroPrefix, -⟩ := failure
      exfalso
      apply notRefused
      refine ⟨Or.inl rfl, by rw [stack]; rfl, ?_⟩
      obtain ⟨suffix, zeroStack⟩ := zeroPrefix
      simp only [Split] at zeroStack
      rw [zeroStack]
      rfl
    · obtain ⟨_, _, _, _, _, _, _, positiveDepth, _⟩ := success
      exact Nat.ne_of_gt positiveDepth
  have occurrence :
      ExactWethChildOccurrence sevm callPre callPost call calldata
        sevm.isStatic := by
    apply exactWethCallOccurrence_of_runCompiled_anyStatic config hfork stack window
      depth
    · exact callGasAvailable_of_runCompiled config hfork crossing gasWord rest stack
    · exact crossing
  have successFlag : ∃ tail, callPost.stack = (1 : B256) :: tail := by
    have shape := occurrence
    unfold ExactWethChildOccurrence ExactWethChildExecution at shape
    obtain ⟨-, -, child, -, -, -, -, -, -, -, -, -, -, -, -, -, -, statusTail,
      statusStack, -⟩ := shape
    have statusNonzero :
        (if child.error.isSome then (0 : B256) else 1) ≠ 0 := by
      intro statusZero
      apply notRefused
      refine ⟨Or.inl rfl, by rw [stack]; rfl, ?_⟩
      rw [statusStack, statusZero]
      rfl
    exact ExactWethChildOccurrence.successFlag_of_nonzero occurrence
      statusStack statusNonzero
  obtain ⟨output, foreign⟩ :=
    returnsTrue (ExactWethChildOccurrence.success_of_post occurrence
      successFlag rfl)
  have returnDataLength : callPost.returnData.length = 32 := by
    rw [output, B256.length_toBytes]
  have outputWindow := callOutputWindow stack crossing hfork successFlag
    returnDataLength
  rw [output] at outputWindow
  obtain ⟨statusTail, statusStack⟩ := successFlag
  obtain ⟨bodyPre, -, bodyState, bodyMemory, bodyRun⟩ :=
    canonicalTrueSuffix_avoiding (tail := [])
      (by rw [statusStack]; exact ⟨statusTail, by simp [Split]⟩)
      returnDataLength outputWindow run
  have callPostWf : Mem.Wf callPost.memory := by
    rcases of_run_call_val_with_depth operandPrefix crossingSource hfork with
      failure | success
    · obtain ⟨zeroPrefix, -⟩ := failure
      have onePrefix : (1 : B256) :: [] <<+ callPost.stack := by
        rw [statusStack]
        exact pref_append [1] statusTail
      exact (B256.zero_ne_one (pref_head_unique zeroPrefix onePrefix)).elim
    · rcases success with
        ⟨parent, child, _, _, _, _, _, -, -, -, parentMemory, -, -, -, -,
          -, -, -, finalMemory, -⟩
      rw [finalMemory, parentMemory]
      exact (Mem.Wf.extends _ callPreWf).write _ _
  refine ⟨bodyPre, ?_, ?_, ?_, ?_, bodyRun⟩
  · rw [bodyMemory]
    exact callPostWf.extend _ _
  · intro offset w above callWindow
    have postWindow := MemWordAt.acrossSuccessfulCall
      (by
        change 0 + 32 ≤ offset
        omega)
      operandPrefix crossingSource hfork ⟨statusTail, statusStack⟩ callWindow
    exact MemWordAt.extend bodyMemory postWindow
  · intro account accountNe
    rw [← foreign account accountNe]
    exact getStor_eq_of_state_eq bodyState account
  · exact (config.of_runCompiled crossing).of_state_eq' bodyState.symm

/-- The inbound `transferFrom(caller, vault, assets)` crossing along an
avoiding walk.  In a frame of either static flag the crossing either refused
(visited) or ran the exact child, which returns canonical `true`. -/
theorem callWethTransferFrom_avoiding {fs : List Func} {sevm : Sevm}
    {entry : Devm} {out : Execution} {body : Func} {image : Bytes}
    {assetsWord assets : B256}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memory : MemoryImage entry image)
    (assetsAt : ImageWordAt image assetsWord assets)
    (assetsAboveCalldata : 96 ≤ (assetsWord * 32).toNat)
    (run : Func.RunCompiledToAvoiding WethChildRefused fs sevm entry
      (Blanc.ProrataWethVault.callWethTransferFrom
        (Blanc.ProrataWethVault.loadWord assetsWord) body) out) :
    ∃ bodyPre,
      Mem.Wf bodyPre.memory ∧
      (∀ {offset : Nat} {w : B256}, 128 ≤ offset →
        MemWordAt entry offset w → MemWordAt bodyPre offset w) ∧
      Devm.getStor bodyPre sevm.currentTarget =
        Devm.getStor entry sevm.currentTarget ∧
      DirectWethConfiguration sevm.currentTarget sevm bodyPre ∧
      Func.RunCompiledToAvoiding WethChildRefused fs sevm bodyPre body out := by
  rw [callWethTransferFrom_sourceShape] at run
  obtain ⟨callPre, staging, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨gasWord, rest, stack, window, callPreWf⟩ :=
    transferFromStaging_boundary memory assetsAt assetsAboveCalldata staging
  have stagingCode : Devm.getCode entry = Devm.getCode callPre :=
    Line.of_inv Devm.getCode (by
      unfold transferFromStaging Blanc.ProrataWethVault.loadWord mstoreAt
        pushList
      simp only [List.map, List.cons_append, List.nil_append]
      line_inv) staging
  have stagingStorage : Devm.getStor entry = Devm.getStor callPre :=
    Line.of_inv Devm.getStor (by
      unfold transferFromStaging Blanc.ProrataWethVault.loadWord mstoreAt
        pushList
      simp only [List.map, List.cons_append, List.nil_append]
      line_inv) staging
  have callConfig := config.of_code_eq (congrFun stagingCode wethAccount).symm
  obtain ⟨bodyPre, bodyWf, bodyWindow, bodyForeign, bodyConfig, bodyRun⟩ :=
    wethMutationCall_avoiding callConfig hfork callPreWf stack window
      (fun success => by
        obtain ⟨-, foreign, -, output⟩ :=
          SuccessfulWethWorldProgramRun.transferFrom_effect
            (ExactWethChildSuccess.worldProgramRun hfork success)
        exact ⟨output, foreign⟩) run
  refine ⟨bodyPre, bodyWf, ?_, ?_, bodyConfig, bodyRun⟩
  · intro offset w above entryWindow
    exact bodyWindow (by omega)
      (entryWindow.acrossTransferFromStaging above staging)
  · rw [bodyForeign _ config.distinct]
    exact (congrFun stagingStorage sevm.currentTarget).symm

/-- The outbound `transfer(receiver, assets)` crossing along an avoiding
walk: it either refused (visited) or ran the exact child, which returns
canonical `true`. -/
theorem callWethTransfer_avoiding {fs : List Func} {sevm : Sevm}
    {entry : Devm} {out : Execution} {body : Func} {image : Bytes}
    {receiverWord assetsWord assets : B256} {receiver : Adr}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memory : MemoryImage entry image)
    (receiverAt : ImageWordAt image receiverWord receiver.toB256)
    (assetsAt : ImageWordAt image assetsWord assets)
    (receiverAboveSelector : 32 ≤ (receiverWord * 32).toNat)
    (assetsAboveReceiver : 64 ≤ (assetsWord * 32).toNat)
    (run : Func.RunCompiledToAvoiding WethChildRefused fs sevm entry
      (Blanc.ProrataWethVault.callWethTransfer
        (Blanc.ProrataWethVault.loadWord receiverWord)
        (Blanc.ProrataWethVault.loadWord assetsWord) body) out) :
    ∃ bodyPre,
      Func.RunCompiledToAvoiding WethChildRefused fs sevm bodyPre body out := by
  rw [callWethTransfer_sourceShape] at run
  obtain ⟨callPre, staging, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨gasWord, rest, stack, window, callPreWf⟩ :=
    transferStaging_boundary memory receiverAt assetsAt receiverAboveSelector
      assetsAboveReceiver staging
  have stagingCode : Devm.getCode entry = Devm.getCode callPre :=
    Line.of_inv Devm.getCode (by
      unfold transferStaging Blanc.ProrataWethVault.loadWord mstoreAt
        pushList
      simp only [List.map, List.cons_append, List.nil_append]
      line_inv) staging
  have callConfig := config.of_code_eq (congrFun stagingCode wethAccount).symm
  obtain ⟨bodyPre, -, -, -, -, bodyRun⟩ :=
    wethMutationCall_avoiding callConfig hfork callPreWf stack window
      (fun success => by
        obtain ⟨-, foreign, -, output⟩ :=
          SuccessfulWethWorldProgramRun.transfer_effect
            (ExactWethChildSuccess.worldProgramRun hfork success)
        exact ⟨output, foreign⟩) run
  exact ⟨bodyPre, bodyRun⟩


/-! ### The vault's own guards, passed on the headline premises -/

section

variable {P : Sevm → Devm → Ninst → Devm → Prop}
  {fs : List Func} {sevm : Sevm}

/-- Any memory reads its own bytes. -/
theorem selfReads (d : Devm) : Mem.Reads d.memory d.memory.data.toList := by
  intro index
  simp

/-- A word window read against the memory's own bytes. -/
theorem MemWordAt.self_toB256 {d : Devm} {offset : Nat} {w : B256}
    (window : MemWordAt d offset w) :
    Bytes.toB256 (d.memory.data.toList.sliceD offset 32 0) = w := by
  rw [window.slice_eq (selfReads d), B256.toB256_toBytes]

/-- The zero-caller guard passes on a nonzero caller. -/
theorem nonzeroCaller_avoiding {pre : Devm} {out : Execution} {body : Func}
    {tail : Stack}
    (callerNonzero : sevm.caller.toB256 ≠ 0)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledToAvoiding P fs sevm pre
      (Blanc.ProrataWethVault.nonzeroCaller body) out) :
    ∃ bodyPre, tail <<+ bodyPre.stack ∧ pre.memory = bodyPre.memory ∧
      pre.state = bodyPre.state ∧
      Func.RunCompiledToAvoiding P fs sevm bodyPre body out := by
  unfold Blanc.ProrataWethVault.nonzeroCaller at run
  obtain ⟨callerPost, callerRun, -, run⟩ :=
    Func.RunCompiledToAvoiding.next_inv run
  obtain ⟨testPost, zeroRun, -, branchRun⟩ :=
    Func.RunCompiledToAvoiding.next_inv run
  have callerSource := Ninst.Run.of_runCompiled callerRun
  have zeroSource := Ninst.Run.of_runCompiled zeroRun
  have callerPush := of_run_caller callerSource
  have flag := prefix_of_iszero zeroSource (prefix_of_push callerPush stack)
  have zeroPrefix : (0 : B256) :: tail <<+ testPost.stack := by
    simpa [B256.eqCheck, callerNonzero] using flag
  obtain ⟨bodyPre, pop, bodyRun, bodyTail⟩ :=
    Func.RunCompiledToAvoiding.zero_branch_of_prefix zeroPrefix branchRun
  have pop' := Devm.PopBurn.of_popBurnBy pop
  exact ⟨bodyPre, bodyTail,
    callerPush.memory.trans
      ((Ninst.Hinv.inv (f := Devm.memory) zeroSource).trans pop'.memory),
    callerPush.state.trans
      ((Ninst.Hinv.inv (f := Devm.state) zeroSource).trans pop'.state),
    bodyRun⟩

/-- The canonical-nonzero-address guard over a produced word passes on a
canonical nonzero word. -/
theorem canonicalNonzero_avoiding {pre : Devm} {out : Execution}
    {image : Bytes} {line : Line} {value : B256} {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (produces : Blanc.ProrataWethVault.ProducesWord sevm line image value)
    (valid : ValidAdr value) (nonzero : value ≠ 0)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledToAvoiding P fs sevm pre
      (line +++ dup 0 ::: checkNonAddress +++
        (Func.revert <?> (iszero ::: (Func.revert <?> body)))) out) :
    ∃ bodyPre, tail <<+ bodyPre.stack ∧ Mem.Wf bodyPre.memory ∧
      Mem.Reads bodyPre.memory image ∧ pre.state = bodyPre.state ∧
      Func.RunCompiledToAvoiding P fs sevm bodyPre body out := by
  obtain ⟨checkPre, valueRun, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨valuePrefix, checkWf, checkReads, valueQuiet⟩ :=
    produces memoryWf memoryReads stack valueRun
  obtain ⟨dupPre, dupRun, -, run⟩ := Func.RunCompiledToAvoiding.next_inv run
  have dupSource := Ninst.Run.of_runCompiled dupRun
  have dupPrefix : value :: value :: tail <<+ dupPre.stack :=
    prefix_of_dup_val dupSource (by show_nth) valuePrefix
  obtain ⟨checkPost, checkRun, branchRun⟩ :=
    Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨flag, flagPrefix, flagValid⟩ := of_check_non_address dupPrefix checkRun
  have checkMemory : checkPre.memory = checkPost.memory :=
    (Ninst.Hinv.inv (f := Devm.memory) dupSource).trans
      (Line.of_inv Devm.memory (by unfold checkNonAddress; line_inv) checkRun)
  have checkState : checkPre.state = checkPost.state :=
    (Ninst.Hinv.inv (f := Devm.state) dupSource).trans
      (Line.of_inv Devm.state (by unfold checkNonAddress; line_inv) checkRun)
  have zeroFlag : (0 : B256) :: value :: tail <<+ checkPost.stack := by
    rw [← flagValid.mpr valid]
    exact flagPrefix
  obtain ⟨zeroPre, pop1, run, zeroTail⟩ :=
    Func.RunCompiledToAvoiding.zero_branch_of_prefix zeroFlag branchRun
  have pop1' := Devm.PopBurn.of_popBurnBy pop1
  obtain ⟨testPre, testRun, -, testBranch⟩ :=
    Func.RunCompiledToAvoiding.next_inv run
  have testSource := Ninst.Run.of_runCompiled testRun
  have testZero : (0 : B256) :: tail <<+ testPre.stack := by
    simpa [B256.eqCheck, nonzero] using prefix_of_iszero testSource zeroTail
  obtain ⟨bodyPre, pop2, bodyRun, bodyTail⟩ :=
    Func.RunCompiledToAvoiding.zero_branch_of_prefix testZero testBranch
  have pop2' := Devm.PopBurn.of_popBurnBy pop2
  have memoryEq : checkPre.memory = bodyPre.memory :=
    checkMemory.trans (pop1'.memory.trans
      ((Ninst.Hinv.inv (f := Devm.memory) testSource).trans pop2'.memory))
  refine ⟨bodyPre, bodyTail, memoryEq ▸ checkWf, memoryEq ▸ checkReads, ?_,
    bodyRun⟩
  exact valueQuiet.1.trans (checkState.trans (pop1'.state.trans
    ((Ninst.Hinv.inv (f := Devm.state) testSource).trans pop2'.state)))

/-- The stable-supply guard of the flows passes at a stable staged supply,
and it moves no memory. -/
theorem guardStableSupply_avoiding {pre : Devm} {out : Execution}
    {supply : B256} {body : Func} {tail : Stack}
    (supplyWindow : MemWordAt pre
      (Blanc.ProrataWethVault.supplyWord * 32).toNat supply)
    (stable : supply.toNat ≤ Blanc.ProrataWethVault.maxSupplyN)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledToAvoiding P fs sevm pre
      (Blanc.ProrataWethVault.guardStableSupply body) out) :
    ∃ bodyPre,
      tail <<+ bodyPre.stack ∧
      (∀ {offset : Nat} {w : B256}, MemWordAt pre offset w →
        MemWordAt bodyPre offset w) ∧
      pre.state = bodyPre.state ∧
      Func.RunCompiledToAvoiding P fs sevm bodyPre body out := by
  unfold Blanc.ProrataWethVault.guardStableSupply at run
  obtain ⟨maxPre, supplyRun, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  have supplyPrefix := prefix_of_loadWord_window supplyWindow stack supplyRun
  have supplyState : pre.state = maxPre.state :=
    Line.of_inv Devm.state
      (by unfold Blanc.ProrataWethVault.loadWord; line_inv) supplyRun
  obtain ⟨testPre, maxRun, -, run⟩ := Func.RunCompiledToAvoiding.next_inv run
  have maxSource := Ninst.Run.of_runCompiled maxRun
  have maxPrefix := prefix_of_push (of_run_pushB256 maxSource) supplyPrefix
  obtain ⟨branchPre, testRun, -, run⟩ := Func.RunCompiledToAvoiding.next_inv run
  have testSource := Ninst.Run.of_runCompiled testRun
  have testPrefix := prefix_of_lt testSource maxPrefix
  have notUnstable : ¬ Blanc.ProrataWethVault.maxSupply < supply := by
    intro unstable
    have := B256.toNat_lt_toNat unstable
    rw [Blanc.ProrataWethVault.maxSupply_toNat] at this
    omega
  have zeroPrefix : (0 : B256) :: tail <<+ branchPre.stack := by
    simpa [B256.ltCheck, notUnstable] using testPrefix
  obtain ⟨bodyPre, bodyPop, bodyRun, bodyPrefix⟩ :=
    Func.RunCompiledToAvoiding.zero_branch_of_prefix zeroPrefix run
  have bodyPop' := Devm.PopBurn.of_popBurnBy bodyPop
  refine ⟨bodyPre, bodyPrefix, ?_, ?_, bodyRun⟩
  · intro offset w window
    exact MemWordAt.of_memory_eq bodyPop'.memory.symm
      (((window.acrossLoadWord supplyRun).acrossNinst maxSource).acrossNinst
        testSource)
  · exact supplyState.trans
      ((Ninst.Hinv.inv (f := Devm.state) maxSource).trans
        ((Ninst.Hinv.inv (f := Devm.state) testSource).trans bodyPop'.state))

end

/-- The flows' shared snapshot along an avoiding walk: the booked WETH balance
and the share supply are staged at their operation words, the stable-supply
guard passes, and the words below the supply word survive. -/
theorem snapshotQuoteState_avoiding {fs : List Func} {sevm : Sevm}
    {entry : Devm} {out : Execution} {arithmetic : Func}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf entry.memory)
    (stable : (Devm.getStorVal entry sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot).toNat ≤
        Blanc.ProrataWethVault.maxSupplyN)
    (run : Func.RunCompiledToAvoiding WethChildRefused fs sevm entry
      (Blanc.ProrataWethVault.snapshotQuoteState arithmetic) out) :
    ∃ quotePre : Devm,
      Mem.Wf quotePre.memory ∧
      MemWordAt quotePre (Blanc.ProrataWethVault.assetsWord * 32).toNat
        ((entry.state.getStor wethAccount).get sevm.currentTarget.toB256) ∧
      MemWordAt quotePre (Blanc.ProrataWethVault.supplyWord * 32).toNat
        (Devm.getStorVal entry sevm.currentTarget
          Blanc.ProrataWethVault.supplySlot) ∧
      (∀ {offset : Nat} {w : B256}, 64 ≤ offset →
        offset + 32 ≤ (Blanc.ProrataWethVault.supplyWord * 32).toNat →
        MemWordAt entry offset w → MemWordAt quotePre offset w) ∧
      Devm.getStor quotePre = Devm.getStor entry ∧
      DirectWethConfiguration sevm.currentTarget sevm quotePre ∧
      Func.RunCompiledToAvoiding WethChildRefused fs sevm quotePre arithmetic
        out := by
  unfold Blanc.ProrataWethVault.snapshotQuoteState at run
  obtain ⟨readPre, assetsPrefix, readWf, readWindows, readStorage,
      readConfig, run⟩ :=
    readTotalAssets_exact_avoiding config hfork memoryWf run
  obtain ⟨slotPre, storeRun, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨slotStack, slotWf, slotReads, storeState⟩ :=
    of_run_mstoreAt_image assetsPrefix readWf (selfReads readPre) storeRun
  have assetsWindow : MemWordAt slotPre
      (Blanc.ProrataWethVault.assetsWord * 32).toNat
      ((entry.state.getStor wethAccount).get sevm.currentTarget.toB256) := by
    refine MemWordAt.of_memImage ⟨slotWf, slotReads⟩ ?_
    have readback := Bytes.sliceD_writeAt readPre.memory.data.toList
      ((entry.state.getStor wethAccount).get
        sevm.currentTarget.toB256).toBytes
      (Blanc.ProrataWethVault.assetsWord * 32).toNat
    rwa [B256.length_toBytes] at readback
  obtain ⟨supply, guardPre, supplyEq, guardStack, supplyWindow,
      supplyPreserves, supplyState, run⟩ :=
    Blanc.ProrataWethVault.capacitySupplyStaging_avoiding slotWf slotStack run
  have slotStorage : Devm.getStor slotPre = Devm.getStor entry :=
    (funext (getStor_eq_of_state_eq storeState)).symm.trans readStorage
  have supplyValue : supply = Devm.getStorVal entry sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot := by
    rw [supplyEq]
    change (Devm.getStor slotPre sevm.currentTarget).get _ =
      (Devm.getStor entry sevm.currentTarget).get _
    rw [slotStorage]
  subst supplyValue
  obtain ⟨quotePre, -, guardPreserves, guardState, run⟩ :=
    guardStableSupply_avoiding supplyWindow stable guardStack run
  have quoteState : slotPre.state = quotePre.state :=
    supplyState.trans guardState
  refine ⟨quotePre, ?_, guardPreserves
      (supplyPreserves (Or.inr (by decide +kernel)) assetsWindow),
    guardPreserves supplyWindow, ?_, ?_, ?_, run⟩
  · exact (guardPreserves supplyWindow).1
  · intro offset w above below window
    apply guardPreserves
    apply supplyPreserves (Or.inl below)
    apply (MemWordAt.acrossMstoreAt (Or.inl (by
      have : (Blanc.ProrataWethVault.supplyWord * 32).toNat + 32 ≤
          (Blanc.ProrataWethVault.assetsWord * 32).toNat := by decide +kernel
      omega)) storeRun)
    exact readWindows above window
  · exact (funext (getStor_eq_of_state_eq quoteState)).symm.trans slotStorage
  · exact readConfig.of_state_eq' (storeState.trans quoteState)


/-- `mstoreAt` of a known stack word, in window form: the stored word is read
back at its offset, and every window the write misses survives. -/
theorem mstoreAt_window {sevm : Sevm} {pre post : Devm} {k v : B256}
    {tail : Stack}
    (stack : v :: tail <<+ pre.stack) (memoryWf : Mem.Wf pre.memory)
    (run : Line.Run sevm pre (mstoreAt k) post) :
    tail <<+ post.stack ∧ Mem.Wf post.memory ∧
      MemWordAt post (k * 32).toNat v ∧
      (∀ {offset : Nat} {w : B256},
        (offset + 32 ≤ (k * 32).toNat ∨ (k * 32).toNat + 32 ≤ offset) →
        MemWordAt pre offset w → MemWordAt post offset w) ∧
      pre.state = post.state := by
  obtain ⟨postStack, postWf, postReads, state⟩ :=
    of_run_mstoreAt_image stack memoryWf (selfReads pre) run
  refine ⟨postStack, postWf, ?_, fun miss window =>
    window.acrossMstoreAt miss run, state⟩
  refine MemWordAt.of_memImage ⟨postWf, postReads⟩ ?_
  have readback := Bytes.sliceD_writeAt pre.memory.data.toList v.toBytes
    (k * 32).toNat
  rwa [B256.length_toBytes] at readback


/-- A window read at one state survives to any state whose memory still reads
the first state's bytes. -/
theorem MemWordAt.of_selfReads {a b : Devm} {offset : Nat} {w : B256}
    (window : MemWordAt a offset w) (memoryWf : Mem.Wf b.memory)
    (reads : Mem.Reads b.memory a.memory.data.toList) :
    MemWordAt b offset w :=
  MemWordAt.of_memImage ⟨memoryWf, reads⟩ (window.slice_eq (selfReads a))

end Blanc.Composition.ProrataWethVault
