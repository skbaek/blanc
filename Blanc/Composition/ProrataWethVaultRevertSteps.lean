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
    rcases of_run_staticcall_val_with_depth operandPrefix crossingSource with
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
  have occurrence := balanceOfStaging_occurrence callConfig memory staging
    depth (staticGasAvailable_of_runCompiled callConfig crossing) crossing
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
    (ExactWethChildSuccess.worldProgramRun success)
  have returnDataLength : callPost.returnData.length = 32 := by
    rw [output, B256.length_toBytes]
  have callPostWf : Mem.Wf callPost.memory := by
    rcases of_run_staticcall_val_with_depth operandPrefix crossingSource with
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
      operandPrefix crossingSource
    apply MemWordAt.extend loadMemory
    exact MemWordAt.of_memory_eq mloadMemory callPostWindow

end Blanc.Composition.ProrataWethVault
