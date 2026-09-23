-- ProrataWethVaultNonrevertViews.lean : the capacity views revert only through
-- a refused WETH `balanceOf`, and `maxRedeem` has no reverting walk at all.

import Blanc.Composition.ProrataWethVaultRevertSteps

namespace Blanc.Composition.ProrataWethVault

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv
open Source

/-!
# Walk-level revert cause of the capacity views

Each core takes a reverting gas-exact walk of the deployed vault and shows
that it visits a refused WETH child.  The walk is entered through the
selector, the nonpayable wrapper and the static-head guard; the canonical
address guard passes on `argValid`; the zero-receiver and unstable-supply
routes return zero and so cannot be the reverting branch; the `balanceOf`
child either was refused (the conclusion) or returned one word; and the
capped arithmetic behind it divides by a nonzero denominator into a
continuation with no `REVERT`.  The exec-level headlines in
`…Nonrevert.lean` add only the inversion `Prog.runCompiledTo_of_exec_revert`.
-/

private theorem vault_returnWord_lookup :
    (Blanc.ProrataWethVault.vault.main ::
        Blanc.ProrataWethVault.vault.aux)[
          Blanc.ProrataWethVault.returnWordSlot]? =
      some Blanc.ProrataWethVault.returnWord := rfl

private theorem vault_maxMintCap_lookup :
    (Blanc.ProrataWethVault.vault.main ::
        Blanc.ProrataWethVault.vault.aux)[
          Blanc.ProrataWethVault.maxMintAfterAssetCapSlot]? =
      some Blanc.ProrataWethVault.maxMintAfterAssetCap := rfl

/-- A self-read memory image. -/
private theorem reads_self (devm : Devm) :
    Mem.Reads devm.memory devm.memory.data.toList := by
  intro index
  simp

/-- **The `maxDeposit` view reverts only through a refused `balanceOf`.**  No
stable-state premise: an unstable supply or zero receiver returns 0 before
any arithmetic. -/
theorem maxDeposit_revert_visits_refused_weth_child
    {sevm : Sevm} {pre d : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf pre.memory)
    (selectorEq : Sevm.selector sevm = selector "maxDeposit" [.address])
    (valueZero : sevm.value = 0)
    (argsPresent :
      B256.ltCheck sevm.data.length.toB256 (Nat.toB256 (4 + 32 * 1)) = 0)
    (argValid : ValidAdr (Sevm.argWord sevm 0))
    (walk : Prog.RunCompiledTo sevm pre Blanc.ProrataWethVault.vault
      (.error (.revert, d))) :
    Prog.RunCompiledToVisiting WethChildRefused sevm pre
      Blanc.ProrataWethVault.vault (.error (.revert, d)) := by
  refine vault_revert_visits_of_body selectorEq (List.mem_of_getElem? (i := 9) rfl)
    valueZero argsPresent walk ?_
  intro bodyPre entryState entryMemory run
  unfold Blanc.ProrataWethVault.maxDeposit at run
  obtain ⟨receiverPre, receiverStack, receiverState, receiverMemory,
      receiverRun⟩ := canonicalAddressArg_avoiding argValid nil_pref run
  have receiverWf : Mem.Wf receiverPre.memory := by
    rw [← receiverMemory, ← entryMemory]
    exact memoryWf
  obtain ⟨supplyEntry, supplyStack, supplyWf, supplyState, supplyRun⟩ :=
    Blanc.ProrataWethVault.zeroArgCapacityBranch_revert receiverWf
      receiverStack receiverRun
  obtain ⟨supply, branchEntry, -, branchStack, supplyWindow, -, branchState,
      branchRun⟩ :=
    Blanc.ProrataWethVault.capacitySupplyStaging_avoiding supplyWf
      supplyStack supplyRun
  obtain ⟨stable, readEntry, readStack, readPreserves, readState, readRun⟩ :=
    Blanc.ProrataWethVault.stableCapacityBranch_revert supplyWindow
      branchStack branchRun
  have readSupplyWindow := readPreserves supplyWindow
  have readConfig := config.of_state_eq' (entryState.trans
    (receiverState.trans (supplyState.trans (branchState.trans readState))))
  obtain ⟨word, arithmeticPre, wordStack, arithmeticWf, arithmeticPreserves,
      arithmeticRun⟩ :=
    readTotalAssets_avoiding readConfig hfork readSupplyWindow.1 readRun
  exact Blanc.ProrataWethVault.maxDeposit_postTotalAssets_no_revert
    arithmeticWf (reads_self arithmeticPre)
    (arithmeticPreserves (by decide +kernel) readSupplyWindow) stable
    wordStack vault_returnWord_lookup arithmeticRun

/-- **The `maxMint` view reverts only through a refused `balanceOf`.** -/
theorem maxMint_revert_visits_refused_weth_child
    {sevm : Sevm} {pre d : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf pre.memory)
    (selectorEq : Sevm.selector sevm = selector "maxMint" [.address])
    (valueZero : sevm.value = 0)
    (argsPresent :
      B256.ltCheck sevm.data.length.toB256 (Nat.toB256 (4 + 32 * 1)) = 0)
    (argValid : ValidAdr (Sevm.argWord sevm 0))
    (walk : Prog.RunCompiledTo sevm pre Blanc.ProrataWethVault.vault
      (.error (.revert, d))) :
    Prog.RunCompiledToVisiting WethChildRefused sevm pre
      Blanc.ProrataWethVault.vault (.error (.revert, d)) := by
  refine vault_revert_visits_of_body selectorEq
    (List.mem_of_getElem? (i := 19) rfl) valueZero argsPresent walk ?_
  intro bodyPre entryState entryMemory run
  unfold Blanc.ProrataWethVault.maxMint at run
  obtain ⟨receiverPre, receiverStack, receiverState, receiverMemory,
      receiverRun⟩ := canonicalAddressArg_avoiding argValid nil_pref run
  have receiverWf : Mem.Wf receiverPre.memory := by
    rw [← receiverMemory, ← entryMemory]
    exact memoryWf
  obtain ⟨supplyEntry, supplyStack, supplyWf, supplyState, supplyRun⟩ :=
    Blanc.ProrataWethVault.zeroArgCapacityBranch_revert receiverWf
      receiverStack receiverRun
  obtain ⟨supply, branchEntry, -, branchStack, supplyWindow, -, branchState,
      branchRun⟩ :=
    Blanc.ProrataWethVault.capacitySupplyStaging_avoiding supplyWf
      supplyStack supplyRun
  obtain ⟨-, readEntry, readStack, readPreserves, readState, readRun⟩ :=
    Blanc.ProrataWethVault.stableCapacityBranch_revert supplyWindow
      branchStack branchRun
  have readSupplyWindow := readPreserves supplyWindow
  have readConfig := config.of_state_eq' (entryState.trans
    (receiverState.trans (supplyState.trans (branchState.trans readState))))
  obtain ⟨word, arithmeticPre, wordStack, arithmeticWf, arithmeticPreserves,
      arithmeticRun⟩ :=
    readTotalAssets_avoiding readConfig hfork readSupplyWindow.1 readRun
  exact Blanc.ProrataWethVault.maxMint_postTotalAssets_no_revert
    arithmeticWf (reads_self arithmeticPre)
    (arithmeticPreserves (by decide +kernel) readSupplyWindow)
    wordStack vault_returnWord_lookup vault_maxMintCap_lookup arithmeticRun

/-- **The `maxWithdraw` view reverts only through a refused `balanceOf`.** -/
theorem maxWithdraw_revert_visits_refused_weth_child
    {sevm : Sevm} {pre d : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf pre.memory)
    (selectorEq : Sevm.selector sevm = selector "maxWithdraw" [.address])
    (valueZero : sevm.value = 0)
    (argsPresent :
      B256.ltCheck sevm.data.length.toB256 (Nat.toB256 (4 + 32 * 1)) = 0)
    (argValid : ValidAdr (Sevm.argWord sevm 0))
    (walk : Prog.RunCompiledTo sevm pre Blanc.ProrataWethVault.vault
      (.error (.revert, d))) :
    Prog.RunCompiledToVisiting WethChildRefused sevm pre
      Blanc.ProrataWethVault.vault (.error (.revert, d)) := by
  refine vault_revert_visits_of_body selectorEq
    (List.mem_of_getElem? (i := 21) rfl) valueZero argsPresent walk ?_
  intro bodyPre entryState entryMemory run
  unfold Blanc.ProrataWethVault.maxWithdraw at run
  obtain ⟨ownerPre, ownerStack, ownerState, ownerMemory, ownerRun⟩ :=
    canonicalAddressArg_avoiding argValid nil_pref run
  have ownerWf : Mem.Wf ownerPre.memory := by
    rw [← ownerMemory, ← entryMemory]
    exact memoryWf
  obtain ⟨amount, supplyEntry, -, supplyStack, amountWindow, amountState,
      supplyRun⟩ :=
    Blanc.ProrataWethVault.capacityAmountStaging_avoiding ownerWf ownerStack
      ownerRun
  obtain ⟨supply, branchEntry, -, branchStack, supplyWindow, supplyPreserves,
      branchState, branchRun⟩ :=
    Blanc.ProrataWethVault.capacitySupplyStaging_avoiding amountWindow.1
      supplyStack supplyRun
  have branchAmountWindow :=
    supplyPreserves (Or.inl (by decide +kernel)) amountWindow
  obtain ⟨stable, readEntry, readStack, readPreserves, readState, readRun⟩ :=
    Blanc.ProrataWethVault.stableCapacityBranch_revert supplyWindow
      branchStack branchRun
  have readSupplyWindow := readPreserves supplyWindow
  have readAmountWindow := readPreserves branchAmountWindow
  have readConfig := config.of_state_eq' (entryState.trans
    (ownerState.trans (amountState.trans (branchState.trans readState))))
  obtain ⟨word, arithmeticPre, wordStack, arithmeticWf, arithmeticPreserves,
      arithmeticRun⟩ :=
    readTotalAssets_avoiding readConfig hfork readSupplyWindow.1 readRun
  exact Blanc.ProrataWethVault.maxWithdraw_postTotalAssets_no_revert
    arithmeticWf (reads_self arithmeticPre)
    (arithmeticPreserves (by decide +kernel) readAmountWindow)
    (arithmeticPreserves (by decide +kernel) readSupplyWindow) stable
    wordStack vault_returnWord_lookup arithmeticRun

/-- **The `maxRedeem` view has no reverting walk at all.**  It makes no
external call. -/
theorem maxRedeem_no_reverting_walk
    {sevm : Sevm} {pre d : Devm}
    (selectorEq : Sevm.selector sevm = selector "maxRedeem" [.address])
    (valueZero : sevm.value = 0)
    (argsPresent :
      B256.ltCheck sevm.data.length.toB256 (Nat.toB256 (4 + 32 * 1)) = 0)
    (argValid : ValidAdr (Sevm.argWord sevm 0))
    (walk : Prog.RunCompiledTo sevm pre Blanc.ProrataWethVault.vault
      (.error (.revert, d))) :
    False := by
  obtain ⟨entry, -, run⟩ := walk
  obtain ⟨bodyPre, -, -, bodyRun⟩ :=
    vault_endpoint_avoiding selectorEq (List.mem_of_getElem? (i := 22) rfl)
      valueZero argsPresent (Func.RunCompiledToAvoiding.of_bot run)
  unfold Blanc.ProrataWethVault.maxRedeem at bodyRun
  obtain ⟨readPre, -, -, -, readRun⟩ :=
    canonicalAddressArg_avoiding argValid nil_pref bodyRun
  have free : Func.revertFreeIn [Blanc.ProrataWethVault.returnWordSlot]
      (arg 0 +++ sload ::: Blanc.ProrataWethVault.returnWord) = true := by
    simp [Blanc.ProrataWethVault.returnWord, returnMemoryRange, Func.return_,
      Func.revertFreeIn_prepend, Func.revertFreeIn]
  exact Func.RunCompiledTo.not_revert_of_revertFreeIn
    (Blanc.ProrataWethVault.returnWord_table_revertFree vault_returnWord_lookup)
    readRun.1 free d rfl

end Blanc.Composition.ProrataWethVault
