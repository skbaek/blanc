-- ProrataWethVaultNonrevert.lean : successful vault flows stay within max*.

import Blanc.ProrataWethVaultMaxArithmetic
import Blanc.Composition.ProrataWethVaultInbound
import Blanc.Composition.ProrataWethVaultOutbound
import Blanc.Composition.ProrataWethVaultNonrevertViews
import Blanc.Composition.ProrataWethVaultTerminals

namespace Blanc.Composition.ProrataWethVault

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv
open Source

/-- **A successful `deposit` stays within `maxDeposit`.**  Together with
`deposit_exec_revert_visits_refused_weth_child`, `maxDeposit(receiver)` is
exactly the largest amount the vault's own guards accept. -/
theorem deposit_success_within_maxDeposit
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq :
      Sevm.selector sevm = selector "deposit" [.uint256, .address]) :
    (Sevm.argWord sevm 0).toNat ≤
      Blanc.ProrataWethVault.maxDepositViewN (Sevm.argWord sevm 1).toNat
        ((pre.state.getStor wethAccount).get
          sevm.currentTarget.toB256).toNat
        (Devm.getStorVal pre sevm.currentTarget
          Blanc.ProrataWethVault.supplySlot).toNat := by
  obtain ⟨-, supply, supplyEq, stable, quoteFits, -, -, receiverNonzero,
      roomFits, -⟩ := deposit_compiled_effect config memoryWf run selectorEq
  have supplyNat : supply.toNat =
      (Devm.getStorVal pre sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot).toNat :=
    congrArg B256.toNat supplyEq
  have amountWord : (Sevm.argWord sevm 0).toNat ≤
      maxWordN := by
    have amountLt : (Sevm.argWord sevm 0).toNat < wordModulusN :=
      B256.toNat_lt _
    unfold maxWordN
    omega
  have receiverNonzeroNat : (Sevm.argWord sevm 1).toNat ≠ 0 :=
    B256.toNat_ne_zero receiverNonzero
  rw [← supplyNat]
  rw [Blanc.ProrataWethVault.maxDepositViewN_eq_of_stable
    receiverNonzeroNat stable]
  apply (Blanc.ProrataWethVault.le_maxDepositN_iff amountWord).2
  rw [B256.toNat_toB256_of_lt quoteFits] at roomFits
  exact roomFits

theorem mint_success_within_maxMint
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq :
      Sevm.selector sevm = selector "mint" [.uint256, .address]) :
    (Sevm.argWord sevm 0).toNat ≤
      Blanc.ProrataWethVault.maxMintViewN (Sevm.argWord sevm 1).toNat
        ((pre.state.getStor wethAccount).get
          sevm.currentTarget.toB256).toNat
        (Devm.getStorVal pre sevm.currentTarget
          Blanc.ProrataWethVault.supplySlot).toNat := by
  obtain ⟨-, supply, supplyEq, stable, quoteFits, -, -, receiverNonzero,
      roomFits, -⟩ := mint_compiled_effect config memoryWf run selectorEq
  have supplyNat : supply.toNat =
      (Devm.getStorVal pre sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot).toNat :=
    congrArg B256.toNat supplyEq
  have receiverNonzeroNat : (Sevm.argWord sevm 1).toNat ≠ 0 :=
    B256.toNat_ne_zero receiverNonzero
  rw [← supplyNat]
  rw [Blanc.ProrataWethVault.maxMintViewN_eq_of_stable
    receiverNonzeroNat stable]
  apply (Blanc.ProrataWethVault.le_maxMintN_iff _ _ _).2
  refine ⟨roomFits, ?_⟩
  unfold maxWordN
  omega

theorem withdraw_success_within_maxWithdraw
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm =
      selector "withdraw" [.uint256, .address, .address]) :
    (Sevm.argWord sevm 0).toNat ≤
      Blanc.ProrataWethVault.maxWithdrawViewN
        (Devm.getStorVal pre sevm.currentTarget (Sevm.argWord sevm 2)).toNat
        ((pre.state.getStor wethAccount).get
          sevm.currentTarget.toB256).toNat
        (Devm.getStorVal pre sevm.currentTarget
          Blanc.ProrataWethVault.supplySlot).toNat := by
  obtain ⟨-, supply, supplyEq, stable, quoteFits, -, -, -, -, -, covered, -, -⟩ :=
    withdraw_compiled_effect config memoryWf run selectorEq
  have supplyNat : supply.toNat =
      (Devm.getStorVal pre sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot).toNat :=
    congrArg B256.toNat supplyEq
  have amountWord : (Sevm.argWord sevm 0).toNat ≤
      maxWordN := by
    have amountLt : (Sevm.argWord sevm 0).toNat < wordModulusN :=
      B256.toNat_lt _
    unfold maxWordN
    omega
  rw [← supplyNat]
  unfold Blanc.ProrataWethVault.maxWithdrawViewN
  rw [if_neg (Nat.not_lt_of_ge stable)]
  apply (Nat.le_min).2
  constructor
  · exact amountWord
  · apply (Blanc.ProrataWethVault.le_maxWithdrawN_iff _ _ _ _).2
    rw [B256.toNat_toB256_of_lt quoteFits] at covered
    exact covered

theorem redeem_success_within_maxRedeem
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm =
      selector "redeem" [.uint256, .address, .address]) :
    (Sevm.argWord sevm 0).toNat ≤
      Blanc.ProrataWethVault.maxRedeemN
        (Devm.getStorVal pre sevm.currentTarget (Sevm.argWord sevm 2)).toNat := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, burnable, -⟩ :=
    redeem_compiled_effect config memoryWf run selectorEq
  simpa [Blanc.ProrataWethVault.maxRedeemN] using burnable

/-! ## Exec-level revert cause of the capacity views

The walk-level cores in `…NonrevertViews.lean`, applied to the reverting
frame's own gas-exact walk (`Prog.runCompiledTo_of_exec_revert`).  So these
are statements about the total interpreter's actual outcome. -/

theorem maxDeposit_exec_revert_visits_refused_weth_child
    {sevm : Sevm} {pre d : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (codeEq : some sevm.code.toList = Prog.compile Blanc.ProrataWethVault.vault)
    (selectorEq : Sevm.selector sevm = selector "maxDeposit" [.address])
    (valueZero : sevm.value = 0)
    (argsPresent :
      B256.ltCheck sevm.data.length.toB256 (Nat.toB256 (4 + 32 * 1)) = 0)
    (argValid : ValidAdr (Sevm.argWord sevm 0))
    (reverted : exec ⟨0, sevm, pre⟩ = .error (.revert, d)) :
    Prog.RunCompiledToVisiting WethChildRefused sevm pre
      Blanc.ProrataWethVault.vault (.error (.revert, d)) := by
  exact maxDeposit_revert_visits_refused_weth_child config memoryWf selectorEq
    valueZero argsPresent argValid
    (Prog.runCompiledTo_of_exec_revert vault_prog_pcFree codeEq reverted)

theorem maxMint_exec_revert_visits_refused_weth_child
    {sevm : Sevm} {pre d : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (codeEq : some sevm.code.toList = Prog.compile Blanc.ProrataWethVault.vault)
    (selectorEq : Sevm.selector sevm = selector "maxMint" [.address])
    (valueZero : sevm.value = 0)
    (argsPresent :
      B256.ltCheck sevm.data.length.toB256 (Nat.toB256 (4 + 32 * 1)) = 0)
    (argValid : ValidAdr (Sevm.argWord sevm 0))
    (reverted : exec ⟨0, sevm, pre⟩ = .error (.revert, d)) :
    Prog.RunCompiledToVisiting WethChildRefused sevm pre
      Blanc.ProrataWethVault.vault (.error (.revert, d)) := by
  exact maxMint_revert_visits_refused_weth_child config memoryWf selectorEq
    valueZero argsPresent argValid
    (Prog.runCompiledTo_of_exec_revert vault_prog_pcFree codeEq reverted)

theorem maxWithdraw_exec_revert_visits_refused_weth_child
    {sevm : Sevm} {pre d : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (codeEq : some sevm.code.toList = Prog.compile Blanc.ProrataWethVault.vault)
    (selectorEq : Sevm.selector sevm = selector "maxWithdraw" [.address])
    (valueZero : sevm.value = 0)
    (argsPresent :
      B256.ltCheck sevm.data.length.toB256 (Nat.toB256 (4 + 32 * 1)) = 0)
    (argValid : ValidAdr (Sevm.argWord sevm 0))
    (reverted : exec ⟨0, sevm, pre⟩ = .error (.revert, d)) :
    Prog.RunCompiledToVisiting WethChildRefused sevm pre
      Blanc.ProrataWethVault.vault (.error (.revert, d)) := by
  exact maxWithdraw_revert_visits_refused_weth_child config memoryWf
    selectorEq valueZero argsPresent argValid
    (Prog.runCompiledTo_of_exec_revert vault_prog_pcFree codeEq reverted)

/-- **The deployed `maxRedeem` view never reverts.**  Only an exceptional
halt (out of gas) remains. -/
theorem maxRedeem_exec_never_reverts
    {sevm : Sevm} {pre : Devm}
    (codeEq : some sevm.code.toList = Prog.compile Blanc.ProrataWethVault.vault)
    (selectorEq : Sevm.selector sevm = selector "maxRedeem" [.address])
    (valueZero : sevm.value = 0)
    (argsPresent :
      B256.ltCheck sevm.data.length.toB256 (Nat.toB256 (4 + 32 * 1)) = 0)
    (argValid : ValidAdr (Sevm.argWord sevm 0))
    (d : Devm) :
    exec ⟨0, sevm, pre⟩ ≠ .error (.revert, d) := by
  intro reverted
  exact maxRedeem_no_reverting_walk selectorEq valueZero argsPresent argValid
    (Prog.runCompiledTo_of_exec_revert vault_prog_pcFree codeEq reverted)

end Blanc.Composition.ProrataWethVault
