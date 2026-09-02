-- ProrataWethVaultViews.lean : exact local views of the compiled vault.

import Blanc.ProrataWethVaultFunctional
import Blanc.Ladder

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

namespace ProrataWethVault

/-!
# Local compiled views

These views are entirely vault-local: they read constants or the share ledger
and never cross the WETH boundary.  The WETH-backed views live downstream in
the composition owner.  Every public theorem starts from the compiled vault
program and uses the exact selector/body seam.
-/

/-- Exact observation made by a successful read-only word endpoint. -/
def WordViewEffect (word : B256) (pre post : Devm) : Prop :=
  ReturnsWord word post ∧
    Devm.getStor pre = Devm.getStor post ∧
    pre.logs = post.logs

private theorem returnConstant_effect
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {word : B256}
    (run : Func.RunCompiledTo fs sevm pre (returnConstant word) (.ok post)) :
    WordViewEffect word pre post := by
  have sourceRun : Func.Run fs sevm pre (returnConstant word) post :=
    Func.Run.of_runCompiled (Func.RunCompiled.of_runCompiledTo_ok run)
  have storage : Devm.getStor pre = Devm.getStor post :=
    Func.of_inv Devm.getStor Devm.getStor (by
      unfold returnConstant returnWord
      func_inv) sourceRun
  have logs : pre.logs = post.logs :=
    Func.of_inv Devm.logs Devm.logs (by
      unfold returnConstant returnWord
      func_inv) sourceRun
  simp only [returnConstant] at sourceRun
  obtain ⟨afterPush, pushRun, returnRun⟩ := of_run_next sourceRun
  have wordPrefix : word :: [] <<+ afterPush.stack :=
    prefix_of_push (of_run_pushB256 pushRun) nil_pref
  have output : ReturnsWord word post := by
    simpa only [returnWord] using
      (returnsWord_of_storeReturn wordPrefix returnRun).1
  exact ⟨output, storage, logs⟩

private theorem totalSupply_body_effect
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (run : Func.RunCompiledTo fs sevm pre totalSupply (.ok post)) :
    WordViewEffect
      (Devm.getStorVal pre sevm.currentTarget supplySlot) pre post := by
  have sourceRun : Func.Run fs sevm pre totalSupply post :=
    Func.Run.of_runCompiled (Func.RunCompiled.of_runCompiledTo_ok run)
  have storage : Devm.getStor pre = Devm.getStor post :=
    Func.of_inv Devm.getStor Devm.getStor (by
      unfold totalSupply pushSupplySlot returnWord
      func_inv) sourceRun
  have logs : pre.logs = post.logs :=
    Func.of_inv Devm.logs Devm.logs (by
      unfold totalSupply pushSupplySlot returnWord
      func_inv) sourceRun
  unfold totalSupply at sourceRun
  rcases of_run_prepend pushSupplySlot _ sourceRun with
    ⟨slotPre, slotRun, sourceRun⟩
  rcases Line.of_run_cons slotRun with ⟨zeroPre, qzero, slotRun⟩
  rcases Line.of_run_cons slotRun with ⟨slotPre', qnot, hnil⟩
  cases hnil
  have hnotZero : ~~~(0 : B256) = B256.max := by decide +kernel
  have pzero : (0 : B256) :: [] <<+ zeroPre.stack :=
    prefix_of_push (of_run_pushB256 qzero) nil_pref
  have pslot : supplySlot :: [] <<+ slotPre.stack := by
    unfold supplySlot
    rw [← hnotZero]
    exact prefix_of_not qnot pzero
  obtain ⟨afterLoad, loadRun, returnRun⟩ := of_run_next sourceRun
  rcases prefix_of_sload loadRun pslot with
    ⟨loaded, loadedPrefix, loadedEq⟩
  have output := (returnsWord_of_storeReturn loadedPrefix (by
    simpa only [returnWord] using returnRun)).1
  rw [loadedEq] at output
  have entryStorage : Devm.getStor pre = Devm.getStor slotPre :=
    Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons qzero (Line.Run.cons qnot Line.Run.nil))
  change ReturnsWord
    ((Devm.getStor slotPre sevm.currentTarget).get supplySlot) post at output
  rw [← congrFun entryStorage sevm.currentTarget] at output
  exact ⟨output, storage, logs⟩

private theorem lift_word_view
    {pre bodyPre post : Devm} {word : B256}
    (entryState : pre.state = bodyPre.state)
    (entryLogs : pre.logs = bodyPre.logs)
    (effect : WordViewEffect word bodyPre post) :
    WordViewEffect word pre post := by
  rcases effect with ⟨output, storage, logs⟩
  refine ⟨output, ?_, entryLogs.trans logs⟩
  exact (funext (getStor_eq_of_state_eq entryState)).trans storage

/-- A successful canonical-address guard reaches its body and proves that the
selected ABI word is address-shaped.  The proof stays on the compiled walk so
downstream effects retain the exact vault auxiliary table. -/
private theorem canonicalAddressArg_body_of_ok
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {index : B256} {body : Func} {tail : Stack}
    (hp : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (canonicalAddressArg index body) (.ok post)) :
    ∃ bodyPre,
      ValidAdr (Sevm.argWord sevm index) ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok post) ∧
      tail <<+ bodyPre.stack ∧
      pre.state = bodyPre.state ∧
      pre.logs = bodyPre.logs := by
  unfold canonicalAddressArg at run
  obtain ⟨afterArg, argLine, run⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨guardPost, guardLine, branchRun⟩ :=
    runCompiledTo_prepend_inv run
  have argPrefix : Sevm.argWord sevm index :: tail <<+ afterArg.stack :=
    prefix_of_arg hp argLine
  obtain ⟨guardWord, guardPrefix, guardValid⟩ :=
    of_check_non_address argPrefix guardLine
  rcases runCompiledTo_branch_inv branchRun with bodyRoute | revertRoute
  · rcases bodyRoute with ⟨bodyPre, guardStack, guardPop, bodyRun⟩
    have zeroPrefix : (0 : B256) :: [] <<+ guardPost.stack :=
      ⟨bodyPre.stack, by simpa [Split] using guardStack⟩
    have guardZero : guardWord = 0 :=
      pref_head_unique guardPrefix zeroPrefix
    have bodyPrefix : tail <<+ bodyPre.stack :=
      (popBurn_pref (Devm.PopBurn.of_popBurnBy guardPop) guardPrefix).2
    exact ⟨bodyPre, guardValid.mp guardZero, bodyRun, bodyPrefix,
      (Line.of_inv Devm.state (by line_inv) argLine).trans
        ((Line.of_inv Devm.state (by line_inv) guardLine).trans
          guardPop.state),
      (Line.of_inv Devm.logs (by line_inv) argLine).trans
        ((Line.of_inv Devm.logs (by line_inv) guardLine).trans
          guardPop.logs)⟩
  · rcases revertRoute with ⟨_, revertPre, -, -, -, revertRun⟩
    rcases runCompiledTo_rev_inv revertRun with ⟨_, impossible, -⟩
    cases impossible

/-- Exact read-only effect of the storage-word body shared by `balanceOf` and
`maxRedeem`. -/
private theorem argStorageWord_effect
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {index : B256}
    (run : Func.RunCompiledTo fs sevm pre
      (arg index +++ sload ::: returnWord) (.ok post)) :
    WordViewEffect
      (Devm.getStorVal pre sevm.currentTarget (Sevm.argWord sevm index))
      pre post := by
  have sourceRun : Func.Run fs sevm pre
      (arg index +++ sload ::: returnWord) post :=
    Func.Run.of_runCompiled (Func.RunCompiled.of_runCompiledTo_ok run)
  have storage : Devm.getStor pre = Devm.getStor post :=
    Func.of_inv Devm.getStor Devm.getStor (by
      unfold returnWord
      func_inv) sourceRun
  have logs : pre.logs = post.logs :=
    Func.of_inv Devm.logs Devm.logs (by
      unfold returnWord
      func_inv) sourceRun
  rcases of_run_prepend (arg index) _ sourceRun with
    ⟨afterArg, argRun, sourceRun⟩
  have argPrefix : Sevm.argWord sevm index :: [] <<+ afterArg.stack :=
    prefix_of_arg nil_pref argRun
  rcases of_run_next sourceRun with ⟨afterLoad, loadRun, returnRun⟩
  rcases prefix_of_sload loadRun argPrefix with
    ⟨loaded, loadedPrefix, loadedEq⟩
  obtain ⟨output, -⟩ := returnsWord_of_storeReturn loadedPrefix (by
    simpa only [returnWord] using returnRun)
  rw [loadedEq] at output
  have entryStorage : Devm.getStor pre = Devm.getStor afterArg :=
    Line.of_inv Devm.getStor (by line_inv) argRun
  change ReturnsWord
    ((Devm.getStor afterArg sevm.currentTarget).get
      (Sevm.argWord sevm index)) post at output
  rw [← entryStorage] at output
  exact ⟨output, storage, logs⟩

private theorem lift_storage_word_view
    {pre bodyPre post : Devm} {target : Adr} {slot : B256}
    (entryState : pre.state = bodyPre.state)
    (entryLogs : pre.logs = bodyPre.logs)
    (effect : WordViewEffect
      (Devm.getStorVal bodyPre target slot) bodyPre post) :
    WordViewEffect (Devm.getStorVal pre target slot) pre post := by
  rcases effect with ⟨output, storage, logs⟩
  have entryStorage : Devm.getStor pre = Devm.getStor bodyPre :=
    funext (getStor_eq_of_state_eq entryState)
  refine ⟨?_, entryStorage.trans storage, entryLogs.trans logs⟩
  change ReturnsWord ((Devm.getStor pre target).get slot) post
  change ReturnsWord ((Devm.getStor bodyPre target).get slot) post at output
  rw [entryStorage]
  exact output

/-! ## Public compiled selectors -/

/-- `asset()` returns the exact configured WETH address word. -/
theorem asset_compiled_effect
    {sevm : Sevm} {pre post : Devm}
    (run : Prog.RunCompiled sevm pre vault post)
    (hselector : Sevm.selector sevm = selector "asset" []) :
    sevm.value = 0 ∧ WordViewEffect assetAddress pre post := by
  have hmember : (selector "asset" [], routed 0 asset) ∈ vaultFuncs := by
    simp [vaultFuncs]
  rcases runCompiled_enters_body_compiled_logs run hselector hmember with
    ⟨bodyPre, hvalue, -, entryState, -, entryLogs, -, bodyRun⟩
  exact ⟨hvalue,
    lift_word_view entryState entryLogs (returnConstant_effect bodyRun)⟩

/-- `decimals()` returns the frozen 21-decimal share precision. -/
theorem decimals_compiled_effect
    {sevm : Sevm} {pre post : Devm}
    (run : Prog.RunCompiled sevm pre vault post)
    (hselector : Sevm.selector sevm = selector "decimals" []) :
    sevm.value = 0 ∧ WordViewEffect 21 pre post := by
  have hmember :
      (selector "decimals" [], routed 0 decimals) ∈ vaultFuncs := by
    simp [vaultFuncs]
  rcases runCompiled_enters_body_compiled_logs run hselector hmember with
    ⟨bodyPre, hvalue, -, entryState, -, entryLogs, -, bodyRun⟩
  exact ⟨hvalue,
    lift_word_view entryState entryLogs (returnConstant_effect bodyRun)⟩

/-- `totalSupply()` returns the exact share-supply storage word. -/
theorem totalSupply_compiled_effect
    {sevm : Sevm} {pre post : Devm}
    (run : Prog.RunCompiled sevm pre vault post)
    (hselector : Sevm.selector sevm = selector "totalSupply" []) :
    sevm.value = 0 ∧
      WordViewEffect
        (Devm.getStorVal pre sevm.currentTarget supplySlot) pre post := by
  have hmember :
      (selector "totalSupply" [], routed 0 totalSupply) ∈ vaultFuncs := by
    simp [vaultFuncs]
  rcases runCompiled_enters_body_compiled_logs run hselector hmember with
    ⟨bodyPre, hvalue, -, entryState, -, entryLogs, -, bodyRun⟩
  have effect := totalSupply_body_effect bodyRun
  have entryStorage : Devm.getStor pre = Devm.getStor bodyPre :=
    funext (getStor_eq_of_state_eq entryState)
  have effect' : WordViewEffect
      (Devm.getStorVal pre sevm.currentTarget supplySlot) bodyPre post := by
    rcases effect with ⟨output, storage, logs⟩
    refine ⟨?_, storage, logs⟩
    change ReturnsWord
      ((Devm.getStor pre sevm.currentTarget).get supplySlot) post
    change ReturnsWord
      ((Devm.getStor bodyPre sevm.currentTarget).get supplySlot) post at output
    rw [entryStorage]
    exact output
  exact ⟨hvalue, lift_word_view entryState entryLogs effect'⟩

/-- `balanceOf(account)` accepts exactly address-shaped account words and
returns the corresponding share-ledger word. -/
theorem balanceOf_compiled_effect
    {sevm : Sevm} {pre post : Devm}
    (run : Prog.RunCompiled sevm pre vault post)
    (hselector :
      Sevm.selector sevm = selector "balanceOf" [.address]) :
    sevm.value = 0 ∧
      ValidAdr (Sevm.argWord sevm 0) ∧
      WordViewEffect
        (Devm.getStorVal pre sevm.currentTarget (Sevm.argWord sevm 0))
        pre post := by
  have hmember :
      (selector "balanceOf" [.address], routed 1 balanceOf) ∈
        vaultFuncs := by
    simp [vaultFuncs]
  rcases runCompiled_enters_body_compiled_logs run hselector hmember with
    ⟨guardPre, hvalue, -, entryState, -, entryLogs, -, guardRun⟩
  rcases canonicalAddressArg_body_of_ok nil_pref guardRun with
    ⟨bodyPre, hvalid, bodyRun, -, guardState, guardLogs⟩
  exact ⟨hvalue, hvalid,
    lift_storage_word_view (entryState.trans guardState)
      (entryLogs.trans guardLogs) (argStorageWord_effect bodyRun)⟩

/-- `maxRedeem(owner)` is the exact share balance of an address-shaped owner
word; in particular the zero address remains an admitted read key. -/
theorem maxRedeem_compiled_effect
    {sevm : Sevm} {pre post : Devm}
    (run : Prog.RunCompiled sevm pre vault post)
    (hselector :
      Sevm.selector sevm = selector "maxRedeem" [.address]) :
    sevm.value = 0 ∧
      ValidAdr (Sevm.argWord sevm 0) ∧
      WordViewEffect
        (Devm.getStorVal pre sevm.currentTarget (Sevm.argWord sevm 0))
        pre post := by
  have hmember :
      (selector "maxRedeem" [.address], routed 1 maxRedeem) ∈
        vaultFuncs := by
    simp [vaultFuncs]
  rcases runCompiled_enters_body_compiled_logs run hselector hmember with
    ⟨guardPre, hvalue, -, entryState, -, entryLogs, -, guardRun⟩
  rcases canonicalAddressArg_body_of_ok nil_pref guardRun with
    ⟨bodyPre, hvalid, bodyRun, -, guardState, guardLogs⟩
  exact ⟨hvalue, hvalid,
    lift_storage_word_view (entryState.trans guardState)
      (entryLogs.trans guardLogs) (argStorageWord_effect bodyRun)⟩

end ProrataWethVault

end Blanc
