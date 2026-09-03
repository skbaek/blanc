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

/-- Exact observation made by a successful read-only dynamic-byte endpoint. -/
def BytesViewEffect (output : Bytes) (pre post : Devm) : Prop :=
  Devm.output post = output ∧
    Devm.getStor pre = Devm.getStor post ∧
    pre.logs = post.logs

/-- Canonical three-word ABI encoding used by the vault's short strings. -/
def shortStringOutput (word shift length : B256) : Bytes :=
  (32 : B256).toBytes ++ length.toBytes ++
    (word <<< shift.toNat).toBytes

def nameOutput : Bytes :=
  shortStringOutput
    (Blanc.String.toBytes "PRORATA WETH Vault").toB256 112 18

def symbolOutput : Bytes :=
  shortStringOutput (Blanc.String.toBytes "prWETH").toB256 208 6

/-- Exact raw allowance key computed by the vault from canonical ABI words. -/
def allowanceKey (owner spender : B256) : B256 :=
  Bytes.keccak (owner.toBytes ++ spender.toBytes)

private lemma slice_three_words (image : Bytes) (a b c : B256) :
    (Bytes.writeAt
      (Bytes.writeAt
        (Bytes.writeAt image 0 a.toBytes)
        32 b.toBytes)
      64 c.toBytes).sliceD 0 96 0 =
        a.toBytes ++ b.toBytes ++ c.toBytes := by
  rw [show (96 : Nat) = 64 + 32 by omega, List.sliceD_split]
  congr 1

/-- Exact body effect of the compact three-word ABI string emitter. -/
private theorem shortString_body_effect
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {word shift length : B256}
    (memoryWf : Mem.Wf pre.memory)
    (run : Func.RunCompiledTo fs sevm pre
      (pushB256 word ::: pushB256 shift ::: shl :::
        pushList [length, 32] +++
        mstoreAt 0 +++ mstoreAt 1 +++ mstoreAt 2 +++
        returnMemoryRange 0 96) (.ok post)) :
    BytesViewEffect (shortStringOutput word shift length) pre post := by
  have sourceRun : Func.Run fs sevm pre
      (pushB256 word ::: pushB256 shift ::: shl :::
        pushList [length, 32] +++
        mstoreAt 0 +++ mstoreAt 1 +++ mstoreAt 2 +++
        returnMemoryRange 0 96) post :=
    Func.Run.of_runCompiled (Func.RunCompiled.of_runCompiledTo_ok run)
  have storage : Devm.getStor pre = Devm.getStor post :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) sourceRun
  have logs : pre.logs = post.logs :=
    Func.of_inv Devm.logs Devm.logs (by func_inv) sourceRun

  obtain ⟨s1, pushWordRun, sourceRun⟩ := of_run_next sourceRun
  have p1 : word :: [] <<+ s1.stack :=
    prefix_of_push (of_run_pushB256 pushWordRun) nil_pref
  obtain ⟨s2, pushShiftRun, sourceRun⟩ := of_run_next sourceRun
  have p2 : shift :: word :: [] <<+ s2.stack :=
    prefix_of_push (of_run_pushB256 pushShiftRun) p1
  obtain ⟨s3, shiftRun, sourceRun⟩ := of_run_next sourceRun
  have p3 : (word <<< shift.toNat) :: [] <<+ s3.stack :=
    prefix_of_shl shiftRun p2
  obtain ⟨s4, pushHeaderRun, sourceRun⟩ :=
    of_run_prepend (pushList [length, 32]) _ sourceRun
  have pushHeaderLine := pushHeaderRun
  rcases Line.of_run_cons pushHeaderRun with
    ⟨afterLength, pushLengthRun, pushHeaderTail⟩
  rcases Line.of_run_cons pushHeaderTail with
    ⟨afterOffset, pushOffsetRun, emptyRun⟩
  cases emptyRun
  have p4 : length :: (word <<< shift.toNat) :: [] <<+
      afterLength.stack :=
    prefix_of_push (of_run_pushB256 pushLengthRun) p3
  have p5 : (32 : B256) :: length :: (word <<< shift.toNat) :: [] <<+
      s4.stack :=
    prefix_of_push (of_run_pushB256 pushOffsetRun) p4
  have entryMemory : pre.memory = s4.memory :=
    (((Ninst.Hinv.inv (f := Devm.memory) pushWordRun).trans
      (Ninst.Hinv.inv (f := Devm.memory) pushShiftRun)).trans
      (Ninst.Hinv.inv (f := Devm.memory) shiftRun)).trans
      (Line.of_inv Devm.memory (by line_inv) pushHeaderLine)
  have reads4 : Mem.Reads s4.memory pre.memory.data.toList := by
    rw [← entryMemory]
    intro index
    simp
  have wf4 : Mem.Wf s4.memory := by
    rw [← entryMemory]
    exact memoryWf

  obtain ⟨s5, storeOffsetRun, sourceRun⟩ :=
    of_run_prepend (mstoreAt 0) _ sourceRun
  obtain ⟨p6, wf5, reads5, -⟩ :=
    of_run_mstoreAt_image p5 wf4 reads4 storeOffsetRun
  obtain ⟨s6, storeLengthRun, sourceRun⟩ :=
    of_run_prepend (mstoreAt 1) _ sourceRun
  obtain ⟨p7, wf6, reads6, -⟩ :=
    of_run_mstoreAt_image p6 wf5 reads5 storeLengthRun
  obtain ⟨s7, storePayloadRun, sourceRun⟩ :=
    of_run_prepend (mstoreAt 2) _ sourceRun
  obtain ⟨p8, -, reads7, -⟩ :=
    of_run_mstoreAt_image p7 wf6 reads6 storePayloadRun
  simp only [show ((0 : B256) * 32).toNat = 0 by decide +kernel,
    show ((1 : B256) * 32).toNat = 32 by decide +kernel,
    show ((2 : B256) * 32).toNat = 64 by decide +kernel] at reads7

  obtain ⟨returnPre, returnRangeRun, returnRun⟩ :=
    of_run_prepend (pushList [96, 0]) _ sourceRun
  have returnRangeLine := returnRangeRun
  rcases Line.of_run_cons returnRangeRun with
    ⟨afterSize, pushSizeRun, returnRangeTail⟩
  rcases Line.of_run_cons returnRangeTail with
    ⟨afterStart, pushStartRun, emptyRun⟩
  cases emptyRun
  have p9 : (96 : B256) :: [] <<+ afterSize.stack :=
    prefix_of_push (of_run_pushB256 pushSizeRun) p8
  have p10 : (0 : B256) :: (96 : B256) :: [] <<+ returnPre.stack :=
    prefix_of_push (of_run_pushB256 pushStartRun) p9
  have returnMemory : s7.memory = returnPre.memory :=
    Line.of_inv Devm.memory (by line_inv) returnRangeLine
  have output : Devm.output post =
      shortStringOutput word shift length := by
    rw [(of_run_return_val p10 returnRun).1,
      show (0 : B256).toNat = 0 from rfl,
      show (96 : B256).toNat = 96 from rfl,
      Mem.Reads.read (returnMemory ▸ reads7) 0 96,
      slice_three_words]
    rfl
  exact ⟨output, storage, logs⟩

theorem returnConstant_effect
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

theorem lift_word_view
    {pre bodyPre post : Devm} {word : B256}
    (entryState : pre.state = bodyPre.state)
    (entryLogs : pre.logs = bodyPre.logs)
    (effect : WordViewEffect word bodyPre post) :
    WordViewEffect word pre post := by
  rcases effect with ⟨output, storage, logs⟩
  refine ⟨output, ?_, entryLogs.trans logs⟩
  exact (funext (getStor_eq_of_state_eq entryState)).trans storage

private theorem lift_bytes_view
    {pre bodyPre post : Devm} {output : Bytes}
    (entryState : pre.state = bodyPre.state)
    (entryLogs : pre.logs = bodyPre.logs)
    (effect : BytesViewEffect output bodyPre post) :
    BytesViewEffect output pre post := by
  rcases effect with ⟨result, storage, logs⟩
  refine ⟨result, ?_, entryLogs.trans logs⟩
  exact (funext (getStor_eq_of_state_eq entryState)).trans storage

/-- A successful canonical-address guard reaches its body and proves that the
selected ABI word is address-shaped.  The proof stays on the compiled walk so
downstream effects retain the exact vault auxiliary table. -/
theorem canonicalAddressArg_body_of_ok
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
      pre.memory = bodyPre.memory ∧
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
      (Line.of_inv Devm.memory (by line_inv) argLine).trans
        ((Line.of_inv Devm.memory (by line_inv) guardLine).trans
          guardPop.memory),
      (Line.of_inv Devm.logs (by line_inv) argLine).trans
        ((Line.of_inv Devm.logs (by line_inv) guardLine).trans
          guardPop.logs)⟩
  · rcases revertRoute with ⟨_, revertPre, -, -, -, revertRun⟩
    rcases runCompiledTo_revert_inv revertRun with ⟨_, impossible, -⟩
    cases impossible

/-- The vault's allowance guard retains the raw key below its collision flag.
When that flag is zero, the key is neither address-shaped nor the reserved
supply word. -/
theorem of_checkAllowanceSlotCollision
    {sevm : Sevm} {pre post : Devm} {key : B256} {tail : Stack}
    (hp : key :: tail <<+ pre.stack)
    (run : Line.Run sevm pre checkAllowanceSlotCollision post) :
    ∃ flag,
      flag :: key :: tail <<+ post.stack ∧
      (flag = 0 → ¬ ValidAdr key ∧ key ≠ supplySlot) := by
  simp only [checkAllowanceSlotCollision] at run
  rcases of_run_append _ run with ⟨beforeOr, guardRun, orRun⟩
  rcases of_run_append _ guardRun with
    ⟨beforeMax, addressRun, maxRun⟩
  rcases Line.of_run_cons addressRun with
    ⟨afterDup, dupRun, checkRun⟩
  rcases of_run_dup dupRun with ⟨word, wordAt, pushed⟩
  have wordEq : word = key := by
    have hget : pre.stack[(0 : Fin 16).val]? = some key :=
      Stack.nth_getElem (Stack.Nth.head key tail) hp
    rw [hget] at wordAt
    injection wordAt with wordAt
    exact wordAt.symm
  subst word
  have duplicated : key :: key :: tail <<+ afterDup.stack :=
    prefix_of_push pushed hp
  rcases of_check_address duplicated checkRun with
    ⟨addressFlag, addressPrefix, addressZero⟩
  rcases Line.of_run_cons maxRun with ⟨afterMaxDup, maxDupRun, isMaxRun⟩
  rcases of_run_dup maxDupRun with ⟨word, wordAt, pushed⟩
  have wordEq : word = key := by
    have hget : beforeMax.stack[(1 : Fin 16).val]? = some key :=
      Stack.nth_getElem
        (Stack.Nth.tail 0 key addressFlag (key :: tail)
          (Stack.Nth.head key tail))
        addressPrefix
    rw [hget] at wordAt
    injection wordAt with wordAt
    exact wordAt.symm
  subst word
  have maxInput : key :: addressFlag :: key :: tail <<+
      afterMaxDup.stack :=
    prefix_of_push pushed addressPrefix
  simp only [isMax] at isMaxRun
  rcases Line.of_run_cons isMaxRun with ⟨afterNot, notRun, isZeroRun⟩
  rcases Line.of_run_cons isZeroRun with ⟨afterMax, zeroRun, hnil⟩
  cases hnil
  have notPrefix : (~~~ key) :: addressFlag :: key :: tail <<+
      afterNot.stack := prefix_of_not notRun maxInput
  have maxPrefix : ((~~~ key) =? 0) :: addressFlag :: key :: tail <<+
      beforeOr.stack := prefix_of_iszero zeroRun notPrefix
  refine ⟨((~~~ key) =? 0) ||| addressFlag,
    prefix_of_or (of_run_singleton orRun) maxPrefix, ?_⟩
  intro guardZero
  rcases B256.of_or_eq_zero guardZero with ⟨maxZero, addressFlagZero⟩
  refine ⟨addressZero.mp addressFlagZero, ?_⟩
  intro keyEq
  rw [keyEq] at maxZero
  have maxIsOne : B256.eqCheck (~~~ supplySlot) 0 = 1 := by
    decide +kernel
  rw [maxIsOne] at maxZero
  exact B256.zero_ne_one maxZero.symm

/-- A successful compiled allowance-collision branch reaches its body with the
raw key retained and derives both namespace-separation facts from the executed
guard.

Family-visible rather than private: the outbound flows reach the same guard
through `spendAllowance`, and the walk is proved once here. -/
theorem allowanceCollisionGuard_body_of_ok
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {key : B256} {tail : Stack} {body : Func}
    (hp : key :: tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (checkAllowanceSlotCollision +++ (Func.revert <?> body)) (.ok post)) :
    ∃ bodyPre,
      ¬ ValidAdr key ∧ key ≠ supplySlot ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok post) ∧
      key :: tail <<+ bodyPre.stack ∧
      pre.state = bodyPre.state ∧
      pre.logs = bodyPre.logs ∧
      pre.memory = bodyPre.memory := by
  obtain ⟨guardPost, guardLine, branchRun⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨flag, guardPrefix, safeOfZero⟩ :=
    of_checkAllowanceSlotCollision hp guardLine
  rcases runCompiledTo_branch_inv branchRun with bodyRoute | revertRoute
  · rcases bodyRoute with ⟨bodyPre, guardStack, guardPop, bodyRun⟩
    have zeroPrefix : (0 : B256) :: [] <<+ guardPost.stack :=
      ⟨bodyPre.stack, by simpa [Split] using guardStack⟩
    have flagZero : flag = 0 :=
      pref_head_unique guardPrefix zeroPrefix
    rcases safeOfZero flagZero with ⟨notAddress, notSupply⟩
    have bodyPrefix : key :: tail <<+ bodyPre.stack :=
      (popBurn_pref (Devm.PopBurn.of_popBurnBy guardPop) guardPrefix).2
    exact ⟨bodyPre, notAddress, notSupply, bodyRun, bodyPrefix,
      (Line.of_inv Devm.state (by line_inv) guardLine).trans guardPop.state,
      (Line.of_inv Devm.logs (by line_inv) guardLine).trans guardPop.logs,
      (Line.of_inv Devm.memory (by line_inv) guardLine).trans
        guardPop.memory⟩
  · rcases revertRoute with ⟨_, revertPre, -, -, -, revertRun⟩
    rcases runCompiledTo_revert_inv revertRun with ⟨_, impossible, -⟩
    cases impossible

private theorem stackStorageWord_effect
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {key : B256} {tail : Stack}
    (hp : key :: tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (sload ::: returnWord) (.ok post)) :
    WordViewEffect (Devm.getStorVal pre sevm.currentTarget key) pre post := by
  have sourceRun : Func.Run fs sevm pre (sload ::: returnWord) post :=
    Func.Run.of_runCompiled (Func.RunCompiled.of_runCompiledTo_ok run)
  have storage : Devm.getStor pre = Devm.getStor post :=
    Func.of_inv Devm.getStor Devm.getStor (by
      unfold returnWord
      func_inv) sourceRun
  have logs : pre.logs = post.logs :=
    Func.of_inv Devm.logs Devm.logs (by
      unfold returnWord
      func_inv) sourceRun
  rcases of_run_next sourceRun with ⟨afterLoad, loadRun, returnRun⟩
  rcases prefix_of_sload loadRun hp with
    ⟨loaded, loadedPrefix, loadedEq⟩
  obtain ⟨output, -⟩ := returnsWord_of_storeReturn loadedPrefix (by
    simpa only [returnWord] using returnRun)
  rw [loadedEq] at output
  exact ⟨output, storage, logs⟩

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

private theorem lift_storage_word_view_of_storage
    {pre bodyPre post : Devm} {target : Adr} {slot : B256}
    (entryStorage : Devm.getStor pre = Devm.getStor bodyPre)
    (entryLogs : pre.logs = bodyPre.logs)
    (effect : WordViewEffect
      (Devm.getStorVal bodyPre target slot) bodyPre post) :
    WordViewEffect (Devm.getStorVal pre target slot) pre post := by
  rcases effect with ⟨output, storage, logs⟩
  refine ⟨?_, entryStorage.trans storage, entryLogs.trans logs⟩
  change ReturnsWord ((Devm.getStor pre target).get slot) post
  change ReturnsWord ((Devm.getStor bodyPre target).get slot) post at output
  rw [entryStorage]
  exact output

private theorem lift_storage_word_view
    {pre bodyPre post : Devm} {target : Adr} {slot : B256}
    (entryState : pre.state = bodyPre.state)
    (entryLogs : pre.logs = bodyPre.logs)
    (effect : WordViewEffect
      (Devm.getStorVal bodyPre target slot) bodyPre post) :
    WordViewEffect (Devm.getStorVal pre target slot) pre post :=
  lift_storage_word_view_of_storage
    (funext (getStor_eq_of_state_eq entryState)) entryLogs effect

/-- Exact body effect of the two-address allowance view.  Canonicality and
namespace separation are conclusions of the successful compiled walk; only
ordinary EVM memory well-formedness is supplied by the caller. -/
private theorem allowance_body_effect
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (memoryWf : Mem.Wf pre.memory)
    (run : Func.RunCompiledTo fs sevm pre allowance (.ok post)) :
    ValidAdr (Sevm.argWord sevm 0) ∧
      ValidAdr (Sevm.argWord sevm 1) ∧
      ¬ ValidAdr
        (allowanceKey (Sevm.argWord sevm 0) (Sevm.argWord sevm 1)) ∧
      allowanceKey (Sevm.argWord sevm 0) (Sevm.argWord sevm 1) ≠
        supplySlot ∧
      WordViewEffect
        (Devm.getStorVal pre sevm.currentTarget
          (allowanceKey (Sevm.argWord sevm 0) (Sevm.argWord sevm 1)))
        pre post := by
  unfold allowance at run
  rcases canonicalAddressArg_body_of_ok nil_pref run with
    ⟨ownerPre, ownerValid, ownerRun, -, ownerState, ownerMemory, ownerLogs⟩
  rcases canonicalAddressArg_body_of_ok nil_pref ownerRun with
    ⟨bodyPre, spenderValid, bodyRun, -, spenderState, spenderMemory,
      spenderLogs⟩
  have bodyMemory : pre.memory = bodyPre.memory :=
    ownerMemory.trans spenderMemory
  have bodyMemoryWf : Mem.Wf bodyPre.memory := by
    rw [← bodyMemory]
    exact memoryWf

  obtain ⟨afterOwnerArg, ownerArgRun, bodyRun⟩ :=
    runCompiledTo_prepend_inv bodyRun
  have ownerPrefix : Sevm.argWord sevm 0 :: [] <<+ afterOwnerArg.stack :=
    prefix_of_arg nil_pref ownerArgRun
  obtain ⟨afterOwnerStore, ownerStoreRun, bodyRun⟩ :=
    runCompiledTo_prepend_inv bodyRun
  obtain ⟨ownerTail, ownerStoreMemory⟩ :=
    of_run_mstoreAt_val ownerStoreRun ownerPrefix

  obtain ⟨afterSpenderArg, spenderArgRun, bodyRun⟩ :=
    runCompiledTo_prepend_inv bodyRun
  have spenderPrefix : Sevm.argWord sevm 1 :: [] <<+
      afterSpenderArg.stack :=
    prefix_of_arg ownerTail spenderArgRun
  obtain ⟨afterSpenderStore, spenderStoreRun, bodyRun⟩ :=
    runCompiledTo_prepend_inv bodyRun
  obtain ⟨spenderTail, spenderStoreMemory⟩ :=
    of_run_mstoreAt_val spenderStoreRun spenderPrefix

  obtain ⟨keccak256Pre, pushWindowRun, bodyRun⟩ :=
    runCompiledTo_prepend_inv bodyRun
  have pushWindowLine := pushWindowRun
  simp only [pushList, List.map] at pushWindowRun
  rcases Line.of_run_cons pushWindowRun with
    ⟨afterPush64, push64Run, pushWindowRun⟩
  rcases Line.of_run_cons pushWindowRun with
    ⟨afterPush0, push0Run, hnil⟩
  cases hnil
  have push64 := of_run_pushB256 push64Run
  have push0 := of_run_pushB256 push0Run
  have windowPrefix : (0 : B256) :: 64 :: [] <<+ keccak256Pre.stack :=
    prefix_of_push push0 (prefix_of_push push64 spenderTail)

  obtain ⟨afterKec, keccak256Run, collisionRun⟩ :=
    runCompiledTo_next_inv bodyRun
  have keccak256Source := Ninst.Run.of_runCompiled keccak256Run
  rcases prefix_of_keccak256_val keccak256Source windowPrefix with
    ⟨hashPrefix, -⟩
  have memoryWindow : (keccak256Pre.memory.read 0 64).1 =
      (Sevm.argWord sevm 0).toBytes ++
        (Sevm.argWord sevm 1).toBytes := by
    rw [← push0.memory, ← push64.memory, spenderStoreMemory,
      ← (Line.of_inv Devm.memory (by line_inv) spenderArgRun),
      ownerStoreMemory,
      ← (Line.of_inv Devm.memory (by line_inv) ownerArgRun)]
    exact Mem.read_two_word_writes
      (image := bodyPre.memory.data.toList) bodyMemoryWf (by
        intro i
        simp) _ _
  have keyPrefix :
      allowanceKey (Sevm.argWord sevm 0) (Sevm.argWord sevm 1) :: [] <<+
        afterKec.stack := by
    change (keccak256Pre.memory.read 0 64).1.keccak :: [] <<+
      afterKec.stack at hashPrefix
    rw [memoryWindow] at hashPrefix
    simpa only [allowanceKey] using hashPrefix

  rcases allowanceCollisionGuard_body_of_ok keyPrefix collisionRun with
    ⟨readPre, keyNotAddress, keyNotSupply, readRun, readPrefix,
      collisionState, collisionLogs, -⟩
  have readEffect := stackStorageWord_effect readPrefix readRun

  have stagedStorage : Devm.getStor bodyPre = Devm.getStor afterKec :=
    (Line.of_inv Devm.getStor (by line_inv) ownerArgRun).trans
      ((Line.of_inv Devm.getStor (by line_inv) ownerStoreRun).trans
        ((Line.of_inv Devm.getStor (by line_inv) spenderArgRun).trans
          ((Line.of_inv Devm.getStor (by line_inv) spenderStoreRun).trans
            ((Line.of_inv Devm.getStor (by line_inv) pushWindowLine).trans
              (Ninst.Hinv.inv (f := Devm.getStor) keccak256Source)))))
  have stagedLogs : bodyPre.logs = afterKec.logs :=
    (Line.of_inv Devm.logs (by line_inv) ownerArgRun).trans
      ((Line.of_inv Devm.logs (by line_inv) ownerStoreRun).trans
        ((Line.of_inv Devm.logs (by line_inv) spenderArgRun).trans
          ((Line.of_inv Devm.logs (by line_inv) spenderStoreRun).trans
            ((Line.of_inv Devm.logs (by line_inv) pushWindowLine).trans
              (Ninst.Hinv.inv (f := Devm.logs) keccak256Source)))))
  have entryStorage : Devm.getStor pre = Devm.getStor readPre :=
    (funext (getStor_eq_of_state_eq ownerState)).trans
      ((funext (getStor_eq_of_state_eq spenderState)).trans
        (stagedStorage.trans
          (funext (getStor_eq_of_state_eq collisionState))))
  have entryLogs : pre.logs = readPre.logs :=
    ownerLogs.trans (spenderLogs.trans
      (stagedLogs.trans collisionLogs))
  exact ⟨ownerValid, spenderValid, keyNotAddress, keyNotSupply,
    lift_storage_word_view_of_storage entryStorage entryLogs readEffect⟩

/-! ## Public compiled selectors -/

/-- `name()` returns the exact canonical dynamic ABI encoding of
`PRORATA WETH Vault`. -/
theorem name_compiled_effect
    {sevm : Sevm} {pre post : Devm}
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre vault post)
    (hselector : Sevm.selector sevm = selector "name" []) :
    sevm.value = 0 ∧ BytesViewEffect nameOutput pre post := by
  have hmember : (selector "name" [], routed 0 name) ∈ vaultFuncs := by
    simp [vaultFuncs]
  rcases runCompiled_enters_body_compiled_logs run hselector hmember with
    ⟨bodyPre, hvalue, -, entryState, entryMemory, entryLogs, -, bodyRun⟩
  have bodyMemoryWf : Mem.Wf bodyPre.memory := by
    rw [← entryMemory]
    exact memoryWf
  have effect : BytesViewEffect nameOutput bodyPre post := by
    simpa only [name, nameOutput] using
      (shortString_body_effect bodyMemoryWf bodyRun)
  exact ⟨hvalue, lift_bytes_view entryState entryLogs effect⟩

/-- `symbol()` returns the exact canonical dynamic ABI encoding of `prWETH`. -/
theorem symbol_compiled_effect
    {sevm : Sevm} {pre post : Devm}
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre vault post)
    (hselector : Sevm.selector sevm = selector "symbol" []) :
    sevm.value = 0 ∧ BytesViewEffect symbolOutput pre post := by
  have hmember : (selector "symbol" [], routed 0 symbol) ∈ vaultFuncs := by
    simp [vaultFuncs]
  rcases runCompiled_enters_body_compiled_logs run hselector hmember with
    ⟨bodyPre, hvalue, -, entryState, entryMemory, entryLogs, -, bodyRun⟩
  have bodyMemoryWf : Mem.Wf bodyPre.memory := by
    rw [← entryMemory]
    exact memoryWf
  have effect : BytesViewEffect symbolOutput bodyPre post := by
    simpa only [symbol, symbolOutput] using
      (shortString_body_effect bodyMemoryWf bodyRun)
  exact ⟨hvalue, lift_bytes_view entryState entryLogs effect⟩

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
    ⟨bodyPre, hvalid, bodyRun, -, guardState, -, guardLogs⟩
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
    ⟨bodyPre, hvalid, bodyRun, -, guardState, -, guardLogs⟩
  exact ⟨hvalue, hvalid,
    lift_storage_word_view (entryState.trans guardState)
      (entryLogs.trans guardLogs) (argStorageWord_effect bodyRun)⟩

/-- `allowance(owner,spender)` returns the exact raw-key storage word.  The
single successful call proves both ABI words canonical and proves the derived
key is outside the balance and supply regions.  Logical pair attribution over
multiple touched keys is deliberately left to the later finite trace-local
collision premise. -/
theorem allowance_compiled_effect
    {sevm : Sevm} {pre post : Devm}
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre vault post)
    (hselector : Sevm.selector sevm =
      selector "allowance" [.address, .address]) :
    sevm.value = 0 ∧
      ValidAdr (Sevm.argWord sevm 0) ∧
      ValidAdr (Sevm.argWord sevm 1) ∧
      ¬ ValidAdr
        (allowanceKey (Sevm.argWord sevm 0) (Sevm.argWord sevm 1)) ∧
      allowanceKey (Sevm.argWord sevm 0) (Sevm.argWord sevm 1) ≠
        supplySlot ∧
      WordViewEffect
        (Devm.getStorVal pre sevm.currentTarget
          (allowanceKey (Sevm.argWord sevm 0) (Sevm.argWord sevm 1)))
        pre post := by
  have hmember :
      (selector "allowance" [.address, .address], routed 2 allowance) ∈
        vaultFuncs := by
    simp [vaultFuncs]
  rcases runCompiled_enters_body_compiled_logs run hselector hmember with
    ⟨bodyPre, hvalue, -, entryState, entryMemory, entryLogs, -, bodyRun⟩
  have bodyMemoryWf : Mem.Wf bodyPre.memory := by
    rw [← entryMemory]
    exact memoryWf
  rcases allowance_body_effect bodyMemoryWf bodyRun with
    ⟨ownerValid, spenderValid, keyNotAddress, keyNotSupply, effect⟩
  exact ⟨hvalue, ownerValid, spenderValid, keyNotAddress, keyNotSupply,
    lift_storage_word_view entryState entryLogs effect⟩

end ProrataWethVault

end Blanc
