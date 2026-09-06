import Blanc.Ladder
import Blanc.ForwardCall

/-!
Reusable execution facts for transient cells, static calls, frame-relative
settlement, observable logs, and transaction-boundary reset.

This module deliberately stays below every contract and records direct
CALL/STATICCALL provenance from the executed opcode edge rather than inferred
message-field coincidence.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

/-! ## Exact transient-cell execution -/

private theorem tra_getD_set_self (tra : Tra) (a : Adr) (s : Stor) :
    (tra.set a s).getD a .empty = s := by
  unfold Tra.set
  split
  · rw [Std.TreeMap.getD_erase]
    have hcmp : compare a a = Ordering.eq := compare_eq_iff_eq.mpr rfl
    rw [hcmp]
    exact (Std.TreeMap.eq_empty_iff_isEmpty.mpr (by assumption)).symm
  · rw [Std.TreeMap.getD_insert]
    simp

private theorem tra_get_set_self (tra : Tra) (a : Adr) (k v : B256) :
    ((tra.setStorVal a k v).getD a .empty).get k = v := by
  rw [Tra.setStorVal, tra_getD_set_self]
  exact Stor.get_set_self _ _ _

private theorem tra_get_set_same_address (tra : Tra) (a : Adr)
    {k j : B256} (hkj : k ≠ j) (v : B256) :
    ((tra.setStorVal a k v).getD a .empty).get j =
      (tra.getD a .empty).get j := by
  rw [Tra.setStorVal, tra_getD_set_self]
  exact Stor.get_set_ne _ hkj v

private theorem tra_get_set_other_address (tra : Tra)
    {a b : Adr} (hab : a ≠ b) (k v j : B256) :
    ((tra.setStorVal a k v).getD b .empty).get j =
      (tra.getD b .empty).get j := by
  simp only [Tra.setStorVal, Tra.set]
  split
  · rw [Std.TreeMap.getD_erase]
    have hcmp : compare a b ≠ Ordering.eq := by
      intro h
      exact hab (compare_eq_iff_eq.mp h)
    simp [hcmp]
  · rw [Std.TreeMap.getD_insert]
    have hcmp : compare a b ≠ Ordering.eq := by
      intro h
      exact hab (compare_eq_iff_eq.mp h)
    simp [hcmp]

/-- An actual successful TSTORE pops key then value, changes exactly the
ordered transient cell `(currentTarget, key)`, leaves persistent state alone,
and can only succeed outside a static context. -/
theorem tstore_run_cell
    {sevm : Sevm} {pre post : Devm} {key value : B256} {tail : List B256}
    (run : Ninst.Run sevm pre (.reg .tstore) post)
    (stack : pre.stack = key :: value :: tail) :
    post.stack = tail ∧
      post.getTransVal sevm.currentTarget key = value ∧
      (∀ otherAddress otherKey,
        (otherAddress, otherKey) ≠ (sevm.currentTarget, key) →
        post.getTransVal otherAddress otherKey =
          pre.getTransVal otherAddress otherKey) ∧
      post.state = pre.state ∧
      Devm.TransientWriteFrame pre post ∧
      sevm.isStatic = false := by
  rcases of_run_reg run with ⟨pc, hr⟩
  have hf := Rinst.tstore_run_transientWriteFrame pc pre sevm
  rw [hr] at hf
  change Devm.TransientWriteFrame pre post at hf
  simp only [Rinst.run, Rinst.runCore, Devm.pop_def, stack, bind,
    Except.bind] at hr
  simp only [Devm.stack, Devm.setMach] at hr
  let d0 : Devm := {
    mach := { stack := tail, memory := pre.mach.memory, gasLeft := pre.mach.gasLeft }
    «meta» := pre.meta
    world := pre.world }
  change (do
    let charged ← chargeGas gasWarmAccess d0
    assertDynamic sevm charged
    .ok (charged.setTransVal sevm.currentTarget key value)) = .ok post at hr
  rcases Except.bind_eq_ok hr with ⟨charged, hc, hr⟩
  rcases Except.bind_eq_ok hr with ⟨u, ha, hr⟩
  injection hr with heq
  subst post
  have hb := Devm.burn_of_chargeGas hc
  constructor
  · exact hb.stack.symm
  constructor
  · exact tra_get_set_self charged.transientStorage
      sevm.currentTarget key value
  constructor
  · intro otherAddress otherKey hne
    change (Std.TreeMap.getD
      (charged.transientStorage.setStorVal sevm.currentTarget key value)
      otherAddress .empty).get otherKey =
      (pre.transientStorage.getD otherAddress .empty).get otherKey
    rw [← hb.transientStorage]
    change (Std.TreeMap.getD
      (pre.transientStorage.setStorVal sevm.currentTarget key value)
      otherAddress .empty).get otherKey =
      (pre.transientStorage.getD otherAddress .empty).get otherKey
    by_cases hadr : sevm.currentTarget = otherAddress
    · subst otherAddress
      apply tra_get_set_same_address
      intro hkey
      exact hne (by simp [hkey])
    · exact tra_get_set_other_address pre.transientStorage hadr
        key value otherKey
  constructor
  · exact hb.state.symm
  constructor
  · exact hf
  · unfold assertDynamic Except.assert at ha
    by_cases hs : sevm.isStatic
    · simp [hs] at ha
    · exact Bool.eq_false_iff.mpr hs

/-- Writing zero clears only the selected cell's read. The accompanying
`tstore_run_cell` theorem retains every unrelated cell. -/
theorem tstore_run_zero
    {sevm : Sevm} {pre post : Devm} {key : B256} {tail : List B256}
    (run : Ninst.Run sevm pre (.reg .tstore) post)
    (stack : pre.stack = key :: 0 :: tail) :
    post.getTransVal sevm.currentTarget key = 0 :=
  (tstore_run_cell run stack).2.1

/-- An actual successful TLOAD pushes the selected `(currentTarget, key)`
read and preserves the entire transient and persistent worlds. -/
theorem tload_run_cell
    {sevm : Sevm} {pre post : Devm} {key : B256} {tail : List B256}
    (run : Ninst.Run sevm pre (.reg .tload) post)
    (stack : pre.stack = key :: tail) :
    post.stack = pre.getTransVal sevm.currentTarget key :: tail ∧
      post.transientStorage = pre.transientStorage ∧
      post.state = pre.state ∧
      Devm.InstructionFrame pre post := by
  rcases of_run_reg run with ⟨pc, hr⟩
  have hf := Rinst.run_instructionFrame pc sevm pre .tload
    (by intro h; cases h) (by intro h; cases h)
  rw [hr] at hf
  change Devm.InstructionFrame pre post at hf
  simp only [Rinst.run, Rinst.runCore, Devm.pop_def, stack, bind,
    Except.bind] at hr
  simp only [Devm.setMach] at hr
  let d0 : Devm := {
    mach := { stack := tail, memory := pre.mach.memory, gasLeft := pre.mach.gasLeft }
    «meta» := pre.meta
    world := pre.world }
  change pushItem (d0.getTransVal sevm.currentTarget key)
      gasWarmAccess d0 = .ok post at hr
  rw [pushItem_def] at hr
  rcases Except.bind_eq_ok hr with ⟨charged, hc, hp⟩
  have hb := Devm.burn_of_chargeGas hc
  have hpush := Devm.push_of_push hp
  constructor
  · have hstack := hpush.stack
    rw [← hb.stack] at hstack
    simpa [Stack.Push, Split, d0, Devm.getTransVal,
      Devm.transientStorage, Devm.stack] using hstack
  exact ⟨hf.transientStorage.symm, hf.state.symm, hf⟩

/-! ## Opcode-proven direct call edges -/

/-- A nonzero-value CALL's exact child message, tied to the actual `.call`
edge. Delegation may choose `code` from another account; the target and code
address equalities below therefore do not claim byte or installation identity. -/
theorem directCall_nonzero_spawn
    {sevm : Sevm} {devm : Devm}
    {gw cw vw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc create mcc mcs : Nat}
    (h_stk : devm.stack = gw :: cw :: vw :: iiw :: isw :: oiw :: osw :: s)
    (h_value : vw ≠ 0)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        cw.toAdr) cw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost cw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_create :
      (if ¬ (d1.getAcct cw.toAdr).Empty then 0 else gNewAccount) = create)
    (h_split : calculateMsgCallGas vw.toNat gw.toNat d1.gasLeft ext
      (acc + create + gasCallValue) = ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft)
    (h_dynamic : sevm.isStatic = false)
    (h_sender : ¬ (d1.getAcct sevm.currentTarget).bal < vw)
    (h_depth : sevm.depth ≠ 0) :
    let parent := callSpawnParent d1 (mcc + ext)
      iiw.toNat isw.toNat oiw.toNat osw.toNat
    let child := valueCallSpawnMsg sevm parent mcs vw cw.toAdr dadr
      iiw.toNat isw.toNat code dp
    Xinst.step sevm devm .call =
        .spawn (Frame.ofCall child) (.call parent oiw.toNat osw.toNat) ∧
      child.currentTarget = cw.toAdr ∧
      child.codeAddress = some dadr ∧
      child.caller = sevm.currentTarget ∧
      child.value = vw ∧ child.shouldTransferValue = true ∧
      child.isStatic = sevm.isStatic ∧
      child.tenv.transientStorage = devm.transientStorage := by
  dsimp only
  refine ⟨Xinst.step_call_nonzero_spawn h_stk h_value h_ext h_del h_acc
    h_create h_split h_gas h_dynamic h_sender h_depth,
    rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · simp [valueCallSpawnMsg, callMsg, h_dynamic]
  · have hf := accessDelegation_instructionFrame
      (addAccessedAddress
        (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) cw.toAdr) cw.toAdr
    rw [h_del] at hf
    exact hf.transientStorage.symm

/-- The zero-value CALL companion, still proven from the actual `.call` edge. -/
theorem directCall_zero_spawn
    {sevm : Sevm} {devm : Devm}
    {gw cw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat}
    (h_stk : devm.stack = gw :: cw :: 0 :: iiw :: isw :: oiw :: osw :: s)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        cw.toAdr) cw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost cw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc = ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft) (h_depth : sevm.depth ≠ 0) :
    let parent := callSpawnParent d1 (mcc + ext)
      iiw.toNat isw.toNat oiw.toNat osw.toNat
    let child := callSpawnMsg sevm parent mcs cw.toAdr dadr
      iiw.toNat isw.toNat code dp
    Xinst.step sevm devm .call =
        .spawn (Frame.ofCall child) (.call parent oiw.toNat osw.toNat) ∧
      child.currentTarget = cw.toAdr ∧
      child.codeAddress = some dadr ∧
      child.caller = sevm.currentTarget ∧
      child.value = 0 ∧ child.shouldTransferValue = true ∧
      child.isStatic = sevm.isStatic ∧
      child.tenv.transientStorage = devm.transientStorage := by
  dsimp only
  refine ⟨Xinst.step_call_zero_value_spawn h_stk h_ext h_del h_acc h_split
    h_gas h_depth, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  have hf := accessDelegation_instructionFrame
    (addAccessedAddress
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) cw.toAdr) cw.toAdr
  rw [h_del] at hf
  exact hf.transientStorage.symm

/-- A STATICCALL's exact child message, tied to the actual `.staticcall` edge. -/
theorem directStaticcall_spawn
    {sevm : Sevm} {devm : Devm}
    {gw tw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat}
    (h_stk : devm.stack = gw :: tw :: iiw :: isw :: oiw :: osw :: s)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        tw.toAdr) tw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost tw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc = ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft) (h_depth : sevm.depth ≠ 0) :
    let parent := callSpawnParent d1 (mcc + ext)
      iiw.toNat isw.toNat oiw.toNat osw.toNat
    let child := staticcallSpawnMsg sevm parent mcs tw.toAdr dadr
      iiw.toNat isw.toNat code dp
    Xinst.step sevm devm .staticcall =
        .spawn (Frame.ofCall child) (.call parent oiw.toNat osw.toNat) ∧
      child.currentTarget = tw.toAdr ∧
      child.codeAddress = some dadr ∧
      child.caller = sevm.currentTarget ∧
      child.value = 0 ∧ child.shouldTransferValue = true ∧
      child.isStatic = true ∧
      child.tenv.transientStorage = devm.transientStorage := by
  dsimp only
  refine ⟨Xinst.step_staticcall_spawn h_stk h_ext h_del h_acc h_split h_gas
    h_depth, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  have hf := accessDelegation_instructionFrame
    (addAccessedAddress
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) tw.toAdr) tw.toAdr
  rw [h_del] at hf
  exact hf.transientStorage.symm

/-- A DELEGATECALL's exact child message, tied to the actual `.delegatecall` edge.
Where the three siblings above put the popped operand in the storage-owner
slot, this one puts `sevm.currentTarget`: the running account keeps its own
storage while `dadr` supplies the code alone, and `caller`/`value` are the
outer frame's rather than the parent's address and zero. As above, delegation
may choose `code` from another account, so the code-address equality claims no
byte or installation identity. -/
theorem directDelegatecall_spawn
    {sevm : Sevm} {devm : Devm}
    {gw cw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat}
    (h_stk : devm.stack = gw :: cw :: iiw :: isw :: oiw :: osw :: s)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        cw.toAdr) cw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost cw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc = ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft) (h_depth : sevm.depth ≠ 0) :
    let parent := callSpawnParent d1 (mcc + ext)
      iiw.toNat isw.toNat oiw.toNat osw.toNat
    let child := delegatecallSpawnMsg sevm parent mcs dadr
      iiw.toNat isw.toNat code dp
    Xinst.step sevm devm .delegatecall =
        .spawn (Frame.ofCall child) (.call parent oiw.toNat osw.toNat) ∧
      child.currentTarget = sevm.currentTarget ∧
      child.codeAddress = some dadr ∧
      child.caller = sevm.caller ∧
      child.value = sevm.value ∧ child.shouldTransferValue = false ∧
      child.isStatic = sevm.isStatic ∧
      child.tenv.transientStorage = devm.transientStorage := by
  dsimp only
  refine ⟨Xinst.step_delegatecall_spawn h_stk h_ext h_del h_acc h_split h_gas
    h_depth, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact Bool.false_or _
  · have hf := accessDelegation_instructionFrame
      (addAccessedAddress
        (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) cw.toAdr) cw.toAdr
    rw [h_del] at hf
    exact hf.transientStorage.symm

/-! ## Frame-relative child settlement -/

/-- A settled-with-error CALL child rolls back to its own message-entry world.
The caught resume keeps the parent's pre-child logs while installing that
restored child-entry world. Parent work already present in `msg` therefore
survives; this is deliberately not an outer-message rollback statement. -/
theorem caughtCall_childSettlement
    {msg : Msg} {xl : Xlot} {child parent resumed : Devm} {oi os : Nat}
    (hpm : ProcessMessage msg xl (.ok child))
    (herr : child.error.isSome)
    (hresume : (Resume.call parent oi os).run (.ok child) = .ok resumed) :
    child.state = msg.benv.state ∧
      child.transientStorage = msg.tenv.transientStorage ∧
      resumed.logs = parent.logs ∧
      resumed.state = msg.benv.state ∧
      resumed.transientStorage = msg.tenv.transientStorage := by
  have hrollback := ProcessMessage.rollback_of_error hpm herr
  have hlogs := Resume.call_logs hresume
  rw [if_pos herr] at hlogs
  have hstate := Resume.call_state hresume
  have htra := Resume.call_transientStorage hresume
  exact ⟨hrollback.1, hrollback.2, hlogs,
    hstate.trans hrollback.1, htra.trans hrollback.2⟩

/-- A clean CALL child contributes its logs and propagates its persistent and
transient worlds through the resume. -/
theorem cleanCall_childSettlement
    {child parent resumed : Devm} {oi os : Nat}
    (hclean : child.error.isSome = false)
    (hresume : (Resume.call parent oi os).run (.ok child) = .ok resumed) :
    resumed.logs = parent.logs ++ child.logs ∧
      resumed.state = child.state ∧
      resumed.transientStorage = child.transientStorage := by
  have hlogs := Resume.call_logs hresume
  rw [if_neg (by simpa using hclean)] at hlogs
  exact ⟨hlogs, Resume.call_state hresume,
    Resume.call_transientStorage hresume⟩

/-! ## Transaction-boundary preparation -/

/-- The exact message-preparation prefix retained from a successful
`processTransaction` run.

The final transaction result does not expose its prepared message, so this
witness keeps the validation, checking, debit, preparation, and final-result
equations together. The transaction environment is written inline on purpose:
this is a narrow projection from Jaune's real prefix, not a parallel trace
abstraction. -/
structure PreparedTransactionMessage
    (benv : Benv) (bout : BlockOutput) (tx : Tx) (index : Nat)
    (state : State) (bout' : BlockOutput) where
  intrinsicGas : Nat
  calldataFloorGasCost : Nat
  sender : Adr
  effectiveGasPrice : Nat
  blobVersionedHashes : List B256
  txBlobGasUsed : Nat
  debitState : State
  msg : Msg
  messageState : State
  output : MsgCallOutput
  validation : validateTransaction benv.beginTransaction.stat.rules tx =
    .ok (intrinsicGas, calldataFloorGasCost)
  checked : checkTransaction benv.beginTransaction
    { bout with transactionsTrie :=
        bout.transactionsTrie.insert (BLT.bytes index.toBytes).toBytes tx } tx =
      .ok (sender, effectiveGasPrice, blobVersionedHashes, txBlobGasUsed)
  debited : (benv.beginTransaction.state.incrNonce sender).subBal sender
    ((tx.gas * effectiveGasPrice +
      if tx.isTypeThree then
        calculateDataFee benv.beginTransaction.stat.rules.blob
          benv.beginTransaction.stat.excessBlobGas tx
      else 0).toB256) = some debitState
  prepared : prepareMessage
    { benv.beginTransaction with state := debitState }
    { transientStorage := (Std.TreeMap.empty : Tra)
      stat :=
        { origin := sender
          gasPrice := effectiveGasPrice
          gas := tx.gas - intrinsicGas
          accessListAddresses :=
            .ofList (benv.beginTransaction.stat.coinbase ::
              tx.accessList.map Prod.fst)
          accessListStorageKeys :=
            .ofList (tx.accessList.map (fun ⟨adr, keys⟩ =>
              keys.map (⟨adr, ·⟩))).flatten
          blobVersionedHashes := blobVersionedHashes
          auths := tx.auths
          indexInBlock := index
          txHash := getTxHash tx } } tx = .ok msg
  messageRun : processMessageCall msg = .ok (messageState, output)
  result : processTransaction benv bout tx index = .ok (state, bout')

/-- Every accepted transaction run retains its actual prepared-message prefix. -/
theorem preparedTransactionMessage_exists
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (h : processTransaction benv bout tx index = .ok (state, bout')) :
    Nonempty (PreparedTransactionMessage benv bout tx index state bout') := by
  have hresult := h
  unfold processTransaction at h
  dsimp only at h
  obtain ⟨prelude, hp, h⟩ := Except.bind_eq_ok h
  cases hp
  obtain ⟨validated, hv, h⟩ := Except.bind_eq_ok h
  obtain ⟨intrinsicGas, calldataFloorGasCost⟩ := validated
  rw [Except.mapError_eq_ok_iff] at hv
  obtain ⟨checked, hc, h⟩ := Except.bind_eq_ok h
  obtain ⟨sender, effectiveGasPrice, blobVersionedHashes,
    txBlobGasUsed⟩ := checked
  obtain ⟨debitState, hd, h⟩ := Except.bind_eq_ok h
  obtain ⟨msg, hm, h⟩ := Except.bind_eq_ok h
  obtain ⟨processed, hpm, h⟩ := Except.bind_eq_ok h
  obtain ⟨messageState, output⟩ := processed
  rw [Except.mapError_eq_ok_iff] at hpm
  exact ⟨⟨intrinsicGas, calldataFloorGasCost, sender,
    effectiveGasPrice, blobVersionedHashes, txBlobGasUsed, debitState, msg,
    messageState, output,
    by simpa [Benv.beginTransaction] using hv,
    by simpa [Benv.beginTransaction] using hc,
    by simpa [Benv.beginTransaction] using Option.toExcept_eq_ok hd,
    by simpa [Benv.beginTransaction] using hm,
    hpm,
    hresult⟩⟩

/-- Transaction-level transient storage starts empty in the message reached by
the real `processTransaction` prefix. This says nothing about rejected
submissions, which need not reach message preparation. -/
theorem PreparedTransactionMessage.transientStorage_eq_empty
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (w : PreparedTransactionMessage benv bout tx index state bout') :
    w.msg.tenv.transientStorage = (Std.TreeMap.empty : Tra) := by
  have hp := w.prepared
  unfold prepareMessage at hp
  split at hp
  all_goals injection hp with heq
  all_goals simp [← heq]

/-! ## Top-level observable logs -/

private theorem processMessageCall_create_error_logs
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (run : processMessageCall.create msg = .ok (state, out))
    (herr : out.error.isSome) : out.logs = [] := by
  unfold processMessageCall.create at run
  dsimp only at run
  split at run
  · cases run
    rfl
  · rcases Except.bind_eq_ok run with ⟨evm, hprocess, hrest⟩
    by_cases clean : evm.error.isNone
    · rw [if_pos clean] at hrest
      rcases Except.bind_eq_ok hrest with ⟨refund, hrefund, hfinal⟩
      cases hfinal
      simp_all
    · rw [if_neg clean] at hrest
      cases hrest
      simp only [if_neg clean]

private theorem processMessageCall_call_error_logs
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (run : processMessageCall.call msg = .ok (state, out))
    (herr : out.error.isSome) : out.logs = [] := by
  unfold processMessageCall.call at run
  dsimp only at run
  split at run
  · simp only [bind, Except.bind] at run
    rcases Except.bind_eq_ok run with ⟨evm, hprocess, hrest⟩
    by_cases clean : evm.error.isNone
    · rw [if_pos clean] at hrest
      rcases Except.bind_eq_ok hrest with ⟨refund, hrefund, hfinal⟩
      cases hfinal
      simp_all
    · rw [if_neg clean] at hrest
      cases hrest
      simp only [if_neg clean]
  · rcases Except.bind_eq_ok run with
      ⟨⟨delegated, setValue⟩, hdelegated, hrest⟩
    simp only [bind, Except.bind] at hrest
    rcases Except.bind_eq_ok hrest with ⟨evm, hprocess, hrest⟩
    by_cases clean : evm.error.isNone
    · rw [if_pos clean] at hrest
      rcases Except.bind_eq_ok hrest with ⟨refund, hrefund, hfinal⟩
      cases hfinal
      simp_all
    · rw [if_neg clean] at hrest
      cases hrest
      simp only [if_neg clean]

/-- An errored top-level message exposes no logs. Its `returnData` remains an
independent output field and is not constrained by this theorem. -/
theorem processMessageCall_error_logs_eq_nil
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (run : processMessageCall msg = .ok (state, out))
    (herr : out.error.isSome) : out.logs = [] := by
  unfold processMessageCall at run
  split at run
  · exact processMessageCall_create_error_logs run herr
  · exact processMessageCall_call_error_logs run herr

/-- The observable-log consequence attached to the message output retained by
a successful transaction-prefix witness. -/
theorem PreparedTransactionMessage.error_logs_eq_nil
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (w : PreparedTransactionMessage benv bout tx index state bout')
    (herr : w.output.error.isSome) : w.output.logs = [] :=
  processMessageCall_error_logs_eq_nil w.messageRun herr

end Blanc
