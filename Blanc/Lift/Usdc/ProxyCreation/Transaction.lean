import Blanc.Lift.Usdc.ProxyCreation.Settlement
import Blanc.TransactionForwardH
import Blanc.ExecutionTraceCreateResult

/-!
# The original proxy constructor in an admitted transaction

Bind the registered creation input to the prepared message of the same actual
transaction trace. The historical transaction and its prestate remain inputs;
this module does not infer chain inclusion from a bytecode or RPC record.
-/

namespace Blanc.Lift.Usdc.ProxyCreation

open Jaune ExecutionTrace

/-- Creator already recorded in the approved `usdc-proxy-creation` provenance.
This literal does not authenticate the transaction's recovered sender. -/
def originalCreator : Adr := 0x95ba4cf87d6723ad9c0db21737d862be80e93911

/-- The registered creator at nonce20 computes the actual proxy address.
This is address arithmetic, not a historical inclusion or freshness proof. -/
theorem original_create_address :
    computeContractAddress originalCreator 20 = usdcProxy := by
  have senderBytes : originalCreator.toBytes =
      [0x95, 0xba, 0x4c, 0xf8, 0x7d, 0x67, 0x23, 0xad, 0x9c, 0x0d,
       0xb2, 0x17, 0x37, 0xd8, 0x62, 0xbe, 0x80, 0xe9, 0x39, 0x11] := by decide +kernel
  have nonceBytes : (UInt64.toBytes 20).sig = [0x14] := by decide +kernel
  have encoding : BLT.toBytes (.list [.bytes
      [0x95, 0xba, 0x4c, 0xf8, 0x7d, 0x67, 0x23, 0xad, 0x9c, 0x0d,
       0xb2, 0x17, 0x37, 0xd8, 0x62, 0xbe, 0x80, 0xe9, 0x39, 0x11], .bytes [0x14]]) =
      [0xd6, 0x94, 0x95, 0xba, 0x4c, 0xf8, 0x7d, 0x67, 0x23, 0xad, 0x9c, 0x0d,
       0xb2, 0x17, 0x37, 0xd8, 0x62, 0xbe, 0x80, 0xe9, 0x39, 0x11, 0x14] := by
    simp only [BLT.toBytes, BLTs.toBytes, BLTs.toBytesJoin, List.length_cons, List.length_nil,
      zero_add, Nat.reduceAdd, Nat.reduceLT, ↓reduceIte, Nat.toUInt8_eq, UInt8.reduceOfNat,
      UInt8.reduceAdd, UInt8.reduceLT, List.append_nil, List.cons_append, List.nil_append]
  unfold computeContractAddress
  rw [senderBytes, nonceBytes, encoding]
  decide +kernel

/-- The admitted creation transaction supplies its constructor message fields.
The target is computed from the actual debited prestate and admitted sender;
neither a separately chosen message nor a separately chosen address is used. -/
theorem transaction_constructor_message
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (receiver : tx.type.receiver? = none)
    (input : tx.data = code.toList) (value : tx.value = 0) :
    trace.msg.target = none ∧ trace.msg.code = code ∧
      trace.msg.value = 0 ∧ trace.msg.codeAddress = none ∧
      trace.msg.caller = trace.sender ∧
      trace.msg.currentTarget = computeContractAddress trace.sender
        (trace.debitState.getNonce trace.sender - 1) := by
  have prepared := trace.prepared
  simp only [prepareMessage, receiver] at prepared
  have message := Except.ok.inj prepared
  rw [← message]
  refine ⟨rfl, ?_, ?_, rfl, rfl, rfl⟩
  · change ({ data := { toList := tx.data } } : ByteArray) = code
    rw [input]
    apply ByteArray.ext
    rw [← Array.toList_inj]
    exact ByteArray.toList_eq_toList_data
  · change tx.value.toB256 = 0
    rw [value]
    rfl

/-- The same admitted transaction installs the original proxy runtime and
constructor storage through its actual refund, fee, deletion and touched-sweep
settlement. The explicit deletion exclusion is still a caller obligation. -/
theorem constructor_effects_of_transactionTrace
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (receiver : tx.type.receiver? = none)
    (input : tx.data = code.toList) (value : tx.value = 0)
    (clean : trace.messageOut.error = none)
    (noDelete : trace.msg.currentTarget ∉ trace.messageOut.accountsToDelete) :
    state.getCode trace.msg.currentTarget = Proxy.code ∧
      state.getStor trace.msg.currentTarget =
        (Stor.empty.set implSlot initialImplementation).set adminSlot
          trace.sender.toB256 := by
  obtain ⟨target, inputCode, zeroValue, codeAddress, caller, _⟩ :=
    transaction_constructor_message trace receiver input value
  have msgStateGas : trace.msg.benv.stat.rules.stateGas = none := by
    rw [prepareMessage_benv trace.prepared]
    exact hsg
  obtain ⟨installed, ⟨retained⟩, _, _, innerClean, sameState⟩ :=
    trace.message.exists_clean_create
      (by rw [target]; rfl) msgStateGas clean
  have effects := constructor_effects_of_createTrace retained
    (by rw [innerClean]; rfl) inputCode zeroValue codeAddress msgStateGas
  have messageCode : trace.messageState.getCode trace.msg.currentTarget = Proxy.code := by
    rw [sameState]
    exact effects.1
  have messageStorage : trace.messageState.getStor trace.msg.currentTarget =
      (Stor.empty.set implSlot initialImplementation).set adminSlot trace.sender.toB256 := by
    rw [sameState, ← caller]
    exact effects.2
  obtain ⟨refund, _, finalState⟩ := trace.exists_selectedFinalStateForm hsg
  have finalCode := congrArg (fun s => s.getCode trace.msg.currentTarget) finalState
  have finalStorage := congrArg (fun s => s.getStor trace.msg.currentTarget) finalState
  rw [finalCode, finalStorage]
  have preserved (r f : B256) := settled_getCode_getStor_of_code_nonempty
    (rules := benv.stat.rules) (touched := trace.messageOut.touchedAccounts.toList)
    (st := trace.messageState) (s := trace.sender) (c := benv.stat.coinbase)
    (w := trace.msg.currentTarget) (dels := trace.messageOut.accountsToDelete.toList)
    (r := r) (f := f)
    (fun a member equal => noDelete (equal ▸ Std.HashSet.mem_toList.mp member))
    (by rw [messageCode]; intro empty
        have length := congrArg List.length empty
        rw [← runtime_window, List.length_sliceD] at length
        cases length)
  exact ⟨(preserved _ _).1.trans messageCode, (preserved _ _).2.trans messageStorage⟩

/-- At the recorded creator and nonce, the actual admitted transaction targets
USDC. Admission supplies the sender's prestate nonce; its real debit and nonce
bump supply the nonce used by `prepareMessage`. -/
theorem transaction_targets_proxy
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (receiver : tx.type.receiver? = none)
    (input : tx.data = code.toList) (value : tx.value = 0)
    (sender : trace.sender = originalCreator) (nonce : tx.nonce = 20) :
    trace.msg.currentTarget = usdcProxy := by
  have target := (transaction_constructor_message trace receiver input value).2.2.2.2.2
  have preNonce := checkTransaction_sender_nonce trace.checked
  change (benv.state.get trace.sender).nonce = tx.nonce at preNonce
  have debitNonce : trace.debitState.getNonce trace.sender = 21 := by
    rw [(State.of_subBal trace.debit).2]
    change (((benv.state.incrNonce trace.sender).setBal trace.sender _).get trace.sender).nonce = 21
    rw [State.setBal_get_nonce]
    simp only [State.incrNonce, State.setAccount_get_self, Acct.clearIfEmpty_nonce]
    rw [preNonce, nonce]
    rfl
  rw [target, debitNonce, sender]
  exact original_create_address

/-- The registered deployment transaction's creator, nonce and input bind the
settled constructor effects to USDC itself. Actual history/cut identity and
message success are still required; no provider response supplies them here. -/
theorem original_constructor_effects_of_transactionTrace
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (receiver : tx.type.receiver? = none)
    (input : tx.data = code.toList) (value : tx.value = 0)
    (sender : trace.sender = originalCreator) (nonce : tx.nonce = 20)
    (clean : trace.messageOut.error = none)
    (noDelete : usdcProxy ∉ trace.messageOut.accountsToDelete) :
    state.getCode usdcProxy = Proxy.code ∧
      state.getStor usdcProxy =
        (Stor.empty.set implSlot initialImplementation).set adminSlot originalCreator.toB256 := by
  have target := transaction_targets_proxy trace receiver input value sender nonce
  have effects := constructor_effects_of_transactionTrace trace hsg receiver input value clean
    (by rw [target]; exact noDelete)
  simpa only [target, sender] using effects

end Blanc.Lift.Usdc.ProxyCreation
