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

end Blanc.Lift.Usdc.ProxyCreation
