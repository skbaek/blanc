import Blanc.Lift.CallRestriction
import Blanc.ExecutionDeletionProvenance
import Blanc.Lift.Deploy
import Blanc.Lift.BalSilent
import Blanc.TransactionForwardH
import Blanc.ExecutionTraceCreateResult
import Blanc.ExecutionIndexedReceipts

/-!
# Checked constructors through their original transaction settlement

Source-level deletion preservation and the actual retained CREATE result feed
refund, fee, deletion and touched-account settlement. Constructor certificates,
runtime windows and original transaction correspondence remain explicit.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- The actual admitted creation transaction supplies its prepared code,
caller, target and empty inherited deletion set, for arbitrary call value. -/
theorem TransactionTrace.creation_message_fields
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput} {code : ByteArray}
    (trace : TransactionTrace benv bout tx index state bout')
    (receiver : tx.type.receiver? = none) (input : tx.data = code.toList) :
    trace.msg.target = none ∧ trace.msg.code = code ∧
      trace.msg.codeAddress = none ∧ trace.msg.caller = trace.sender ∧
      trace.msg.currentTarget = computeContractAddress trace.sender
        (trace.debitState.getNonce trace.sender - 1) ∧
      trace.msg.inheritedDeletions = .emptyWithCapacity := by
  have prepared := trace.prepared
  simp only [prepareMessage, receiver] at prepared
  rw [← Except.ok.inj prepared]
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
  change ({ data := { toList := tx.data } } : ByteArray) = code
  rw [input]
  apply ByteArray.ext
  rw [← Array.toList_inj]
  exact ByteArray.toList_eq_toList_data

/-- Every retained node of a checked constructor without external instructions
executes at the original creation target. Entry facts come from the actual
CREATE trace, including when its settled root list is empty. -/
theorem ProcessCreateMessageTrace.retainedNodes_currentTarget_of_noExecs
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    {code : ByteArray} {c : Lift.Cert}
    (trace : ProcessCreateMessageTrace msg out)
    (checked : Lift.Cert.check code c = true)
    (noExecs : ∀ f ∈ c.prog, f.execsSatisfy (fun _ => false) = true)
    (codeEq : msg.code = code) (stateGas : msg.benv.stat.rules.stateGas = none) :
    ∀ R ∈ trace.settledRoots, ∀ n ∈ Exec.retainedNodes R.run,
      n.sevm.currentTarget = msg.currentTarget := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none => intro R member; cases member
  | @some pc sevm pre raw run =>
    intro R member
    simp only [ProcessCreateMessageTrace.settledRoots] at member
    split at member
    · simp only [RetainedXlot.settledRoots] at member
      split at member
      · rw [List.mem_singleton] at member
        subst R
        intro n node
        have enter := (RunFrame.some_inv process).1
        have childGas := Frame.enter_run_benvStat enter
        have gas := processCreateMessage.msg_benvStat msg
        have chain := Lift.rawNodes_parentPrefix_of_noExecs_noStateGas
          (F := ⟨pc, sevm, pre, raw, run⟩) checked noExecs (Frame.enter_run_pc enter)
          ((Frame.enter_run_code enter).trans codeEq)
          (by rw [childGas]
              change (processCreateMessage.msg msg).benv.stat.rules.stateGas = none
              rw [gas]
              exact stateGas)
          n ((Exec.retainedNodes_sublist_rawNodes run).subset node)
        rw [Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain]
        exact Frame.enter_run_currentTarget enter
      · cases member
    · cases member

/-- The original CREATE arm of the message wrapper preserves the constructor's
target classification; a collision contributes no settled root. -/
theorem MessageCallTrace.retainedNodes_currentTarget_of_create_noExecs
    {msg : Msg} {state : State} {out : MsgCallOutput}
    {code : ByteArray} {c : Lift.Cert}
    (trace : MessageCallTrace msg state out)
    (target : msg.target = none) (checked : Lift.Cert.check code c = true)
    (noExecs : ∀ f ∈ c.prog, f.execsSatisfy (fun _ => false) = true)
    (codeEq : msg.code = code) (stateGas : msg.benv.stat.rules.stateGas = none) :
    ∀ R ∈ trace.settledRoots, ∀ n ∈ Exec.retainedNodes R.run,
      n.sevm.currentTarget = msg.currentTarget := by
  cases trace with
  | createCollision => intro R member; cases member
  | createRun targetNone collision evm core inner result =>
    exact inner.retainedNodes_currentTarget_of_noExecs checked noExecs codeEq stateGas
  | callRun targetSome delegated refund delegation execMsg execMsgEq evm core inner result =>
    rw [target] at targetSome
    cases targetSome

/-- An admitted original creation transaction supplies all root-entry facts
needed to keep every retained constructor node at its prepared target. -/
theorem TransactionTrace.retainedNodes_currentTarget_of_create_noExecs
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput} {code : ByteArray} {c : Lift.Cert}
    (trace : TransactionTrace benv bout tx index state bout')
    (receiver : tx.type.receiver? = none) (input : tx.data = code.toList)
    (checked : Lift.Cert.check code c = true)
    (noExecs : ∀ f ∈ c.prog, f.execsSatisfy (fun _ => false) = true)
    (stateGas : benv.stat.rules.stateGas = none) :
    ∀ R ∈ trace.settledRoots, ∀ n ∈ Exec.retainedNodes R.run,
      n.sevm.currentTarget = trace.msg.currentTarget := by
  obtain ⟨target, codeEq, _⟩ := trace.creation_message_fields receiver input
  exact trace.message.retainedNodes_currentTarget_of_create_noExecs
    target checked noExecs codeEq (by rw [prepareMessage_benv trace.prepared]; exact stateGas)

/-- A checked original constructor cannot contribute a retained node at a
different protected account. No successful-outcome premise is needed. -/
theorem TransactionTrace.retainedNodes_currentTarget_ne_of_create_noExecs
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput} {code : ByteArray} {c : Lift.Cert} {protectedP : Adr}
    (trace : TransactionTrace benv bout tx index state bout')
    (receiver : tx.type.receiver? = none) (input : tx.data = code.toList)
    (checked : Lift.Cert.check code c = true)
    (noExecs : ∀ f ∈ c.prog, f.execsSatisfy (fun _ => false) = true)
    (stateGas : benv.stat.rules.stateGas = none)
    (apart : trace.msg.currentTarget ≠ protectedP) :
    ∀ R ∈ trace.settledRoots, ∀ n ∈ Exec.retainedNodes R.run,
      n.sevm.currentTarget ≠ protectedP := by
  intro R root n node
  rw [trace.retainedNodes_currentTarget_of_create_noExecs
    receiver input checked noExecs stateGas R root n node]
  exact apart

/-- Nonempty installed code and its storage survive the actual transaction's
refund, fee, deletion fold and touched sweep when its final deletion set omits
that account. Constructor consumers derive both premises from their source run. -/
theorem TransactionTrace.getCode_getStor_of_message_nonempty
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput} {target : Adr}
    (trace : TransactionTrace benv bout tx index state bout')
    (stateGas : benv.stat.rules.stateGas = none)
    (notDeleted : target ∉ trace.messageOut.accountsToDelete)
    (nonempty : (trace.messageState.getCode target).toList ≠ []) :
    state.getCode target = trace.messageState.getCode target ∧
      state.getStor target = trace.messageState.getStor target := by
  obtain ⟨refund, _, finalState⟩ := trace.exists_selectedFinalStateForm stateGas
  have finalCode := congrArg (fun s => s.getCode target) finalState
  have finalStorage := congrArg (fun s => s.getStor target) finalState
  rw [finalCode, finalStorage]
  exact settled_getCode_getStor_of_code_nonempty
    (fun a member equal => notDeleted (equal ▸ Std.HashSet.mem_toList.mp member)) nonempty

/-- Original admission and debit recover the CREATE address from this
transaction's admitted sender and signed nonce, without a prestate nonce premise. -/
theorem TransactionTrace.creation_target_eq
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (receiver : tx.type.receiver? = none) :
    trace.msg.currentTarget = computeContractAddress trace.sender tx.nonce := by
  have prepared := trace.prepared
  simp only [prepareMessage, receiver] at prepared
  have target : trace.msg.currentTarget = computeContractAddress trace.sender
      (trace.debitState.getNonce trace.sender - 1) :=
    congrArg Msg.currentTarget (Except.ok.inj prepared).symm
  have nonceEq : (benv.state.get trace.sender).nonce = tx.nonce :=
    checkTransaction_sender_nonce trace.checked
  have debitNonce : trace.debitState.getNonce trace.sender = tx.nonce + 1 := by
    rw [(State.of_subBal trace.debit).2]
    change (((benv.state.incrNonce trace.sender).setBal trace.sender _).get trace.sender).nonce = _
    rw [State.setBal_get_nonce]
    simp only [State.incrNonce, State.setAccount_get_self, Acct.clearIfEmpty_nonce, nonceEq]
  rw [target, debitNonce, UInt64.add_sub_cancel]

/-- Carry constructor-local effects through the actual retained CREATE and
the outer transaction. Each producer is checked on that CREATE witness; it
must establish deletion preservation as well as nonempty code and storage. -/
theorem TransactionTrace.getCode_getStor_of_create_effects
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput} {code : ByteArray}
    {window : Bytes} {storage : Stor}
    (trace : TransactionTrace benv bout tx index state bout')
    (stateGas : benv.stat.rules.stateGas = none)
    (receiver : tx.type.receiver? = none) (input : tx.data = code.toList)
    (clean : trace.messageOut.error = none) (nonempty : window ≠ [])
    (effects : ∀ {installed}, ProcessCreateMessageTrace trace.msg (.ok installed) →
      installed.error.isSome = false →
      installed.accountsToDelete = trace.msg.inheritedDeletions ∧
        (installed.getCode trace.msg.currentTarget).toList = window ∧
        installed.getStor trace.msg.currentTarget = storage) :
    (state.getCode trace.msg.currentTarget).toList = window ∧
      state.getStor trace.msg.currentTarget = storage := by
  obtain ⟨target, _, _, _, _, inherited⟩ := trace.creation_message_fields receiver input
  have msgStateGas : trace.msg.benv.stat.rules.stateGas = none := by
    rw [prepareMessage_benv trace.prepared]
    exact stateGas
  obtain ⟨installed, ⟨retained⟩, _, _, innerClean, sameState, deletions⟩ :=
    trace.message.exists_clean_create_with_deletions
      (by rw [target]; rfl) msgStateGas clean
  obtain ⟨preserved, codeEq, storageEq⟩ := effects retained (by rw [innerClean]; rfl)
  have noDelete : trace.msg.currentTarget ∉ trace.messageOut.accountsToDelete := by
    rw [deletions, preserved, inherited]
    exact AdrSet.not_mem_empty
  have messageCode : (trace.messageState.getCode trace.msg.currentTarget).toList = window := by
    rw [sameState]
    exact codeEq
  have messageStorage : trace.messageState.getStor trace.msg.currentTarget = storage := by
    rw [sameState]
    exact storageEq
  have final := trace.getCode_getStor_of_message_nonempty stateGas noDelete
    (fun empty => nonempty (messageCode.symm.trans empty))
  exact ⟨(congrArg ByteArray.toList final.1).trans messageCode, final.2.trans messageStorage⟩

end Blanc.ExecutionTrace

namespace Blanc.Lift

open Jaune ExecutionTrace

/-- A checked balance-silent constructor preserves its inherited deletions
through the actual source run, touch, code charge and installation. -/
theorem createTrace_deletions_of_balSilent
    {code : ByteArray} {c : Cert} {entry : SFunc} {S : List Nat}
    {msg : Msg} {installed : Devm}
    (checked : Cert.check code c = true) (codeEq : msg.code = code)
    (first : c.prog[0]? = some entry)
    (closed : BalSilentSet c.prog S = true)
    (silent : entry.balSilent = true) (refs : entry.refs.all (· ∈ S) = true)
    (trace : ProcessCreateMessageTrace msg (.ok installed))
    (clean : installed.error.isSome = false) (codeAddress : msg.codeAddress = none)
    (stateGas : msg.benv.stat.rules.stateGas = none) :
    installed.accountsToDelete = msg.inheritedDeletions := by
  obtain ⟨benv, raw, charged, transfer, executed, rawClean, charge, source, installedEq⟩ :=
    createTrace_source_witness checked codeEq first trace clean codeAddress stateGas
  have frame := SFunc.RunP.balance_deletion_frame_of_balSilent (fun h => h)
    closed silent refs source
  have rawDeletion : raw.accountsToDelete = msg.inheritedDeletions :=
    congrArg (fun p => p.2.1) frame
  have chargedDeletion := congrArg Prod.fst (chargeCodeGas_delSets_ok charge)
  rw [installedEq]
  change charged.accountsToDelete = msg.inheritedDeletions
  exact chargedDeletion.trans rawDeletion

/-- The two helper entries reached by the legacy owner constructor form a
closed balance-silent set. No runtime-byte or historical assumption is used. -/
theorem legacyOwnerConstructor_balSilentSet
    {fs : List SFunc} {sizeBytes offsetBytes : Bytes}
    {sizeBound : sizeBytes.length ≤ 32} {offsetBound : offsetBytes.length ≤ 32}
    (ownerEntry : fs[1]? = some SolcStorageReturn.legacyOwnerInit)
    (returnEntry : fs[2]? = some (solcRuntimeReturn sizeBytes offsetBytes sizeBound offsetBound)) :
    BalSilentSet fs [1, 2] = true := by
  simp only [BalSilentSet, List.all_cons, List.all_nil, ownerEntry, returnEntry]
  rfl

/-- The actual legacy constructor reaches no deletion-producing instruction. -/
theorem legacyOwnerConstructor_deletions_of_createTrace
    {code : ByteArray} {c : Cert} {msg : Msg} {installed : Devm}
    {sizeBytes offsetBytes : Bytes}
    {sizeBound : sizeBytes.length ≤ 32} {offsetBound : offsetBytes.length ≤ 32}
    (checked : Cert.check code c = true) (codeEq : msg.code = code)
    (first : c.prog[0]? = some legacyOwnerConstructor)
    (ownerEntry : c.prog[1]? = some SolcStorageReturn.legacyOwnerInit)
    (returnEntry : c.prog[2]? = some (solcRuntimeReturn sizeBytes offsetBytes sizeBound offsetBound))
    (trace : ProcessCreateMessageTrace msg (.ok installed))
    (clean : installed.error.isSome = false) (codeAddress : msg.codeAddress = none)
    (stateGas : msg.benv.stat.rules.stateGas = none) :
    installed.accountsToDelete = msg.inheritedDeletions := by
  exact createTrace_deletions_of_balSilent checked codeEq first
    (legacyOwnerConstructor_balSilentSet ownerEntry returnEntry) rfl rfl
    trace clean codeAddress stateGas

/-- The actual admitted legacy creation transaction installs the returned
runtime window and owner storage through its complete settlement. Source
execution proves deletion exclusion; successful entry value is arbitrary. -/
theorem legacyOwnerConstructor_effects_of_transactionTrace
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput} {code : ByteArray} {c : Cert}
    {sizeBytes offsetBytes : Bytes}
    {sizeBound : sizeBytes.length ≤ 32} {offsetBound : offsetBytes.length ≤ 32}
    {size offset : B256}
    (checked : Cert.check code c = true)
    (first : c.prog[0]? = some legacyOwnerConstructor)
    (ownerEntry : c.prog[1]? = some SolcStorageReturn.legacyOwnerInit)
    (returnEntry : c.prog[2]? = some (solcRuntimeReturn sizeBytes offsetBytes sizeBound offsetBound))
    (sizeWord : sizeBytes.toB256 = size) (offsetWord : offsetBytes.toB256 = offset)
    (nonzero : size.toNat ≠ 0)
    (trace : TransactionTrace benv bout tx index state bout')
    (stateGas : benv.stat.rules.stateGas = none)
    (receiver : tx.type.receiver? = none) (input : tx.data = code.toList)
    (clean : trace.messageOut.error = none) :
    (state.getCode trace.msg.currentTarget).toList =
        code.sliceD offset.toNat size.toNat (Linst.toUInt8 .stop) ∧
      state.getStor trace.msg.currentTarget =
        solcOwnerConstructorStorage Stor.empty trace.sender := by
  obtain ⟨_, codeEq, codeAddress, caller, _, _⟩ :=
    trace.creation_message_fields receiver input
  have msgStateGas : trace.msg.benv.stat.rules.stateGas = none := by
    rw [prepareMessage_benv trace.prepared]
    exact stateGas
  refine trace.getCode_getStor_of_create_effects stateGas receiver input clean ?_ ?_
  · intro empty
    have length := congrArg List.length empty
    rw [ByteArray.length_sliceD, List.length_nil] at length
    exact nonzero length
  · intro installed retained innerClean
    refine ⟨legacyOwnerConstructor_deletions_of_createTrace checked codeEq first
      ownerEntry returnEntry retained innerClean codeAddress msgStateGas, ?_⟩
    have effects := legacyOwnerConstructor_effects_of_createTrace checked codeEq first
      ownerEntry returnEntry sizeWord offsetWord nonzero retained innerClean codeAddress msgStateGas
    rw [caller] at effects
    exact effects

/-- The successful receipt in the original configured block supplies the
clean transaction result. Installation is at this exact cut's after-state. -/
theorem legacyOwnerConstructor_effects_of_txSplit_receipt
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    {code : ByteArray} {c : Cert} {sizeBytes offsetBytes : Bytes}
    {sizeBound : sizeBytes.length ≤ 32} {offsetBound : offsetBytes.length ≤ 32}
    {size offset : B256}
    (checked : Cert.check code c = true)
    (first : c.prog[0]? = some legacyOwnerConstructor)
    (ownerEntry : c.prog[1]? = some SolcStorageReturn.legacyOwnerInit)
    (returnEntry : c.prog[2]? = some (solcRuntimeReturn sizeBytes offsetBytes sizeBound offsetBound))
    (sizeWord : sizeBytes.toB256 = size) (offsetWord : offsetBytes.toB256 = offset)
    (nonzero : size.toNat ≠ 0)
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (stateGas : block.fork.ruleSet.stateGas = none)
    (receiver : cut.tx.type.receiver? = none) (input : cut.tx.data = code.toList)
    {receipt : Fin 5 × Receipt}
    (lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes cut.index.toBytes)]? =
      some receipt) (succeeded : receipt.2.succeeded = true) :
    (cut.afterBenv.state.getCode cut.head.msg.currentTarget).toList =
        code.sliceD offset.toNat size.toNat (Linst.toUInt8 .stop) ∧
      cut.afterBenv.state.getStor cut.head.msg.currentTarget =
        solcOwnerConstructorStorage Stor.empty cut.head.sender := by
  have cutStateGas : cut.benv.stat.rules.stateGas = none := by
    have stat : cut.benv.stat = (initBenv block.fork pre block.block.header).stat :=
      block.txSplit_stat cut
    rw [stat]
    exact stateGas
  exact legacyOwnerConstructor_effects_of_transactionTrace checked first ownerEntry returnEntry
    sizeWord offsetWord nonzero cut.head cutStateGas receiver input
    (block.txSplit_error_eq_none_of_receipt cut stateGas lookup succeeded)

/-- A proved runtime window and CREATE-address arithmetic specialize the original-cut
installation result. Neither installed code nor constructor storage is assumed. -/
theorem legacyOwnerConstructor_runtime_of_txSplit_receipt
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    {code runtime : ByteArray} {c : Cert} {sizeBytes offsetBytes : Bytes}
    {sizeBound : sizeBytes.length ≤ 32} {offsetBound : offsetBytes.length ≤ 32}
    {size offset : B256} {address : Adr}
    (checked : Cert.check code c = true)
    (first : c.prog[0]? = some legacyOwnerConstructor)
    (ownerEntry : c.prog[1]? = some SolcStorageReturn.legacyOwnerInit)
    (returnEntry : c.prog[2]? = some (solcRuntimeReturn sizeBytes offsetBytes sizeBound offsetBound))
    (sizeWord : sizeBytes.toB256 = size) (offsetWord : offsetBytes.toB256 = offset)
    (nonzero : size.toNat ≠ 0)
    (window : code.sliceD offset.toNat size.toNat (Linst.toUInt8 .stop) = runtime.toList)
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (stateGas : block.fork.ruleSet.stateGas = none)
    (receiver : cut.tx.type.receiver? = none) (input : cut.tx.data = code.toList)
    (addressEq : computeContractAddress cut.head.sender cut.tx.nonce = address)
    {receipt : Fin 5 × Receipt}
    (lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes cut.index.toBytes)]? =
      some receipt) (succeeded : receipt.2.succeeded = true) :
    cut.afterBenv.state.getCode address = runtime ∧
      cut.afterBenv.state.getStor address =
        solcOwnerConstructorStorage Stor.empty cut.head.sender := by
  have effects := legacyOwnerConstructor_effects_of_txSplit_receipt checked first ownerEntry
    returnEntry sizeWord offsetWord nonzero block cut stateGas receiver input lookup succeeded
  have target := (cut.head.creation_target_eq receiver).trans addressEq
  rw [target] at effects
  refine ⟨?_, effects.2⟩
  apply ByteArray.ext
  rw [← Array.toList_inj]
  simpa only [ByteArray.toList_eq_toList_data] using effects.1.trans window

/-- The two helper entries reached by the modern owner constructor form a
closed balance-silent set. No runtime-byte or historical assumption is used. -/
theorem solcOwnerConstructor_balSilentSet
    {fs : List SFunc} {sizeBytes offsetBytes : Bytes}
    {sizeBound : sizeBytes.length ≤ 32} {offsetBound : offsetBytes.length ≤ 32}
    (ownerEntry : fs[1]? = some SolcStorageReturn.ownerInit)
    (returnEntry : fs[2]? = some (solcRuntimeReturn sizeBytes offsetBytes sizeBound offsetBound)) :
    BalSilentSet fs [1, 2] = true := by
  simp only [BalSilentSet, List.all_cons, List.all_nil, ownerEntry, returnEntry]
  rfl

/-- The actual modern constructor reaches no deletion-producing instruction. -/
theorem solcOwnerConstructor_deletions_of_createTrace
    {code : ByteArray} {c : Cert} {msg : Msg} {installed : Devm}
    {sizeBytes offsetBytes : Bytes}
    {sizeBound : sizeBytes.length ≤ 32} {offsetBound : offsetBytes.length ≤ 32}
    (checked : Cert.check code c = true) (codeEq : msg.code = code)
    (first : c.prog[0]? = some solcOwnerConstructor)
    (ownerEntry : c.prog[1]? = some SolcStorageReturn.ownerInit)
    (returnEntry : c.prog[2]? = some (solcRuntimeReturn sizeBytes offsetBytes sizeBound offsetBound))
    (trace : ProcessCreateMessageTrace msg (.ok installed))
    (clean : installed.error.isSome = false) (codeAddress : msg.codeAddress = none)
    (stateGas : msg.benv.stat.rules.stateGas = none) :
    installed.accountsToDelete = msg.inheritedDeletions := by
  exact createTrace_deletions_of_balSilent checked codeEq first
    (solcOwnerConstructor_balSilentSet ownerEntry returnEntry) rfl rfl
    trace clean codeAddress stateGas

/-- The modern checked owner constructor installs its runtime window and
owner storage through complete transaction settlement; deletion preservation
is derived from the same checked source, without an exclusion oracle. -/
theorem solcOwnerConstructor_effects_of_transactionTrace
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput} {code : ByteArray} {c : Cert}
    {sizeBytes offsetBytes : Bytes}
    {sizeBound : sizeBytes.length ≤ 32} {offsetBound : offsetBytes.length ≤ 32}
    {size offset : B256}
    (checked : Cert.check code c = true)
    (first : c.prog[0]? = some solcOwnerConstructor)
    (ownerEntry : c.prog[1]? = some SolcStorageReturn.ownerInit)
    (returnEntry : c.prog[2]? = some (solcRuntimeReturn sizeBytes offsetBytes sizeBound offsetBound))
    (sizeWord : sizeBytes.toB256 = size) (offsetWord : offsetBytes.toB256 = offset)
    (nonzero : size.toNat ≠ 0)
    (trace : TransactionTrace benv bout tx index state bout')
    (stateGas : benv.stat.rules.stateGas = none)
    (receiver : tx.type.receiver? = none) (input : tx.data = code.toList)
    (clean : trace.messageOut.error = none) :
    (state.getCode trace.msg.currentTarget).toList =
        code.sliceD offset.toNat size.toNat (Linst.toUInt8 .stop) ∧
      state.getStor trace.msg.currentTarget =
        solcOwnerConstructorStorage Stor.empty trace.sender := by
  obtain ⟨_, codeEq, codeAddress, caller, _, _⟩ :=
    trace.creation_message_fields receiver input
  have msgStateGas : trace.msg.benv.stat.rules.stateGas = none := by
    rw [prepareMessage_benv trace.prepared]
    exact stateGas
  refine trace.getCode_getStor_of_create_effects stateGas receiver input clean ?_ ?_
  · intro empty
    have length := congrArg List.length empty
    rw [ByteArray.length_sliceD, List.length_nil] at length
    exact nonzero length
  · intro installed retained innerClean
    refine ⟨solcOwnerConstructor_deletions_of_createTrace checked codeEq first
      ownerEntry returnEntry retained innerClean codeAddress msgStateGas, ?_⟩
    have effects := solcOwnerConstructor_effects_of_createTrace checked codeEq first
      ownerEntry returnEntry sizeWord offsetWord nonzero retained innerClean codeAddress msgStateGas
    rw [caller] at effects
    exact effects.2

/-- The successful receipt in the original configured block supplies the
clean transaction result. Installation is at this exact cut's after-state. -/
theorem solcOwnerConstructor_effects_of_txSplit_receipt
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    {code : ByteArray} {c : Cert} {sizeBytes offsetBytes : Bytes}
    {sizeBound : sizeBytes.length ≤ 32} {offsetBound : offsetBytes.length ≤ 32}
    {size offset : B256}
    (checked : Cert.check code c = true)
    (first : c.prog[0]? = some solcOwnerConstructor)
    (ownerEntry : c.prog[1]? = some SolcStorageReturn.ownerInit)
    (returnEntry : c.prog[2]? = some (solcRuntimeReturn sizeBytes offsetBytes sizeBound offsetBound))
    (sizeWord : sizeBytes.toB256 = size) (offsetWord : offsetBytes.toB256 = offset)
    (nonzero : size.toNat ≠ 0)
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (stateGas : block.fork.ruleSet.stateGas = none)
    (receiver : cut.tx.type.receiver? = none) (input : cut.tx.data = code.toList)
    {receipt : Fin 5 × Receipt}
    (lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes cut.index.toBytes)]? =
      some receipt) (succeeded : receipt.2.succeeded = true) :
    (cut.afterBenv.state.getCode cut.head.msg.currentTarget).toList =
        code.sliceD offset.toNat size.toNat (Linst.toUInt8 .stop) ∧
      cut.afterBenv.state.getStor cut.head.msg.currentTarget =
        solcOwnerConstructorStorage Stor.empty cut.head.sender := by
  have cutStateGas : cut.benv.stat.rules.stateGas = none := by
    have stat : cut.benv.stat = (initBenv block.fork pre block.block.header).stat :=
      block.txSplit_stat cut
    rw [stat]
    exact stateGas
  exact solcOwnerConstructor_effects_of_transactionTrace checked first ownerEntry returnEntry
    sizeWord offsetWord nonzero cut.head cutStateGas receiver input
    (block.txSplit_error_eq_none_of_receipt cut stateGas lookup succeeded)

/-- A proved runtime window and CREATE-address arithmetic specialize the original-cut
installation result. Neither installed code nor constructor storage is assumed. -/
theorem solcOwnerConstructor_runtime_of_txSplit_receipt
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    {code runtime : ByteArray} {c : Cert} {sizeBytes offsetBytes : Bytes}
    {sizeBound : sizeBytes.length ≤ 32} {offsetBound : offsetBytes.length ≤ 32}
    {size offset : B256} {address : Adr}
    (checked : Cert.check code c = true)
    (first : c.prog[0]? = some solcOwnerConstructor)
    (ownerEntry : c.prog[1]? = some SolcStorageReturn.ownerInit)
    (returnEntry : c.prog[2]? = some (solcRuntimeReturn sizeBytes offsetBytes sizeBound offsetBound))
    (sizeWord : sizeBytes.toB256 = size) (offsetWord : offsetBytes.toB256 = offset)
    (nonzero : size.toNat ≠ 0)
    (window : code.sliceD offset.toNat size.toNat (Linst.toUInt8 .stop) = runtime.toList)
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (stateGas : block.fork.ruleSet.stateGas = none)
    (receiver : cut.tx.type.receiver? = none) (input : cut.tx.data = code.toList)
    (addressEq : computeContractAddress cut.head.sender cut.tx.nonce = address)
    {receipt : Fin 5 × Receipt}
    (lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes cut.index.toBytes)]? =
      some receipt) (succeeded : receipt.2.succeeded = true) :
    cut.afterBenv.state.getCode address = runtime ∧
      cut.afterBenv.state.getStor address =
        solcOwnerConstructorStorage Stor.empty cut.head.sender := by
  have effects := solcOwnerConstructor_effects_of_txSplit_receipt checked first ownerEntry
    returnEntry sizeWord offsetWord nonzero block cut stateGas receiver input lookup succeeded
  have target := (cut.head.creation_target_eq receiver).trans addressEq
  rw [target] at effects
  refine ⟨?_, effects.2⟩
  apply ByteArray.ext
  rw [← Array.toList_inj]
  simpa only [ByteArray.toList_eq_toList_data] using effects.1.trans window

end Blanc.Lift

namespace Blanc.ExecutionTrace

open Jaune

/-- A certified CREATE segment and later terminal safety carry a newly
installed nonempty runtime through the same outer transaction. Earlier
SELFDESTRUCT contexts are excluded by actual CREATE admission and chronology;
the constructor certificate excludes its own terminals. Only the later
runtime/delegation classifier remains a caller obligation. -/
theorem TransactionTrace.created_runtime_survives_of_later_terminal_safe
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (stateGas : benv.stat.rules.stateGas = none)
    {R : Exec.Frame} (root : R ∈ trace.settledRoots)
    (rootGas : R.sevm.benvStat.rules.stateGas = none)
    {before after : List Exec.Deriv} {spawnNode observed : Exec.Deriv}
    {frame : Frame} {resume : Resume} {pc' : Nat} {child : Evm} {raw : Execution}
    (step : Evm.step ⟨spawnNode.pc, spawnNode.sevm, spawnNode.devm⟩ =
      .spawn frame resume pc')
    (enter : frame.enter = .run child) (create : frame.isCreate = true)
    (childRun : Exec child.pc child.sta child.dyna raw)
    (nodeGas : spawnNode.sevm.benvStat.rules.stateGas = none)
    (chronology : Exec.retainedNodes R.run =
      before ++ spawnNode :: (Exec.retainedNodes childRun ++ after))
    {constructorCode : ByteArray} {certificate : Lift.Cert}
    (checked : Lift.Cert.check constructorCode certificate = true)
    (constructorImage : child.sta.code = constructorCode)
    (noExecs : ∀ f ∈ certificate.prog, f.execsSatisfy (fun _ => false) = true)
    (noSelfdestruct : certificate.noSelfdestruct = true)
    (laterSafe : ∀ n ∈ after, n.sevm.currentTarget = frame.inner.currentTarget →
      ¬ Linst.At n.sevm.code n.pc .selfdestruct)
    (observation : observed ∈ after)
    (runtimeNonempty : (observed.devm.getCode frame.inner.currentTarget).toList ≠ []) :
    frame.inner.currentTarget ∉ trace.messageOut.accountsToDelete ∧
      state.getCode frame.inner.currentTarget = observed.devm.getCode frame.inner.currentTarget := by
  have constructorSafe := Lift.rawNodes_not_selfdestruct_of_noExecs_noStateGas
    (F := ⟨child.pc, child.sta, child.dyna, raw, childRun⟩)
    checked noExecs noSelfdestruct (Frame.enter_run_pc enter) constructorImage
    (by rw [Evm.step_spawn_child_benvStat step enter]; exact nodeGas)
  have allSafe : ∀ n ∈ Exec.retainedNodes R.run,
      n.sevm.currentTarget = frame.inner.currentTarget →
      ¬ Linst.At n.sevm.code n.pc .selfdestruct := by
    intro n member target destruct
    rw [chronology] at member
    rcases List.mem_append.mp member with earlier | rest
    · obtain ⟨first, middle, same⟩ := List.append_of_mem earlier
      have ordered : Exec.retainedNodes R.run =
          first ++ n :: (middle ++ spawnNode :: (Exec.retainedNodes childRun ++ after)) := by
        rw [chronology, same]
        simp only [List.append_assoc, List.cons_append]
      exact (trace.settledRoot_create_ne_of_earlier_selfdestruct root rootGas
        ordered destruct nodeGas step create) target.symm
    · rcases List.mem_cons.mp rest with equal | inTail
      · subst n
        obtain ⟨x, decoded, _, _⟩ := Evm.step_spawn_inv step
        unfold Xinst.At at decoded
        unfold Linst.At at destruct
        rw [decoded] at destruct
        cases destruct
      · rcases List.mem_append.mp inTail with inConstructor | later
        · exact constructorSafe n
            ((Exec.retainedNodes_sublist_rawNodes childRun).subset inConstructor) destruct
        · exact laterSafe n later target destruct
  have retained : observed ∈ Exec.retainedNodes R.run := by
    rw [chronology]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ observation))
  exact ⟨trace.not_deleted_of_retained_terminal_safe stateGas root allSafe,
    trace.retainedNode_getCode_of_terminal_safe stateGas root retained runtimeNonempty allSafe⟩

end Blanc.ExecutionTrace
