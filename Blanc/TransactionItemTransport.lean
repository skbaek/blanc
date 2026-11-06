import Blanc.ExecutionTrieBinding
import Blanc.TransactionHistoricalForward

/-!
# A transaction's trace depends only on its RLP item

`Tx.toBLT` trims leading zero bytes of the signature scalars, so a block's transaction trie fixes a
legacy slot's `Tx` only up to those bytes. Those bytes are not observable in execution: sender
recovery reads the scalars as words, the transaction hash reads the RLP item, and nothing else reads
them. `TransactionTrace.ofItem` carries a retained transaction trace to any legacy transaction with
the same RLP item: the same prepared message, the same message trace and the same state. Only the
transaction output's transaction trie differs, which holds the `Tx` itself.

`HoldsItem slots i tx` says slot `i` holds a legacy transaction with `tx`'s RLP item: what a block's
transaction root can say about a slot. `StagedBodyTrace.txSplitOfItem` cuts a body there, and
`StagedBodyTrace.exists_item_head` gives that cut's trace at `tx` itself.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- Legacy transactions with one RLP item differ at most in their signature scalars' bytes. -/
theorem legacy_eq_of_item {tx tx' : Tx} {gasPrice gasPrice' : Nat} {receiver receiver' : Option Adr}
    (type : tx.type = .zero gasPrice receiver) (type' : tx'.type = .zero gasPrice' receiver')
    (same : tx.toBLT = tx'.toBLT) : tx' = { tx with r := tx'.r, s := tx'.s } := by
  obtain ⟨nonce, price, gas, rcv, value, data, v, -, -⟩ := legacy_fields_of_toBLT_eq type type' same
  obtain ⟨n, g, va, d, w, r, s, ty⟩ := tx
  obtain ⟨n', g', va', d', w', r', s', ty'⟩ := tx'
  dsimp only at type type' nonce price gas rcv value data v
  subst type type' price rcv nonce gas value data v
  rfl

section Sig

variable (tx : Tx) (r s : Bytes)

/-- Validation does not read the signature. -/
theorem validateTransaction_sig (rules : ForkRules) (sender : Adr) :
    validateTransaction rules { tx with r := r, s := s } sender =
      validateTransaction rules tx sender := rfl

variable {tx r s}

/-- Sender recovery reads the signature's scalars as words. -/
theorem recoverSender_sig (chainId : UInt64) (hr : r.toB256 = tx.r.toB256)
    (hs : s.toB256 = tx.s.toB256) :
    recoverSender chainId { tx with r := r, s := s } = recoverSender chainId tx := by
  unfold recoverSender
  dsimp only
  rw [hr, hs]
  rfl

/-- Admission reads the signature only through sender recovery, and the block output only through
its gas counters. -/
theorem checkTransaction_sig (benv : Benv) (bout : BlockOutput) (index : Nat)
    (hr : r.toB256 = tx.r.toB256) (hs : s.toB256 = tx.s.toB256) :
    checkTransaction benv (transactionPreludeBout bout { tx with r := r, s := s } index)
        { tx with r := r, s := s } =
      checkTransaction benv (transactionPreludeBout bout tx index) tx := by
  unfold checkTransaction
  rw [recoverSender_sig _ hr hs]
  rfl

/-- The transaction environment reads the signature only through the transaction hash. -/
theorem transactionTenv_sig (benv : Benv) (index : Nat) (sender : Adr)
    (effectiveGasPrice intrinsicGas : Nat) (blobVersionedHashes : List B256)
    (hash : getTxHash { tx with r := r, s := s } = getTxHash tx) :
    transactionTenv benv { tx with r := r, s := s } index sender effectiveGasPrice intrinsicGas
        blobVersionedHashes =
      transactionTenv benv tx index sender effectiveGasPrice intrinsicGas blobVersionedHashes := by
  unfold transactionTenv
  rw [hash]
  rfl

end Sig

section Transport

variable {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat} {state : State}
  {bout' : BlockOutput} {r s : Bytes}

/-- With no state gas, validation runs at the zero sender. -/
theorem TransactionTrace.validation_zero (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none) :
    validateTransaction benv.stat.rules tx 0 =
      .ok (trace.intrinsicGas, trace.calldataFloorGasCost) := by
  have run := trace.validationSender_run
  have hsg' : benv.beginTransaction.stat.rules.stateGas = none := hsg
  rw [hsg'] at run
  have zero : trace.validationSender = 0 := (Except.ok.inj run).symm
  rw [← zero]
  exact trace.validation

/-- The trace's transaction with other signature bytes settles to the same state. -/
theorem TransactionTrace.process_sig (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none) (hbal : benv.stat.rules.bal = none)
    (hr : r.toB256 = tx.r.toB256) (hs : s.toB256 = tx.s.toB256)
    (hash : getTxHash { tx with r := r, s := s } = getTxHash tx) :
    ∃ bout'', processTransaction benv bout { tx with r := r, s := s } index = .ok (state, bout'') := by
  obtain ⟨refund, hrefund, -⟩ := trace.exists_selectedFinalStateForm hsg
  obtain ⟨_, original, -⟩ := processTransaction_of_stages_selected_receipts hsg hbal
    (trace.validation_zero hsg) trace.checked trace.debit trace.prepared trace.message.result hrefund
  have sameState := (Prod.mk.inj (Except.ok.inj (trace.result.symm.trans original))).1
  obtain ⟨bout'', moved, -⟩ := processTransaction_of_stages_selected_receipts
    (tx := { tx with r := r, s := s }) hsg hbal
    ((validateTransaction_sig tx r s _ _).trans (trace.validation_zero hsg))
    ((checkTransaction_sig _ _ _ hr hs).trans trace.checked) trace.debit
    (by
      rw [transactionTenv_sig _ _ _ _ _ _ hash]
      exact trace.prepared)
    trace.message.result hrefund
  refine ⟨bout'', ?_⟩
  rw [sameState]
  exact moved

/-- **A retained transaction trace, carried to other signature bytes.** The message and its trace
are the same; only the block output's transaction trie differs. -/
noncomputable def TransactionTrace.ofSig (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none) (hbal : benv.stat.rules.bal = none)
    (hr : r.toB256 = tx.r.toB256) (hs : s.toB256 = tx.s.toB256)
    (hash : getTxHash { tx with r := r, s := s } = getTxHash tx) :
    TransactionTrace benv bout { tx with r := r, s := s } index state
      (Classical.choose (trace.process_sig hsg hbal hr hs hash)) where
  validationSender := trace.validationSender
  intrinsicGas := trace.intrinsicGas
  calldataFloorGasCost := trace.calldataFloorGasCost
  sender := trace.sender
  effectiveGasPrice := trace.effectiveGasPrice
  blobVersionedHashes := trace.blobVersionedHashes
  txBlobGasUsed := trace.txBlobGasUsed
  debitState := trace.debitState
  msg := trace.msg
  messageState := trace.messageState
  messageOut := trace.messageOut
  validation := trace.validation
  checked := (checkTransaction_sig _ _ _ hr hs).trans trace.checked
  debit := trace.debit
  prepared := by
    rw [transactionTenv_sig _ _ _ _ _ _ hash]
    exact trace.prepared
  message := trace.message
  result := Classical.choose_spec (trace.process_sig hsg hbal hr hs hash)
  validationSender_run := by
    have run := trace.validationSender_run
    have hsg' : benv.beginTransaction.stat.rules.stateGas = none := hsg
    rw [hsg'] at run ⊢
    exact run

end Transport

/-- The hash reads the RLP item. -/
theorem getTxHash_of_item {tx tx' : Tx} (same : tx.toBLT = tx'.toBLT) :
    getTxHash tx = getTxHash tx' := by
  unfold getTxHash
  rw [same]

/-- **A retained legacy trace, at any legacy transaction with the same RLP item.** The same state and
the same message output and frames; only the block output's transaction trie differs. -/
theorem TransactionTrace.exists_of_item {benv : Benv} {bout : BlockOutput} {tx tx' : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none) (hbal : benv.stat.rules.bal = none)
    {gasPrice gasPrice' : Nat} {receiver receiver' : Option Adr}
    (type : tx.type = .zero gasPrice receiver) (type' : tx'.type = .zero gasPrice' receiver')
    (same : tx.toBLT = tx'.toBLT) :
    ∃ (bout'' : BlockOutput) (moved : TransactionTrace benv bout tx' index state bout''),
      moved.settledFrames = trace.settledFrames ∧ moved.messageOut = trace.messageOut := by
  obtain ⟨-, -, -, -, -, -, -, hr, hs⟩ := legacy_fields_of_toBLT_eq type type' same
  have hash := getTxHash_of_item same
  obtain ⟨r, s, rfl⟩ : ∃ r s, tx' = { tx with r := r, s := s } :=
    ⟨_, _, legacy_eq_of_item type type' same⟩
  exact ⟨_, trace.ofSig hsg hbal hr.symm hs.symm hash.symm, rfl, rfl⟩

/-- Slot `i` holds a legacy transaction with `tx`'s RLP item. -/
def HoldsItem (slots : List (Bytes ⊕ Tx)) (i : Nat) (tx : Tx) : Prop :=
  ∃ tx₀ gasPrice receiver, slots[i]? = some (.inr tx₀) ∧ tx₀.type = .zero gasPrice receiver ∧
    tx₀.toBLT = tx.toBLT

section Body

variable {benv : Benv} {slots : List (Bytes ⊕ Tx)} {ommers : List Header} {wds : List Withdrawal}
  {state : State} {bout : BlockOutput} (body : StagedBodyTrace benv slots ommers wds state bout)
  {i : Nat} {tx : Tx}

/-- The body's cut at a slot holding an item. -/
noncomputable def StagedBodyTrace.txSplitOfItem (held : HoldsItem slots i tx) :
    body.transactions.TxSplit i := by
  apply body.transactions.splitAt i
  rw [indexedTransactions_length]
  obtain ⟨tx₀, _, _, atIndex, -, -⟩ := held
  exact (List.getElem?_eq_some_iff.mp (body.decodedTxs_getElem_of_slot (tx := tx₀) atIndex rfl)).1

/-- **The trace at a slot holding `tx`'s item, at `tx` itself.** Whatever the slot's signature bytes,
any cut there has a trace of the legacy transaction `tx`, with the cut's state, frames and message
output. -/
theorem StagedBodyTrace.exists_item_head (cut : body.transactions.TxSplit i)
    (held : HoldsItem slots i tx) {gasPrice : Nat} {receiver : Option Adr}
    (type : tx.type = .zero gasPrice receiver)
    (hsg : cut.benv.stat.rules.stateGas = none) (hbal : cut.benv.stat.rules.bal = none) :
    cut.index = i ∧ ∃ (bout'' : BlockOutput)
      (head : TransactionTrace cut.benv cut.bout tx cut.index cut.txState bout''),
      head.settledFrames = cut.head.settledFrames ∧ head.messageOut = cut.head.messageOut := by
  obtain ⟨tx₀, _, _, atIndex, type₀, same⟩ := held
  obtain ⟨index, sameTx⟩ := body.txSplit_tx_eq_of_slot cut (tx := tx₀) atIndex rfl
  refine ⟨index, ?_⟩
  obtain ⟨_, tx₁, _, _, _, _, _, _, head, _, _, _⟩ := cut
  dsimp only at sameTx hsg hbal index ⊢
  subst sameTx
  exact head.exists_of_item hsg hbal type₀ type same

end Body

end Blanc.ExecutionTrace
