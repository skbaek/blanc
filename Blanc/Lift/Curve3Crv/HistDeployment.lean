import Blanc.Lift.Curve3Crv.Creation.HistoricalTxTrace
import Blanc.Lift.Curve3Crv.HistCommittedHistory
import Blanc.ExecutionBodyTransactionCut

/-!
# 3Crv from its actual deployment: the deployment record and the whole-span headline

`C3crvDeploymentTo checkpoint` is the single deployment premise for the 3Crv LP token at a
later `checkpoint`: the retained `HistFork` mainnet block that deployed it (block 10,809,467,
timestamp 1,599,414,946), its slot 76 holding the recorded signed creation transaction
`Creation.HistoricalTx.tx`, that slot's successful receipt, the configured history from the
end of that block to `checkpoint`, and trace-local freshness (HASH-T) of the keys the raw
token frames of the rest of the block and that history may touch. Funds, gas, nonce, sender
code, target freshness, the installed code, the deployed storage and the initial invariant are
theorems, not fields.

Derived API, for the conservation and policy headlines:

* `C3crvDeploymentTo.cut` / `.trace` / `.invocations` / `.keys` — the creation cut, the mid
  history after it, the settlement-committed writer invocations at the token from the
  transaction after the creation onwards, and the tracked keys they extend;
* `.created` — right after the creation transaction the token holds the certified runtime and
  the storage `deployedStor deployer`, with `VyInv` for `curveDeployedState deployer` (minter
  the deployer, supply and balances zero) over no live keys;
* `.history_from_deployment` — the model run, from that deployed state, over exactly the
  committed invocations, each step justified by its frame's `OwnerAnswerH` owner evidence, ending
  in the state the checkpoint storage represents, whose total supply equals the sum of its
  balances; `.frames` carries the same run frame by frame (each committed frame's own opening and
  closing storage abstract its model step), which the public headlines in `Headline.lean` read.
-/

namespace Blanc.Lift.Curve3Crv

open Jaune Blanc.ExecutionTrace Blanc.Lift.Curve3Crv.Creation

/-- **The 3Crv deployment record**: the actual creation transaction in its retained Muir block,
its successful receipt, the later configured history to `checkpoint`, and HASH-T. -/
structure C3crvDeploymentTo (checkpoint : BlockChain) where
  pre : BlockChain
  completed : BlockChain
  block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed
  number : block.block.header.number = 10809467
  time : block.block.header.timestamp = 1599414946
  entry : Bytes ⊕ Tx
  slot : block.block.txs[76]? = some entry
  decoded : decodeTx block.fork.ruleSet entry = .ok HistoricalTx.tx
  receipt : Fin 5 × Receipt
  lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes (76 : Nat).toBytes)]? =
    some receipt
  succeeded : receipt.2.succeeded = true
  history : ConfiguredHistoryTraceIn HistFork mainnetChainConfig completed checkpoint
  fresh : FreshKeys (fun _ => False)
    (midTouchedKeysIn tokenAddress
      ((MidHistoryTraceIn.tail block (block.bodyTrace.txSplitOfSlot slot decoded)).append
        history))

namespace C3crvDeploymentTo

variable {checkpoint : BlockChain} (d : C3crvDeploymentTo checkpoint)

/-- The creation transaction's cut of the deployment block. -/
noncomputable def cut : d.block.bodyTrace.transactions.TxSplit 76 :=
  d.block.bodyTrace.txSplitOfSlot d.slot d.decoded

/-- The rest of the deployment block followed by the history to the checkpoint. -/
noncomputable def trace :
    MidHistoryTraceIn HistFork mainnetChainConfig d.cut.afterBenv checkpoint :=
  (MidHistoryTraceIn.tail d.block d.cut).append d.history

/-- The settlement-committed writer invocations at the token after its creation, in order. -/
noncomputable def invocations : List WriterInvocation :=
  midCommittedInvocationsIn tokenAddress d.trace

/-- The keys tracked at the checkpoint: those the committed invocations touch. -/
noncomputable def keys : Key → Prop :=
  Key.extend (fun _ => False) (invocationKeys d.invocations)

/-- **The deployment right after the creation transaction.** -/
theorem created :
    (d.cut.afterBenv.state.getCode tokenAddress).toList = Blanc.Lift.Curve3Crv.code.toList ∧
      d.cut.afterBenv.state.getStor tokenAddress = deployedStor deployer.toB256 ∧
      VyInv (d.cut.afterBenv.state.getStor tokenAddress) (curveDeployedState deployer)
        (fun _ => False) := by
  obtain ⟨index, sameTx⟩ := d.block.bodyTrace.txSplitOfSlot_spec d.slot d.decoded
  have lookup : d.block.blockOutput.receiptsTrie[BLT.toBytes (.bytes d.cut.index.toBytes)]? =
      some d.receipt := by
    change d.block.blockOutput.receiptsTrie[BLT.toBytes
      (.bytes (d.block.bodyTrace.txSplitOfSlot d.slot d.decoded).index.toBytes)]? = _
    rw [index]
    exact d.lookup
  obtain ⟨hcode, hstor, -, -⟩ :=
    HistoricalTx.actual_block_cut d.block d.number d.time d.cut sameTx lookup d.succeeded
  have hstor' : d.cut.afterBenv.state.getStor tokenAddress = deployedStor deployer.toB256 := hstor
  exact ⟨hcode, hstor', by rw [hstor']; exact deployedStor_vyInv deployer deployer_balSlot⟩

/-- **3Crv from its actual deployment to the checkpoint.** The runtime stays installed, and the
model run from the deployed state (`curveDeployedState deployer`) over exactly the committed
writer invocations after the creation exists, is justified step by step by `OwnerAnswerH`,
ends in a state the checkpoint storage represents over the touched keys, and conserves supply. -/
theorem history_from_deployment :
    some (checkpoint.state.getCode tokenAddress).toList = c3crvSem.image ∧
      ∃ s, InvRunBy OwnerAnswerH (curveDeployedState deployer) d.invocations s ∧
        runInvocations (curveDeployedState deployer) d.invocations = some s ∧
        VyInv (checkpoint.state.getStor tokenAddress) s d.keys ∧
        Blanc.Curve3Crv.Conserved s := by
  obtain ⟨hcode, -, hinv⟩ := d.created
  have installed : some (d.cut.afterBenv.state.getCode tokenAddress).toList = c3crvSem.image := by
    rw [hcode]
    rfl
  exact c3crv_mid_history_committedHist d.trace installed hinv d.fresh

/-- The keys the raw token frames of the rest of the deployment block and of the history touch,
including frames that later roll back (the keys `fresh` is about). -/
noncomputable def touched : List Key :=
  midTouchedKeysIn tokenAddress d.trace

/-- **The committed replay from the deployment, frame by frame.** The model run from the deployed
state over exactly the committed invocations, each step justified by `OwnerAnswerH`; every committed
invocation's own opening and closing token storage abstract the model step it runs over keys among
`touched`; the checkpoint storage abstracts the final state; and the invocations' keys are among
`touched`. -/
theorem frames :
    ∃ s, InvRunBy OwnerAnswerH (curveDeployedState deployer) d.invocations s ∧
      (∀ inv ∈ d.invocations,
        FrameModelBy OwnerAnswerH tokenAddress (Key.extend (fun _ => False) d.touched) inv) ∧
      VyInv (checkpoint.state.getStor tokenAddress) s d.keys ∧
      ∀ k ∈ invocationKeys d.invocations, Key.extend (fun _ => False) d.touched k := by
  obtain ⟨hcode, -, hinv⟩ := d.created
  have installed : some (d.cut.afterBenv.state.getCode tokenAddress).toList = c3crvSem.image := by
    rw [hcode]
    rfl
  exact (c3crv_mid_history_framesHist d.trace installed hinv d.fresh).2

end C3crvDeploymentTo

end Blanc.Lift.Curve3Crv
