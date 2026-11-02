import Blanc.Composition.LiveUsdcWeth9B26213219WethObserved
import Blanc.Lift.Weth9.Creation.Block.Binding

/-!
# WETH9's creation block anchored at its hash

`WethHashAnchor block` replaces the RPC-supplied creation observation (`WethOriginalObservation`)
by one external fact, the block hash, plus three binding instances of HASH-T's shape: separation
over a two-element list of values the trace itself computes and the recorded one.

| premise | content | kind |
|---|---|---|
| A | `block.block.header.hash = blockHash₀` | the single external fact |
| HASH-B | `headerSep`, `txsSep`, `receiptsSep` | finite, trace-local, satisfiable (`Separated.pair_self`) |
| C | `block` and `history` are configured `HistFork` traces | history validity (no seal check) |
| D | HASH-T over the keys the history touches (`fresh`) | finite, trace-local |

Each HASH-B instance is, in context, the equation it delivers (`Separated.pair_iff`): it fails
only under a Keccak collision (header) or a collision of Jaune's `trie` on two entry lists
(transactions, receipts), not under bad RPC data. The trie instances are structural: no
Merkle–Patricia reduction of `trie` to Keccak is proved. They are stated over entry lists, never
over `NTB` trees (tree equality includes shape).

From the anchor, the kernel-checked header hash (`header₀_hash`), the kernel-checked roots
(`txTrie_root`, `receiptTrie_root`) and the recorded entries at key 85 give the observation
(`WethHashAnchor.observation`); exit, backing and net flow follow through `WethObservedHistory`.
-/

namespace Blanc.Composition.LiveUsdcWeth9B26213219

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Weth9.Creation

/-- The block hash of WETH9's creation block, and HASH-B: Keccak separation of the trace's
header encoding from the recorded one, and `trie` separation of the trace's transaction and
receipt entry lists from the recorded ones. -/
structure WethHashAnchor {pre completed : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed) : Prop where
  hash : block.block.header.hash = Weth9.Creation.Block.blockHash₀
  headerSep : Separated Bytes.keccak
    [(Header.toBLT block.block.header).toBytes, (Header.toBLT Weth9.Creation.Block.header₀).toBytes]
  txsSep : Separated (fun entries => trie (Std.TreeMap.ofList entries ntbCmp))
    [transactionsEntries block.blockOutput, Weth9.Creation.Block.txEntries₀]
  receiptsSep : Separated (fun entries => trie (Std.TreeMap.ofList entries ntbCmp))
    [receiptsEntries block.blockOutput, Weth9.Creation.Block.receiptEntries₀]

/-- The anchored block's observation: number and timestamp from the bound header, the slot-85
legacy transaction and the key-85 receipt from the bound entry lists. -/
theorem WethHashAnchor.observation {pre completed : BlockChain}
    {block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed}
    (anchor : WethHashAnchor block) : WethOriginalObservation block where
  number := Weth9.Creation.Block.number_of_separated anchor.hash anchor.headerSep
  timestamp := Weth9.Creation.Block.timestamp_of_separated anchor.hash anchor.headerSep
  slot := by
    have entries : transactionsEntries block.blockOutput = Weth9.Creation.Block.txEntries₀ :=
      anchor.txsSep.pair_eq <| (block.txsRoot_eq_trie).symm.trans <|
        (Weth9.Creation.Block.txsRoot_of_separated anchor.hash anchor.headerSep).trans
          Weth9.Creation.Block.txTrie_root.symm
    have value : txTrieValue SignedInput.tx = SignedInput.signedBytes :=
      (txTrieValue_of_legacy rfl).trans SignedInput.canonical
    refine block.legacy_slot_of_transactionsEntries (i := 85) rfl ?_ ?_
    · rw [value, SignedInput.signedBytes, List.length_append, List.length_append,
        code_toList_length]
      decide +kernel
    · rw [entries, value]
      exact Weth9.Creation.Block.txEntries₀_creation
  receipt := by
    have entries : receiptsEntries block.blockOutput = Weth9.Creation.Block.receiptEntries₀ :=
      anchor.receiptsSep.pair_eq <| (block.receiptRoot_eq_trie).symm.trans <|
        (Weth9.Creation.Block.receiptRoot_of_separated anchor.hash anchor.headerSep).trans
          Weth9.Creation.Block.receiptTrie_root.symm
    refine block.receipt_of_receiptsEntries ?_ ?_
    · simp only [receiptTrieValue, BLT.toBytes_eq_toBytesS, Nat.toBytes_eq_toBytesS]
      decide +kernel
    · rw [entries]
      exact Weth9.Creation.Block.receiptEntries₀_creation

/-- The anchored original creation block joined to a configured history ending at `checkpoint`,
with HASH-T over the keys that history touches: `WethObservedHistory` with the hash anchor in
place of the observation. -/
structure WethAnchoredHistory (checkpoint : BlockChain) where
  pre : BlockChain
  completed : BlockChain
  block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed
  anchor : WethHashAnchor block
  history : ConfiguredHistoryTraceIn HistFork mainnetChainConfig completed checkpoint
  fresh : Weth9.KeysFresh (fun _ => False)
    (Weth9.midTouchedKeysIn Weth9.Creation.weth9Address
      ((MidHistoryTraceIn.tail block anchor.observation.cut).append history))

/-- The observed history the anchor derives. -/
def WethAnchoredHistory.toObserved {checkpoint : BlockChain}
    (h : WethAnchoredHistory checkpoint) : WethObservedHistory checkpoint :=
  ⟨h.pre, h.completed, h.block, h.anchor.observation, h.history, h.fresh⟩

/-- **WETH9 backing from the block hash.** -/
theorem weth9_backed_anchored {checkpoint : BlockChain} (h : WethAnchoredHistory checkpoint) :
    Weth9.EtherBacked (Weth9.midTouchedKeysIn weth h.toObserved.deployment.trace)
      (checkpoint.state.getStor weth) (checkpoint.state.bal weth) :=
  weth9_backed_observed h.toObserved

/-- **WETH9 net flow from the block hash.** -/
theorem weth9_net_flow_anchored {checkpoint : BlockChain} (h : WethAnchoredHistory checkpoint) :
    Weth9.NetFlow (Weth9.midTouchedKeysIn weth h.toObserved.deployment.trace)
      (Weth9.replayCalls (Weth9.midCommittedInvocationsIn weth h.toObserved.deployment.trace))
      (checkpoint.state.getStor weth) :=
  weth9_net_flow_observed h.toObserved

/-- **WETH9 exit from the block hash.** `weth9_exit_observed` at the anchored history. -/
theorem weth9_exit_anchored {checkpoint : BlockChain} (h : WethAnchoredHistory checkpoint)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat} {E : Adr} {wad : B256}
    {chainId : UInt64} {maxPriorityFee maxFee : Nat}
    (hstate : benv.state = checkpoint.state)
    (hfork : CoveredFork benv.stat.fork)
    (htype : tx.type = .two chainId maxPriorityFee maxFee (some weth) [])
    (hvalue : tx.value = 0) (hdata : tx.data = Weth9.withdrawCalldata wad)
    (hchain : chainId = benv.stat.chainId)
    (hprio : maxPriorityFee ≤ maxFee) (hbase : benv.stat.baseFeePerGas ≤ maxFee)
    (hgas : Weth9.withdrawIntrinsicGas wad + Weth9.withdrawFrameGas wad + 811 ≤ tx.gas)
    (hcap : tx.gas ≤ 16777216)
    (hroom : tx.gas ≤ benv.stat.blockGasLimit - bout.blockGasUsed)
    (hrecover : recoverSender benv.stat.chainId tx = .ok E)
    (hnonce : (benv.state.get E).nonce = tx.nonce) (hnonceMax : tx.nonce ≠ UInt64.max)
    (hnocode : (benv.state.getCode E).size = 0)
    (hfunds : tx.gas * maxFee ≤ (benv.state.get E).bal.toNat)
    (hprecE : benv.stat.rules.isPrecomp E = false)
    (hprecCa : benv.stat.rules.isPrecomp weth = false)
    (hholder : h.toObserved.deployment.keys (.bal E))
    (hbal : wad ≤ (checkpoint.state.getStor weth).get (Weth9.balSlot E))
    (hcbE : benv.stat.coinbase ≠ E) (hcbCa : benv.stat.coinbase ≠ weth)
    (hfresh : weth ∉ benv.createdAccounts)
    (hcbSafe : State.Protected benv.state benv.stat.coinbase ∨
      benv.state.getStor benv.stat.coinbase = .empty) :
    ∃ (st : Jaune.State) (bout' : BlockOutput),
      processTransaction benv bout tx index = .ok (st, bout') ∧
      bout'.cumulativeGasUsed = bout.cumulativeGasUsed +
        Weth9.withdrawGasUsed ((checkpoint.state.getStor weth).get (Weth9.balSlot E)) wad ∧
      bout'.blockGasUsed = bout.blockGasUsed +
        Weth9.withdrawGasUsed ((checkpoint.state.getStor weth).get (Weth9.balSlot E)) wad ∧
      st.getStor weth = (checkpoint.state.getStor weth).set (Weth9.balSlot E)
        ((checkpoint.state.getStor weth).get (Weth9.balSlot E) - wad) ∧
      (∀ a, a ≠ weth → st.getStor a = checkpoint.state.getStor a) ∧
      (st.get E).nonce = tx.nonce + 1 ∧
      (st.get E).bal = checkpoint.state.bal E -
          (tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
            benv.stat.baseFeePerGas)).toB256 + wad +
        ((tx.gas -
            Weth9.withdrawGasUsed ((checkpoint.state.getStor weth).get (Weth9.balSlot E)) wad) *
          (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
            benv.stat.baseFeePerGas)).toB256 ∧
      (st.get weth).bal = checkpoint.state.bal weth - wad ∧
      ((checkpoint.state.bal E).toNat + wad.toNat < 2 ^ 256 →
        (st.get E).bal.toNat +
            Weth9.withdrawGasUsed ((checkpoint.state.getStor weth).get (Weth9.balSlot E)) wad *
          (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas) =
          (checkpoint.state.bal E).toNat + wad.toNat) :=
  weth9_exit_observed h.toObserved hstate hfork htype hvalue hdata hchain hprio hbase hgas hcap
    hroom hrecover hnonce hnonceMax hnocode hfunds hprecE hprecCa hholder hbal hcbE hcbCa hfresh
    hcbSafe

end Blanc.Composition.LiveUsdcWeth9B26213219
