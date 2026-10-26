import Blanc.Lift.Usdc.HistoryAnchorBodyGenerated
import Blanc.Lift.Usdc.HistoryAnchorBodyInput

/-!
# Frozen C/D signed-byte facts at an original body transaction cut

The generated producer proves strict Jaune decoding and canonical encoding of
all 74 C and 53 D signed legacy envelopes, retaining their complete order and
selected positions 22/38. These are deterministic facts about frozen bytes.

The consumer takes the original configured block and its supplied actual
TxSplit. Its full-body equality remains an explicit unresolved external
obligation. It is an internal conditional interface, not an adopted final ENV
premise or a historical-body, sender, admission, state, receipt or P1 assertion.
No synthetic execution or block-end replacement is constructed here.

The packet's numeric e7e0fe39… / d07cbde8… hash comparisons remain finite packet
evidence. The Lean identity below binds Jaune's transaction hash to the exact
signed bytes without trusting a normalized RPC hash or recovered sender.
-/

namespace Blanc.Lift.Usdc.HistoryAnchorBody

open Jaune Blanc.ExecutionTrace

/-- Exact C transaction fields derived from its signed legacy bytes. -/
theorem c_fields :
    c22Tx.nonce = 20 ∧ c22Tx.type.receiver? = none ∧
      c22Tx.value = 0 ∧ c22Tx.gas = 6721975 ∧
      c22Tx.data = ProxyCreation.code.toList :=
  ⟨rfl, rfl, rfl, rfl, c_creation_input⟩

/-- Exact D call fields derived from its signed legacy bytes. This is a
factory request, without an assertion that the request executed or succeeded. -/
theorem d_fields :
    d38Tx.nonce = 205 ∧
      d38Tx.type.receiver? = some 0x5c69bee701ef814a2b6a3edd4b1652cb9cc5aa6f ∧
      d38Tx.value = 0 ∧ d38Tx.gas = 3770079 ∧
      d38Tx.data = [
        0xc9, 0xc6, 0x53, 0x96,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0xc0, 0x2a, 0xaa, 0x39, 0xb2, 0x23, 0xfe, 0x8d, 0x0a, 0x0e,
        0x5c, 0x4f, 0x27, 0xea, 0xd9, 0x08, 0x3c, 0x75, 0x6c, 0xc2,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0xa0, 0xb8, 0x69, 0x91, 0xc6, 0x21, 0x8b, 0x36, 0xc1, 0xd1,
        0x9d, 0x4a, 0x2e, 0x9e, 0xb0, 0xce, 0x36, 0x06, 0xeb, 0x48] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Canonical C transaction identity uses exactly the frozen signed envelope. -/
theorem c_hash_bytes : getTxHash c22Tx = c22Signed.keccak := by
  unfold getTxHash
  rw [c22_canonical]

/-- Canonical D transaction identity uses exactly the frozen signed envelope. -/
theorem d_hash_bytes : getTxHash d38Tx = d38Signed.keccak := by
  unfold getTxHash
  rw [d38_canonical]

section OriginalCut

variable {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post)

/-- The exact full frozen C body identifies the original supplied cut's
transaction; no replacement cut or trace is synthesized. -/
theorem c_original_cut (cut : block.bodyTrace.transactions.TxSplit 22)
    (body : block.block.txs = cBody) :
    cut.index = 22 ∧ cut.tx = c22Tx :=
  block.bodyTrace.txSplit_tx_eq_of_inr cut body c_selected

/-- The exact full frozen D body identifies the original supplied cut's
transaction; every later same-block transaction remains in its actual suffix. -/
theorem d_original_cut (cut : block.bodyTrace.transactions.TxSplit 38)
    (body : block.block.txs = dBody) :
    cut.index = 38 ∧ cut.tx = d38Tx :=
  block.bodyTrace.txSplit_tx_eq_of_inr cut body d_selected

/-- C's original actual constructor transaction obtains precisely the input
fields needed by the existing constructor consumer. Sender recovery and the
actual execution outcome are still separate producer obligations. -/
theorem c_original_cut_fields (cut : block.bodyTrace.transactions.TxSplit 22)
    (body : block.block.txs = cBody) :
    cut.index = 22 ∧ cut.tx.nonce = 20 ∧ cut.tx.type.receiver? = none ∧
      cut.tx.value = 0 ∧ cut.tx.data = ProxyCreation.code.toList ∧
      getTxHash cut.tx = c22Signed.keccak := by
  obtain ⟨index, tx⟩ := c_original_cut block cut body
  refine ⟨index, ?_⟩
  rw [tx]
  exact ⟨c_fields.1, c_fields.2.1, c_fields.2.2.1,
    c_creation_input, c_hash_bytes⟩

/-- D's original actual transaction obtains its exact decoded identity and
factory-call fields. The real head trace, settlement and suffix stay supplied
by the original cut; no state or receipt conclusion is assumed. -/
theorem d_original_cut_fields (cut : block.bodyTrace.transactions.TxSplit 38)
    (body : block.block.txs = dBody) :
    cut.index = 38 ∧ cut.tx.nonce = 205 ∧
      cut.tx.type.receiver? = some 0x5c69bee701ef814a2b6a3edd4b1652cb9cc5aa6f ∧
      cut.tx.value = 0 ∧ cut.tx.data = d38F5 ∧
      getTxHash cut.tx = d38Signed.keccak := by
  obtain ⟨index, tx⟩ := d_original_cut block cut body
  refine ⟨index, ?_⟩
  rw [tx]
  exact ⟨d_fields.1, d_fields.2.1, d_fields.2.2.1, rfl, d_hash_bytes⟩

end OriginalCut

end Blanc.Lift.Usdc.HistoryAnchorBody
