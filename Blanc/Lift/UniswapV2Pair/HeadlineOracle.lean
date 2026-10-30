import Blanc.Lift.UniswapV2Pair.OracleCallReceipt
import Blanc.Lift.UniswapV2Pair.PairOuterCalls

/-!
# Headline: the Pair's price oracle, per outer call (`pair_oracle`)

For every outer call of a configured history at the Uniswap V2 Pair (`OuterPairCall`: a committed
non-static Pair frame that no other non-static Pair frame encloses), the stored words at the call's
entry (`preS`) and committed exit (`postS`) satisfy `OracleAdvance`:

* each cumulative price word advances by the TWAP increment (`twapIncrement`) of the *entry*
  reserve words over the stored-timestamp advance (`timestampAdvance`, modulo `2 ^ 32`), modulo
  `2 ^ 256`;
* the stored timestamp word stays, or becomes the call's block time modulo `2 ^ 32`.

Re-entered Pair frames inside the call are part of it.  The proof is `pair_history_outer_call`
(each outer call is one consumed source invocation between the model states its storage
represents) and the one-invocation model lemma `runTyped_oracle_call`.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune Blanc Blanc.ExecutionTrace

/-- The advance of the Pair's stored `uint32` timestamp from `pre` to `post`, modulo `2 ^ 32`. -/
def timestampAdvance (pre post : Stor) : Nat :=
  wrapElapsed (timestampWord pre).toNat (timestampWord post).toNat

/-- **The oracle law of one call**, over the Pair storage at its entry (`pre`) and exit (`post`)
and its block time: `price0 += ⌊r1·2^112/r0⌋·Δ` and `price1 += ⌊r0·2^112/r1⌋·Δ` modulo `2 ^ 256`
(zero when `Δ` or a reserve is zero), with `r0`, `r1` the entry reserves and `Δ` the stored-timestamp
advance; the stored timestamp stays or becomes `time mod 2^32`. -/
def OracleAdvance (pre post : Stor) (time : B256) : Prop :=
  (price0Word post).toNat = ((price0Word pre).toNat +
      twapIncrement (reserve0Word pre).toNat (reserve1Word pre).toNat
        (timestampAdvance pre post)) % 2 ^ 256 ∧
    (price1Word post).toNat = ((price1Word pre).toNat +
      twapIncrement (reserve1Word pre).toNat (reserve0Word pre).toNat
        (timestampAdvance pre post)) % 2 ^ 256 ∧
    (timestampWord post = timestampWord pre ∨ (timestampWord post).toNat = time.toNat % 2 ^ 32)

theorem uint32_toB256_toNat (x : UInt32) : x.toB256.toNat = x.toNat := by
  simp only [UInt32.toB256, B256.toNat, B128.toNat, B128.zero_eq,
    UInt64.toNat_zero, Nat.zero_shiftLeft, Nat.zero_or, UInt32.toNat_toUInt64]

theorem WriterRep.timestampWord_toNat {K : WriterKey → Prop} {s : Stor} {st : State}
    (rep : WriterRep K s st) : (timestampWord s).toNat = st.blockTimestampLast.toNat := by
  rw [rep.timestampWord_eq, uint32_toB256_toNat]

/-- **Uniswap V2 oracle, per outer call.**  From a checkpoint whose Pair storage represents a
model state, every outer Pair call of the history advances the cumulative price words by the TWAP
increment of its entry reserves over the stored-timestamp advance, modulo `2 ^ 256`, and leaves
the stored timestamp unchanged or at its block time modulo `2 ^ 32`. -/
theorem pair_oracle {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace)) :
    ∀ f, OuterPairCall pair trace f →
      OracleAdvance (preS pair f) (postS pair f) f.sevm.benvStat.time := by
  intro f outer
  obtain ⟨s, st, st', out, K, K', frameEq, -, consumed, -, outEq, pre, post⟩ :=
    pair_history_outer_call trace installed initial fresh f outer
  have run := (runTyped_of_exact consumed.positional.forget).1
  have law := runTyped_oracle_call st s.source.context s.source.entry s.transcript
  rw [run, outEq] at law
  have ts : s.source.context.timestamp = f.sevm.benvStat.time := by
    rw [← frameEq]
    rfl
  obtain ⟨p0, p1, stamp⟩ := law
  refine ⟨?_, ?_, ?_⟩
  · rw [post.price0Word_eq, pre.price0Word_eq, pre.reserve0Word_toNat, pre.reserve1Word_toNat,
      timestampAdvance, pre.timestampWord_toNat, post.timestampWord_toNat]
    exact p0
  · rw [post.price1Word_eq, pre.price1Word_eq, pre.reserve0Word_toNat, pre.reserve1Word_toNat,
      timestampAdvance, pre.timestampWord_toNat, post.timestampWord_toNat]
    exact p1
  · rcases stamp with same | moved
    · left
      rw [post.timestampWord_eq, pre.timestampWord_eq, same]
    · right
      rw [post.timestampWord_toNat, moved, ts]

end Blanc.Lift.UniswapV2Pair
