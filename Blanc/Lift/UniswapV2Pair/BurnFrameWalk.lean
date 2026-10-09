import Blanc.Lift.UniswapV2Pair.BurnPrefixWalk
import Blanc.Lift.UniswapV2Pair.BurnDispatchWalk
import Blanc.Lift.UniswapV2Pair.BurnSuffixWalk
import Blanc.Lift.UniswapV2Pair.MintPrefixWalk
import Blanc.Lift.UniswapV2Pair.MintCanonical

/-! Same-derivation Burn fee, pricing and physical suffix joins. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The actual LP burn scratch and event data writes miss the helper sentinel. -/
theorem burnLP_sentinel {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {fromWord value : B256} {G : Nat} (wf : Mem.Wf M) :
    memWord (lpBurnPost sevm b R M fromWord value G).memory 96 = memWord M 96 := by
  have wf1 := wf.write 0 fromWord.toAdr.toB256.toBytes
  have wf2 := wf1.write 32 (1 : B256).toBytes
  have wf3 := wf2.write 0 fromWord.toAdr.toB256.toBytes
  have wf4 := wf3.write 32 (1 : B256).toBytes
  simp only [lpBurnPost, lpBurnBalancePost, lpBurnSupplyPost, St.memory, memWord]
  rw [Mem.read_write_disjoint wf4 128 value.toBytes (Or.inr (by decide : 96 + 32 ≤ 128)),
    Mem.read_write_disjoint wf3 32 (1 : B256).toBytes
      (Or.inl (by rw [B256.length_toBytes]; decide : 32 + (1 : B256).toBytes.length ≤ 96)),
    Mem.read_write_disjoint wf2 0 fromWord.toAdr.toB256.toBytes
      (Or.inl (by rw [B256.length_toBytes]; decide : 0 + fromWord.toAdr.toB256.toBytes.length ≤ 96)),
    Mem.read_write_disjoint wf1 32 (1 : B256).toBytes
      (Or.inl (by rw [B256.length_toBytes]; decide : 32 + (1 : B256).toBytes.length ≤ 96)),
    Mem.read_write_disjoint wf 0 fromWord.toAdr.toB256.toBytes
      (Or.inl (by rw [B256.length_toBytes]; decide : 0 + fromWord.toAdr.toB256.toBytes.length ≤ 96))]

/-- Every actual fee branch preserves Burn's helper sentinel. On positive LP
minting, the scratch/event memory is identical to the checked LP burn layout. -/
theorem burnFeePost_sentinel {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {K w r0 r1 : B256} {G : Nat} (wf : Mem.Wf M) :
    memWord (feeBranchPost sevm b R M K w r0 r1 G).memory 96 = memWord M 96 := by
  unfold feeBranchPost
  split
  · rfl
  · unfold feeOnPost
    split
    · rfl
    · split
      · unfold feeGrowthPost feeLiquidityPost
        split
        · rfl
        · simpa only [lpMintPost, lpMintSupplyPost, lpMintCreditPost, lpMintMemory,
            lpBurnPost, lpBurnBalancePost, lpBurnSupplyPost, St.memory] using
            (burnLP_sentinel (sevm := sevm) (b := b) (R := R) (fromWord := w)
              (value := feeNumeratorWord sevm b (feeLastRoot K) (feeReserveRoot r0 r1) /
                feeDenominatorWord (feeLastRoot K) (feeReserveRoot r0 r1)) (G := G) wf)
      · rfl

/-- Initial Burn balance staging and reply writes preserve the helper sentinel. -/
theorem burnBalanceReply_sentinel {M : Mem} (wf : Mem.Wf M) (pair : Adr) (out : Bytes) :
    memWord (balanceReplyMemory M pair out) 96 = memWord M 96 := by
  have wfQ : Mem.Wf (balanceRequestMemory M pair) :=
    (wf.write 128 balanceOfSelectorWord.toBytes).write 132 pair.toB256.toBytes
  simp only [balanceReplyMemory, memWord]
  rw [Mem.read_write_disjoint (wfQ.extends [(128, 36), (128, 32)]) 128 (out.take 32)
    (Or.inr (by decide : 96 + 32 ≤ 128)),
    ((Mem.reads_data (balanceRequestMemory M pair)).extends [(128, 36), (128, 32)]).read,
    ← (Mem.reads_data (balanceRequestMemory M pair)).read]
  simp only [balanceRequestMemory]
  rw [Mem.read_write_disjoint (wf.write 128 balanceOfSelectorWord.toBytes) 132 pair.toB256.toBytes
      (Or.inr (by decide : 96 + 32 ≤ 132)),
    Mem.read_write_disjoint wf 128 balanceOfSelectorWord.toBytes
      (Or.inr (by decide : 96 + 32 ≤ 128))]

/-- Burn's fee request, allocation and answer writes preserve the helper sentinel. -/
theorem burnFeeReply_sentinel {M : Mem} (wf : Mem.Wf M) (out : Bytes) :
    memWord (feeReplyMemory M out) 96 = memWord M 96 := by
  have wfQ : Mem.Wf (feeRequestMemory M) := wf.write 128 feeToSelectorWord.toBytes
  simp only [feeReplyMemory, memWord]
  rw [Mem.read_write_disjoint (wfQ.extends [(128, 4), (128, 32)]) 128 (out.take 32)
    (Or.inr (by decide : 96 + 32 ≤ 128)),
    ((Mem.reads_data (feeRequestMemory M)).extends [(128, 4), (128, 32)]).read,
    ← (Mem.reads_data (feeRequestMemory M)).read]
  simp only [feeRequestMemory]
  rw [Mem.read_write_disjoint wf 128 feeToSelectorWord.toBytes
    (Or.inr (by decide : 96 + 32 ≤ 128))]

/-- The actual Pair balance SLOAD scratch before fee68 misses the helper sentinel. -/
theorem burnFeeScratch_sentinel {M : Mem} (wf : Mem.Wf M) (pair : Adr) :
    memWord (feeBurnMemory M pair) 96 = memWord M 96 := by
  simp only [feeBurnMemory, transferScratch, memWord]
  rw [Mem.read_write_disjoint (wf.write 0 pair.toB256.toBytes) 32 (1 : B256).toBytes
      (Or.inl (by rw [B256.length_toBytes]; decide : 32 + (1 : B256).toBytes.length ≤ 96)),
    Mem.read_write_disjoint wf 0 pair.toB256.toBytes
      (Or.inl (by rw [B256.length_toBytes]; decide : 0 + pair.toB256.toBytes.length ≤ 96))]

end Blanc.Lift.UniswapV2Pair
