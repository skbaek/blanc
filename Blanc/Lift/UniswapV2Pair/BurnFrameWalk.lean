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

/-- Both physical transfers and both final balance calls belong to one source
run; producer reply bounds supply the pointer needed by the complete suffix. -/
theorem burnTransfers_suffix_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {seg : Seg}
    {supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ : B256}
    (project : ∀ {e d i d'}, P e d i d' → Ninst.Run e d i d')
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (sentinel : memWord M 96 = 0) (notCut : 14 ∉ C)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M G)
      t_168d_c13 seg) :
    ∃ (tx0 tx1 : Devm) (out0 out1 : Bytes) (d0 d1 : Devm) (gas finalSize : Nat),
      let p := burnSecondTransferPointer tx0.returnData tx1.returnData
      let p0 := burnFirstTransferPointer tx0.returnData
      let N := if tx1.returnData = [] then tx1.memory else
        Blanc.Lift.bytesArrayMemory tx1.memory (p0 + 164) tx1.returnData
      let Q0 := skimRequestMemory N p sevm.currentTarget
      let Q1 := skimRequestMemory (burnBalanceReplyMemory Q0 p out0) p sevm.currentTarget
      let finalM := burnSuffixMemory sevm d1 (burnBalanceReplyMemory Q1 p out1) p r0 r1
        (Bytes.toB256 (out0.take 32)) (Bytes.toB256 (out1.take 32)) amount0 amount1
      (∃ before0, P sevm before0 (.exec .call) tx0) ∧
      (∃ before1, P sevm before1 (.exec .call) tx1) ∧
      tx0.returnData.length < 2 ^ 160 ∧ tx1.returnData.length < 2 ^ 160 ∧
      (tx0.returnData = [] ∨ (32 ≤ tx0.returnData.length ∧
        Bytes.toB256 (tx0.returnData.sliceD 0 32 0) ≠ 0)) ∧
      (tx1.returnData = [] ∨ (32 ≤ tx1.returnData.length ∧
        Bytes.toB256 (tx1.returnData.sliceD 0 32 0) ≠ 0)) ∧
      (∃ before0, P sevm before0 (.exec .staticcall) d0) ∧
      (∃ before1, P sevm before1 (.exec .staticcall) d1) ∧
      StaticAnswered sevm (temporalAccountAccessBase tx1
        (token0 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr)
        (token0 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr
        (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out0 ∧
      StaticAnswered sevm (temporalAccountAccessBase d0
        (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr)
        (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr
        (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out1 ∧
      32 ≤ out0.length ∧ out0.length < 2 ^ 256 ∧
      32 ≤ out1.length ∧ out1.length < 2 ^ 256 ∧
      (Bytes.toB256 (out0.take 32)).toNat < 2 ^ 112 ∧
      (Bytes.toB256 (out1.take 32)).toNat < 2 ^ 112 ∧
      seg = .done (.returned (St
        (burnSuffixPost sevm d1 r0 r1 (Bytes.toB256 (out0.take 32)) (Bytes.toB256 (out1.take 32))
          f toWord amount0 amount1) (amount1 :: amount0 :: R) finalM gas)) ∧
      PtrMem p finalSize finalM ∧ 96 ≤ p.toNat ∧ p.toNat + 64 < 2 ^ 256 ∧
      p.toNat + 64 ≤ finalSize := by
  obtain ⟨gw0, cg0, tx0, residual0, gw1, cg1, tx1, residual1,
    call0, call1, _, _, calldata0, calldata1, memory0, memory1, output0, output1,
    width0, width1, accepted0, accepted1, midMem, midSentinel, fit64, finalMem,
    firstTail, secondTail⟩ := burnTransfers_caller_inv project fork mem sentinel run
  obtain ⟨low, high⟩ := burnFinalPointer_bounds width0 width1
  obtain ⟨bgw0, bcg0, d0, out0, bgw1, bcg1, d1, out1, updateCallGas, updateGas, gas,
    bcall0, bcall1, post0, post1, long0, full0, long1, full1, answer0, answer1,
    bound0, bound1, mutable, updateRun, returned, ⟨finalSize, finalPtr, covered⟩⟩ :=
    burnFinalBalances_suffix_inv project fork finalMem low high notCut secondTail
  exact ⟨tx0, tx1, out0, out1, d0, d1, gas, finalSize,
    ⟨_, call0⟩, ⟨_, call1⟩, width0, width1, accepted0, accepted1,
    ⟨_, bcall0⟩, ⟨_, bcall1⟩, answer0, answer1, long0, full0, long1, full1,
    bound0, bound1, returned, finalPtr, low, fit64, covered⟩

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

/-- The actual fee return supplies represented storage, pointer memory, the
literal pricing state and an unchanged sentinel from one retained observation. -/
theorem burnFee_pricing_input_inv {K : WriterKey → Prop} {st : State} {D : Exec.Deriv}
    {sevm : Sevm} {b feePost : Devm} {R : List B256} {M : Mem} {C : List Nat} {seg : Seg}
    {L b1 b0 token1 token0 r1 r0 toWord extρ : B256}
    (mem : PtrMem 128 192 M)
    (observation : FeeMintSourceObservation K st D sevm b
      (burnFeeLocals L b1 b0 token1 token0 r1 r0 toWord extρ R) M r1 r0 0x15e2 (.returned feePost))
    (suffix : SFunc.RunCutP (StepIn D) cert.prog sevm C feePost t_15e2_c37 seg) :
    WriterRep (feeBranchSourceKeys K st sevm (feeKLastWorld sevm observation.d)
      (Bytes.toB256 (observation.out.take 32)) r0 r1)
      (feePost.getStor sevm.currentTarget)
      (feeBranchSourceFee st sevm (feeKLastWorld sevm observation.d)
        (Bytes.toB256 (observation.out.take 32)) r0 r1).state ∧
    PtrMem 128 192 feePost.memory ∧
    SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St feePost (feeOnWord (Bytes.toB256 (observation.out.take 32)) ::
        0 :: L :: b1 :: b0 :: token1 :: token0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R)
        feePost.memory feePost.gasLeft) t_15e2_c37 seg ∧
    memWord feePost.memory 96 = memWord M 96 := by
  have returned := observation.returned
  rw [observation.last] at returned
  have postEq := Outcome.returned.inj returned
  have rep : WriterRep
      (feeBranchSourceKeys K st sevm (feeKLastWorld sevm observation.d)
        (Bytes.toB256 (observation.out.take 32)) r0 r1)
      (feePost.getStor sevm.currentTarget)
      (feeBranchSourceFee st sevm (feeKLastWorld sevm observation.d)
        (Bytes.toB256 (observation.out.take 32)) r0 r1).state := by
    have storageEq := congrArg (fun world : Devm => world.getStor sevm.currentTarget) postEq
    exact storageEq.symm ▸ observation.sourceResult.2.1
  have machine := mintFeePost_machine (sevm := sevm) (b := feeKLastWorld sevm observation.d)
    (R := burnFeeLocals L b1 b0 token1 token0 r1 r0 toWord extρ R)
    (K := st.kLast) (w := Bytes.toB256 (observation.out.take 32))
    (r0 := r0) (r1 := r1) (G := observation.residual)
    (feeReplyMemory_ptr observation.out (feeRequestMemory_ptr mem))
  rw [← postEq] at machine
  have self := St.self (d := feePost) machine.1 rfl
  have raw : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St feePost (feeOnWord (Bytes.toB256 (observation.out.take 32)) ::
        0 :: L :: b1 :: b0 :: token1 :: token0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R)
        feePost.memory feePost.gasLeft) t_15e2_c37 seg := by
    have transported := (congrArg (fun world : Devm =>
      SFunc.RunCutP (StepIn D) cert.prog sevm C world t_15e2_c37 seg) self).mp suffix
    simpa only [burnFeeLocals] using transported
  have actualSentinel : memWord feePost.memory 96 = memWord M 96 := by
    rw [postEq]
    exact (burnFeePost_sentinel (feeReplyMemory_ptr observation.out (feeRequestMemory_ptr mem)).wf).trans
      (burnFeeReply_sentinel mem.wf observation.out)
  exact ⟨rep, machine.2, raw, actualSentinel⟩

end Blanc.Lift.UniswapV2Pair
