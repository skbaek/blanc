import Blanc.Lift.UniswapV2Pair.BurnPrefixWalk
import Blanc.Lift.UniswapV2Pair.BurnDispatchWalk
import Blanc.Lift.UniswapV2Pair.BurnSuffixWalk
import Blanc.Lift.UniswapV2Pair.MintPrefixWalk

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
    call0, call1, calldata0, calldata1, memory0, memory1, output0, output1,
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

/-- Successful pricing, physical LP debit and all four following token calls
produce an exact internal return and the pointer carrier for public ABI encoding. -/
theorem burnPricing_return_inv {K : WriterKey → Prop} {st : State}
    {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {seg : Seg}
    {f L b1 b0 token1 token0 r1 r0 toWord extρ : B256}
    (project : ∀ {e d i d'}, P e d i d' → Ninst.Run e d i d')
    (fork : CoveredFork sevm.benvStat.fork) (notCut13 : 13 ∉ C) (notCut14 : 14 ∉ C)
    (mem : PtrMem 128 192 M) (sentinel : memWord M 96 = 0)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (lpMintTouched sevm.currentTarget))
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (f :: 0 :: L :: b1 :: b0 :: token1 :: token0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R) M G)
      t_15e2_c37 seg) :
    let supply := b.getStorVal sevm.currentTarget 0
    let a0 := (L * b0) / supply
    let a1 := (L * b1) / supply
    let locals := burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 a1 a0 toWord extρ R
    burnAmounts L b0 b1 supply = .ok (a0.toNat, a1.toNat) ∧
    0 < a0.toNat ∧ 0 < a1.toNat ∧ supply = st.totalSupply ∧
    ∃ (burnGas residual : Nat) (tx0 tx1 d0 d1 : Devm) (out0 out1 : Bytes) (gas finalSize : Nat),
      let p := burnSecondTransferPointer tx0.returnData tx1.returnData
      let p0 := burnFirstTransferPointer tx0.returnData
      let N := if tx1.returnData = [] then tx1.memory else
        Blanc.Lift.bytesArrayMemory tx1.memory (p0 + 164) tx1.returnData
      let Q0 := skimRequestMemory N p sevm.currentTarget
      let Q1 := skimRequestMemory (burnBalanceReplyMemory Q0 p out0) p sevm.currentTarget
      let finalM := burnSuffixMemory sevm d1 (burnBalanceReplyMemory Q1 p out1) p r0 r1
        (Bytes.toB256 (out0.take 32)) (Bytes.toB256 (out1.take 32)) a0 a1
      SFunc.RunP P cert.prog sevm
        (St (afterSload sevm b 0) (L :: sevm.currentTarget.toB256 :: 0x168d :: locals) M burnGas)
        t_2992_c63 (.returned (lpBurnPost sevm (afterSload sevm b 0) locals
          M sevm.currentTarget.toB256 L residual)) ∧
      LPBurnSourceResult K st sevm (afterSload sevm b 0) locals M sevm.currentTarget.toB256 L residual ∧
      (∃ before0, P sevm before0 (.exec .call) tx0) ∧
      (∃ before1, P sevm before1 (.exec .call) tx1) ∧
      (∃ before0, P sevm before0 (.exec .staticcall) d0) ∧
      (∃ before1, P sevm before1 (.exec .staticcall) d1) ∧
      seg = .done (.returned (St
        (burnSuffixPost sevm d1 r0 r1 (Bytes.toB256 (out0.take 32)) (Bytes.toB256 (out1.take 32))
          f toWord a0 a1) (a1 :: a0 :: R) finalM gas)) ∧
      PtrMem p finalSize finalM ∧ 96 ≤ p.toNat ∧ p.toNat + 64 < 2 ^ 256 := by
  obtain ⟨mul0, mul1, nonzero, supplyEq, amounts, positive0, positive1, mutable,
    burnGas, residual, callee, source, transferTail⟩ :=
    burnPricing_inv project fork notCut13 mem rep fresh run
  have postMem : PtrMem 128 192
      (lpBurnPost sevm (afterSload sevm b 0)
        (burnPricedLocals (b.getStorVal sevm.currentTarget 0) f L b1 b0 token1 token0 r1 r0
          ((L * b1) / b.getStorVal sevm.currentTarget 0)
          ((L * b0) / b.getStorVal sevm.currentTarget 0) toWord extρ R)
        M sevm.currentTarget.toB256 L residual).memory := by
    have ptr := lpMintMemory_ptr (lpMintScratch_ptr mem sevm.currentTarget.toB256)
      sevm.currentTarget.toB256 L
    simpa only [lpBurnPost, lpBurnBalancePost, lpBurnSupplyPost, St.memory, lpMintMemory] using ptr
  have postSentinel : memWord
      (lpBurnPost sevm (afterSload sevm b 0)
        (burnPricedLocals (b.getStorVal sevm.currentTarget 0) f L b1 b0 token1 token0 r1 r0
          ((L * b1) / b.getStorVal sevm.currentTarget 0)
          ((L * b0) / b.getStorVal sevm.currentTarget 0) toWord extρ R)
        M sevm.currentTarget.toB256 L residual).memory 96 = 0 :=
    (burnLP_sentinel mem.wf).trans sentinel
  have postSelf := St.self (d := lpBurnPost sevm (afterSload sevm b 0)
    (burnPricedLocals (b.getStorVal sevm.currentTarget 0) f L b1 b0 token1 token0 r1 r0
      ((L * b1) / b.getStorVal sevm.currentTarget 0)
      ((L * b0) / b.getStorVal sevm.currentTarget 0) toWord extρ R)
    M sevm.currentTarget.toB256 L residual) (by rfl) rfl
  rw [postSelf] at transferTail
  obtain ⟨tx0, tx1, out0, out1, d0, d1, gas, finalSize,
    call0, call1, width0, width1, accepted0, accepted1, bcall0, bcall1,
    answer0, answer1, long0, full0, long1, full1, bound0, bound1,
    returned, finalMem, low, high, covered⟩ :=
    burnTransfers_suffix_inv project fork postMem postSentinel notCut14 transferTail
  exact ⟨amounts, positive0, positive1, supplyEq, burnGas, residual,
    tx0, tx1, d0, d1, out0, out1, gas, finalSize, callee, source,
    call0, call1, bcall0, bcall1, returned, finalMem, low, high⟩

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

/-- A retained actual fee return supplies the full Burn callee's normal return,
physical LP debit, four token occurrences and actual pointer carrier. -/
theorem burnFee_return_inv {K : WriterKey → Prop} {st : State} {D : Exec.Deriv}
    {sevm : Sevm} {b feePost : Devm} {R : List B256} {M : Mem} {C : List Nat} {seg : Seg}
    {L b1 b0 token1 token0 r1 r0 toWord extρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (notCut13 : 13 ∉ C) (notCut14 : 14 ∉ C)
    (mem : PtrMem 128 192 M) (sentinel : memWord M 96 = 0)
    (observation : FeeMintSourceObservation K st D sevm b
      (burnFeeLocals L b1 b0 token1 token0 r1 r0 toWord extρ R) M r1 r0 0x15e2 (.returned feePost))
    (tracked : K (.balance sevm.currentTarget))
    (suffix : SFunc.RunCutP (StepIn D) cert.prog sevm C feePost t_15e2_c37 seg) :
    let keys := feeBranchSourceKeys K st sevm (feeKLastWorld sevm observation.d)
      (Bytes.toB256 (observation.out.take 32)) r0 r1
    let fee := feeBranchSourceFee st sevm (feeKLastWorld sevm observation.d)
      (Bytes.toB256 (observation.out.take 32)) r0 r1
    let f := feeOnWord (Bytes.toB256 (observation.out.take 32))
    let supply := feePost.getStorVal sevm.currentTarget 0
    let a0 := (L * b0) / supply
    let a1 := (L * b1) / supply
    let locals := burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 a1 a0 toWord extρ R
    burnAmounts L b0 b1 supply = .ok (a0.toNat, a1.toNat) ∧
    0 < a0.toNat ∧ 0 < a1.toNat ∧ supply = fee.state.totalSupply ∧
    ∃ (burnGas residual : Nat) (tx0 tx1 d0 d1 : Devm) (out0 out1 : Bytes) (gas finalSize : Nat),
      let p := burnSecondTransferPointer tx0.returnData tx1.returnData
      let p0 := burnFirstTransferPointer tx0.returnData
      let N := if tx1.returnData = [] then tx1.memory else
        Blanc.Lift.bytesArrayMemory tx1.memory (p0 + 164) tx1.returnData
      let Q0 := skimRequestMemory N p sevm.currentTarget
      let Q1 := skimRequestMemory (burnBalanceReplyMemory Q0 p out0) p sevm.currentTarget
      let finalM := burnSuffixMemory sevm d1 (burnBalanceReplyMemory Q1 p out1) p r0 r1
        (Bytes.toB256 (out0.take 32)) (Bytes.toB256 (out1.take 32)) a0 a1
      SFunc.RunP (StepIn D) cert.prog sevm
        (St (afterSload sevm feePost 0) (L :: sevm.currentTarget.toB256 :: 0x168d :: locals) feePost.memory burnGas)
        t_2992_c63 (.returned (lpBurnPost sevm (afterSload sevm feePost 0) locals
          feePost.memory sevm.currentTarget.toB256 L residual)) ∧
      LPBurnSourceResult keys fee.state sevm (afterSload sevm feePost 0) locals feePost.memory sevm.currentTarget.toB256 L residual ∧
      (∃ before0, (StepIn D) sevm before0 (.exec .call) tx0) ∧
      (∃ before1, (StepIn D) sevm before1 (.exec .call) tx1) ∧
      (∃ before0, (StepIn D) sevm before0 (.exec .staticcall) d0) ∧
      (∃ before1, (StepIn D) sevm before1 (.exec .staticcall) d1) ∧
      seg = .done (.returned (St
        (burnSuffixPost sevm d1 r0 r1 (Bytes.toB256 (out0.take 32)) (Bytes.toB256 (out1.take 32))
          f toWord a0 a1) (a1 :: a0 :: R) finalM gas)) ∧
      PtrMem p finalSize finalM ∧ 96 ≤ p.toNat ∧ p.toNat + 64 < 2 ^ 256 := by
  obtain ⟨rep, ptr, raw, same⟩ := burnFee_pricing_input_inv mem observation suffix
  have trackedAfter : (feeBranchSourceKeys K st sevm (feeKLastWorld sevm observation.d)
      (Bytes.toB256 (observation.out.take 32)) r0 r1) (.balance sevm.currentTarget) := by
    unfold feeBranchSourceKeys
    split
    · exact tracked
    · split
      · exact tracked
      · split
        · split
          · exact tracked
          · exact Or.inl tracked
        · exact tracked
  have fresh : WriterFreshKeys
      (feeBranchSourceKeys K st sevm (feeKLastWorld sevm observation.d)
        (Bytes.toB256 (observation.out.take 32)) r0 r1) (lpMintTouched sevm.currentTarget) := by
    apply Blanc.SlotFootprint.FreshKeys.of_universe rep.inj rep.apart (fun _ h => h)
    intro k member
    have eq := List.mem_singleton.mp (show k ∈ [WriterKey.balance sevm.currentTarget] from member)
    subst k
    exact trackedAfter
  exact burnPricing_return_inv (fun h => StepIn.toRun h) fork notCut13 notCut14 ptr
    (same.trans sentinel) rep fresh raw

/-- Actual Burn fee-recipient separation is requested only at represented
same-D decoder continuations; full frame adapters derive it from HASH-T. -/
def BurnPrefixFresh (K : WriterKey → Prop) (st : State) (D : Exec.Deriv)
    (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem) (toWord extρ : B256) (seg : Seg) : Prop :=
      let locked := burnLockedWorld sevm b
      let reserveWorld := afterSload sevm locked 8
      let r0 := reserve0Read (locked.getStorVal sevm.currentTarget 8)
      let r1 := reserve1Read (locked.getStorVal sevm.currentTarget 8)
      let mask : B256 := 0xffffffffffffffffffffffffffffffffffffffff
      let t0 := mask &&& reserveWorld.getStorVal sevm.currentTarget 6
      let t1 := mask &&& (afterSload sevm reserveWorld 6).getStorVal sevm.currentTarget 7
      ∀ (out0 : Bytes) (d1 : Devm) (out1 : Bytes) (gas : Nat),
        let M1 := balanceReplyMemory (balanceReplyMemory M sevm.currentTarget out0) sevm.currentTarget out1
        WriterRep K (d1.getStor sevm.currentTarget) { st with unlocked := 0 } →
        SFunc.RunCutP (StepIn D) cert.prog sevm []
          (St d1 (out1.length.toB256 :: 128 :: 0 :: Bytes.toB256 (out0.take 32) ::
            t1 :: t0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R) M1 gas) t_15c3_c37 seg →
        FeeMintSourceFresh K { st with unlocked := 0 } D sevm (feeBurnWorld sevm d1)
          (burnFeeLocals (feeBurnLiquidity sevm d1) (feeBurnBalance1 M1)
            (Bytes.toB256 (out0.take 32)) t1 t0 r1 r0 toWord extρ R)
          (feeBurnMemory M1 sevm.currentTarget) r1 r0 0x15e2

/-- Literal Burn entry derives a positive two-word return, its actual pointer
and six token calls plus the retained fee callee from the same derivation. -/
theorem burnPrefix_return_inv {K : WriterKey → Prop} {st : State} {D : Exec.Deriv}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat}
    {toWord extρ : B256} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (sentinel : memWord M 96 = 0)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (tracked : K (.balance sevm.currentTarget))
    (fresh : BurnPrefixFresh K st D sevm b R M toWord extρ seg)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St b (toWord :: extρ :: R) M G) t_13f5_c37 seg) :
    b.getStorVal sevm.currentTarget 12 = 1 ∧ sevm.isStatic = false ∧
    ∃ (amount0 amount1 : B256) (post : Devm) (p : B256) (n : Nat),
      seg = .done (.returned post) ∧ post.stack = amount1 :: amount0 :: R ∧
      PtrMem p n post.memory ∧ 96 ≤ p.toNat ∧ p.toNat + 64 < 2 ^ 256 ∧
      0 < amount0.toNat ∧ 0 < amount1.toNat ∧
      ∃ (feeBefore feePost d0 d1 tx0 tx1 final0 final1 : Devm),
        SFunc.RunP (StepIn D) cert.prog sevm feeBefore t_26ec_c68 (.returned feePost) ∧
        (∃ before0, StepIn D sevm before0 (.exec .staticcall) d0) ∧
        (∃ before1, StepIn D sevm before1 (.exec .staticcall) d1) ∧
        (∃ before0, StepIn D sevm before0 (.exec .call) tx0) ∧
        (∃ before1, StepIn D sevm before1 (.exec .call) tx1) ∧
        (∃ before0, StepIn D sevm before0 (.exec .staticcall) final0) ∧
        (∃ before1, StepIn D sevm before1 (.exec .staticcall) final1) := by
  obtain ⟨unlocked, mutable, d0, out0, d1, out1, feeGas, feePost,
    call0, call1, answer0, answer1, long0, width0, long1, width1, feeRep,
    cached, balance1, feeRun, ⟨observation⟩, suffix⟩ :=
    burnEntry_fee_source_inv fork mem rep tracked fresh run
  have reply0 := balanceReplyMemory_ptr out0 (balanceRequestMemory_ptr mem sevm.currentTarget)
  have reply1 := balanceReplyMemory_ptr out1 (balanceRequestMemory_ptr reply0 sevm.currentTarget)
  have scratch := feeBurnMemory_ptr reply1 sevm.currentTarget
  have same : memWord (feeBurnMemory
      (balanceReplyMemory (balanceReplyMemory M sevm.currentTarget out0) sevm.currentTarget out1)
      sevm.currentTarget) 96 = 0 := by
    rw [burnFeeScratch_sentinel reply1.wf sevm.currentTarget,
      burnBalanceReply_sentinel reply0.wf sevm.currentTarget out1,
      burnBalanceReply_sentinel mem.wf sevm.currentTarget out0]
    exact sentinel
  obtain ⟨amounts, positive0, positive1, supplyEq, burnGas, residual,
    tx0, tx1, final0, final1, lastOut0, lastOut1, gas, finalSize,
    lpRun, lpSource, txCall0, txCall1, finalCall0, finalCall1,
    returned, finalMem, low, high⟩ :=
    burnFee_return_inv fork (by decide : 13 ∉ ([] : List Nat)) (by decide : 14 ∉ ([] : List Nat))
      scratch same observation tracked suffix
  exact ⟨unlocked, mutable, _, _, _, _, finalSize, returned, rfl,
    finalMem, low, high, positive0, positive1, _, feePost, d0, d1, tx0, tx1, final0, final1,
    feeRun, call0, call1, txCall0, txCall1, finalCall0, finalCall1⟩

/-- Successful actual pc-zero Burn returns its real two payout words and keeps
the same-D callee, token occurrences and terminal RETURN available to frame adapters. -/
theorem burnPc0_return_inv {K : WriterKey → Prop} {st : State} {D : Exec.Deriv}
    {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (tracked : K (.balance sevm.currentTarget))
    (fresh : ∀ gas calleeOutcome,
      SFunc.RunP (StepIn D) cert.prog sevm
        (St b [(0xffffffffffffffffffffffffffffffffffffffff : B256) &&& Sevm.dataWord sevm 4,
          0x053d, 0x89afcb44] getterInitMemory gas) t_13f5_c37 calleeOutcome →
      BurnPrefixFresh K st D sevm b [0x89afcb44] getterInitMemory
        ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& Sevm.dataWord sevm 4)
        0x053d (.done calleeOutcome))
    (run : SFunc.RunP (StepIn D) cert.prog sevm (St b [] Mem.empty G) t_0000_c0 o) :
    b.getStorVal sevm.currentTarget 12 = 1 ∧ sevm.isStatic = false ∧
    ∃ (calleeGas : Nat) (calleePost publicPost : Devm) (amount0 amount1 p : B256) (n abiGas : Nat),
      SFunc.RunP (StepIn D) cert.prog sevm
        (St b [(0xffffffffffffffffffffffffffffffffffffffff : B256) &&& Sevm.dataWord sevm 4,
          0x053d, 0x89afcb44] getterInitMemory calleeGas) t_13f5_c37 (.returned calleePost) ∧
      calleePost.stack = [amount1, amount0, 0x89afcb44] ∧ PtrMem p n calleePost.memory ∧
      96 ≤ p.toNat ∧ p.toNat + 64 < 2 ^ 256 ∧ 0 < amount0.toNat ∧ 0 < amount1.toNat ∧
      o = .halted publicPost ∧ publicPost.output = amount0.toBytes ++ amount1.toBytes ∧
      (∀ a, publicPost.getStor a = calleePost.getStor a) ∧ publicPost.logs = calleePost.logs ∧
      Linst.Run sevm
        (St calleePost [p, 64, 0x89afcb44] (burnEventMemory calleePost.memory p amount0 amount1) abiGas)
        .return_ (.ok publicPost) ∧
      ∃ (feeBefore feePost d0 d1 tx0 tx1 final0 final1 : Devm),
        SFunc.RunP (StepIn D) cert.prog sevm feeBefore t_26ec_c68 (.returned feePost) ∧
        (∃ before0, StepIn D sevm before0 (.exec .staticcall) d0) ∧
        (∃ before1, StepIn D sevm before1 (.exec .staticcall) d1) ∧
        (∃ before0, StepIn D sevm before0 (.exec .call) tx0) ∧
        (∃ before1, StepIn D sevm before1 (.exec .call) tx1) ∧
        (∃ before0, StepIn D sevm before0 (.exec .staticcall) final0) ∧
        (∃ before1, StepIn D sevm before1 (.exec .staticcall) final1) := by
  obtain ⟨value, size, calleeGas, calleeOutcome, callee, tail⟩ := burnPc0_caller_inv selector run
  obtain ⟨unlocked, mutable, amount0, amount1, calleePost, p, n,
    returned, stack, ptr, low, high, positive0, positive1, occurrences⟩ :=
    burnPrefix_return_inv fork getterInitMemory_ptr burnEntryMemory_sentinel rep tracked
      (fresh calleeGas calleeOutcome callee) (SFunc.runP_iff_runCutP_nil.mp callee)
  have outcomeEq := Seg.done.inj returned
  rw [outcomeEq] at callee tail
  have self := St.self (d := calleePost) stack rfl
  have canonical := (congrArg (fun start : Devm =>
    SFunc.RunCutP (StepIn D) cert.prog sevm [] start t_053d_c83 (.done o)) self).mp tail
  obtain ⟨abiGas, publicPost, halted, terminal, output, stor, logs⟩ :=
    burnAbi_return_inv (fun h => StepIn.toRun h) ptr low high canonical
  exact ⟨unlocked, mutable, calleeGas, calleePost, publicPost, amount0, amount1, p, n, abiGas,
    callee, stack, ptr, low, high, positive0, positive1, Seg.done.inj halted,
    output, stor, logs, terminal, occurrences⟩

/-- The derivation is exactly the supplied successful raw Exec; the64-byte
return and retained Burn callee therefore concern that invocation. -/
theorem burnRaw_return_inv {K : WriterKey → Prop} {st : State}
    {sevm : Sevm} {b publicPost : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (tracked : K (.balance sevm.currentTarget))
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok publicPost))
    (fresh : ∀ gas calleeOutcome,
      SFunc.RunP (StepIn ⟨0, sevm, St b [] Mem.empty G, .ok publicPost, run⟩) cert.prog sevm
        (St b [(0xffffffffffffffffffffffffffffffffffffffff : B256) &&& Sevm.dataWord sevm 4,
          0x053d, 0x89afcb44] getterInitMemory gas) t_13f5_c37 calleeOutcome →
      BurnPrefixFresh K st ⟨0, sevm, St b [] Mem.empty G, .ok publicPost, run⟩ sevm b
        [0x89afcb44] getterInitMemory
        ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& Sevm.dataWord sevm 4)
        0x053d (.done calleeOutcome)) :
    b.getStorVal sevm.currentTarget 12 = 1 ∧ sevm.isStatic = false ∧
    ∃ (calleeGas : Nat) (calleePost : Devm) (amount0 amount1 p : B256) (n : Nat),
      SFunc.RunP (StepIn ⟨0, sevm, St b [] Mem.empty G, .ok publicPost, run⟩) cert.prog sevm
        (St b [(0xffffffffffffffffffffffffffffffffffffffff : B256) &&& Sevm.dataWord sevm 4,
          0x053d, 0x89afcb44] getterInitMemory calleeGas) t_13f5_c37 (.returned calleePost) ∧
      calleePost.stack = [amount1, amount0, 0x89afcb44] ∧ PtrMem p n calleePost.memory ∧
      0 < amount0.toNat ∧ 0 < amount1.toNat ∧
      publicPost.output = amount0.toBytes ++ amount1.toBytes ∧
      (∀ a, publicPost.getStor a = calleePost.getStor a) ∧ publicPost.logs = calleePost.logs := by
  obtain ⟨f, entry, lifted⟩ := lift_sound_in cert_check codeEq fork run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  obtain ⟨unlocked, mutable, calleeGas, calleePost, post, amount0, amount1, p, n, abiGas,
    callee, stack, ptr, low, high, positive0, positive1, returned, output, stor, logs,
    terminal, occurrences⟩ := burnPc0_return_inv fork selector rep tracked fresh lifted
  cases returned
  exact ⟨unlocked, mutable, calleeGas, calleePost, amount0, amount1, p, n,
    callee, stack, ptr, positive0, positive1, output, stor, logs⟩

end Blanc.Lift.UniswapV2Pair
