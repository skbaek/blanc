import Blanc.Lift.UniswapV2Pair.BurnPositionalPricingFacts

namespace Blanc.Lift.UniswapV2Pair
open Jaune

theorem BurnFourCallsH.lp_source_result {root : Exec.Deriv} {sevm : Sevm} {b post : Devm} {w : BurnSchedule}
    {K : WriterKey → Prop} {st : State} (r : BurnFourCallsH root sevm b w)
    (rep : WriterRep K
      (r.pricing.devm.getStor r.three.fee.occurrence.call.returned.sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (lpMintTouched r.three.fee.occurrence.call.returned.sevm.currentTarget))
    (success : root.exn = .ok post) (stateGas : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none) :
    let e := r.three.fee.occurrence.call.returned.sevm
    let L := feeBurnLiquidity r.three.initial.second.returned.sevm
      r.three.initial.second.returned.devm
    let supply := r.pricing.devm.getStorVal e.currentTarget 0
    B256.Nofm L (Bytes.toB256 (r.three.initial.out0.take 32)) ∧
    B256.Nofm L (Bytes.toB256 (r.three.initial.out1.take 32)) ∧ supply ≠ 0 ∧
    supply = st.totalSupply ∧
    burnAmounts L (Bytes.toB256 (r.three.initial.out0.take 32))
      (Bytes.toB256 (r.three.initial.out1.take 32)) supply =
        .ok ((r.three.amount0 r.pricing).toNat, (r.three.amount1 r.pricing).toNat) ∧
    0 < (r.three.amount0 r.pricing).toNat ∧ 0 < (r.three.amount1 r.pricing).toNat ∧
    e.isStatic = false ∧
    LPBurnSourceResultH K st e (afterSloadH e r.pricing.devm 0)
      (r.three.pricedLocals r.pricing) r.pricing.devm.memory e.currentTarget.toB256 L r.residual := by
  have reached := r.three.fee.occurrence.call.sameFrame.snoc r.three.fee.occurrence.call.edge
  have outcome : r.three.fee.occurrence.call.returned.exn = .ok post :=
    (Blanc.Exec.Deriv.ParentPrefix.exn_eq reached).trans success
  have env : r.three.fee.occurrence.call.returned.sevm = sevm :=
    (Blanc.Exec.Deriv.ParentPrefix.sevm_eq reached).trans
      ((Blanc.Exec.Deriv.ParentPrefix.sevm_eq r.transfer.sameFrame).symm.trans r.transfer_sevm)
  have forkRet : r.three.fee.occurrence.call.returned.sevm.benvStat.rules.stateGas = none ∧ r.three.fee.occurrence.call.returned.sevm.benvStat.rules.bal = none := by
    rw [env]
    exact ⟨stateGas, bal⟩
  obtain ⟨o, run⟩ := r.pricing_data.cut.placed.sourceRunH cert_check
    (r.pricing_data.cut.exn_eq.trans outcome) (r.pricing_data.cut.sevm_eq ▸ forkRet.1)
  obtain ⟨gas, state⟩ := r.pricing_data.cut.state
  rw [r.pricing_data.cut.sevm_eq, r.pricing_data.cut.tree, state] at run
  obtain ⟨product0, product1, nonzero, supplyEq, amounts, positive0, positive1,
      mutable, _, _, _, source, _⟩ := burnPricing_invH (fun step => StepIn.toRun step)
    forkRet.1 forkRet.2 (by decide : 13 ∉ []) r.pricing_memory rep fresh
    (by simpa only [BurnThreeCallsH.feeReturnLocals, burnFeeLocals] using
      SFunc.runP_iff_runCutP_nil.mp run)
  have readRep : WriterRep K
      ((afterSloadH r.three.fee.occurrence.call.returned.sevm r.pricing.devm 0).getStor
        r.three.fee.occurrence.call.returned.sevm.currentTarget) st := by
    rw [afterSloadH_getStor]
    exact rep
  obtain ⟨balance, supply, _, _⟩ := lpBurnLP_inv source.1
  have reads := lpBurn_source_readsH
    (fromWord := r.three.fee.occurrence.call.returned.sevm.currentTarget.toB256)
    (value := feeBurnLiquidity r.three.initial.second.returned.sevm
      r.three.initial.second.returned.devm) readRep
    (by simpa only [toAdr_toB256] using fresh)
  have actual := lpBurn_source_resultH (R := r.three.pricedLocals r.pricing)
    (M := r.pricing.devm.memory) (G := r.residual)
    (fromWord := r.three.fee.occurrence.call.returned.sevm.currentTarget.toB256)
    (value := feeBurnLiquidity r.three.initial.second.returned.sevm
      r.three.initial.second.returned.devm) readRep
    (by simpa only [toAdr_toB256] using fresh)
    (by rw [reads.1]; exact balance) (by rw [reads.2]; exact supply)
  exact ⟨product0, product1, nonzero, supplyEq, amounts, positive0, positive1,
    mutable, actual⟩

/-- The same actual pricing cursor derives finite payouts and LP acceptance;
the result is instantiated at the retained physical transfer world's gas. -/
theorem BurnFourCalls.lp_source_result {root : Exec.Deriv} {sevm : Sevm} {b post : Devm}
    {K : WriterKey → Prop} {st : State} (r : BurnFourCalls root sevm b)
    (rep : WriterRep K
      (r.pricing.devm.getStor r.three.fee.occurrence.call.returned.sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (lpMintTouched r.three.fee.occurrence.call.returned.sevm.currentTarget))
    (success : root.exn = .ok post) (fork : CoveredFork sevm.benvStat.fork) :
    let e := r.three.fee.occurrence.call.returned.sevm
    let L := feeBurnLiquidity r.three.initial.second.returned.sevm
      r.three.initial.second.returned.devm
    let supply := r.pricing.devm.getStorVal e.currentTarget 0
    B256.Nofm L (Bytes.toB256 (r.three.initial.out0.take 32)) ∧
    B256.Nofm L (Bytes.toB256 (r.three.initial.out1.take 32)) ∧ supply ≠ 0 ∧
    supply = st.totalSupply ∧
    burnAmounts L (Bytes.toB256 (r.three.initial.out0.take 32))
      (Bytes.toB256 (r.three.initial.out1.take 32)) supply =
        .ok ((r.three.amount0 r.pricing).toNat, (r.three.amount1 r.pricing).toNat) ∧
    0 < (r.three.amount0 r.pricing).toNat ∧ 0 < (r.three.amount1 r.pricing).toNat ∧
    e.isStatic = false ∧
    LPBurnSourceResult K st e (afterSload e r.pricing.devm 0)
      (r.three.pricedLocals r.pricing) r.pricing.devm.memory e.currentTarget.toB256 L r.residual := by
  have h := BurnFourCallsH.lp_source_result (r.toH fork) rep fresh success fork.rules_stateGas_none
    fork.rules_bal_none
  have f : CoveredFork r.three.fee.occurrence.call.returned.sevm.benvStat.fork := by
    rw [(Cursor.parentStep_sevm r.three.fee.occurrence.call.edge).trans
      (r.three.fee.occurrence.sevm_eq.trans
        ((Cursor.parentStep_sevm r.three.initial.second.edge).trans r.three.initial.second_sevm))]
    exact fork
  simp only [BurnFourCalls.toH, BurnThreeCalls.toH, PairFeeObservation.toH] at h
  simp only [LPBurnSourceResultH_of_covered f, afterSloadH_of_eip2929 f.rules_access] at h
  exact h


end Blanc.Lift.UniswapV2Pair
