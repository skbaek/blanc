import Blanc.Lift.UniswapV2Pair.BurnPositionalPricingFacts

namespace Blanc.Lift.UniswapV2Pair
open Jaune

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
  have reached := r.three.fee.occurrence.call.sameFrame.snoc r.three.fee.occurrence.call.edge
  have outcome : r.three.fee.occurrence.call.returned.exn = .ok post :=
    (Blanc.Exec.Deriv.ParentPrefix.exn_eq reached).trans success
  have env : r.three.fee.occurrence.call.returned.sevm = sevm :=
    (Blanc.Exec.Deriv.ParentPrefix.sevm_eq reached).trans
      ((Blanc.Exec.Deriv.ParentPrefix.sevm_eq r.transfer.sameFrame).symm.trans r.transfer_sevm)
  have forkRet : CoveredFork r.three.fee.occurrence.call.returned.sevm.benvStat.fork := by
    rw [env]
    exact fork
  obtain ⟨o, run⟩ := r.pricing_data.cut.placed.sourceRun cert_check
    (r.pricing_data.cut.exn_eq.trans outcome) (r.pricing_data.cut.sevm_eq ▸ forkRet)
  obtain ⟨gas, state⟩ := r.pricing_data.cut.state
  rw [r.pricing_data.cut.sevm_eq, r.pricing_data.cut.tree, state] at run
  obtain ⟨product0, product1, nonzero, supplyEq, amounts, positive0, positive1,
      mutable, _, _, _, source, _⟩ := burnPricing_inv (fun step => StepIn.toRun step)
    forkRet (by decide : 13 ∉ []) r.pricing_memory rep fresh
    (by simpa only [BurnThreeCalls.feeReturnLocals, burnFeeLocals] using
      SFunc.runP_iff_runCutP_nil.mp run)
  have readRep : WriterRep K
      ((afterSload r.three.fee.occurrence.call.returned.sevm r.pricing.devm 0).getStor
        r.three.fee.occurrence.call.returned.sevm.currentTarget) st := by
    rw [afterSload_getStor]
    exact rep
  obtain ⟨balance, supply, _, _⟩ := lpBurnLP_inv source.1
  have reads := lpBurn_source_reads
    (fromWord := r.three.fee.occurrence.call.returned.sevm.currentTarget.toB256)
    (value := feeBurnLiquidity r.three.initial.second.returned.sevm
      r.three.initial.second.returned.devm) readRep
    (by simpa only [toAdr_toB256] using fresh)
  have actual := lpBurn_source_result (R := r.three.pricedLocals r.pricing)
    (M := r.pricing.devm.memory) (G := r.residual)
    (fromWord := r.three.fee.occurrence.call.returned.sevm.currentTarget.toB256)
    (value := feeBurnLiquidity r.three.initial.second.returned.sevm
      r.three.initial.second.returned.devm) readRep
    (by simpa only [toAdr_toB256] using fresh)
    (by rw [reads.1]; exact balance) (by rw [reads.2]; exact supply)
  exact ⟨product0, product1, nonzero, supplyEq, amounts, positive0, positive1,
    mutable, actual⟩

end Blanc.Lift.UniswapV2Pair
