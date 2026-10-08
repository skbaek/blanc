import Blanc.Lift.Weth9.FootHistory
import Blanc.ExecutionTransactionPrefixAdmission

/-! WETH9 footprint at every actual transaction boundary of a configured
block, after both opening system calls and a retained decoded prefix. -/

namespace Blanc.Lift.Weth9

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- Trace-local keys of the prior history, the opening calls, and the actual
transaction prefix. Rolled-back raw entries remain included. -/
def prefixTouchedKeys {cfg : ChainConfig} {checkpoint boundary completed : BlockChain}
    (ca : Adr) (history : ConfiguredHistoryTrace cfg checkpoint boundary)
    (block : ConfiguredBlockTrace cfg boundary completed) {n : Nat}
    (cut : block.bodyTrace.transactions.PrefixSplit n) : List Key :=
  historyTouchedKeys ca history ++
    (block.bodyTrace.transactionPrefixFrames cut).flatMap fun root =>
      if root.sevm.currentTarget = ca then frameKeys root.sevm else []

/-- Installed code, finite ledger backing and storage support at any retained
transaction prefix, derived from the checkpoint and one trace-local freshness
premise. No invariant at the endpoint is assumed. -/
theorem weth9_prefix_footprint_universe
    {ca : Adr} {cfg : ChainConfig} {checkpoint boundary completed : BlockChain}
    {K₀ : Key → Prop} (history : ConfiguredHistoryTrace cfg checkpoint boundary)
    (block : ConfiguredBlockTrace cfg boundary completed) {n : Nat}
    (cut : block.bodyTrace.transactions.PrefixSplit n)
    (_position : n ≤ block.bodyTrace.decodedTxs.length)
    (installed : some (checkpoint.state.getCode ca).toList = weth9Sem.image)
    (sumNof : SumNof checkpoint.state.bal)
    (initial : FootInv K₀ (checkpoint.state.getStor ca) (checkpoint.state.bal ca))
    (fresh : KeysFresh K₀ (prefixTouchedKeys ca history block cut)) :
    some (cut.benv.state.getCode ca).toList = weth9Sem.image ∧ SumNof cut.benv.state.bal ∧
      FootInv (Key.extend K₀ (prefixTouchedKeys ca history block cut))
        (cut.benv.state.getStor ca) (cut.benv.state.bal ca) := by
  let U := Key.extend K₀ (prefixTouchedKeys ca history block cut)
  have extended : FootInv U (checkpoint.state.getStor ca) (checkpoint.state.bal ca) :=
    initial.extend fresh
  have priorAdmission : history.FrameAdmitted ca (footEntry U) := by
    apply (history.frameAdmitted_iff_rawFrames ca _).2
    intro root member target k touched
    exact Or.inr (List.mem_append.mpr (Or.inl (touchedKeys_mem member target touched)))
  have prefixAdmission : ∀ root ∈ block.bodyTrace.transactionPrefixFrames cut,
      root.sevm.currentTarget = ca → footEntry U root.sevm root.devm := by
    intro root member target k touched
    apply Or.inr
    apply List.mem_append.mpr
    apply Or.inr
    exact List.mem_flatMap.mpr ⟨root, member, by simpa only [target, ite_true] using touched⟩
  have start : (footSpec U).StateInv ca checkpoint.state :=
    footSpec_stateInv_iff.mpr ⟨installed, sumNof, extended.support, extended.backed⟩
  have boundaryInv := history.stateInv_admitted_sem
    (footSpec_preservesAdmitted ca extended.inj) priorAdmission start
  have openingInv : (footSpec U).BenvInv ca
      (initBenv block.fork boundary block.block.header) :=
    ⟨boundaryInv, block.not_mem_openingCreatedAccounts ca⟩
  have openingBound : sum (initBenv block.fork boundary block.block.header).state.bal < 2 ^ 256 := by
    have bound := block.openingBound
    omega
  have finish := block.bodyTrace.transactionPrefix_benvInv_admitted_sem cut
    (footSpec_preservesAdmitted ca extended.inj) block.covered prefixAdmission openingBound openingInv
  obtain ⟨hcode, hside, hsup, hback⟩ := footSpec_stateInv_iff.mp finish.state
  exact ⟨hcode, hside, ⟨hsup, extended.inj, extended.apart, hback⟩⟩

end Blanc.Lift.Weth9
