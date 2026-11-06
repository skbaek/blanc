import Blanc.ExecutionMidHistoryCallers
import Blanc.ExecutionMidHistoryIn
import Blanc.ExecutionMidHistoryInCallerExclusion

/-!
# An installed contract originates no root of a mid history

`ConfiguredHistoryTrace.settledRoots_caller_ne_of_code` over a mid history on a fork domain `F` without
state gas: a contract whose state invariant holds at the mid history's start is the checked sender of
no remaining transaction (`TransactionTrace.sender_ne_sem`, EIP-3607 through the invariant's installed
code), so, being distinct from the system address, it is the caller of no settled root. Unlike
`MidHistoryTraceIn.settledRoots_caller_ne_of_senderQueries` it takes no premise about the senders.
-/

namespace Blanc.ExecutionTrace

open Jaune

variable {F : Fork → Prop} {C : ByteArray} {c : ContractSpecSem} {ca : Adr}
  {entry : Sevm → Devm → Prop}

/-- A transaction list opened at the invariant has no sender at the contract. -/
theorem ApplyTransactionsTrace.noSenderAt_of_benvInvIn
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (preserves : c.PreservesAdmittedIn F ca entry)
    (hF : F benv.stat.fork) (hsg : benv.stat.rules.stateGas = none)
    (admitted : trace.FrameAdmitted ca entry) (sumNof : sum benv.state.bal < 2 ^ 256)
    (inv : c.BenvInv ca benv)
    (K : InstalledRuntimeSafety C) (image : c.sem.image = some C.toList) :
    trace.NoSenderAt ca := by
  induction trace with
  | nil => trivial
  | @cons index tx txs benv bout txState txBout finalBenv finalBout head tail ih =>
    have headInv : c.BenvInv ca (benv.withState txState) :=
      head.benvInv_admitted_semIn preserves hF hsg admitted.1 sumNof inv K image
    have nextSum : sum (benv.withState txState).state.bal < 2 ^ 256 :=
      Nat.lt_of_le_of_lt
        (by simpa only [Benv.withState] using processTransaction_sum_le head.result hsg) sumNof
    exact ⟨head.sender_ne_sem inv.state inv.ca,
      ih (by simpa only [Benv.withState] using hF) (by simpa only [Benv.withState] using hsg)
        admitted.2 nextSum headInv⟩

/-- A staged body opened at the invariant has no sender at the contract. -/
theorem StagedBodyTrace.noSenderAt_of_benvInvIn
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (preserves : c.PreservesAdmittedIn F ca entry)
    (hF : F benv.stat.fork) (hsg : benv.stat.rules.stateGas = none)
    (admitted : trace.FrameAdmitted ca entry)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (inv : c.BenvInv ca benv)
    (K : InstalledRuntimeSafety C) (image : c.sem.image = some C.toList) :
    trace.transactions.NoSenderAt ca := by
  have beacon := trace.beacon.stateInv_and_sum_le_admitted_semIn
    preserves hF hsg admitted.beacon inv K image
  have beaconInv : c.BenvInv ca (benv.withState trace.beaconState) :=
    ⟨beacon.1, by simpa only [Benv.withState] using inv.ca⟩
  have history := trace.history.stateInv_and_sum_le_admitted_semIn
    preserves (by simpa only [Benv.withState] using hF)
    (by simpa only [Benv.withState] using hsg) admitted.history beaconInv K image
  have historyInv : c.BenvInv ca
      ((benv.withState trace.beaconState).withState trace.historyState) :=
    ⟨history.1, by simpa only [Benv.withState] using beaconInv.ca⟩
  have historyLe : sum trace.historyState.bal ≤ sum benv.state.bal :=
    le_trans (by simpa only [Benv.withState] using history.2) beacon.2
  exact trace.transactions.noSenderAt_of_benvInvIn preserves
    (by simpa only [Benv.withState] using hF) (by simpa only [Benv.withState] using hsg)
    admitted.transactions (by change sum trace.historyState.bal < 2 ^ 256; omega) historyInv K image

/-- **A mid history opened at the invariant has no sender at the contract.** -/
theorem MidHistoryTraceIn.noSenderAt_of_stateInv {cfg : ChainConfig} {start : Benv}
    {future : BlockChain} (trace : MidHistoryTraceIn F cfg start future)
    (preserves : c.PreservesAdmittedIn F ca entry) (capabilities : BodyStageCapabilities F)
    (admitted : trace.FrameAdmitted ca entry) (rewards : trace.RewardCreditsFunded)
    (inv : c.StateInv ca start.state)
    (K : InstalledRuntimeSafety C) (image : c.sem.image = some C.toList) :
    trace.NoSenderAt ca := by
  induction trace with
  | @tail boundary _ _ block cut =>
    have hsg : (initBenv block.fork boundary block.block.header).stat.rules.stateGas = none :=
      capabilities.stateGas_none block.forkIn
    have stat := block.txSplit_stat cut
    have afterBound : sum cut.txState.bal + wdsum block.block.wds < 2 ^ 256 :=
      block.txSplit_bound cut capabilities
    have afterF : F cut.afterBenv.stat.fork := by rw [stat]; exact block.forkIn
    have afterSg : cut.afterBenv.stat.rules.stateGas = none := by rw [stat]; exact hsg
    exact cut.after.noSenderAt_of_benvInvIn preserves afterF afterSg admitted.1 (by simp only [Benv.withState]; omega)
      ⟨inv, block.txSplit_notCreated cut ca⟩ K image
  | step prior block ih =>
    exact ⟨ih admitted.1 rewards.1 inv,
      block.bodyTrace.noSenderAt_of_benvInvIn preserves block.forkIn
        (capabilities.stateGas_none block.forkIn) admitted.2 block.withdrawalsBound
        ⟨prior.stateInv_admitted_semIn preserves capabilities admitted.1 rewards.1 inv K image,
          AdrSet.not_mem_empty⟩ K image⟩

/-- **An installed code originates no settled root of a mid history.** -/
theorem MidHistoryTraceIn.settledRoots_caller_ne_of_stateInv {cfg : ChainConfig} {start : Benv}
    {future : BlockChain} (trace : MidHistoryTraceIn F cfg start future)
    (preserves : c.PreservesAdmittedIn F ca entry) (capabilities : BodyStageCapabilities F)
    (admitted : trace.FrameAdmitted ca entry) (rewards : trace.RewardCreditsFunded)
    (inv : c.StateInv ca start.state)
    (K : InstalledRuntimeSafety C) (image : c.sem.image = some C.toList)
    (notSystem : ca ≠ systemAddress) :
    ∀ R ∈ trace.settledRoots, R.sevm.caller ≠ ca :=
  trace.settledRoots_caller_ne_of_noSender
    (trace.noSenderAt_of_stateInv preserves capabilities admitted rewards inv K image) notSystem

end Blanc.ExecutionTrace
