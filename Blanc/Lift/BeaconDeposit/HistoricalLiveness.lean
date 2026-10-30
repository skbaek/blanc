import Blanc.Lift.BeaconDeposit.HistoricalViews
import Blanc.Lift.BeaconDeposit.DepositExec

/-! Exact-gas modern deposit liveness at B reached by the accepted historical seam.
Original-storage reads, sentry conditions and residual gas are the unchanged
frame donor's. No historical-fork liveness or gas extension is asserted. -/

namespace Blanc.Lift.BeaconDeposit

open Jaune Blanc.ExecutionTrace

variable {ca : Adr} {D C C1 P B : BlockChain} {initialHistory : List B256}
    (dc : ConfiguredHistoryTraceIn HistFork mainnetChainConfig D C)
    (first : ConfiguredBlockTraceIn HistFork mainnetChainConfig C C1)
    (tail : ConfiguredHistoryTraceIn HistFork mainnetChainConfig C1 P)
    (modern : ConfiguredHistoryTrace mainnetChainConfig P B)
    (anchors : HistoricalSeamAnchors D C P first.block)
    (checkpointEmpty : D.state.getCode 2 = ByteArray.empty)
    (historicalNoFrame : ∀ root ∈ ((dc.step first).append tail).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ (2 : Adr))
    (rewards : ((dc.step first).append tail).RewardCreditsFunded)
    (modernSystemNoAuthority : ∀ p ∈ systemContracts, modern.NoAuthorityAt p.1)
    (modernNoAuthority : modern.NoAuthorityAt 2)
    (modernNoFrame : ∀ root ∈ modern.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ (2 : Adr))
    (installed : D.state.getCode ca = code)
    (invariant : SolInv (D.state.getStor ca) initialHistory)

include anchors checkpointEmpty
  historicalNoFrame rewards modernSystemNoAuthority modernNoAuthority modernNoFrame installed
  invariant

/-- A model-accepted modern deposit at the same reached B appends precisely one
model node and event, preserves foreign storage, and leaves exactly residual G.
The reached invariant is produced by the actual D/C/C1/P/B seam. -/
theorem historicalSeam_deposit_live (sevm : Sevm) (base : Devm) (G : Nat)
    (s' : BeaconDeposit.Acc) (ev : BeaconDeposit.DepositEvent)
    (target : sevm.currentTarget = ca) (state : base.state = B.state)
    (hcode : sevm.code = code)
    (hdataLength : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = BeaconDeposit.depositSelector)
    (hdec : DepositDecodable sevm)
    (hOk : BeaconDeposit.deposit Bytes.sha256 (solAcc (Devm.getStor base sevm.currentTarget))
      (argBytes sevm 0) (argBytes sevm 1) (argBytes sevm 2) (argRoot sevm) sevm.value.toNat =
        .ok (s', ev))
    (hsha : ShaReady sevm base) (hdepth : sevm.depth ≠ 0) (hstatic : sevm.isStatic = false)
    (hsentryLive : gCallStipend < G + 52 +
      bodyLiveCostOf (base.getOrigStorVal sevm sevm.currentTarget
        (solBranchSlot (bodyDepth sevm base))) sevm base)
    (hsentryCount : gCallStipend < G + 4 +
      bodyInsertGasOf (base.getOrigStorVal sevm sevm.currentTarget
        (solBranchSlot (bodyDepth sevm base))) sevm base +
      countStoreCostOf (base.getOrigStorVal sevm sevm.currentTarget solCountSlot)
        (bodyCount sevm base))
    (hbound : G + 1 + bodyGasOf (base.getOrigStorVal sevm sevm.currentTarget
        (solBranchSlot (bodyDepth sevm base)))
      (base.getOrigStorVal sevm sevm.currentTarget solCountSlot) sevm base < 2 ^ 256) :
    ∃ post, Nonempty (Exec 0 sevm (St base [] Mem.empty
        (G + depositGasOf (base.getOrigStorVal sevm sevm.currentTarget
          (solBranchSlot (bodyDepth sevm base)))
          (base.getOrigStorVal sevm sevm.currentTarget solCountSlot) sevm base)) (.ok post)) ∧
      post.gasLeft = G ∧
      solAcc (Devm.getStor post sevm.currentTarget) = s' ∧
      SolInv (Devm.getStor post sevm.currentTarget)
        ((initialHistory ++ committedNodesIn ca (((dc.step first).append tail).append modern.toHistForkIn)) ++ [BeaconDeposit.depositDataNode Bytes.sha256 (argBytes sevm 0)
          (argBytes sevm 1) (argBytes sevm 2)
          (BeaconDeposit.le64 (sevm.value.toNat / BeaconDeposit.oneGwei))]) ∧
      (∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor base a) ∧
      post.logs = base.logs ++ [BeaconDeposit.depositEventLog sevm.currentTarget ev] := by
  have atFrame := historicalSeam_frame_solInv dc first tail modern anchors
    checkpointEmpty historicalNoFrame rewards modernSystemNoAuthority
    modernNoAuthority modernNoFrame installed invariant sevm base target state
  exact deposit_exec_solInv sevm base G _ s' ev hcode hdataLength hcd hsel hdec atFrame hOk
    hsha hdepth hstatic hsentryLive hsentryCount hbound

end Blanc.Lift.BeaconDeposit
