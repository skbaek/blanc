import Blanc.Lift.BeaconDeposit.HistoricalSeam
import Blanc.Lift.BeaconDeposit.Views

/-! Modern view executions at the same state B reached by the accepted historical seam.
The storage invariant is produced by the actual seam, not an extra endpoint premise. -/

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

/-- The actual seam producer, transported to the current frame at the same reached B. -/
theorem historicalSeam_frame_solInv (sevm : Sevm) (base : Devm)
    (target : sevm.currentTarget = ca) (state : base.state = B.state) :
    SolInv (Devm.getStor base sevm.currentTarget) (initialHistory ++ committedNodesIn ca (((dc.step first).append tail).append modern.toHistForkIn)) := by
  have reached := historicalSeam_wholeSpan_solInv dc first tail modern anchors
    checkpointEmpty historicalNoFrame rewards modernSystemNoAuthority
    modernNoAuthority modernNoFrame installed invariant
  rw [target]
  have storage : Devm.getStor base ca = B.state.getStor ca :=
    congrArg (fun world : State => world.getStor ca) state
  rw [storage]
  exact reached

/-- A warm count view at reached B returns the exact extracted-history length,
with the unchanged exact gas, world, accessed keys and logs. -/
theorem historicalSeam_count_warm (sevm : Sevm) (base : Devm) (G : Nat)
    (target : sevm.currentTarget = ca) (state : base.state = B.state)
    (hcode : sevm.code = code)
    (hdataLength : 4 ≤ sevm.data.length) (hdataBound : sevm.data.length < 2 ^ 256)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = BeaconDeposit.getDepositCountSelector)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hwarm : (⟨sevm.currentTarget, countSlot⟩ : Adr × B256) ∈ base.accessedStorageKeys) :
    ∃ post, Nonempty (Exec 0 sevm
        (base.setMach ⟨[], Mem.empty, G + countGasWarm, base.stateGas⟩) (.ok post)) ∧
      post.gasLeft = G ∧
      post.output = BeaconDeposit.abiDynamicBytesReturn (BeaconDeposit.le64 (initialHistory ++ committedNodesIn ca (((dc.step first).append tail).append modern.toHistForkIn)).length) ∧
      post.state = base.state ∧ post.accessedStorageKeys = base.accessedStorageKeys ∧
      post.logs = base.logs := by
  have atFrame := historicalSeam_frame_solInv dc first tail modern anchors
    checkpointEmpty historicalNoFrame rewards modernSystemNoAuthority
    modernNoAuthority modernNoFrame installed invariant sevm base target state
  obtain ⟨Mf, run⟩ := get_deposit_count_warm_exec_history sevm base _ _ G hcode hdataLength
    hdataBound hvalue hselector hfork hwarm rfl atFrame
  exact ⟨_, run, rfl, rfl, rfl, rfl, rfl⟩

/-- A cold count view at that same reached B uses the original cold gas formula,
returns the same history length, and adds exactly the accessed count key. -/
theorem historicalSeam_count_cold (sevm : Sevm) (base : Devm) (G : Nat)
    (target : sevm.currentTarget = ca) (state : base.state = B.state)
    (hcode : sevm.code = code)
    (hdataLength : 4 ≤ sevm.data.length) (hdataBound : sevm.data.length < 2 ^ 256)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = BeaconDeposit.getDepositCountSelector)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hcold : (⟨sevm.currentTarget, countSlot⟩ : Adr × B256) ∉ base.accessedStorageKeys) :
    ∃ post, Nonempty (Exec 0 sevm
        (base.setMach ⟨[], Mem.empty, G + countGasCold, base.stateGas⟩) (.ok post)) ∧
      post.gasLeft = G ∧
      post.output = BeaconDeposit.abiDynamicBytesReturn (BeaconDeposit.le64 (initialHistory ++ committedNodesIn ca (((dc.step first).append tail).append modern.toHistForkIn)).length) ∧
      post.state = base.state ∧
      post.accessedStorageKeys =
        (addAccessedStorageKey base sevm.currentTarget countSlot).accessedStorageKeys ∧
      post.logs = base.logs := by
  have atFrame := historicalSeam_frame_solInv dc first tail modern anchors
    checkpointEmpty historicalNoFrame rewards modernSystemNoAuthority
    modernNoAuthority modernNoFrame installed invariant sevm base target state
  obtain ⟨countWord, countBound⟩ := solCount_eq_of_solInv atFrame
  have countRead : base.getStorVal sevm.currentTarget countSlot = Nat.toB256 (initialHistory ++ committedNodesIn ca (((dc.step first).append tail).append modern.toHistForkIn)).length :=
    countWord
  obtain ⟨Mf, -, -, -, run⟩ := get_deposit_count_cold_exec sevm base _ G hcode hdataLength
    hdataBound hvalue hselector hfork hcold countRead
  rw [B256.toNat_toB256, Nat.lo_eq_of_lt (by omega)] at run
  exact ⟨_, run, rfl, rfl, rfl, rfl, rfl⟩

/-- The root view at reached B returns the mixed root of the same exact ordered
extraction; its original gas bound and all-storage/log preservation are unchanged. -/
theorem historicalSeam_root_view (sevm : Sevm) (base : Devm) (G : Nat)
    (target : sevm.currentTarget = ca) (state : base.state = B.state)
    (hcode : sevm.code = code)
    (hdataLength : 4 ≤ sevm.data.length) (hdataBound : sevm.data.length < 2 ^ 256)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = BeaconDeposit.getDepositRootSelector)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound : G + rootViewGas sevm base (initialHistory ++ committedNodesIn ca (((dc.step first).append tail).append modern.toHistForkIn)).length + 6000 < 2 ^ 256) :
    ∃ post, Nonempty (Exec 0 sevm
        (base.setMach ⟨[], Mem.empty, G + rootViewGas sevm base (initialHistory ++ committedNodesIn ca (((dc.step first).append tail).append modern.toHistForkIn)).length,
          base.stateGas⟩) (.ok post)) ∧
      post.gasLeft = G ∧
      post.output = (BeaconDeposit.mixedRootOf Bytes.sha256 (initialHistory ++ committedNodesIn ca (((dc.step first).append tail).append modern.toHistForkIn))).toBytes ∧
      (∀ a, Devm.getStor post a = Devm.getStor base a) ∧ post.logs = base.logs := by
  have atFrame := historicalSeam_frame_solInv dc first tail modern anchors
    checkpointEmpty historicalNoFrame rewards modernSystemNoAuthority
    modernNoAuthority modernNoFrame installed invariant sevm base target state
  exact get_deposit_root_exec_mixedRoot sevm base _ _ G hcode hdataLength hdataBound hvalue
    hselector hfork rfl atFrame hnodeleg hwarm hpre hdepth hbound

end Blanc.Lift.BeaconDeposit
