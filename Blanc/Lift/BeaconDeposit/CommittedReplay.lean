import Blanc.Lift.BeaconDeposit.Refines
import Blanc.Lift.BeaconDeposit.Ladder
import Blanc.ExecutionAccountingReplay
import Blanc.ExecutionTraceSettledFrames

namespace Blanc.Lift.BeaconDeposit

open Jaune Blanc.ExecutionAccountingReplay Blanc.ExecutionTrace

/-- A settled execution frame contributes its decoded node exactly when it
executes the deposit selector at the selected contract address. -/
def committedFrameNodes (ca : Adr) (frame : Exec.Frame) : List B256 :=
  if frame.sevm.currentTarget = ca then frameAccepted frame.sevm else []

/-- Deposits extracted in execution order from the supplied retained history.
Both interpreter and message settlement prune discarded subtrees first. -/
def committedNodes {cfg : ChainConfig} {checkpoint future : BlockChain}
    (ca : Adr) (trace : ConfiguredHistoryTrace cfg checkpoint future) : List B256 :=
  trace.settledFrames.flatMap (committedFrameNodes ca)



/-- A history segment carries every admitted initial history to the same
initial history followed by this segment. Storage is the replay boundary. -/
def DepositReplay (pre : Stor) (nodes : List B256) (post : Stor) : Prop :=
  ∀ history, SolInv pre history → SolInv post (history ++ nodes)

theorem DepositReplay.nil (storage : Stor) : DepositReplay storage [] storage := by
  intro history invariant
  simpa only [List.append_nil] using invariant

theorem DepositReplay.append {pre middle post : Stor} {left right : List B256}
    (first : DepositReplay pre left middle)
    (second : DepositReplay middle right post) :
    DepositReplay pre (left ++ right) post := by
  intro history invariant
  simpa only [List.append_assoc] using second _ (first _ invariant)

/-- Beacon's replay reads storage only. Value transfers and balance credits
therefore contribute an empty history segment. -/
def depositCarrier (ca : Adr) : ReplayCarrier ca where
  Snap := Stor
  Step := B256
  Tag := Unit
  Replay := DepositReplay
  ofState state := state.getStor ca
  frameEntry _ state := state.getStor ca
  nil := DepositReplay.nil
  silent := fun storage _ => storage
  credit := by
    intro _ _ _ _ storage _ _
    exact ⟨[], by rw [storage]; exact DepositReplay.nil _⟩
  entry_eq_ofState := by
    intro _ _ _ _ transfer _
    exact congrFun (benvAfterTransfer_getStor_eq transfer) ca

/-- Replay nodes and committed-frame nodes use the same ordered observation. -/
def depositObservation (ca : Adr) : ReplayObservation (depositCarrier ca) where
  O := B256
  obs := id
  obs_nil := rfl
  obs_append := fun _ _ => rfl
  frameObs := committedFrameNodes ca
  credit := by
    intro _ pre post _ storage _ _
    refine ⟨[], ?_, rfl⟩
    change DepositReplay (pre.getStor ca) [] (post.getStor ca)
    rw [storage]
    exact DepositReplay.nil _

end Blanc.Lift.BeaconDeposit
