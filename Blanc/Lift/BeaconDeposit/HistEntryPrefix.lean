import Blanc.Lift.BeaconDeposit.HistDeployment
import Blanc.ExecutionInOwnCode
import Blanc.ExecutionAccountingPositionalHistory
namespace Blanc.Lift.BeaconDeposit
open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
private theorem classification_ownSpawns (ca : Adr) : OwnSpawnsIn ca code := by
  intro root node x pc installed _ hsg chain instruction
  exact Or.inr (Or.inl (parentPrefix_exec_staticcallH pc installed hsg chain instruction))

private theorem classification_admitted {B : BlockChain} (d : BeaconDeploymentTo B) :
    d.trace.FrameAdmitted Creation.depositAddress beaconEntry := by
  let historical := (d.dc.step d.first).append d.tail
  have initial : beaconSpec.StateInv Creation.depositAddress d.D.state :=
    ⟨by rw [d.deployed.1]; rfl, trivial, ⟨[], d.deployed.2⟩⟩
  have rewards := historical.rewardCreditsFunded BodyStageCapabilities.historical
  obtain ⟨left, atPrague, emptyPrague⟩ := configuredHistoryIn_environment historical
    (d.anchors.historicalOpenings d.dc d.first d.tail)
    (fun p _ => d.anchors.historicalPragueNoAuthorityAt d.dc d.first d.tail p.1)
    d.checkpointEmpty (d.anchors.historicalPragueNoAuthorityAt d.dc d.first d.tail 2)
    d.historicalNoFrame rewards initial
  have codePrague := ContractSpecSem.StateInv.getCode_eq_of_image (C := code) rfl atPrague
  have avoid := d.modern.systemCreateAvoid d.anchors.pragueInstalled d.modernSystemNoAuthority
  have right := beaconEntry_of_env d.modern d.modern.frameAdmitted_calldata
    (system_of_installed d.modern d.anchors.pragueInstalled d.modernSystemNoAuthority
      avoid.2 codePrague) emptyPrague d.modernNoAuthority d.modernNoFrame
  rw [d.trace.frameAdmitted_iff_rawFrames]
  intro root member target
  change root ∈ (historical.append d.modern.toHistForkIn).rawFrames at member
  rw [ConfiguredHistoryTraceIn.rawFrames_append,
    ConfiguredHistoryTrace.toHistForkIn_rawFrames] at member
  rcases List.mem_append.mp member with member | member
  · exact (historical.frameAdmitted_iff_rawFrames _ _).mp left root member target
  · exact (d.modern.frameAdmitted_iff_rawFrames _ _).mp right root member target

private theorem classification_frame_facts {B : BlockChain} (d : BeaconDeploymentTo B)
    (idx : Nat) (fr : Exec.Frame) (hlookup : d.trace.settledFrames[idx]? = some fr)
    (target : fr.sevm.currentTarget = depositContractAddress) :
    fr.pc = 0 ∧ HistFork fr.sevm.benvStat.fork ∧ fr.sevm.code = code ∧
    Exec.FreshEntry fr.sevm fr.pre ∧ fr.sevm.data.length < 2 ^ 256 ∧
    ShaReadyRules fr.sevm fr.pre := by
  have member : fr ∈ d.trace.settledFrames := List.mem_of_getElem? hlookup
  have atCreation : fr.sevm.currentTarget = Creation.depositAddress := target
  have installed : some (d.D.state.getCode Creation.depositAddress).toList = beaconSem.image := by
    rw [d.deployed.1]; rfl
  have own := d.trace.settled_ownCodeIn beaconSem Creation.depositAddress
    beaconInstalledCertH.nonempty beaconInstalledCertH.notDelegation
    (classification_ownSpawns Creation.depositAddress) BodyStageCapabilities.historical
    (d.trace.rewardCreditsFunded BodyStageCapabilities.historical) installed
    beaconInstalledCertH.runtimeSafety rfl fr member
  have raw := d.trace.mem_rawFrames_of_mem_settledFrames fr member
  have ready := (d.trace.frameAdmitted_iff_rawFrames _ _).mp
    (classification_admitted d) _ raw atCreation
  have fresh := (d.trace.frameAdmitted_iff_rawFrames _ _).mp
    (d.trace.freshFrameAdmitted Creation.depositAddress) _ raw atCreation
  refine ⟨own.2.1, own.2.2.1, own.2.2.2.2 atCreation, fresh, ready.1, ?_⟩
  exact ⟨fun _ => ready.2.1, ready.2.2, isPrecomp_two_hist own.2.2.1,
    own.2.2.2.1, own.2.2.1.bal_none⟩
end Blanc.Lift.BeaconDeposit
