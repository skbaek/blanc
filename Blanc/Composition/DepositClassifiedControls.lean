import Blanc.Corpus.Freeze.DepositCells
import Blanc.Lift.BeaconDeposit.Init
import Blanc.Lift.BeaconDeposit.Body

/-!
# D-S2 control: minimum-deposit floor deletion and permissive-selector runtime mutant

Proves `Blanc.Corpus.Freeze.Deposit.D_S2_control` (`d_s2_control` / `D_S2_control_proved`):
1. Deleting the 1 ETH minimum-value guard (`depositWithoutFloor`) accepts a positive sub-1-ETH
   1-gwei deposit (`floor_model_accepts`) that `Classified` rejects on every frame and history
   (`every_frame_rejects_oneGwei`).
2. Replacing the deployed runtime at `depositAddr` with a single-byte `STOP` runtime (`mutantCode`)
   admits a settled-shaped frame (`mutantFrame`) at `.prague` with valid `SolInv _ []` on an
   unrecognized selector, which `Classified` rejects (`mutant_rejects`).
-/

namespace Blanc.Composition.DepositClassifiedControls

open Jaune Blanc Blanc.Lift.BeaconDeposit
open Blanc.Corpus.Freeze.Deposit

def floorPk : Bytes := List.replicate 48 0
def floorWc : Bytes := List.replicate 32 0
def floorSig : Bytes := List.replicate 96 0
def floorRoot : B256 := BeaconDeposit.depositDataNode Bytes.sha256
  floorPk floorWc floorSig (BeaconDeposit.le64 1)
def floorPost : BeaconDeposit.Acc :=
  ⟨BeaconDeposit.setSlot BeaconDeposit.Acc.empty.branch 0 floorRoot, 1⟩
def floorEvent : BeaconDeposit.DepositEvent :=
  ⟨floorPk, floorWc, BeaconDeposit.le64 1, floorSig, BeaconDeposit.le64 0⟩

theorem floor_model_accepts :
    depositWithoutFloor Bytes.sha256 BeaconDeposit.Acc.empty
      floorPk floorWc floorSig floorRoot BeaconDeposit.oneGwei =
      .ok (floorPost, floorEvent) := by
  have hpk : floorPk.length = 48 := rfl
  have hwc : floorWc.length = 32 := rfl
  have hsig : floorSig.length = 96 := rfl
  have hmod : BeaconDeposit.oneGwei % BeaconDeposit.oneGwei = 0 := by decide
  have hdiv : BeaconDeposit.oneGwei / BeaconDeposit.oneGwei = 1 := by decide
  have hhi : ¬ (2 ^ 64 - 1 < 1) := by decide
  have hcap : (0 : Nat) < 2 ^ 32 - 1 := by decide
  unfold depositWithoutFloor
  simp only [hpk, hwc, hsig, hmod, hdiv, hhi, ne_eq, not_true_eq_false, ↓reduceIte,
    BeaconDeposit.Acc.empty, hcap]
  have hnode : BeaconDeposit.depositDataNode Bytes.sha256 floorPk floorWc floorSig
      (BeaconDeposit.le64 1) = floorRoot := rfl
  simp only [hnode, not_true_eq_false, ↓reduceIte, BeaconDeposit.walk, zero_add, Nat.mod_succ]
  rfl

theorem every_frame_rejects_oneGwei (fr : Exec.Frame) (history : List B256)
    (value : fr.sevm.value.toNat = BeaconDeposit.oneGwei) :
    ¬ ∃ o : DepositOutcome, Classified fr history o := by
  rintro ⟨o, hc⟩
  cases o with
  | deposit =>
      obtain ⟨-, -, s', ev, hOk, -⟩ := hc
      have hv := (deposit_ok_facts hOk).2.2.2.1
      rw [value] at hv
      exact absurd hv (by decide)
  | getDepositRoot | getDepositCount | supportsInterface =>
      have hv : fr.sevm.value = 0 := hc.2.1
      rw [hv] at value
      exact absurd value (by decide)

def mutantCode : ByteArray := ⟨#[0]⟩
def mutantState : State := State.setPresent (.empty : State) depositAddr
  ⟨1, 0, beaconZeroStor, mutantCode⟩
def mutantBenv : Benv := { (default : Benv) with state := mutantState }
def mutantMsg : Msg where
  benv := mutantBenv
  tenv := default
  caller := 1
  target := some depositAddr
  currentTarget := depositAddr
  gas := 0
  value := 0
  data := [0, 0, 0, 0]
  codeAddress := some depositAddr
  code := mutantCode
  depth := 1
  shouldTransferValue := false
  isStatic := false
  accessedAddresses := .emptyWithCapacity
  accessedStorageKeys := .emptyWithCapacity
  disablePrecompiles := false

def mutant_run :
    Exec 0 (initSevm mutantMsg) (initDevm mutantMsg) (.ok (initDevm mutantMsg)) :=
  Exec.halt (Evm.step_last (l := .stop) rfl)

def mutantFrame : Exec.Frame := Exec.Frame.ofRun mutant_run (by rfl)

theorem mutant_rejects :
    mutantFrame.sevm.code = mutantCode ∧
    mutantFrame.sevm.currentTarget = depositAddr ∧
    CoveredFork mutantFrame.sevm.benvStat.fork ∧
    SolInv (mutantFrame.pre.getStor depositAddr) [] ∧
    ¬ ∃ o : DepositOutcome, Classified mutantFrame [] o := by
  refine ⟨rfl, rfl, CoveredFork.prague, ?_, ?_⟩
  · have hst : mutantFrame.pre.getStor depositAddr = beaconZeroStor := by
      change (mutantState.get depositAddr).stor = beaconZeroStor
      rw [mutantState, State.get_setPresent_self]
    rw [hst]
    exact beacon_zero_init
  · rintro ⟨o, hc⟩
    have hsel0 : Sevm.selector mutantFrame.sevm = 0 := by decide
    cases o with
    | deposit =>
        have hs := hsel0.symm.trans (hc.1.trans BeaconDeposit.depositSelector_eq)
        exact absurd hs (by decide)
    | getDepositRoot =>
        have hs := hsel0.symm.trans (hc.1.trans BeaconDeposit.getDepositRootSelector_eq)
        exact absurd hs (by decide)
    | getDepositCount =>
        have hs := hsel0.symm.trans (hc.1.trans BeaconDeposit.getDepositCountSelector_eq)
        exact absurd hs (by decide)
    | supportsInterface =>
        have hsup : BeaconDeposit.supportsInterfaceSelector = 0x01ffc9a7 := by decide +kernel
        have hs := hsel0.symm.trans (hc.1.trans hsup)
        exact absurd hs (by decide)

theorem d_s2_control : Blanc.Corpus.Freeze.Deposit.D_S2_control :=
  ⟨⟨floorPk, floorWc, floorSig, floorRoot, BeaconDeposit.oneGwei, floorPost, floorEvent,
      by decide, by decide, floor_model_accepts, every_frame_rejects_oneGwei⟩,
   ⟨mutantCode, mutantFrame, mutant_rejects⟩⟩

/-- Alias matching the integration header signature. -/
theorem D_S2_control_proved : Blanc.Corpus.Freeze.Deposit.D_S2_control := d_s2_control

end Blanc.Composition.DepositClassifiedControls
