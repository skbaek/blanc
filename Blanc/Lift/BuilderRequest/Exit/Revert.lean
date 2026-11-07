import Blanc.Lift.BuilderRequest.Exit.Message
import Blanc.Lift.BuilderRequest.Revert

/-!
# The exit contract's reverting frames under Amsterdam

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`.

Every non-system frame at the code with the gas to reach it: slot 0 on the inhibitor, value below the quoted fee, calldata
of neither form, or a fee read carrying value, executes `REVERT`. Each is a positive statement.
-/

namespace Blanc.Lift.BuilderRequest.Exit

open Jaune
open RequestFee (selected)

/-- The entries the cuts name: the window and the fee loop. -/
def cutEntries : List Nat := [0, 0x57, 0, 0, 0, 0, 0x63]

/-- The guard, cut where value is below the fee. -/
def lowCut : SFunc :=
  .dest (.next (.reg .callvalue) (.next (.reg .lt) (.next (.push [0x01, 0xc6] (by decide))
    (.branch .undefined rev0))))

theorem revert_at : Linst.At code 0x1c9 .revert := by unfold Linst.At; kernel_rfl

theorem low_cut : userPath.Cut .undefined lowCut cutEntries 0x1c9 := ⟨by decide +kernel, by decide +kernel⟩
theorem badLength_cut : userPath.Cut (UserPath.badLengthCut userPath) .undefined cutEntries 0x1c9 :=
  ⟨by decide +kernel, by decide +kernel⟩
theorem paidRead_cut : userPath.Cut (UserPath.paidReadCut userPath) .undefined cutEntries 0x1c9 :=
  ⟨by decide +kernel, by decide +kernel⟩
theorem inhibit_cut : cutOk code [] 0x1c9 0 none (inhibitCut userPath.systemDest userPath.shape.revert) = true := by
  decide +kernel

variable {s : Sevm} {b : Devm} {n : Nat} {out : B256}

theorem frameReverts_inhibited (hcode : s.code = code) (hfork : s.benvStat.fork = .amsterdam)
    (caller : s.caller ≠ systemAddress) (inhibited : b.getStorVal s.currentTarget 0 = B256.max) :
    FrameReverts s b (revertBound 0) :=
  Blanc.Lift.BuilderRequest.frameReverts_inhibited inhibit_cut revert_at hcode hfork caller inhibited

/-- **Calldata of neither form reverts.** -/
theorem frameReverts_badLength (hcode : s.code = code) (hfork : s.benvStat.fork = .amsterdam)
    (caller : s.caller ≠ systemAddress) (off : b.getStorVal s.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 2 s b) 17 1 17 0 n out)
    (other : s.data.length.toB256 ≠ (48 : B256)) (nonzero : s.data.length.toB256 ≠ 0) :
    FrameReverts s b (revertBound n) :=
  UserPath.frameReverts_badLength (k := userPath) rfl rfl badLength_cut revert_at hcode hfork caller off wordRun
    other nonzero

/-- **A fee read carrying value reverts.** -/
theorem frameReverts_paidRead (hcode : s.code = code) (hfork : s.benvStat.fork = .amsterdam)
    (caller : s.caller ≠ systemAddress) (off : b.getStorVal s.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 2 s b) 17 1 17 0 n out)
    (empty : s.data = []) (paid : s.value ≠ 0) :
    FrameReverts s b (revertBound n) :=
  UserPath.frameReverts_paidRead (k := userPath) rfl rfl paidRead_cut revert_at hcode hfork caller off wordRun empty paid

/-- **A submission below the fee reverts, on a fork's steps.** 48 bytes of calldata, slot 0 off the inhibitor, and
value below the fee the bytes quote: the frame executes `REVERT`, charging no state gas. -/
theorem frameReverts_not_admitted_on {l : StorageSteps s} (v : l.Valid)
    (hcode : s.code = code)
    (caller : s.caller ≠ systemAddress) (hlen : s.data.length = 48)
    (off : b.getStorVal s.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 2 s b) 17 1 17 0 n out)
    (hmeter : (l.feeBase b).stateGas = b.stateGas)
    (rejected : ¬ Admits s.data s.value (out / (17 : B256))) :
    FrameReverts s b (revertBound n) := by
  have hp0 := v.push0
  have word : s.data.length.toB256 = userPath.shape.len.word := by rw [hlen]; rfl
  generalize hfee : out / (17 : B256) = fee at rejected
  have low : s.value < fee := by
    rw [B256.lt_iff_toNat_lt_toNat]
    unfold Admits at rejected
    omega
  refine UserPath.frameReverts_of_arm_on (k := userPath) v (X := 5 + 10 + 3 + 3 + 2 + 1) (S := []) rfl rfl
    low_cut revert_at hcode caller off wordRun hmeter (by omega) fun G => ?_
  rw [hfee]
  simp only [selected]
  rw [ite_eq_left word]
  have hgas : G + (5 + 10 + 3 + 3 + 2 + 1) = (G + 2 + 2 + 1) + 10 + 3 + 3 + 2 + 1 := by omega
  rw [hgas]
  unfold lowCut
  refine rx_dest ?_
  refine rx_callvalue (by change 1 < 1024; decide) ?_
  refine rx_lt (v := 1) ?_ (by change 0 < 1024; decide) ?_
  · simp only [B256.ltCheck, ite_eq_left low]
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  exact rx_branch_succ (by decide : (1 : B256) ≠ 0) (rev0_exact hp0 (by decide))

/-- **A submission below the fee reverts.** 48 bytes of calldata, slot 0 off the inhibitor, and value below the fee the
bytes quote: the frame executes `REVERT`, charging no state gas. -/
theorem frameReverts_not_admitted (hcode : s.code = code) (hfork : s.benvStat.fork = .amsterdam)
    (caller : s.caller ≠ systemAddress) (hlen : s.data.length = 48)
    (off : b.getStorVal s.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 2 s b) 17 1 17 0 n out)
    (rejected : ¬ Admits s.data s.value (out / (17 : B256))) :
    FrameReverts s b (revertBound n) :=
  frameReverts_not_admitted_on (amsterdamSteps_valid hfork) hcode caller hlen off wordRun
    (UserPath.feeBase_stateGas s b) rejected

end Blanc.Lift.BuilderRequest.Exit
