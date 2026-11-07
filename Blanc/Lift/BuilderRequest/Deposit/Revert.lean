import Blanc.Lift.BuilderRequest.Deposit.Message
import Blanc.Lift.BuilderRequest.Revert

/-!
# The deposit contract's reverting frames under Amsterdam

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`.

Every non-system frame at the code with the gas to reach it: slot 0 on the inhibitor, a submission the guards do not
admit, calldata of neither form, or a fee read carrying value, executes `REVERT`. Each is a positive statement.
-/

namespace Blanc.Lift.BuilderRequest.Deposit

open Jaune
open RequestFee (selected)
open RequestSystem (dispatchGas)

/-- The entries the cuts name: the window and the fee loop. -/
def cutEntries : List Nat := [0, 0x58, 0, 0, 0, 0, 0x64]

/-- The guards, cut where value is below the fee. -/
def lowCut : SFunc :=
  .dest (.next (.reg (.dup 0)) (.next (.reg .callvalue) (.next (.reg .lt) (.next (.push [0x02, 0x70] (by decide))
    (.branch .undefined rev0)))))

/-- The guards, cut where less than 1 ETH is credited. -/
def floorCut : SFunc :=
  .dest (.next (.reg (.dup 0)) (.next (.reg .callvalue) (.next (.reg .lt) (.next (.push [0x02, 0x70] (by decide))
    (.branch (.next (.push [0x38] (by decide)) (.next (.reg .calldataload)
      (.next (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)) (.next (.reg .and)
      (.next (.reg (.dup 0)) (.next (.push [0x3b, 0x9a, 0xca, 0x00] (by decide)) (.next (.reg .gt)
      (.next (.push [0x02, 0x70] (by decide)) (.branch .undefined rev0))))))))) .undefined)))))

/-- The guards, cut where value does not cover the credit and the fee. -/
def coverCut : SFunc :=
  .dest (.next (.reg (.dup 0)) (.next (.reg .callvalue) (.next (.reg .lt) (.next (.push [0x02, 0x70] (by decide))
    (.branch (.next (.push [0x38] (by decide)) (.next (.reg .calldataload)
      (.next (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)) (.next (.reg .and)
      (.next (.reg (.dup 0)) (.next (.push [0x3b, 0x9a, 0xca, 0x00] (by decide)) (.next (.reg .gt)
      (.next (.push [0x02, 0x70] (by decide))
        (.branch (.next (.push [0x3b, 0x9a, 0xca, 0x00] (by decide)) (.next (.reg .mul) (.next (.reg (.swap 0))
          (.next (.reg .callvalue) (.next (.reg .sub) (.next (.reg .lt) (.next (.push [0x02, 0x70] (by decide))
          (.branch .undefined rev0))))))))
          .undefined))))))))) .undefined)))))

theorem revert_at : Linst.At code 0x273 .revert := by unfold Linst.At; kernel_rfl

theorem low_cut : userPath.Cut .undefined lowCut cutEntries 0x273 := ⟨by decide +kernel, by decide +kernel⟩
theorem floor_cut : userPath.Cut .undefined floorCut cutEntries 0x273 := ⟨by decide +kernel, by decide +kernel⟩
theorem cover_cut : userPath.Cut .undefined coverCut cutEntries 0x273 := ⟨by decide +kernel, by decide +kernel⟩
theorem badLength_cut : userPath.Cut (UserPath.badLengthCut userPath) .undefined cutEntries 0x273 :=
  ⟨by decide +kernel, by decide +kernel⟩
theorem paidRead_cut : userPath.Cut (UserPath.paidReadCut userPath) .undefined cutEntries 0x273 :=
  ⟨by decide +kernel, by decide +kernel⟩
theorem inhibit_cut : cutOk code [] 0x273 0 none (inhibitCut userPath.systemDest userPath.shape.revert) = true := by
  decide +kernel

variable {s : Sevm} {b : Devm} {n : Nat} {out : B256}

theorem frameReverts_inhibited (hcode : s.code = code) (hfork : s.benvStat.fork = .amsterdam)
    (caller : s.caller ≠ systemAddress) (inhibited : b.getStorVal s.currentTarget 0 = B256.max) :
    FrameReverts s b (revertBound 0) :=
  Blanc.Lift.BuilderRequest.frameReverts_inhibited inhibit_cut revert_at hcode hfork caller inhibited

/-- **Calldata of neither form reverts.** -/
theorem frameReverts_badLength (hcode : s.code = code) (hfork : s.benvStat.fork = .amsterdam)
    (caller : s.caller ≠ systemAddress) (off : b.getStorVal s.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 8 s b) 17 1 17 0 n out)
    (other : s.data.length.toB256 ≠ (184 : B256)) (nonzero : s.data.length.toB256 ≠ 0) :
    FrameReverts s b (revertBound n) :=
  UserPath.frameReverts_badLength (k := userPath) rfl rfl badLength_cut revert_at hcode hfork caller off wordRun
    other nonzero

/-- **A fee read carrying value reverts.** -/
theorem frameReverts_paidRead (hcode : s.code = code) (hfork : s.benvStat.fork = .amsterdam)
    (caller : s.caller ≠ systemAddress) (off : b.getStorVal s.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 8 s b) 17 1 17 0 n out)
    (empty : s.data = []) (paid : s.value ≠ 0) :
    FrameReverts s b (revertBound n) :=
  UserPath.frameReverts_paidRead (k := userPath) rfl rfl paidRead_cut revert_at hcode hfork caller off wordRun empty paid

/-- **A submission the guards do not admit reverts.** 184 bytes of calldata, slot 0 off the inhibitor, and either less
than 1 ETH credited or value below the credit plus the fee the bytes quote: the frame executes `REVERT`, charging no
state gas. -/
theorem frameReverts_not_admitted (hcode : s.code = code) (hfork : s.benvStat.fork = .amsterdam)
    (caller : s.caller ≠ systemAddress) (hlen : s.data.length = 184)
    (off : b.getStorVal s.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 8 s b) 17 1 17 0 n out)
    (rejected : ¬ Admits s.data s.value (out / (17 : B256))) :
    FrameReverts s b (revertBound n) := by
  have hp0 := amsterdam_push0 hfork
  have word : s.data.length.toB256 = userPath.shape.len.word := by rw [hlen]; rfl
  generalize hfee : out / (17 : B256) = fee at rejected
  by_cases low : s.value < fee
  · refine UserPath.frameReverts_of_arm (k := userPath) (X := 5 + 10 + 3 + 3 + 2 + 3 + 1) (S := [fee]) rfl rfl low_cut
      revert_at hcode hfork caller off wordRun (by omega) fun G => ?_
    rw [hfee]
    simp only [selected]
    rw [ite_eq_left word]
    have hgas : G + (5 + 10 + 3 + 3 + 2 + 3 + 1) = (G + 2 + 2 + 1) + 10 + 3 + 3 + 2 + 3 + 1 := by omega
    rw [hgas]
    unfold lowCut
    refine rx_dest ?_
    refine rx_dup1 (by change 1 < 1024; decide) ?_
    refine rx_callvalue (by change 2 < 1024; decide) ?_
    refine rx_lt (v := 1) ?_ (by change 1 < 1024; decide) ?_
    · simp only [B256.ltCheck, ite_eq_left low]
    refine rx_push rfl (by change 2 < 1024; decide) ?_
    exact rx_branch_succ (by decide : (1 : B256) ≠ 0) (rev0_exact hp0 (by change 2 < 1024; decide))
  by_cases floor : amountGwei s < Bytes.toB256 [0x3b, 0x9a, 0xca, 0x00]
  · refine UserPath.frameReverts_of_arm (k := userPath)
      (X := 5 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 10 + 3 + 3 + 2 + 3 + 1) (S := [amountGwei s, fee]) rfl rfl floor_cut
      revert_at hcode hfork caller off wordRun (by omega) fun G => ?_
    rw [hfee]
    simp only [selected]
    rw [ite_eq_left word]
    have hgas : G + (5 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 10 + 3 + 3 + 2 + 3 + 1) =
        (G + 2 + 2 + 1) + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 10 + 3 + 3 + 2 + 3 + 1 := by omega
    rw [hgas]
    unfold floorCut
    refine rx_dest ?_
    refine rx_dup1 (by change 1 < 1024; decide) ?_
    refine rx_callvalue (by change 2 < 1024; decide) ?_
    refine rx_lt (v := 0) ?_ (by change 1 < 1024; decide) ?_
    · simp only [B256.ltCheck, ite_eq_right low]
    refine rx_push rfl (by change 2 < 1024; decide) ?_
    refine rx_branch_zero ?_
    refine rx_push rfl (by change 1 < 1024; decide) ?_
    refine rx_calldataload (by change 1 < 1024; decide) ?_
    refine rx_push (w := amountMask) rfl (by change 2 < 1024; decide) ?_
    refine rx_and (v := amountGwei s) rfl (by change 1 < 1024; decide) ?_
    refine rx_dup1 (by change 2 < 1024; decide) ?_
    refine rx_push rfl (by change 3 < 1024; decide) ?_
    refine rx_gt (v := 1) ?_ (by change 2 < 1024; decide) ?_
    · simp only [B256.gtCheck, ite_eq_left floor]
    refine rx_push rfl (by change 3 < 1024; decide) ?_
    exact rx_branch_succ (by decide : (1 : B256) ≠ 0) (rev0_exact (S := [amountGwei s, fee]) hp0 (by change 3 < 1024; decide))
  have paid : fee.toNat ≤ s.value.toNat := by
    rw [B256.lt_iff_toNat_lt_toNat] at low
    omega
  have enough : 10 ^ 18 ≤ creditOf s.data := by
    rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0x3b, 0x9a, 0xca, 0x00]).toNat = 10 ^ 9 by decide] at floor
    rw [← creditedWei_eq, creditedWei]
    omega
  have short : s.value - fee < Bytes.toB256 [0x3b, 0x9a, 0xca, 0x00] * amountGwei s := by
    rw [B256.lt_iff_toNat_lt_toNat, gwei_mul, value_sub paid]
    have hnot : ¬ (creditedWei s + fee.toNat ≤ s.value.toNat) := fun h => rejected ⟨enough, h⟩
    omega
  refine UserPath.frameReverts_of_arm (k := userPath)
    (X := 5 + 10 + 3 + 3 + 3 + 2 + 3 + 5 + 3 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 10 + 3 + 3 + 2 + 3 + 1)
    (S := []) rfl rfl cover_cut revert_at hcode hfork caller off wordRun (by omega) fun G => ?_
  rw [hfee]
  simp only [selected]
  rw [ite_eq_left word]
  have hgas : G + (5 + 10 + 3 + 3 + 3 + 2 + 3 + 5 + 3 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 10 + 3 + 3 + 2 + 3 + 1) =
      (G + 2 + 2 + 1) + 10 + 3 + 3 + 3 + 2 + 3 + 5 + 3 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 10 + 3 + 3 + 2 + 3 + 1 := by
    omega
  rw [hgas]
  unfold coverCut
  refine rx_dest ?_
  refine rx_dup1 (by change 1 < 1024; decide) ?_
  refine rx_callvalue (by change 2 < 1024; decide) ?_
  refine rx_lt (v := 0) ?_ (by change 1 < 1024; decide) ?_
  · simp only [B256.ltCheck, ite_eq_right low]
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  refine rx_branch_zero ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine rx_calldataload (by change 1 < 1024; decide) ?_
  refine rx_push (w := amountMask) rfl (by change 2 < 1024; decide) ?_
  refine rx_and (v := amountGwei s) rfl (by change 1 < 1024; decide) ?_
  refine rx_dup1 (by change 2 < 1024; decide) ?_
  refine rx_push rfl (by change 3 < 1024; decide) ?_
  refine rx_gt (v := 0) ?_ (by change 2 < 1024; decide) ?_
  · simp only [B256.gtCheck, ite_eq_right floor]
  refine rx_push rfl (by change 3 < 1024; decide) ?_
  refine rx_branch_zero ?_
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  refine rx_mul rfl (by change 1 < 1024; decide) ?_
  refine rx_swap1 ?_
  refine rx_callvalue (by change 2 < 1024; decide) ?_
  refine rx_sub' rfl (by change 1 < 1024; decide) ?_
  refine rx_lt (v := 1) ?_ (by decide) ?_
  · simp only [B256.ltCheck, ite_eq_left short]
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  exact rx_branch_succ (by decide : (1 : B256) ≠ 0) (rev0_exact (S := []) hp0 (by decide))

end Blanc.Lift.BuilderRequest.Deposit
