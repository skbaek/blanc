import Blanc.Lift.BuilderRequest.Static
import Blanc.Lift.BuilderRequest.Deposit.Revert

/-!
# The deposit contract in a static frame, under Amsterdam

Frame level only: see `BuilderRequest/Static.lean`.
-/

namespace Blanc.Lift.BuilderRequest.Deposit

open Jaune
open RequestFee (selected)

/-- The guards, then the count bump up to its `SSTORE`, at byte 0xd5. -/
def staticCut : SFunc :=
  .dest (.next (.reg (.dup 0)) (.next (.reg .callvalue) (.next (.reg .lt) (.next (.push [0x02, 0x70] (by decide))
    (.branch (.next (.push [0x38] (by decide)) (.next (.reg .calldataload)
      (.next (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)) (.next (.reg .and)
      (.next (.reg (.dup 0)) (.next (.push [0x3b, 0x9a, 0xca, 0x00] (by decide)) (.next (.reg .gt)
      (.next (.push [0x02, 0x70] (by decide))
        (.branch (.next (.push [0x3b, 0x9a, 0xca, 0x00] (by decide)) (.next (.reg .mul) (.next (.reg (.swap 0))
          (.next (.reg .callvalue) (.next (.reg .sub) (.next (.reg .lt) (.next (.push [0x02, 0x70] (by decide))
          (.branch countBumpCut .undefined))))))))
          .undefined))))))))) .undefined)))))

theorem sstore_at : Ninst.At code 0xd5 (.reg .sstore) := by unfold Ninst.At; kernel_rfl

theorem static_cut : userPath.Cut .undefined staticCut cutEntries 0xd5 := ⟨by decide +kernel, by decide +kernel⟩

variable {s : Sevm} {b : Devm} {n : Nat} {out : B256}

/-- **A submission in a static frame fails at its first `SSTORE`.** 184 bytes of calldata, slot 0 off the inhibitor and the guards' `Admitted`: the frame passes the fee path and the guards, reads the count, and halts with `writeInStaticContext`, from the frame's start, having taken a
charge `X` of regular gas from `gasLeft`; any gas above that reaches the failure. Frame level. -/
theorem frame_static_submission (hcode : s.code = code) (hfork : s.benvStat.fork = .amsterdam)
    (caller : s.caller ≠ systemAddress) (hlen : s.data.length = 184) (hs : s.isStatic = true)
    (off : b.getStorVal s.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 8 s b) 17 1 17 0 n out)
    (admitted : Admitted s (out / (17 : B256))) :
    ∃ X, X ≤ revertBound n + 12 + gasColdSload ∧ ∀ G, ∃ raw, Nonempty (Exec 0 s (St b [] .empty (G + X)) (.error (.halt (.writeInStaticContext .none), raw))) := by
  have word : s.data.length.toB256 = userPath.shape.len.word := by rw [hlen]; rfl
  generalize hfee : out / (17 : B256) = fee at admitted
  have paid : fee.toNat ≤ s.value.toNat := by
    have := admitted.covered
    omega
  have notLow : ¬ s.value < fee := by
    rw [B256.lt_iff_toNat_lt_toNat]
    exact Nat.not_lt_of_ge paid
  have floor : 10 ^ 9 ≤ (amountGwei s).toNat := by
    have := admitted.credited
    simp only [creditedWei] at this
    omega
  have notFloor : ¬ amountGwei s < Bytes.toB256 [0x3b, 0x9a, 0xca, 0x00] := by
    rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0x3b, 0x9a, 0xca, 0x00]).toNat = 10 ^ 9 by decide]
    exact Nat.not_lt_of_ge floor
  have notCover : ¬ s.value - fee < Bytes.toB256 [0x3b, 0x9a, 0xca, 0x00] * amountGwei s := by
    rw [B256.lt_iff_toNat_lt_toNat, gwei_mul, value_sub paid]
    have := admitted.covered
    omega
  generalize hbase : (amsterdamSteps s).feeBase b = base
  refine ⟨countBumpGas s base + 88 + (amsterdamSteps s).feePathGas b n + RequestSystem.dispatchGas, ?_, fun G => ?_⟩
  · have h1 := countBumpGas_le s base
    have h2 := UserPath.feePath_charge_le s b n 88 (by omega)
    omega
  have hat : Ninst.At s.code 0xd5 (.reg .sstore) := by rw [hcode]; exact sstore_at
  obtain ⟨raw, hraw⟩ := exec_sstore_static (b := afterSloadA s base 1) (S := []) (M := .empty) (G := G) (k := 1)
    (v := 1 + base.getStorVal s.currentTarget 1) hfork hs hat
  refine ⟨raw, ?_⟩
  have htail : SFunc.RunExact (userPath.cutProg .undefined staticCut) s
      (St base [fee] .empty (G + countBumpGas s base + 88))
      (selected s userPath.shape.len.word .undefined staticCut)
      (.halted (St (afterSloadA s base 1) [1, 1 + base.getStorVal s.currentTarget 1] .empty G)) := by
    simp only [selected]
    rw [ite_eq_left word]
    have hgas : G + countBumpGas s base + 88 = (G + countBumpGas s base) + 10 + 3 + 3 + 3 + 2 + 3 + 5 + 3
        + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 10 + 3 + 3 + 2 + 3 + 1 := by
      omega
    rw [hgas]
    unfold staticCut
    refine rx_dest ?_
    refine rx_dup1 (by change 1 < 1024; decide) ?_
    refine rx_callvalue (by change 2 < 1024; decide) ?_
    refine rx_lt (v := 0) ?_ (by change 1 < 1024; decide) ?_
    · simp only [B256.ltCheck, ite_eq_right notLow]
    refine rx_push rfl (by change 2 < 1024; decide) ?_
    refine rx_branch_zero ?_
    refine rx_push rfl (by change 1 < 1024; decide) ?_
    refine rx_calldataload (by change 1 < 1024; decide) ?_
    refine rx_push (w := amountMask) rfl (by change 2 < 1024; decide) ?_
    refine rx_and (v := amountGwei s) rfl (by change 1 < 1024; decide) ?_
    refine rx_dup1 (by change 2 < 1024; decide) ?_
    refine rx_push rfl (by change 3 < 1024; decide) ?_
    refine rx_gt (v := 0) ?_ (by change 2 < 1024; decide) ?_
    · simp only [B256.gtCheck, ite_eq_right notFloor]
    refine rx_push rfl (by change 3 < 1024; decide) ?_
    refine rx_branch_zero ?_
    refine rx_push rfl (by change 2 < 1024; decide) ?_
    refine rx_mul rfl (by change 1 < 1024; decide) ?_
    refine rx_swap1 ?_
    refine rx_callvalue (by change 2 < 1024; decide) ?_
    refine rx_sub' rfl (by change 1 < 1024; decide) ?_
    refine rx_lt (v := 0) ?_ (by decide) ?_
    · simp only [B256.ltCheck, ite_eq_right notCover]
    refine rx_push rfl (by change 1 < 1024; decide) ?_
    exact rx_branch_zero (countBump_exact hfork)
  subst hbase
  have := UserPath.exec_of_arm (k := userPath) rfl rfl static_cut hcode hfork caller off (out := out) wordRun (by rw [hfee]; exact htail) hraw
  have hg : G + (countBumpGas s ((amsterdamSteps s).feeBase b) + 88 + (amsterdamSteps s).feePathGas b n + RequestSystem.dispatchGas) =
      G + countBumpGas s ((amsterdamSteps s).feeBase b) + 88 + (amsterdamSteps s).feePathGas b n + RequestSystem.dispatchGas := by
    simp only [Nat.add_assoc]
  rw [hg]
  exact this

variable {pre post : Devm} {l : StorageSteps s}

/-- **A successful frame in a static context is a fee read.** On any fork's steps: a submission's law has `isStatic = false`. Frame level. -/
theorem static_frame_is_read (v : l.Valid) (hcode : s.code = code) (stack : pre.stack = [])
    (aligned : pre.memory.size % 32 = 0) (wf : Mem.Wf pre.memory) (lengthBound : s.data.length < 2 ^ 256)
    (caller : s.caller ≠ systemAddress) (hs : s.isStatic = true) (exec : Exec 0 s pre (.ok post)) :
    s.data = [] ∧ ∃ iterations finalOutput, UserPath.FeeReadOn l 8 pre post iterations finalOutput := by
  rcases exec_user_frame_on v hcode stack aligned wf lengthBound caller exec with ⟨_, _, h⟩ | ⟨i, o, empty, h⟩
  · have hd := h.dynamic
    rw [hs] at hd
    cases hd
  · exact ⟨empty, i, o, h⟩

end Blanc.Lift.BuilderRequest.Deposit
