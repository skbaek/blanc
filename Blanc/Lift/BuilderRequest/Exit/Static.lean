import Blanc.Lift.BuilderRequest.Static
import Blanc.Lift.BuilderRequest.Exit.Revert

/-!
# The exit contract in a static frame, under Amsterdam

Frame level only: see `BuilderRequest/Static.lean`.
-/

namespace Blanc.Lift.BuilderRequest.Exit

open Jaune
open RequestFee (selected)

/-- The guard, then the count bump up to its `SSTORE`, at byte 0xad. -/
def staticCut : SFunc :=
  .dest (.next (.reg .callvalue) (.next (.reg .lt) (.next (.push [0x01, 0xc6] (by decide))
    (.branch countBumpCut .undefined))))

theorem sstore_at : Ninst.At code 0xad (.reg .sstore) := by unfold Ninst.At; kernel_rfl

theorem static_cut : userPath.Cut .undefined staticCut cutEntries 0xad := ⟨by decide +kernel, by decide +kernel⟩

variable {s : Sevm} {b : Devm} {n : Nat} {out : B256}

/-- **A submission in a static frame fails at its first `SSTORE`.** 48 bytes of calldata, slot 0 off the inhibitor and value covering the
quote: the frame passes the fee path and the guard, reads the count, and halts with `writeInStaticContext`, from the frame's start, having taken a
charge `X` of regular gas from `gasLeft`; any gas above that reaches the failure. Frame level. -/
theorem frame_static_submission (hcode : s.code = code) (hfork : s.benvStat.fork = .amsterdam)
    (caller : s.caller ≠ systemAddress) (hlen : s.data.length = 48) (hs : s.isStatic = true)
    (off : b.getStorVal s.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 2 s b) 17 1 17 0 n out)
    (cov : (out / (17 : B256)).toNat ≤ s.value.toNat) :
    ∃ X, X ≤ revertBound n + 12 + gasColdSload ∧ ∀ G, ∃ raw, Nonempty (Exec 0 s (St b [] .empty (G + X)) (.error (.halt (.writeInStaticContext .none), raw))) := by
  have word : s.data.length.toB256 = userPath.shape.len.word := by rw [hlen]; rfl
  have notLow : ¬ s.value < out / (17 : B256) := by
    rw [B256.lt_iff_toNat_lt_toNat]
    exact Nat.not_lt_of_ge cov
  generalize hbase : (amsterdamSteps s).feeBase b = base
  refine ⟨countBumpGas s base + 19 + (amsterdamSteps s).feePathGas b n + RequestSystem.dispatchGas, ?_, fun G => ?_⟩
  · have h1 := countBumpGas_le s base
    have h2 := UserPath.feePath_charge_le s b n 19 (by omega)
    omega
  have hat : Ninst.At s.code 0xad (.reg .sstore) := by rw [hcode]; exact sstore_at
  obtain ⟨raw, hraw⟩ := exec_sstore_static (b := afterSloadA s base 1) (S := []) (M := .empty) (G := G) (k := 1)
    (v := 1 + base.getStorVal s.currentTarget 1) hfork hs hat
  refine ⟨raw, ?_⟩
  have htail : SFunc.RunExact (userPath.cutProg .undefined staticCut) s
      (St base [out / (17 : B256)] .empty (G + countBumpGas s base + 19))
      (selected s userPath.shape.len.word .undefined staticCut)
      (.halted (St (afterSloadA s base 1) [1, 1 + base.getStorVal s.currentTarget 1] .empty G)) := by
    simp only [selected]
    rw [ite_eq_left word]
    have hgas : G + countBumpGas s base + 19 = (G + countBumpGas s base) + 10 + 3 + 3 + 2 + 1 := by omega
    rw [hgas]
    unfold staticCut
    refine rx_dest ?_
    refine rx_callvalue (by change 1 < 1024; decide) ?_
    refine rx_lt (v := 0) ?_ (by change 0 < 1024; decide) ?_
    · simp only [B256.ltCheck, ite_eq_right notLow]
    refine rx_push rfl (by change 1 < 1024; decide) ?_
    exact rx_branch_zero (countBump_exact hfork)
  subst hbase
  have := UserPath.exec_of_arm (k := userPath) rfl rfl static_cut hcode hfork caller off wordRun htail hraw
  have hg : G + (countBumpGas s ((amsterdamSteps s).feeBase b) + 19 + (amsterdamSteps s).feePathGas b n + RequestSystem.dispatchGas) =
      G + countBumpGas s ((amsterdamSteps s).feeBase b) + 19 + (amsterdamSteps s).feePathGas b n + RequestSystem.dispatchGas := by
    simp only [Nat.add_assoc]
  rw [hg]
  exact this

variable {pre post : Devm} {l : StorageSteps s}

/-- **A successful frame in a static context is a fee read.** On any fork's steps: a submission's law has `isStatic = false`. Frame level. -/
theorem static_frame_is_read (v : l.Valid) (hcode : s.code = code) (stack : pre.stack = [])
    (aligned : pre.memory.size % 32 = 0) (wf : Mem.Wf pre.memory) (lengthBound : s.data.length < 2 ^ 256)
    (caller : s.caller ≠ systemAddress) (hs : s.isStatic = true) (exec : Exec 0 s pre (.ok post)) :
    s.data = [] ∧ ∃ iterations finalOutput, UserPath.FeeReadOn l 2 pre post iterations finalOutput := by
  rcases exec_user_frame_on v hcode stack aligned wf lengthBound caller exec with ⟨_, _, h⟩ | ⟨i, o, empty, h⟩
  · have hd := h.dynamic
    rw [hs] at hd
    cases hd
  · exact ⟨empty, i, o, h⟩

end Blanc.Lift.BuilderRequest.Exit
