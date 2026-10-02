import Blanc.Lift.HistoryStorage.Jumps
import Blanc.Lift.HistoryStorage.Prog
import Blanc.Lift.ExactWalkSolc
import Blanc.Lift.WalkSteps

namespace Blanc.Lift.HistoryStorage

open Jaune
open Blanc.Lift

private theorem system_push :
    Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe] =
      systemAddress.toB256 := rfl

theorem body_run {fs : List SFunc} {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hsentry : gCallStipend < G +
      sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0)) :
    ∃ post : Devm, SFunc.RunExact fs sevm
      (St b [] M (G + 22 +
        sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
          (Sevm.dataWord sevm 0))) t_0046_c0 (.halted post) := by
  refine ⟨St (afterSstore sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
      (Sevm.dataWord sevm 0)) [] M G, ?_⟩
  dsimp only [t_0046_c0]
  rw [show G + 22 +
      sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 21 + sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0)) + 1 by omega]
  rdest
  rw [show G + 21 +
      sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 19 + sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0)) + 2 by omega]
  refine rx_push0 (S := []) (by decide) ?_
  rw [show G + 19 +
      sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 16 + sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0)) + 3 by omega]
  refine rx_calldataload (S := []) (x := 0) (by decide) ?_
  rw [show G + 16 +
      sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 13 + sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0)) + 3 by omega]
  refine rx_push (S := [Sevm.dataWord sevm 0]) (x := 0x1f) (xs := [0xff])
    (w := (0x1fff : B256)) (by decide)
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  rw [show G + 13 +
      sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 10 + sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0)) + 3 by omega]
  refine rx_push (S := [(0x1fff : B256), Sevm.dataWord sevm 0])
    (x := 0x01) (xs := []) (w := 1) (by decide)
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  rw [show G + 10 +
      sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 8 + sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0)) + 2 by omega]
  refine rx_number (S := [1, (0x1fff : B256), Sevm.dataWord sevm 0])
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  rw [show G + 8 +
        sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 5 + sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0)) + 3 by omega]
  refine rx_sub (S := [(0x1fff : B256), Sevm.dataWord sevm 0])
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  rw [show G + 5 +
      sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0)) + 5 by omega]
  refine rx_mod (S := [Sevm.dataWord sevm 0]) (by rfl)
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_sstore hfork hsentry hstatic ?_
  exact Blanc.Lift.rx_stop

theorem root_run {fs : List SFunc} {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hcaller : sevm.caller = systemAddress)
    (hsentry : gCallStipend < G +
        sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0)) :
    ∃ post : Devm, SFunc.RunExact fs sevm
      (St b [] M (G + 21 + 22 +
        sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
          (Sevm.dataWord sevm 0))) t_0000_c0 (.halted post) := by
  obtain ⟨post, hbody⟩ := body_run (fs := fs) (sevm := sevm) (b := b) (M := M)
    (G := G) hfork hstatic hsentry
  refine ⟨post, ?_⟩
  dsimp only [t_0000_c0]
  rw [show G + 21 + 22 +
      sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 19 + 22 +
        sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
          (Sevm.dataWord sevm 0)) + 2 by omega]
  refine rx_caller (S := []) (by decide) ?_
  rw [show G + 19 + 22 +
        sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 16 + 22 +
        sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
          (Sevm.dataWord sevm 0)) + 3 by omega]
  refine rx_push (S := [sevm.caller.toB256]) system_push
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  rw [show G + 16 + 22 +
      sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 13 + 22 +
        sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
          (Sevm.dataWord sevm 0)) + 3 by omega]
  refine rx_eq (by rw [hcaller])
    (by decide) ?_
  rw [show G + 13 + 22 +
        sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 10 + 22 +
        sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
          (Sevm.dataWord sevm 0)) + 3 by omega]
  refine rx_push rfl (by decide) ?_
  rw [show G + 10 + 22 +
      sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 22 +
        sstoreCost sevm b ((sevm.benvStat.number.toB256 - 1) % (0x1fff : B256))
          (Sevm.dataWord sevm 0)) + 10 by omega]
  exact rx_branch_succ (by decide) hbody

end Blanc.Lift.HistoryStorage
