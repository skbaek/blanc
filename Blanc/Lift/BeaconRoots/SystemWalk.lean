import Blanc.Lift.BeaconRoots.Jumps
import Blanc.Lift.BeaconRoots.Prog
import Blanc.Lift.ExactWalkSolc
import Blanc.Lift.CreationOps
import Blanc.Lift.WalkSteps

namespace Blanc.Lift.BeaconRoots

open Jaune
open Blanc.Lift

private theorem system_push :
    Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe] =
      systemAddress.toB256 := rfl

theorem body_run {fs : List SFunc} {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hsentry1 : gCallStipend < G + 15 +
      sstoreCost sevm
        (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
        ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
        (Sevm.dataWord sevm 0))
    (hsentry2 : gCallStipend < G +
      sstoreCost sevm
        (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
        ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
        (Sevm.dataWord sevm 0)) :
    ∃ post : Devm, SFunc.RunExact fs sevm
      (St b [] M (G + 31 +
        sstoreCost sevm b (sevm.benvStat.time % (0x1fff : B256))
          sevm.benvStat.time +
      sstoreCost sevm
          (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256))
            sevm.benvStat.time)
          ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
          (Sevm.dataWord sevm 0))) t_004d_c0 (.halted post) := by
  let key := sevm.benvStat.time % (0x1fff : B256)
  let key₂ := (0x1fff : B256) + key
  let b₁ := afterSstore sevm b key sevm.benvStat.time
  let post := St (afterSstore sevm b₁ key₂ (Sevm.dataWord sevm 0)) [] M (G + 1)
  refine ⟨post, ?_⟩
  dsimp only [key, key₂, b₁, post]
  rw [show G + 31 +
      sstoreCost sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time +
      sstoreCost sevm
        (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
        ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 30 +
        sstoreCost sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time +
        sstoreCost sevm
          (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
          ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
          (Sevm.dataWord sevm 0)) + 1 by omega]
  dsimp only [t_004d_c0]
  rdest
  rw [show G + 30 +
      sstoreCost sevm b (sevm.benvStat.time % (0x1fff : B256))
        sevm.benvStat.time +
      sstoreCost sevm
        (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256))
          sevm.benvStat.time)
        ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 27 +
        sstoreCost sevm b (sevm.benvStat.time % (0x1fff : B256))
          sevm.benvStat.time +
        sstoreCost sevm
          (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256))
            sevm.benvStat.time)
          ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
          (Sevm.dataWord sevm 0)) + 3 by omega]
  refine rx_push (S := []) (x := 0x00) (xs := [0x1f, 0xff]) (w := (0x1fff : B256))
    (by decide +kernel) (by decide) ?_
  rw [show G + 27 +
      sstoreCost sevm b (sevm.benvStat.time % (0x1fff : B256))
        sevm.benvStat.time +
      sstoreCost sevm
        (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256))
          sevm.benvStat.time)
        ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 25 +
        sstoreCost sevm b (sevm.benvStat.time % (0x1fff : B256))
          sevm.benvStat.time +
        sstoreCost sevm
          (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256))
            sevm.benvStat.time)
          ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
          (Sevm.dataWord sevm 0)) + 2 by omega]
  refine Blanc.Lift.rx_timestamp (S := [(0x1fff : B256)]) (by decide) ?_
  rw [show G + 25 +
      sstoreCost sevm b (sevm.benvStat.time % (0x1fff : B256))
        sevm.benvStat.time +
      sstoreCost sevm
        (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256))
          sevm.benvStat.time)
        ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 20 +
        sstoreCost sevm b (sevm.benvStat.time % (0x1fff : B256))
          sevm.benvStat.time +
        sstoreCost sevm
          (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256))
            sevm.benvStat.time)
          ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
          (Sevm.dataWord sevm 0)) + 5 by omega]
  refine rx_mod (by rfl) (by rroom) ?_
  rw [show G + 20 +
      sstoreCost sevm b (sevm.benvStat.time % (0x1fff : B256))
        sevm.benvStat.time +
      sstoreCost sevm
        (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256))
          sevm.benvStat.time)
        ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 18 +
        sstoreCost sevm b (sevm.benvStat.time % (0x1fff : B256))
          sevm.benvStat.time +
        sstoreCost sevm
          (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256))
            sevm.benvStat.time)
          ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
          (Sevm.dataWord sevm 0)) + 2 by omega]
  refine Blanc.Lift.rx_timestamp (S := [sevm.benvStat.time % (0x1fff : B256)])
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  rw [show G + 18 +
      sstoreCost sevm b (sevm.benvStat.time % (0x1fff : B256))
        sevm.benvStat.time +
      sstoreCost sevm
        (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256))
          sevm.benvStat.time)
        ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 15 +
        sstoreCost sevm b (sevm.benvStat.time % (0x1fff : B256))
          sevm.benvStat.time +
        sstoreCost sevm
          (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256))
            sevm.benvStat.time)
          ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
          (Sevm.dataWord sevm 0)) + 3 by omega]
  rdup
  rw [show G + 15 +
      sstoreCost sevm b (sevm.benvStat.time % (0x1fff : B256))
        sevm.benvStat.time +
      sstoreCost sevm
        (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256))
          sevm.benvStat.time)
        ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 15 +
        sstoreCost sevm
          (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256))
            sevm.benvStat.time)
          ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
          (Sevm.dataWord sevm 0)) +
        sstoreCost sevm b (sevm.benvStat.time % (0x1fff : B256))
          sevm.benvStat.time by omega]
  rsstoreO
  rw [show G + 15 +
      sstoreCost sevm
        (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
        ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 13 +
        sstoreCost sevm
          (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
          ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
          (Sevm.dataWord sevm 0)) + 2 by omega]
  refine rx_push0 (fs := fs) (sevm := sevm)
    (b := afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
    (M := M)
    (G := G + 13 + sstoreCost sevm
      (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
      ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
      (Sevm.dataWord sevm 0))
    (S := [sevm.benvStat.time % (0x1fff : B256)])
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  rw [show G + 13 +
      sstoreCost sevm
        (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
        ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 10 +
        sstoreCost sevm
          (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
          ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
          (Sevm.dataWord sevm 0)) + 3 by omega]
  refine rx_calldataload (fs := fs) (sevm := sevm)
    (b := afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
    (M := M)
    (G := G + 10 + sstoreCost sevm
      (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
      ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
      (Sevm.dataWord sevm 0))
    (S := [sevm.benvStat.time % (0x1fff : B256)]) (x := 0)
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  rw [show G + 10 +
      sstoreCost sevm
        (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
        ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 7 +
        sstoreCost sevm
          (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
          ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
          (Sevm.dataWord sevm 0)) + 3 by omega]
  refine rx_swap1 (fs := fs) (sevm := sevm)
    (b := afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
    (M := M)
    (G := G + 7 + sstoreCost sevm
      (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
      ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
      (Sevm.dataWord sevm 0))
    (S := []) (x := Sevm.dataWord sevm 0)
    (y := sevm.benvStat.time % (0x1fff : B256)) ?_
  rw [show G + 7 +
      sstoreCost sevm
        (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
        ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 4 +
        sstoreCost sevm
          (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
          ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
          (Sevm.dataWord sevm 0)) + 3 by omega]
  refine rx_push (fs := fs) (sevm := sevm)
    (b := afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
    (M := M)
    (G := G + 4 + sstoreCost sevm
      (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
      ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
      (Sevm.dataWord sevm 0))
    (S := [sevm.benvStat.time % (0x1fff : B256), Sevm.dataWord sevm 0])
    (x := 0x00) (xs := [0x1f, 0xff]) (w := (0x1fff : B256))
    (by decide)
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  rw [show G + 4 +
      sstoreCost sevm
        (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
        ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 1 +
        sstoreCost sevm
          (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
          ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
          (Sevm.dataWord sevm 0)) + 3 by omega]
  refine rx_add (fs := fs) (sevm := sevm)
    (b := afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
    (M := M)
    (G := G + 1 + sstoreCost sevm
      (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
      ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
      (Sevm.dataWord sevm 0))
    (S := [Sevm.dataWord sevm 0]) (x := (0x1fff : B256))
    (y := sevm.benvStat.time % (0x1fff : B256))
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  rsstoreO
  exact Blanc.Lift.rx_stop

theorem root_run {fs : List SFunc} {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hcaller : sevm.caller = systemAddress)
    (hsentry1 : gCallStipend < G + 15 +
      sstoreCost sevm
        (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
        ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
        (Sevm.dataWord sevm 0))
    (hsentry2 : gCallStipend < G +
      sstoreCost sevm
        (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
        ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
        (Sevm.dataWord sevm 0)) :
    ∃ post : Devm, SFunc.RunExact fs sevm
      (St b [] M (G + 21 + 31 +
        sstoreCost sevm b (sevm.benvStat.time % (0x1fff : B256))
          sevm.benvStat.time +
        sstoreCost sevm
          (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256))
            sevm.benvStat.time)
            ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
            (Sevm.dataWord sevm 0))) t_0000_c0 (.halted post) := by
  obtain ⟨post, hbody⟩ := body_run (fs := fs) (sevm := sevm) (b := b) (M := M)
    (G := G) hfork hstatic hsentry1 hsentry2
  refine ⟨post, ?_⟩
  dsimp only [t_0000_c0]
  rw [show G + 21 + 31 +
      sstoreCost sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time +
      sstoreCost sevm
        (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
        ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 19 + 31 +
        sstoreCost sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time +
        sstoreCost sevm
          (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
          ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
          (Sevm.dataWord sevm 0)) + 2 by omega]
  refine rx_caller (S := []) (by decide) ?_
  rw [show G + 19 + 31 +
      sstoreCost sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time +
      sstoreCost sevm
        (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
        ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 16 + 31 +
        sstoreCost sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time +
        sstoreCost sevm
          (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
          ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
          (Sevm.dataWord sevm 0)) + 3 by omega]
  refine rx_push (S := [sevm.caller.toB256]) system_push
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  rw [show G + 16 + 31 +
      sstoreCost sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time +
      sstoreCost sevm
        (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
        ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 13 + 31 +
        sstoreCost sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time +
        sstoreCost sevm
          (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
          ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
          (Sevm.dataWord sevm 0)) + 3 by omega]
  refine rx_eq (S := [])
    (x := systemAddress.toB256) (y := sevm.caller.toB256) (v := 1)
    (by rw [hcaller]; simp only [B256.eqCheck, ite_true])
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  rw [show G + 13 + 31 +
      sstoreCost sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time +
      sstoreCost sevm
        (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
        ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 10 + 31 +
        sstoreCost sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time +
        sstoreCost sevm
          (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
          ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
          (Sevm.dataWord sevm 0)) + 3 by omega]
  refine rx_push rfl (by decide) ?_
  rw [show G + 10 + 31 +
      sstoreCost sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time +
      sstoreCost sevm
        (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
        ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
        (Sevm.dataWord sevm 0) =
      (G + 31 +
        sstoreCost sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time +
        sstoreCost sevm
          (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
          ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
          (Sevm.dataWord sevm 0)) + 10 by omega]
  exact rx_branch_succ (by decide) hbody

end Blanc.Lift.BeaconRoots
