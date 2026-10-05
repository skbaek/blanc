import Blanc.Lift.BeaconRoots.Jumps
import Blanc.Lift.BeaconRoots.Prog
import Blanc.Lift.ExactWalkSolc
import Blanc.Lift.CreationOps
import Blanc.Lift.WalkSteps
import Blanc.Lift.Vyper
import Blanc.ExecutionTraceSystemCode
import Blanc.ExecutionNoninterference
import Blanc.SystemCallForward
import Blanc.StorageRefund

namespace Blanc.Lift.BeaconRoots

open Jaune
open ExecutionTrace
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
    SFunc.RunExact fs sevm
      (St b [] M (G + 31 +
        sstoreCost sevm b (sevm.benvStat.time % (0x1fff : B256))
          sevm.benvStat.time +
      sstoreCost sevm
          (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256))
            sevm.benvStat.time)
          ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
          (Sevm.dataWord sevm 0))) t_004d_c0
      (.halted (St (afterSstore sevm
        (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
        ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256)) (Sevm.dataWord sevm 0))
        [] M (G + 1))) := by
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
    SFunc.RunExact fs sevm
      (St b [] M (G + 21 + 31 +
        sstoreCost sevm b (sevm.benvStat.time % (0x1fff : B256))
          sevm.benvStat.time +
        sstoreCost sevm
          (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256))
            sevm.benvStat.time)
            ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
            (Sevm.dataWord sevm 0))) t_0000_c0
      (.halted (St (afterSstore sevm
        (afterSstore sevm b (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
        ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256)) (Sevm.dataWord sevm 0))
        [] M (G + 1))) := by
  have hbody := body_run (fs := fs) (sevm := sevm) (b := b) (M := M)
    (G := G) hfork hstatic hsentry1 hsentry2
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

def systemMsg (benv : Benv) : Msg :=
  systemCallMsg benv beaconRootsAddress beaconRootsCode
    benv.stat.parentBeaconBlockRoot.toBytes

def systemSevm (benv : Benv) : Sevm := initSevm (systemMsg benv)

def systemBase (benv : Benv) : Devm := initDevm (systemMsg benv)

/-- The timestamp slot the SYSTEM call writes: `timestamp mod 8191`. -/
def systemKey (benv : Benv) : B256 := (systemSevm benv).benvStat.time % (0x1fff : B256)

/-- The root slot the SYSTEM call writes, `8191` slots above the timestamp slot. -/
def systemRootKey (benv : Benv) : B256 := (0x1fff : B256) + systemKey benv

/-- The parent beacon root the SYSTEM call stores. -/
def systemValue (benv : Benv) : B256 := Sevm.dataWord (systemSevm benv) 0

/-- The frame after the timestamp store. -/
def systemMid (benv : Benv) : Devm :=
  afterSstore (systemSevm benv) (systemBase benv) (systemKey benv)
    (systemSevm benv).benvStat.time

def systemCost (benv : Benv) : Nat :=
  sstoreCost (systemSevm benv) (systemBase benv) (systemKey benv)
      (systemSevm benv).benvStat.time +
    sstoreCost (systemSevm benv) (systemMid benv) (systemRootKey benv) (systemValue benv)

/-- The exact halted frame of the SYSTEM call. -/
def systemPost (benv : Benv) : Devm :=
  St (afterSstore (systemSevm benv) (systemMid benv) (systemRootKey benv) (systemValue benv))
    [] .empty (systemTransactionGas - (52 + systemCost benv) + 1)

theorem system_seed (benv : Benv) :
    (systemSevm benv).caller = systemAddress ∧
    (systemSevm benv).currentTarget = beaconRootsAddress ∧
    (systemSevm benv).isStatic = false ∧
    (systemSevm benv).code = beaconRootsCode ∧
    (systemSevm benv).depth = 1024 ∧
    (systemBase benv).stack = [] ∧
    (systemBase benv).memory = .empty ∧
    (systemBase benv).gasLeft = systemTransactionGas ∧
    (systemBase benv).refundCounter = 0 ∧
    (systemBase benv).output = [] ∧
    (systemBase benv).error = none ∧
    (systemBase benv).state = benv.state ∧
    (systemSevm benv).codeAddress = some beaconRootsAddress := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem system_exec {benv : Benv} (fork : CoveredFork benv.stat.fork) :
    exec (initEvm (systemMsg benv)) = .ok (systemPost benv) := by
  let sevm := systemSevm benv
  let base := systemBase benv
  let c₁ := sstoreCost sevm base (systemKey benv) sevm.benvStat.time
  let c₂ := sstoreCost sevm (systemMid benv) (systemRootKey benv) (systemValue benv)
  let G := systemTransactionGas - (52 + systemCost benv)
  have hcostEq : systemCost benv = c₁ + c₂ := rfl
  have hgas : systemTransactionGas = 30000000 := by rfl
  have hcost1 : c₁ ≤ 22100 := by
    dsimp only [c₁]
    have h := sstoreCost_le sevm base (systemKey benv) sevm.benvStat.time
    simp only [gasColdSload, gasStorageSet] at h
    exact h
  have hcost2 : c₂ ≤ 22100 := by
    dsimp only [c₂]
    have h := sstoreCost_le sevm (systemMid benv) (systemRootKey benv) (systemValue benv)
    simp only [gasColdSload, gasStorageSet] at h
    exact h
  have hGbound : gCallStipend < G := by
    dsimp only [G]
    rw [hgas, hcostEq]
    norm_num only [gCallStipend]
    omega
  have hrun := root_run (fs := prog) (sevm := sevm) (b := base)
    (M := .empty) (G := G) fork (system_seed benv).2.2.1
    (system_seed benv).1 (by omega) (by omega)
  have hG' : G + 21 + 31 +
      sstoreCost sevm base (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time +
      sstoreCost sevm (afterSstore sevm base (sevm.benvStat.time % (0x1fff : B256))
        sevm.benvStat.time)
        ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
        (Sevm.dataWord sevm 0) = systemTransactionGas := by
    change G + 21 + 31 + c₁ + c₂ = systemTransactionGas
    dsimp only [G]
    rw [hgas, hcostEq]
    omega
  have hrun' : SFunc.RunExact prog sevm
      (St base [] .empty systemTransactionGas) t_0000_c0 (.halted (systemPost benv)) := by
    rw [hG'] at hrun
    exact hrun
  have hexec : Nonempty (Exec 0 sevm
      (St base [] .empty systemTransactionGas) (.ok (systemPost benv))) := by
    apply lift_exact cert_check jumps_ok (system_seed benv).2.2.2.1 fork
    exact ⟨t_0000_c0, prog_root, hrun'⟩
  change Nonempty (Exec 0 sevm
    (St base [] .empty systemTransactionGas) (.ok (systemPost benv))) at hexec
  have entry : St base [] .empty systemTransactionGas = base := by
    rfl
  rw [entry] at hexec
  exact (exec_iff_exec_eq _ _ _ _).mp hexec

theorem member : (beaconRootsAddress, beaconRootsCode) ∈ systemContracts := by
  simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false]
  exact Or.inl trivial

/-- The two ring-buffer slots are distinct. -/
theorem systemKey_ne (benv : Benv) : systemKey benv ≠ systemRootKey benv := by
  intro same
  have hlt : (systemKey benv).toNat < 8191 := by
    rw [systemKey, B256.toNat_mod (by decide)]
    exact Nat.mod_lt _ (by decide)
  have hnat := congrArg B256.toNat same
  rw [systemRootKey, B256.toNat_add] at hnat
  have hconst : (0x1fff : B256).toNat = 8191 := by decide
  rw [hconst, Nat.lo_eq_of_lt (by omega)] at hnat
  omega

/-- The SYSTEM frame halts cleanly, with a non-negative refund counter, having
written exactly its two ring-buffer slots. -/
theorem systemPost_facts (benv : Benv) :
    (systemPost benv).error = none ∧
    0 ≤ (systemPost benv).refundCounter ∧
    (systemPost benv).state =
      (benv.state.setStorVal beaconRootsAddress (systemKey benv)
        (systemSevm benv).benvStat.time).setStorVal beaconRootsAddress
        (systemRootKey benv) (systemValue benv) := by
  refine ⟨?_, ?_, ?_⟩
  · change (afterSstore (systemSevm benv) (systemMid benv) _ _).error = none
    rw [afterSstore_error, systemMid, afterSstore_error]
    rfl
  · change 0 ≤ (afterSstore (systemSevm benv) (systemMid benv) _ _).refundCounter
    have first : (0 : Int) ≤ (systemMid benv).refundCounter :=
      afterSstore_refundCounter_ge_of_original_eq_current _ _ _ _ rfl
    refine first.trans (afterSstore_refundCounter_ge_of_original_eq_current _ _ _ _ ?_)
    rw [getStorVal_eq_getStor, systemMid, afterSstore_getStor_self,
      Stor.get_set_ne _ (systemKey_ne benv), ← getStorVal_eq_getStor]
    rfl
  · change (afterSstore (systemSevm benv) (systemMid benv) _ _).state = _
    rw [afterSstore_state, systemMid, afterSstore_state]
    rfl

/-- **The EIP-4788 unchecked system call** on the real installed code: it succeeds and
its state is the input state with its two ring-buffer slots written, so every other
account is untouched. -/
theorem processUncheckedSystemTransaction_beaconRoots {benv : Benv}
    (fork : CoveredFork benv.stat.fork)
    (installed : benv.state.getCode beaconRootsAddress = beaconRootsCode) :
    processUncheckedSystemTransaction benv beaconRootsAddress
        benv.stat.parentBeaconBlockRoot.toBytes =
      .ok ((systemPost benv).state, systemCallOutput (systemPost benv)) ∧
    (systemPost benv).state =
      (benv.state.setStorVal beaconRootsAddress (systemKey benv)
        (systemSevm benv).benvStat.time).setStorVal beaconRootsAddress
        (systemRootKey benv) (systemValue benv) ∧
    ∀ a, beaconRootsAddress ≠ a → (systemPost benv).state.get a = benv.state.get a := by
  have facts := systemPost_facts benv
  refine ⟨processUncheckedSystemTransaction_of_exec member fork installed (system_exec fork)
    facts.1 facts.2.1, facts.2.2, fun a different => ?_⟩
  rw [facts.2.2, State.get_setStorVal_ne _ _ _ different,
    State.get_setStorVal_ne _ _ _ different]

end Blanc.Lift.BeaconRoots
