import Blanc.Lift.BeaconRoots.Jumps
import Blanc.Lift.BeaconRoots.Prog
import Blanc.Lift.ExactWalkSolc
import Blanc.Lift.CreationOps
import Blanc.Lift.WalkSteps
import Blanc.Lift.Vyper
import Blanc.ExecutionTraceSystemCode
import Blanc.ExecutionNoninterference

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

def systemMsg (benv : Benv) : Msg :=
  processSystemTransactionMsg benv.beginTransaction
    (processSystemTransactionTenv benv.beginTransaction)
    beaconRootsAddress benv.stat.parentBeaconBlockRoot.toBytes beaconRootsCode

def systemSevm (benv : Benv) : Sevm := initSevm (systemMsg benv)

def systemBase (benv : Benv) : Devm := initDevm (systemMsg benv)

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

theorem system_exec_exists {benv : Benv} (fork : CoveredFork benv.stat.fork) :
    ∃ post : Devm, exec (initEvm (systemMsg benv)) = .ok post := by
  let sevm := systemSevm benv
  let base := systemBase benv
  let key := sevm.benvStat.time % (0x1fff : B256)
  let key₂ := (0x1fff : B256) + key
  let b₁ := afterSstore sevm base key sevm.benvStat.time
  let c₁ := sstoreCost sevm base key sevm.benvStat.time
  let c₂ := sstoreCost sevm b₁ key₂ (Sevm.dataWord sevm 0)
  let G := systemTransactionGas - (52 + c₁ + c₂)
  have hgas : systemTransactionGas = 30000000 := by rfl
  have hcost1 : c₁ ≤ 22100 := by
    dsimp only [c₁]
    have h := sstoreCost_le sevm base key sevm.benvStat.time
    simp only [gasColdSload, gasStorageSet] at h
    exact h
  have hcost2 : c₂ ≤ 22100 := by
    dsimp only [c₂]
    have h := sstoreCost_le sevm b₁ key₂ (Sevm.dataWord sevm 0)
    simp only [gasColdSload, gasStorageSet] at h
    exact h
  have hcost : c₁ + c₂ ≤ systemTransactionGas - 52 := by
    have h1 := hcost1
    have h2 := hcost2
    rw [hgas]
    omega
  have hsum : c₁ + c₂ ≤ 44200 := by omega
  have hG : G + 52 + c₁ + c₂ = systemTransactionGas := by
    rw [hgas]
    dsimp only [G]
    omega
  have hGbound : gCallStipend < G := by
    dsimp only [G]
    rw [hgas]
    norm_num only [gCallStipend]
    omega
  obtain ⟨post, hrun⟩ := root_run (fs := prog) (sevm := sevm) (b := base)
    (M := .empty) (G := G) fork (system_seed benv).2.2.1
    (system_seed benv).1 (by omega) (by omega)
  have hG' : G + 21 + 31 +
      sstoreCost sevm base (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time +
      sstoreCost sevm (afterSstore sevm base (sevm.benvStat.time % (0x1fff : B256))
        sevm.benvStat.time)
        ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
        (Sevm.dataWord sevm 0) = systemTransactionGas := by
    dsimp only [sevm, base, key, key₂, b₁, c₁, c₂] at hG ⊢
    omega
  have hrun' : SFunc.RunExact prog sevm
      (St base [] .empty systemTransactionGas) t_0000_c0 (.halted post) := by
    rw [hG'] at hrun
    exact hrun
  have hexec : Nonempty (Exec 0 sevm
      (St base [] .empty systemTransactionGas) (.ok post)) := by
    apply lift_exact cert_check jumps_ok (system_seed benv).2.2.2.1 fork
    exact ⟨t_0000_c0, prog_root, hrun'⟩
  refine ⟨post, ?_⟩
  change exec (initEvm (systemMsg benv)) = .ok post
  change Nonempty (Exec 0 sevm
    (St base [] .empty systemTransactionGas) (.ok post)) at hexec
  have entry : St base [] .empty systemTransactionGas = base := by
    rfl
  rw [entry] at hexec
  exact (exec_iff_exec_eq _ _ _ _).mp hexec

theorem beaconRoots_trace_target_of_installed
    {benv : Benv} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv beaconRootsAddress
      benv.stat.parentBeaconBlockRoot.toBytes state out)
    (installed : SystemCodeInstalled benv.state) :
    ∀ root ∈ trace.rawFrames, root.sevm.currentTarget = beaconRootsAddress := by
  exact trace.rawFrames_target_of_installed (c := beaconRootsCode)
    (by simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false]
        exact Or.inl trivial) installed

theorem beaconRoots_no_foreign_write {benv : Benv} {pre : Devm} {out : Execution}
    {sevm : Sevm} (run : Exec 0 sevm pre out)
    (hsevm : sevm = systemSevm benv) (owner : Adr) (key : B256)
    (different : beaconRootsAddress ≠ owner) :
    Exec.NoRetainedWriteTo run owner key := by
  subst sevm
  obtain ⟨hreach, _, _⟩ := systemContracts_facts (beaconRootsAddress, beaconRootsCode)
    (by simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false]
        exact Or.inl trivial)
  apply Exec.noRetainedWriteTo_of_frame_owners_ne run
  intro root member
  have hroot := Exec.rawFrameRoots_of_reach run
    (noPushBefore_zero _ _) hreach root member
  rw [hroot]
  exact different

end Blanc.Lift.BeaconRoots
