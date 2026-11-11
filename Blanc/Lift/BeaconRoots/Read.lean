import Blanc.Lift.SystemExecution.BeaconRoots.SystemWalk
import Blanc.Lift.AccumulatedWalk
import Blanc.Lift.WalkKit
import Blanc.Lift.RequestSystem.PathInv

namespace Blanc.Lift.BeaconRoots

open Jaune Blanc.Lift AccumulatedWalk
open Blanc.Lift.SystemExecution.BeaconRoots

/-- The two storage-read successors of the ordinary path. -/
def readBase (sevm : Sevm) (b : Devm) : Devm :=
  afterSload sevm (afterSload sevm b (Sevm.dataWord sevm 0 % (0x1fff : B256)))
    ((0x1fff : B256) + Sevm.dataWord sevm 0 % (0x1fff : B256))

def readWord (sevm : Sevm) (b : Devm) : B256 :=
  b.getStorVal sevm.currentTarget ((0x1fff : B256) + Sevm.dataWord sevm 0 % (0x1fff : B256))

def readPost (sevm : Sevm) (b : Devm) (G : Nat) : Devm :=
  chargedRetPost (readBase sevm b) [] (Mem.empty.write 0 (readWord sevm b).toBytes) G 0 32

/-- The accepted read path is walked at its actual warm/cold storage charges. -/
theorem read_path {sevm : Sevm} {b : Devm} (G : Nat)
    (fork : CoveredFork sevm.benvStat.fork) (length : sevm.data.length = 32)
    (nonzero : Sevm.dataWord sevm 0 ≠ 0)
    (tag : b.getStorVal sevm.currentTarget (Sevm.dataWord sevm 0 % (0x1fff : B256)) = Sevm.dataWord sevm 0) :
    SFunc.RunExact cert.prog sevm (St b [] .empty
      (G + sloadCost sevm (afterSload sevm b (Sevm.dataWord sevm 0 % (0x1fff : B256)))
          ((0x1fff : B256) + Sevm.dataWord sevm 0 % (0x1fff : B256)) +
        sloadCost sevm b (Sevm.dataWord sevm 0 % (0x1fff : B256)) + 99))
      t_001a_c0 (.halted (readPost sevm b G)) := by
  wrun!
  simp only [length, B256.eqCheck]
  apply rx_branch_succ (by decide)
  refine rx_dest ?_
  refine rx_push0 (CoveredFork.rules_push0 fork) (by wroom) ?_
  wrun!
  simp only [B256.eqCheck, ite_eq_right nonzero]
  apply rx_branch_zero
  wrun!
  rw [Nat.add_right_comm (G + _) _ 36]
  refine rx_sload_sel fork.shanghaiOnwards (by wroom) ?_
  wrun!
  simp only [tag, B256.eqCheck, ite_true]
  apply rx_branch_succ (by decide)
  wrun!
  rw [Nat.add_right_comm G _ 13]
  refine rx_sload_sel fork.shanghaiOnwards (by wroom) ?_
  refine rx_push0 (CoveredFork.rules_push0 fork) (by wroom) ?_
  rw [afterSload_getStorVal]
  refine rx_mstore (c := 6) (by rw [St.extCost_eq (n := 0) rfl]; rfl) rfl ?_
  wrun! 1
  refine rx_push0 (CoveredFork.rules_push0 fork) (by wroom) ?_
  have hext : chargedRetExt (Mem.empty.write 0 (readWord sevm b).toBytes) 0 32 = 0 := by
    unfold chargedRetExt
    rw [Mem.size_write_word_at]
    rfl
  have h := rx_return_charged (fs := cert.prog) (sevm := sevm) (b := readBase sevm b)
    (S := []) (M := Mem.empty.write 0 (readWord sevm b).toBytes) (G := G) (i := 0) (sz := 32)
  rw [hext, Nat.add_zero] at h
  exact h

/-- The read path plus the actual caller dispatcher has exactly 120 non-storage gas. -/
theorem exec_read_exact {sevm : Sevm} {b : Devm} (G : Nat)
    (code : sevm.code = beaconRootsCode) (fork : CoveredFork sevm.benvStat.fork)
    (caller : sevm.caller ≠ systemAddress) (length : sevm.data.length = 32)
    (nonzero : Sevm.dataWord sevm 0 ≠ 0)
    (tag : b.getStorVal sevm.currentTarget (Sevm.dataWord sevm 0 % (0x1fff : B256)) = Sevm.dataWord sevm 0) :
    Nonempty (Exec 0 sevm (St b [] .empty
      (G + sloadCost sevm (afterSload sevm b (Sevm.dataWord sevm 0 % (0x1fff : B256)))
          ((0x1fff : B256) + Sevm.dataWord sevm 0 % (0x1fff : B256)) +
        sloadCost sevm b (Sevm.dataWord sevm 0 % (0x1fff : B256)) + 120)) (.ok (readPost sevm b G))) := by
  exact RequestFee.exec_of_dispatch_user cert_check jumps_ok (progNoExec_of_all (by decide +kernel))
    (dest := ⟨0x4d, [], by decide⟩) (user := t_001a_c0) (system := t_004d_c0) rfl code caller
      (read_path G fork length nonzero tag)

/-- The two read keys are different, so loading the tag does not warm the root key. -/
theorem read_keys_ne (t : B256) : t % (0x1fff : B256) ≠ (0x1fff : B256) + t % (0x1fff : B256) := by
  intro same
  have hlt : (t % (0x1fff : B256)).toNat < 8191 := by
    rw [B256.toNat_mod (by decide)]
    exact Nat.mod_lt _ (by decide)
  have hnat := congrArg B256.toNat same
  rw [B256.toNat_add] at hnat
  have hconst : (0x1fff : B256).toNat = 8191 := by decide
  rw [hconst, Nat.lo_eq_of_lt (by omega)] at hnat
  omega

end Blanc.Lift.BeaconRoots
