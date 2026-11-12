import Blanc.Lift.BeaconDeposit.BodySpec
import Blanc.Lift.InvWalkWorld
import Blanc.Lift.WalkInvKit

/-!
# Safety segment D: the dispatcher, inverted

A successful run of the dispatcher (entry 0) from the frame's start enters one of the four
wrappers with the selector on the stack and `mem0` in memory, the base untouched; it enters the
`deposit` wrapper (entry 32) exactly when the selector is `deposit`'s.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

private theorem safe_dispatch_core {sevm : Sevm} {b post : Devm} {G : Nat}
    (run : SFunc.Run prog sevm (St b [] Mem.empty G) t_0000_c0 (.halted post)) :
    4 ≤ sevm.data.length.toB256.toNat ∧
    ∃ k G' g, k ∈ [31, 32, 33, 34] ∧
      (k = 31 ↔ Sevm.selector sevm = BeaconDeposit.supportsInterfaceSelector) ∧
      (k = 32 ↔ Sevm.selector sevm = BeaconDeposit.depositSelector) ∧
      (k = 33 ↔ Sevm.selector sevm = BeaconDeposit.getDepositCountSelector) ∧
      (k = 34 ↔ Sevm.selector sevm = BeaconDeposit.getDepositRootSelector) ∧
      prog[k]? = some g ∧
      SFunc.Run prog sevm (St b [Sevm.selector sevm] mem0 G') g (.halted post) := by
  have eq_of_ne : ∀ {x y : B256}, B256.eqCheck x y ≠ 0 → x = y := by
    intro x y h
    unfold B256.eqCheck at h
    split at h
    · assumption
    · exact absurd rfl h
  have ne_of_eq : ∀ {x y : B256}, B256.eqCheck x y = 0 → x ≠ y := by
    intro x y h hxy
    simp only [B256.eqCheck, hxy, ite_true] at h
    exact absurd h (by decide)
  have hsup : BeaconDeposit.supportsInterfaceSelector = Bytes.toB256 [0x01, 0xff, 0xc9, 0xa7] := by
    rw [show BeaconDeposit.supportsInterfaceSelector = (0x01ffc9a7 : B256) by decide +kernel]; decide
  have hdep : BeaconDeposit.depositSelector = Bytes.toB256 [0x22, 0x89, 0x51, 0x18] := by
    rw [BeaconDeposit.depositSelector_eq]; decide
  have hcnt : BeaconDeposit.getDepositCountSelector = Bytes.toB256 [0x62, 0x1f, 0xd1, 0x30] := by
    rw [BeaconDeposit.getDepositCountSelector_eq]; decide
  have hrot : BeaconDeposit.getDepositRootSelector = Bytes.toB256 [0xc5, 0xf2, 0x89, 0x2f] := by
    rw [BeaconDeposit.getDepositRootSelector_eq]; decide
  have hsel : Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Sevm.selector sevm := by
    rw [show Bytes.toB256 [0x00] = 0 by decide, show (Bytes.toB256 [0xe0]).toNat = 224 by decide]
    rfl
  have hm : Mem.empty.write (Bytes.toB256 [0x40]).toNat (Bytes.toB256 [0x80]).toBytes = mem0 :=
    rfl
  have run := run.cut
  -- t_0000_c0: the free pointer and the `CALLDATASIZE < 4` test
  unfold t_0000_c0 at run
  winv 7
  rcases ric_branch run with ⟨hw4, G8, run⟩ | ⟨-, G8, run⟩
  swap; · exact (run.false_of_noOk (by decide)).elim
  have hcds4 : 4 ≤ sevm.data.length.toB256.toNat := by
    have hge := toNat_ge_of_ltCheck_eq_zero hw4
    simpa only [show (Bytes.toB256 [0x04] : B256).toNat = 4 by decide] using hge
  refine ⟨hcds4, ?_⟩
  rw [hm] at run
  -- t_000d_c0: the selector and the first comparison
  unfold t_000d_c0 at run
  winv 4
  rw [hsel] at run
  winv 4
  obtain ⟨g31, hg31⟩ : ∃ g, prog[31]? = some g := ⟨_, rfl⟩
  rcases ric_branchTo (by simp only [List.not_mem_nil, not_false_eq_true]) hg31 run with ⟨hw, G17, run⟩ | ⟨hw, G17, run⟩
  swap
  · have h31_eq : Sevm.selector sevm = Bytes.toB256 [0x01, 0xff, 0xc9, 0xa7] := (eq_of_ne hw).symm
    refine ⟨31, G17, g31,
      by simp only [List.mem_cons, Nat.reduceEqDiff, List.not_mem_nil, or_self, or_false],
      ⟨fun _ => h31_eq.trans hsup.symm, fun _ => rfl⟩,
      ⟨fun h => absurd h (by decide), fun h => absurd (h31_eq.symm.trans (h.trans hdep)) (by decide)⟩,
      ⟨fun h => absurd h (by decide), fun h => absurd (h31_eq.symm.trans (h.trans hcnt)) (by decide)⟩,
      ⟨fun h => absurd h (by decide), fun h => absurd (h31_eq.symm.trans (h.trans hrot)) (by decide)⟩,
      hg31, run.uncut⟩
  have h31 := ne_of_eq hw
  -- t_001e_c0: `deposit`
  unfold t_001e_c0 at run
  winv 4
  obtain ⟨g32, hg32⟩ : ∃ g, prog[32]? = some g := ⟨_, rfl⟩
  rcases ric_branchTo (by simp only [List.not_mem_nil, not_false_eq_true]) hg32 run with ⟨hw, G22, run⟩ | ⟨hw, G22, run⟩
  swap
  · have h32_eq : Sevm.selector sevm = Bytes.toB256 [0x22, 0x89, 0x51, 0x18] := (eq_of_ne hw).symm
    refine ⟨32, G22, g32,
      by simp only [List.mem_cons, Nat.succ_ne_self, Nat.reduceEqDiff, List.not_mem_nil, or_self, or_false, or_true],
      ⟨fun h => absurd h (by decide), fun h => absurd (h32_eq.symm.trans (h.trans hsup)) (by decide)⟩,
      ⟨fun _ => h32_eq.trans hdep.symm, fun _ => rfl⟩,
      ⟨fun h => absurd h (by decide), fun h => absurd (h32_eq.symm.trans (h.trans hcnt)) (by decide)⟩,
      ⟨fun h => absurd h (by decide), fun h => absurd (h32_eq.symm.trans (h.trans hrot)) (by decide)⟩,
      hg32, run.uncut⟩
  have h32 := ne_of_eq hw
  -- t_0029_c0: `get_deposit_count`
  unfold t_0029_c0 at run
  winv 4
  obtain ⟨g33, hg33⟩ : ∃ g, prog[33]? = some g := ⟨_, rfl⟩
  rcases ric_branchTo (by simp only [List.not_mem_nil, not_false_eq_true]) hg33 run with ⟨hw, G27, run⟩ | ⟨hw, G27, run⟩
  swap
  · have h33_eq : Sevm.selector sevm = Bytes.toB256 [0x62, 0x1f, 0xd1, 0x30] := (eq_of_ne hw).symm
    refine ⟨33, G27, g33,
      by simp only [List.mem_cons, Nat.reduceEqDiff, Nat.succ_ne_self, List.not_mem_nil, or_self, or_false, or_true],
      ⟨fun h => absurd h (by decide), fun h => absurd (h33_eq.symm.trans (h.trans hsup)) (by decide)⟩,
      ⟨fun h => absurd h (by decide), fun h => absurd (h33_eq.symm.trans (h.trans hdep)) (by decide)⟩,
      ⟨fun _ => h33_eq.trans hcnt.symm, fun _ => rfl⟩,
      ⟨fun h => absurd h (by decide), fun h => absurd (h33_eq.symm.trans (h.trans hrot)) (by decide)⟩,
      hg33, run.uncut⟩
  have h33 := ne_of_eq hw
  -- t_0034_c0: `get_deposit_root`, and the miss
  unfold t_0034_c0 at run
  winv 4
  obtain ⟨g34, hg34⟩ : ∃ g, prog[34]? = some g := ⟨_, rfl⟩
  rcases ric_branchTo (by simp only [List.not_mem_nil, not_false_eq_true]) hg34 run with ⟨-, G32, run⟩ | ⟨hw, G32, run⟩
  · exact (run.false_of_noOk (by decide)).elim
  · have h34_eq : Sevm.selector sevm = Bytes.toB256 [0xc5, 0xf2, 0x89, 0x2f] := (eq_of_ne hw).symm
    refine ⟨34, G32, g34,
      by simp only [List.mem_cons, Nat.reduceEqDiff, Nat.succ_ne_self, List.not_mem_nil, or_false, or_true],
      ⟨fun h => absurd h (by decide), fun h => absurd (h34_eq.symm.trans (h.trans hsup)) (by decide)⟩,
      ⟨fun h => absurd h (by decide), fun h => absurd (h34_eq.symm.trans (h.trans hdep)) (by decide)⟩,
      ⟨fun h => absurd h (by decide), fun h => absurd (h34_eq.symm.trans (h.trans hcnt)) (by decide)⟩,
      ⟨fun _ => h34_eq.trans hrot.symm, fun _ => rfl⟩,
      hg34, run.uncut⟩

/-- Every successful dispatcher entry passes the `CALLDATASIZE < 4` guard. -/
theorem safe_dispatch_cds {sevm : Sevm} {b post : Devm} {G : Nat}
    (run : SFunc.Run prog sevm (St b [] Mem.empty G) t_0000_c0 (.halted post)) :
    4 ≤ sevm.data.length.toB256.toNat :=
  (safe_dispatch_core run).1

/-- Full four-selector dispatcher inversion. -/
theorem safe_dispatch_full {sevm : Sevm} {b post : Devm} {G : Nat}
    (run : SFunc.Run prog sevm (St b [] Mem.empty G) t_0000_c0 (.halted post)) :
    ∃ k G' g, k ∈ [31, 32, 33, 34] ∧
      (k = 31 ↔ Sevm.selector sevm = BeaconDeposit.supportsInterfaceSelector) ∧
      (k = 32 ↔ Sevm.selector sevm = BeaconDeposit.depositSelector) ∧
      (k = 33 ↔ Sevm.selector sevm = BeaconDeposit.getDepositCountSelector) ∧
      (k = 34 ↔ Sevm.selector sevm = BeaconDeposit.getDepositRootSelector) ∧
      prog[k]? = some g ∧
      SFunc.Run prog sevm (St b [Sevm.selector sevm] mem0 G') g (.halted post) :=
  (safe_dispatch_core run).2

-- SEGMENT: safeDispatch
/-- **Dispatcher inversion (`t_0000_c0`, about 25 nodes).**

Proof sketch.  `cases` on the run through `t_0000_c0`, `t_000d_c0`, `t_001e_c0`, `t_0029_c0`,
`t_0034_c0`: each `.next` step is a `Ninst.Run` (`push`, `mstore` giving `mem0` from
`Mem.empty`, `calldatasize`, `lt`, `calldataload`, `shr`, `dup`, `eq`) inverted with the stack
lemmas the WETH9 and port walks use (`of_run_push`, `prefix_of_*`, `Ninst.Hinv`), which also show
the non-machine fields unchanged, so each intermediate state is `St b S M G'`; each `JUMPI` is
`.zero`/`.succ` or `.toZero`/`.toSucc`, with the condition word fixing the branch.  The
`CALLDATASIZE < 4` arm and the last miss end in `t_003f_c0` (`PUSH 0 DUP REVERT`), which has no
successful `Linst.Run`.  The selectors `0x01ffc9a7`, `0x22895118`, `0x621fd130`, `0xc5f2892f` are
distinct (`decide`), which gives the `k = 32 ↔ …` clause. -/
theorem safe_dispatch {sevm : Sevm} {b post : Devm} {G : Nat}
    (run : SFunc.Run prog sevm (St b [] Mem.empty G) t_0000_c0 (.halted post)) :
    ∃ k G' g, k ∈ [31, 32, 33, 34] ∧
      (k = 32 ↔ Sevm.selector sevm = BeaconDeposit.depositSelector) ∧ prog[k]? = some g ∧
      SFunc.Run prog sevm (St b [Sevm.selector sevm] mem0 G') g (.halted post) := by
  obtain ⟨k, G', g, hk, -, hk32, -, -, hg, hrun⟩ := safe_dispatch_full run
  exact ⟨k, G', g, hk, hk32, hg, hrun⟩

end Blanc.Lift.BeaconDeposit
