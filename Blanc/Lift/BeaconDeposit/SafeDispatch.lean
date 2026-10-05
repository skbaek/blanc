import Blanc.Lift.BeaconDeposit.BodySpec
import Blanc.Lift.InvWalkWorld

/-!
# Safety segment D: the dispatcher, inverted

A successful run of the dispatcher (entry 0) from the frame's start enters one of the four
wrappers with the selector on the stack and `mem0` in memory, the base untouched; it enters the
`deposit` wrapper (entry 32) exactly when the selector is `deposit`'s.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

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
  have hdep : BeaconDeposit.depositSelector = Bytes.toB256 [0x22, 0x89, 0x51, 0x18] := by
    rw [BeaconDeposit.depositSelector_eq]; decide
  have hsel : Sevm.dataWord sevm (Bytes.toB256 [0x00]) >>> (Bytes.toB256 [0xe0]).toNat =
      Sevm.selector sevm := by
    rw [show Bytes.toB256 [0x00] = 0 by decide, show (Bytes.toB256 [0xe0]).toNat = 224 by decide]
    rfl
  have hm : Mem.empty.write (Bytes.toB256 [0x40]).toNat (Bytes.toB256 [0x80]).toBytes = mem0 :=
    rfl
  have run := run.cut
  -- t_0000_c0: the free pointer and the `CALLDATASIZE < 4` test
  unfold t_0000_c0 at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_calldatasize s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_lt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G8, run⟩ | ⟨-, G8, run⟩
  swap; · exact (run.false_of_noOk (by decide)).elim
  rw [hm] at run
  -- t_000d_c0: the selector and the first comparison
  unfold t_000d_c0 at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_calldataload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_shr s1
  rw [hsel] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G13, rfl⟩ := ri_dup (w := Sevm.selector sevm) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_eq s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_push s1
  obtain ⟨g31, hg31⟩ : ∃ g, prog[31]? = some g := ⟨_, rfl⟩
  rcases ric_branchTo (by simp only [List.not_mem_nil, not_false_eq_true]) hg31 run with ⟨hw, G17, run⟩ | ⟨hw, G17, run⟩
  swap
  · refine ⟨31, G17, g31, by simp only [List.mem_cons, Nat.reduceEqDiff, List.not_mem_nil,
    or_self, or_false], ⟨fun h => absurd h (by decide), fun h => ?_⟩, hg31, run.uncut⟩
    rw [hdep, ← eq_of_ne hw] at h
    exact absurd h (by decide)
  have h31 := ne_of_eq hw
  -- t_001e_c0: `deposit`
  unfold t_001e_c0 at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G18, rfl⟩ := ri_dup (w := Sevm.selector sevm) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G19, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_eq s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_push s1
  obtain ⟨g32, hg32⟩ : ∃ g, prog[32]? = some g := ⟨_, rfl⟩
  rcases ric_branchTo (by simp only [List.not_mem_nil, not_false_eq_true]) hg32 run with ⟨hw, G22, run⟩ | ⟨hw, G22, run⟩
  swap
  · refine ⟨32, G22, g32, by simp only [List.mem_cons, Nat.succ_ne_self, Nat.reduceEqDiff,
    List.not_mem_nil, or_self, or_false, or_true], ⟨fun _ => ?_, fun _ => rfl⟩, hg32, run.uncut⟩
    rw [hdep, ← eq_of_ne hw]
  have h32 := ne_of_eq hw
  -- t_0029_c0: `get_deposit_count`
  unfold t_0029_c0 at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G23, rfl⟩ := ri_dup (w := Sevm.selector sevm) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G24, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G25, rfl⟩ := ri_eq s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G26, rfl⟩ := ri_push s1
  obtain ⟨g33, hg33⟩ : ∃ g, prog[33]? = some g := ⟨_, rfl⟩
  rcases ric_branchTo (by simp only [List.not_mem_nil, not_false_eq_true]) hg33 run with ⟨hw, G27, run⟩ | ⟨hw, G27, run⟩
  swap
  · refine ⟨33, G27, g33, by simp only [List.mem_cons, Nat.reduceEqDiff, Nat.succ_ne_self,
    List.not_mem_nil, or_self, or_false, or_true], ⟨fun h => absurd h (by decide), fun h => ?_⟩, hg33, run.uncut⟩
    rw [hdep] at h
    exact absurd h.symm h32
  -- t_0034_c0: `get_deposit_root`, and the miss
  unfold t_0034_c0 at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G28, rfl⟩ := ri_dup (w := Sevm.selector sevm) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G29, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G30, rfl⟩ := ri_eq s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G31, rfl⟩ := ri_push s1
  obtain ⟨g34, hg34⟩ : ∃ g, prog[34]? = some g := ⟨_, rfl⟩
  rcases ric_branchTo (by simp only [List.not_mem_nil, not_false_eq_true]) hg34 run with ⟨-, G32, run⟩ | ⟨hw, G32, run⟩
  · exact (run.false_of_noOk (by decide)).elim
  · refine ⟨34, G32, g34, by simp only [List.mem_cons, Nat.reduceEqDiff, Nat.succ_ne_self,
    List.not_mem_nil, or_false, or_true], ⟨fun h => absurd h (by decide), fun h => ?_⟩, hg34, run.uncut⟩
    rw [hdep] at h
    exact absurd h.symm h32

end Blanc.Lift.BeaconDeposit
