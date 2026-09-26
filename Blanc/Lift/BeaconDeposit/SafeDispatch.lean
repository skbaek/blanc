import Blanc.Lift.BeaconDeposit.BodySpec

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
  sorry

end Blanc.Lift.BeaconDeposit
