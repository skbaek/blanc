import Blanc.Lift.Usdc.RefineAdminBodies
import Blanc.Lift.Usdc.RefineAdminBodiesMint
import Blanc.Lift.Usdc.RefineAdminDispatch

/-!
# The admin calls from the implementation's entry (U6f)

`*_run`: a halting run of the implementation certificate from entry `0` whose selector is an admin
call passed that call's guards and leaves the proxy's storage at its writes.
-/

namespace Blanc.Lift.Usdc.Impl

open Jaune Blanc Blanc.Lift

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {r : Seg}

/-- **`pause` from the implementation's entry**: the guards it passed and its storage effect. -/
theorem pause_run (hfork : CoveredFork sevm.benvStat.fork) {D : Devm}
    (hsel : Blanc.Sevm.selector sevm = 0x8456cb59)
    (run : SFunc.RunCut cert.prog sevm [] (St b S M G) t_0000_c0 (.done (.halted D))) :
      sevm.caller.toB256 =? (ff20 &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [1])) ≠ 0 ∧
      D.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set (Bytes.toB256 [1]) (Bytes.toB256 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ||| Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 0, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [1])) := by
  obtain ⟨_, _, _, run⟩ := dispatch_pause hsel run
  unfold t_0a4b_c150 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_callRet (E := [42]) (g := t_2b3c_c42) (by decide) (by decide) rfl run; obtain ⟨_, D, callee, run⟩ := run
  obtain ⟨_, _, _, rfl, f1, hs⟩ := pause_body hfork callee
  unfold t_0489_c150 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  -- LAST .stop
  obtain rfl := Outcome.halted.inj (Seg.done.inj (ric_stop run))
  exact ⟨f1, hs⟩

/-- **`unpause` from the implementation's entry**: the guards it passed and its storage effect. -/
theorem unpause_run (hfork : CoveredFork sevm.benvStat.fork) {D : Devm}
    (hsel : Blanc.Sevm.selector sevm = 0x3f4ba83a)
    (run : SFunc.RunCut cert.prog sevm [] (St b S M G) t_0000_c0 (.done (.halted D))) :
      sevm.caller.toB256 =? (ff20 &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [1])) ≠ 0 ∧
      D.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set (Bytes.toB256 [1]) (Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 0, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [1])) := by
  obtain ⟨_, _, _, run⟩ := dispatch_unpause hsel run
  unfold t_07f3_c166 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_callRet (E := [59]) (g := t_1e02_c59) (by decide) (by decide) rfl run; obtain ⟨_, D, callee, run⟩ := run
  obtain ⟨_, _, _, rfl, f1, hs⟩ := unpause_body hfork callee
  unfold t_0489_c166 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  -- LAST .stop
  obtain rfl := Outcome.halted.inj (Seg.done.inj (ric_stop run))
  exact ⟨f1, hs⟩

/-- **`updatePauser` from the implementation's entry**: the guards it passed and its storage effect. -/
theorem updatePauser_run (hfork : CoveredFork sevm.benvStat.fork) {D : Devm}
    (hsel : Blanc.Sevm.selector sevm = 0x554bab3c)
    (run : SFunc.RunCut cert.prog sevm [] (St b S M G) t_0000_c0 (.done (.halted D))) :
      ((Nat.toB256 (List.length sevm.data) - Bytes.toB256 [4]) <? Bytes.toB256 [32]) =? 0 ≠ 0 ∧
      sevm.caller.toB256 =? (ff20 &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [0])) ≠ 0 ∧
       ff20 &&& Sevm.dataWord sevm (Bytes.toB256 [4]) &&& ff20 ≠ 0 ∧
      D.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set (Bytes.toB256 [1]) (ff20 &&& (ff20 &&& Sevm.dataWord sevm (Bytes.toB256 [4])) ||| hi96 &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [1])) := by
  obtain ⟨_, _, _, run⟩ := dispatch_updatePauser hsel run
  unfold t_0954_c158 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldatasize s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sub s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_lt s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h1, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_096a_c158 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldataload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_callRet (E := [51]) (g := t_28b9_c51) (by decide) (by decide) rfl run; obtain ⟨_, D, callee, run⟩ := run
  obtain ⟨_, _, _, rfl, f1, f2, hs⟩ := updatePauser_body hfork callee
  unfold t_0489_c158 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  -- LAST .stop
  obtain rfl := Outcome.halted.inj (Seg.done.inj (ric_stop run))
  exact ⟨h1, f1, f2, hs⟩

/-- **`updateMasterMinter` from the implementation's entry**: the guards it passed and its storage effect. -/
theorem updateMasterMinter_run (hfork : CoveredFork sevm.benvStat.fork) {D : Devm}
    (hsel : Blanc.Sevm.selector sevm = 0xaa20e1e4)
    (run : SFunc.RunCut cert.prog sevm [] (St b S M G) t_0000_c0 (.done (.halted D))) :
      ((Nat.toB256 (List.length sevm.data) - Bytes.toB256 [4]) <? Bytes.toB256 [32]) =? 0 ≠ 0 ∧
      sevm.caller.toB256 =? (ff20 &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [0])) ≠ 0 ∧
       ff20 &&& Sevm.dataWord sevm (Bytes.toB256 [4]) &&& ff20 ≠ 0 ∧
      D.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set (Bytes.toB256 [8]) (ff20 &&& (ff20 &&& Sevm.dataWord sevm (Bytes.toB256 [4])) ||| hi96 &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [8])) := by
  obtain ⟨_, _, _, run⟩ := dispatch_updateMasterMinter hsel run
  unfold t_0cd4_c139 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldatasize s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sub s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_lt s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h1, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_0cea_c139 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldataload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_callRet (E := [31]) (g := t_3109_c31) (by decide) (by decide) rfl run; obtain ⟨_, D, callee, run⟩ := run
  obtain ⟨_, _, _, rfl, f1, f2, hs⟩ := updateMasterMinter_body hfork callee
  unfold t_0489_c139 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  -- LAST .stop
  obtain rfl := Outcome.halted.inj (Seg.done.inj (ric_stop run))
  exact ⟨h1, f1, f2, hs⟩

/-- **`updateBlacklister` from the implementation's entry**: the guards it passed and its storage effect. -/
theorem updateBlacklister_run (hfork : CoveredFork sevm.benvStat.fork) {D : Devm}
    (hsel : Blanc.Sevm.selector sevm = 0xad38bf22)
    (run : SFunc.RunCut cert.prog sevm [] (St b S M G) t_0000_c0 (.done (.halted D))) :
      ((Nat.toB256 (List.length sevm.data) - Bytes.toB256 [4]) <? Bytes.toB256 [32]) =? 0 ≠ 0 ∧
      sevm.caller.toB256 =? (ff20 &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [0])) ≠ 0 ∧
       ff20 &&& Sevm.dataWord sevm (Bytes.toB256 [4]) &&& ff20 ≠ 0 ∧
      D.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set (Bytes.toB256 [2]) (ff20 &&& (ff20 &&& Sevm.dataWord sevm (Bytes.toB256 [4])) ||| hi96 &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [2])) := by
  obtain ⟨_, _, _, run⟩ := dispatch_updateBlacklister hsel run
  unfold t_0d3a_c141 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldatasize s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sub s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_lt s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h1, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_0d50_c141 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldataload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_callRet (E := [33]) (g := t_329b_c33) (by decide) (by decide) rfl run; obtain ⟨_, D, callee, run⟩ := run
  obtain ⟨_, _, _, rfl, f1, f2, hs⟩ := updateBlacklister_body hfork callee
  unfold t_0489_c141 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  -- LAST .stop
  obtain rfl := Outcome.halted.inj (Seg.done.inj (ric_stop run))
  exact ⟨h1, f1, f2, hs⟩

/-- **`updateRescuer` from the implementation's entry**: the guards it passed and its storage effect. -/
theorem updateRescuer_run (hfork : CoveredFork sevm.benvStat.fork) {D : Devm}
    (hsel : Blanc.Sevm.selector sevm = 0x2ab60045)
    (run : SFunc.RunCut cert.prog sevm [] (St b S M G) t_0000_c0 (.done (.halted D))) :
      ((Nat.toB256 (List.length sevm.data) - Bytes.toB256 [4]) <? Bytes.toB256 [32]) =? 0 ≠ 0 ∧
      sevm.caller.toB256 =? (ff20 &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [0])) ≠ 0 ∧
       ff20 &&& Sevm.dataWord sevm (Bytes.toB256 [4]) &&& ff20 ≠ 0 ∧
      D.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set (Bytes.toB256 [14]) (ff20 &&& Sevm.dataWord sevm (Bytes.toB256 [4]) &&& ff20 ||| hi96 &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [14])) := by
  obtain ⟨_, _, _, run⟩ := dispatch_updateRescuer hsel run
  unfold t_04ce_c176 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldatasize s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sub s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_lt s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h1, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_04e4_c176 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldataload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_callRet (E := [69]) (g := t_16f2_c69) (by decide) (by decide) rfl run; obtain ⟨_, D, callee, run⟩ := run
  obtain ⟨_, _, _, rfl, f1, f2, hs⟩ := updateRescuer_body hfork callee
  unfold t_0489_c176 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  -- LAST .stop
  obtain rfl := Outcome.halted.inj (Seg.done.inj (ric_stop run))
  exact ⟨h1, f1, f2, hs⟩

/-- **`transferOwnership` from the implementation's entry**: the guards it passed and its storage effect. -/
theorem transferOwnership_run (hfork : CoveredFork sevm.benvStat.fork) {D : Devm}
    (hsel : Blanc.Sevm.selector sevm = 0xf2fde38b)
    (run : SFunc.RunCut cert.prog sevm [] (St b S M G) t_0000_c0 (.done (.halted D))) :
      ((Nat.toB256 (List.length sevm.data) - Bytes.toB256 [4]) <? Bytes.toB256 [32]) =? 0 ≠ 0 ∧
      sevm.caller.toB256 =? (ff20 &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [0])) ≠ 0 ∧
       ff20 &&& Sevm.dataWord sevm (Bytes.toB256 [4]) &&& ff20 ≠ 0 ∧
      D.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set (Bytes.toB256 [0]) (ff20 &&& (ff20 &&& Sevm.dataWord sevm (Bytes.toB256 [4])) ||| hi96 &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [0])) := by
  obtain ⟨_, _, _, run⟩ := dispatch_transferOwnership hsel run
  unfold t_118e_c126 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldatasize s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sub s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_lt s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h1, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_11a4_c126 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldataload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_callRet (E := [16, 85]) (g := t_3bfd_c16) (by decide) (by decide) rfl run; obtain ⟨_, D, callee, run⟩ := run
  obtain ⟨_, _, _, rfl, f1, f2, hs⟩ := transferOwnership_body hfork callee
  unfold t_0489_c126 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  -- LAST .stop
  obtain rfl := Outcome.halted.inj (Seg.done.inj (ric_stop run))
  exact ⟨h1, f1, f2, hs⟩

/-- **`removeMinter` from the implementation's entry**: the guards it passed and its storage effect. -/
theorem removeMinter_run (hfork : CoveredFork sevm.benvStat.fork) {D : Devm}
    (hsel : Blanc.Sevm.selector sevm = 0x3092afd5)
    (run : SFunc.RunCut cert.prog sevm [] (St b S M G) t_0000_c0 (.done (.halted D))) :
      ((Nat.toB256 (List.length sevm.data) - Bytes.toB256 [4]) <? Bytes.toB256 [32]) =? 0 ≠ 0 ∧
      sevm.caller.toB256 =? (ff20 &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [8])) ≠ 0 ∧
      D.getStor sevm.currentTarget = ((b.getStor sevm.currentTarget).set (mapSlot (ff20 &&& Sevm.dataWord sevm (Bytes.toB256 [4]) &&& ff20) (Bytes.toB256 [12])) (Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 0] &&& (b.getStor sevm.currentTarget).get (mapSlot (ff20 &&& Sevm.dataWord sevm (Bytes.toB256 [4]) &&& ff20) (Bytes.toB256 [12])))).set (mapSlot (ff20 &&& Sevm.dataWord sevm (Bytes.toB256 [4]) &&& ff20) (Bytes.toB256 [13])) (Bytes.toB256 [0]) := by
  obtain ⟨_, _, _, run⟩ := dispatch_removeMinter hsel run
  unfold t_0534_c172 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldatasize s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sub s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_lt s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h1, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_054a_c172 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldataload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_callRet (E := [65]) (g := t_18bb_c65) (by decide) (by decide) rfl run; obtain ⟨_, D, callee, run⟩ := run
  obtain ⟨_, _, _, rfl, f1, hs⟩ := removeMinter_body hfork callee
  unfold t_0428_c172 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sub s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_add s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  rw [ric_return run]
  exact ⟨h1, f1, hs⟩

/-- **`configureMinter` from the implementation's entry**: the guards it passed and its storage effect. -/
theorem configureMinter_run (hfork : CoveredFork sevm.benvStat.fork) {D : Devm}
    (hsel : Blanc.Sevm.selector sevm = 0x4e44d956)
    (run : SFunc.RunCut cert.prog sevm [] (St b S M G) t_0000_c0 (.done (.halted D))) :
      ((Nat.toB256 (List.length sevm.data) - Bytes.toB256 [4]) <? Bytes.toB256 [64]) =? 0 ≠ 0 ∧
       (Bytes.toB256 [255] &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [1]) / Bytes.toB256 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) =? 0 ≠ 0 ∧
      sevm.caller.toB256 =? (ff20 &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [8])) ≠ 0 ∧
      D.getStor sevm.currentTarget = ((b.getStor sevm.currentTarget).set (mapSlot (Sevm.dataWord sevm (Bytes.toB256 [4]) &&& ff20 &&& ff20) (Bytes.toB256 [12])) (Bytes.toB256 [1] ||| Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 0] &&& (b.getStor sevm.currentTarget).get (mapSlot (Sevm.dataWord sevm (Bytes.toB256 [4]) &&& ff20 &&& ff20) (Bytes.toB256 [12])))).set (mapSlot (Sevm.dataWord sevm (Bytes.toB256 [4]) &&& ff20 &&& ff20) (Bytes.toB256 [13])) (Sevm.dataWord sevm (Bytes.toB256 [32] + Bytes.toB256 [4])) := by
  obtain ⟨_, _, _, run⟩ := dispatch_configureMinter hsel run
  unfold t_0913_c163 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldatasize s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sub s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_lt s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h1, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_0929_c163 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldataload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_add s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldataload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_callRet (E := [56]) (g := t_26ef_c56) (by decide) (by decide) rfl run; obtain ⟨_, D, callee, run⟩ := run
  obtain ⟨_, _, _, rfl, f1, f2, hs⟩ := configureMinter_body hfork callee
  unfold t_0428_c163 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sub s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_add s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  rw [ric_return run]
  exact ⟨h1, f1, f2, hs⟩

/-- **`unBlacklist` from the implementation's entry**: the guards it passed and its storage effect. -/
theorem unBlacklist_run (hfork : CoveredFork sevm.benvStat.fork) {D : Devm}
    (hsel : Blanc.Sevm.selector sevm = 0x1a895266)
    (run : SFunc.RunCut cert.prog sevm [] (St b S M G) t_0000_c0 (.done (.halted D))) :
      ((Nat.toB256 (List.length sevm.data) - Bytes.toB256 [4]) <? Bytes.toB256 [32]) =? 0 ≠ 0 ∧
      sevm.caller.toB256 =? (ff20 &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [2])) ≠ 0 ∧
      D.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set (mapSlot (ff20 &&& Sevm.dataWord sevm (Bytes.toB256 [4]) &&& ff20) (Bytes.toB256 [9])) (lo255 &&& (b.getStor sevm.currentTarget).get (mapSlot (ff20 &&& (ff20 &&& Sevm.dataWord sevm (Bytes.toB256 [4]))) (Bytes.toB256 [9]))) := by
  obtain ⟨_, _, _, run⟩ := dispatch_unBlacklist hsel run
  unfold t_0456_c174 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldatasize s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sub s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_lt s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h1, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_046c_c174 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldataload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_callRet (E := [10, 67, 96, 104, 109]) (g := t_137a_c67) (by decide) (by decide) rfl run; obtain ⟨_, D, callee, run⟩ := run
  obtain ⟨_, _, _, rfl, f1, hs⟩ := unBlacklist_body hfork callee
  unfold t_0489_c174 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  -- LAST .stop
  obtain rfl := Outcome.halted.inj (Seg.done.inj (ric_stop run))
  exact ⟨h1, f1, hs⟩

/-- **`blacklist` from the implementation's entry**: the guards it passed and its storage effect. -/
theorem blacklist_run (hfork : CoveredFork sevm.benvStat.fork) {D : Devm}
    (hsel : Blanc.Sevm.selector sevm = 0xf9f92be4)
    (run : SFunc.RunCut cert.prog sevm [] (St b S M G) t_0000_c0 (.done (.halted D))) :
      ((Nat.toB256 (List.length sevm.data) - Bytes.toB256 [4]) <? Bytes.toB256 [32]) =? 0 ≠ 0 ∧
      sevm.caller.toB256 =? (ff20 &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [2])) ≠ 0 ∧
      D.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set (mapSlot (ff20 &&& Sevm.dataWord sevm (Bytes.toB256 [4]) &&& ff20) (Bytes.toB256 [9])) (Bytes.toB256 [128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ||| (b.getStor sevm.currentTarget).get (mapSlot (ff20 &&& Sevm.dataWord sevm (Bytes.toB256 [4]) &&& ff20) (Bytes.toB256 [9]))) := by
  obtain ⟨_, _, _, run⟩ := dispatch_blacklist hsel run
  unfold t_11c1_c127 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldatasize s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sub s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_lt s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h1, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_11d7_c127 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldataload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_callRet (E := [10, 17, 86, 96, 109]) (g := t_3d50_c17) (by decide) (by decide) rfl run; obtain ⟨_, D, callee, run⟩ := run
  obtain ⟨_, _, _, rfl, f1, hs⟩ := blacklist_body hfork callee
  unfold t_0489_c127 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  -- LAST .stop
  obtain rfl := Outcome.halted.inj (Seg.done.inj (ric_stop run))
  exact ⟨h1, f1, hs⟩

/-- **`mint` from the implementation's entry**: the guards it passed and its storage effect. -/
theorem mint_run (hfork : CoveredFork sevm.benvStat.fork) {D : Devm}
    (hsel : Blanc.Sevm.selector sevm = 0x40c10f19)
    (run : SFunc.RunCut cert.prog sevm [] (St b S M G) t_0000_c0 (.done (.halted D))) :
      ((Nat.toB256 (List.length sevm.data) - Bytes.toB256 [4]) <? Bytes.toB256 [64]) =? 0 ≠ 0 ∧
       (Bytes.toB256 [255] &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [1]) / Bytes.toB256 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) =? 0 ≠ 0 ∧
      Bytes.toB256 [255] &&& (b.getStor sevm.currentTarget).get (mapSlot sevm.caller.toB256 (Bytes.toB256 [12])) ≠ 0 ∧
       (Bytes.toB256 [1] =? (b.getStor sevm.currentTarget).get (mapSlot (ff20 &&& sevm.caller.toB256) (Bytes.toB256 [9])) >>> (Bytes.toB256 [255]).toNat) =? 0 ≠ 0 ∧
       (Bytes.toB256 [1] =? (b.getStor sevm.currentTarget).get (mapSlot (ff20 &&& (Sevm.dataWord sevm (Bytes.toB256 [4]) &&& ff20)) (Bytes.toB256 [9])) >>> (Bytes.toB256 [255]).toNat) =? 0 ≠ 0 ∧
       Sevm.dataWord sevm (Bytes.toB256 [4]) &&& ff20 &&& ff20 ≠ 0 ∧
      Sevm.dataWord sevm (Bytes.toB256 [32] + Bytes.toB256 [4]) >? Bytes.toB256 [0] ≠ 0 ∧
       (Sevm.dataWord sevm (Bytes.toB256 [32] + Bytes.toB256 [4]) >? (b.getStor sevm.currentTarget).get (mapSlot sevm.caller.toB256 (Bytes.toB256 [13]))) =? 0 ≠ 0 ∧
       (Sevm.dataWord sevm (Bytes.toB256 [32] + Bytes.toB256 [4]) + (b.getStor sevm.currentTarget).get (Bytes.toB256 [11])) <? (b.getStor sevm.currentTarget).get (Bytes.toB256 [11]) = 0 ∧
       (Sevm.dataWord sevm (Bytes.toB256 [32] + Bytes.toB256 [4]) + (lo255 &&& ((b.getStor sevm.currentTarget).set (Bytes.toB256 [11]) (Sevm.dataWord sevm (Bytes.toB256 [32] + Bytes.toB256 [4]) + (b.getStor sevm.currentTarget).get (Bytes.toB256 [11]))).get (mapSlot (ff20 &&& (Sevm.dataWord sevm (Bytes.toB256 [4]) &&& ff20)) (Bytes.toB256 [9])))) <? (lo255 &&& ((b.getStor sevm.currentTarget).set (Bytes.toB256 [11]) (Sevm.dataWord sevm (Bytes.toB256 [32] + Bytes.toB256 [4]) + (b.getStor sevm.currentTarget).get (Bytes.toB256 [11]))).get (mapSlot (ff20 &&& (Sevm.dataWord sevm (Bytes.toB256 [4]) &&& ff20)) (Bytes.toB256 [9]))) = 0 ∧
       (Sevm.dataWord sevm (Bytes.toB256 [32] + Bytes.toB256 [4]) + (lo255 &&& ((b.getStor sevm.currentTarget).set (Bytes.toB256 [11]) (Sevm.dataWord sevm (Bytes.toB256 [32] + Bytes.toB256 [4]) + (b.getStor sevm.currentTarget).get (Bytes.toB256 [11]))).get (mapSlot (ff20 &&& (Sevm.dataWord sevm (Bytes.toB256 [4]) &&& ff20)) (Bytes.toB256 [9])))) >? lo255 = 0 ∧
       Bytes.toB256 [1] =? ((b.getStor sevm.currentTarget).set (Bytes.toB256 [11]) (Sevm.dataWord sevm (Bytes.toB256 [32] + Bytes.toB256 [4]) + (b.getStor sevm.currentTarget).get (Bytes.toB256 [11]))).get (mapSlot (ff20 &&& (Sevm.dataWord sevm (Bytes.toB256 [4]) &&& ff20)) (Bytes.toB256 [9])) >>> (Bytes.toB256 [255]).toNat = 0 ∧
       Sevm.dataWord sevm (Bytes.toB256 [32] + Bytes.toB256 [4]) >? (b.getStor sevm.currentTarget).get (mapSlot sevm.caller.toB256 (Bytes.toB256 [13])) = 0 ∧
      D.getStor sevm.currentTarget = (((b.getStor sevm.currentTarget).set (Bytes.toB256 [11]) (Sevm.dataWord sevm (Bytes.toB256 [32] + Bytes.toB256 [4]) + (b.getStor sevm.currentTarget).get (Bytes.toB256 [11]))).set (mapSlot (Sevm.dataWord sevm (Bytes.toB256 [4]) &&& ff20 &&& ff20) (Bytes.toB256 [9])) (Sevm.dataWord sevm (Bytes.toB256 [32] + Bytes.toB256 [4]) + (lo255 &&& ((b.getStor sevm.currentTarget).set (Bytes.toB256 [11]) (Sevm.dataWord sevm (Bytes.toB256 [32] + Bytes.toB256 [4]) + (b.getStor sevm.currentTarget).get (Bytes.toB256 [11]))).get (mapSlot (ff20 &&& (Sevm.dataWord sevm (Bytes.toB256 [4]) &&& ff20)) (Bytes.toB256 [9]))))).set (mapSlot sevm.caller.toB256 (Bytes.toB256 [13])) ((b.getStor sevm.currentTarget).get (mapSlot sevm.caller.toB256 (Bytes.toB256 [13])) - Sevm.dataWord sevm (Bytes.toB256 [32] + Bytes.toB256 [4])) := by
  obtain ⟨_, _, _, run⟩ := dispatch_mint hsel run
  unfold t_07fb_c160 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldatasize s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sub s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_lt s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h1, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_0811_c160 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldataload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_add s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldataload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_callRet (E := [7, 53, 83, 96, 98, 99, 100]) (g := t_1ec5_c53) (by decide) (by decide) rfl run; obtain ⟨_, D, callee, run⟩ := run
  obtain ⟨_, _, _, rfl, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, hs⟩ := mint_body hfork callee
  unfold t_0428_c160 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sub s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_add s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  rw [ric_return run]
  exact ⟨h1, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, hs⟩

/-- **`burn` from the implementation's entry**: the guards it passed and its storage effect. -/
theorem burn_run (hfork : CoveredFork sevm.benvStat.fork) {D : Devm}
    (hsel : Blanc.Sevm.selector sevm = 0x42966c68)
    (run : SFunc.RunCut cert.prog sevm [] (St b S M G) t_0000_c0 (.done (.halted D))) :
      ((Nat.toB256 (List.length sevm.data) - Bytes.toB256 [4]) <? Bytes.toB256 [32]) =? 0 ≠ 0 ∧
       (Bytes.toB256 [255] &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [1]) / Bytes.toB256 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) =? 0 ≠ 0 ∧
      Bytes.toB256 [255] &&& (b.getStor sevm.currentTarget).get (mapSlot sevm.caller.toB256 (Bytes.toB256 [12])) ≠ 0 ∧
       (Bytes.toB256 [1] =? (b.getStor sevm.currentTarget).get (mapSlot (ff20 &&& sevm.caller.toB256) (Bytes.toB256 [9])) >>> (Bytes.toB256 [255]).toNat) =? 0 ≠ 0 ∧
      Sevm.dataWord sevm (Bytes.toB256 [4]) >? Bytes.toB256 [0] ≠ 0 ∧
       ((lo255 &&& (b.getStor sevm.currentTarget).get (mapSlot (ff20 &&& sevm.caller.toB256) (Bytes.toB256 [9]))) <? Sevm.dataWord sevm (Bytes.toB256 [4])) =? 0 ≠ 0 ∧
       ((lo255 &&& (b.getStor sevm.currentTarget).get (mapSlot (ff20 &&& sevm.caller.toB256) (Bytes.toB256 [9]))) - Sevm.dataWord sevm (Bytes.toB256 [4])) >? lo255 = 0 ∧
       Bytes.toB256 [1] =? ((b.getStor sevm.currentTarget).set (Bytes.toB256 [11]) ((b.getStor sevm.currentTarget).get (Bytes.toB256 [11]) - Sevm.dataWord sevm (Bytes.toB256 [4]))).get (mapSlot (ff20 &&& sevm.caller.toB256) (Bytes.toB256 [9])) >>> (Bytes.toB256 [255]).toNat = 0 ∧
      Sevm.dataWord sevm (Bytes.toB256 [4]) >? (b.getStor sevm.currentTarget).get (Bytes.toB256 [11]) = 0 ∧
       Sevm.dataWord sevm (Bytes.toB256 [4]) >? (lo255 &&& (b.getStor sevm.currentTarget).get (mapSlot (ff20 &&& sevm.caller.toB256) (Bytes.toB256 [9]))) = 0 ∧
      D.getStor sevm.currentTarget = ((b.getStor sevm.currentTarget).set (Bytes.toB256 [11]) ((b.getStor sevm.currentTarget).get (Bytes.toB256 [11]) - Sevm.dataWord sevm (Bytes.toB256 [4]))).set (mapSlot (sevm.caller.toB256 &&& ff20) (Bytes.toB256 [9])) ((lo255 &&& (b.getStor sevm.currentTarget).get (mapSlot (ff20 &&& sevm.caller.toB256) (Bytes.toB256 [9]))) - Sevm.dataWord sevm (Bytes.toB256 [4])) := by
  obtain ⟨_, _, _, run⟩ := dispatch_burn hsel run
  unfold t_0834_c161 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldatasize s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sub s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_lt s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h1, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_084a_c161 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_calldataload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_callRet (E := [54, 83, 96, 99, 100]) (g := t_2296_c54) (by decide) (by decide) rfl run; obtain ⟨_, D, callee, run⟩ := run
  obtain ⟨_, _, _, rfl, f1, f2, f3, f4, f5, f6, f7, f8, f9, hs⟩ := burn_body hfork callee
  unfold t_0489_c161 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  -- LAST .stop
  obtain rfl := Outcome.halted.inj (Seg.done.inj (ric_stop run))
  exact ⟨h1, f1, f2, f3, f4, f5, f6, f7, f8, f9, hs⟩

end Blanc.Lift.Usdc.Impl
