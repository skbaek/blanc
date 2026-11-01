import Blanc.LidoCircuitBreaker
import Blanc.LinearDispatchCorrectness
import Blanc.Forward
import Blanc.Reverts
import Blanc.ForwardCall
import Mathlib.Tactic.FinCases

/-!
# The CircuitBreaker's public dispatcher, walked once

`runtimeMain_dispatch_runCompiledTo` crosses the entry guard, `fsig`, the two
selected `splitDispatch` pivots and the selected `linearDispatchWith` group for
every one of the seventeen entries of `funcs`, over an **abstract** function
table and an **abstract** body run.  Each public-dispatch theorem downstream is
an instance: it never unfolds the dispatcher, the compiled table or the
`selector` keccaks into its own goal.

Two causes kept the old per-site walks at `maxRecDepth` 591-764, and both are
avoided here:

* the walks evaluated `selector "…" […]` (one `String.keccak` each) to decide
  every pivot and miss comparison; here the table is restated once with numeral
  keys (`funcs_eq_words`, each word proved by `decide +kernel`);
* the walks carried the concrete `runtimeMain dp :: aux` table and the unfolded
  dispatcher through every step; here the table `fs` is a variable and the
  selected body is generalized before the walk.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

/-! ## One step of each CircuitBreaker-specific dispatcher shape

The linear-chain arms are shared (`Blanc/LinearDispatchCorrectness.lean`). -/

section Arms

variable {fs : List Func} {sevm : Sevm} {base : Devm} {tail : Stack}
    {mem : Mem} {sg : StateGasMeter} {ex : Execution} {G : Nat}

/-- A `splitDispatch` pivot above the selector takes the left half. -/
theorem splitDispatch_left_runCompiledTo {p sel : B256} {l r : Func}
    (hp : p ≠ 0) (hgt : (p >? sel) = 1) (hroom : tail.length < 1022)
    (hl : Func.RunCompiledTo fs sevm (base.setMach ⟨sel :: tail, mem, G, sg⟩) l ex) :
    Func.RunCompiledTo fs sevm (base.setMach ⟨sel :: tail, mem, G + 23, sg⟩)
      (splitDispatch p l r) ex := by
  have hpush : pushCost p.toBytes.sig = 3 := pushCost_of_ne_zero hp
  unfold splitDispatch
  func_run (4) [1]
  simpa only [Nat.add_sub_cancel] using hl

/-- A `splitDispatch` pivot not above the selector takes the right half. -/
theorem splitDispatch_right_runCompiledTo {p sel : B256} {l r : Func}
    (hp : p ≠ 0) (hgt : (p >? sel) = 0) (hroom : tail.length < 1022)
    (hr : Func.RunCompiledTo fs sevm (base.setMach ⟨sel :: tail, mem, G, sg⟩) r ex) :
    Func.RunCompiledTo fs sevm (base.setMach ⟨sel :: tail, mem, G + 22, sg⟩)
      (splitDispatch p l r) ex := by
  have hpush : pushCost p.toBytes.sig = 3 := pushCost_of_ne_zero hp
  unfold splitDispatch
  func_run (4) [0]
  simpa only [Nat.add_sub_cancel] using hr

/-- The nonpayable, short-calldata entry guard of `runtimeMain`, then `fsig`. -/
theorem entryGuard_runCompiledTo {sel : B256} {X : Func}
    (h_push0 : sevm.benvStat.rules.op.push0 = true)
    (h_shifts : sevm.benvStat.rules.op.shifts = true)
    (hvalue : sevm.value = 0) (hlt : sevm.data.length.toB256 <? 4 = 0)
    (hsel : Sevm.selector sevm = sel)
    (hX : Func.RunCompiledTo fs sevm (base.setMach ⟨[sel], Mem.empty, G, sg⟩) X ex) :
    Func.RunCompiledTo fs sevm (base.setMach ⟨[], Mem.empty, G + 37, sg⟩)
      (callvalue ::: pushB256 4 ::: calldatasize ::: lt ::: Ninst.or :::
        (Func.revert <?> (fsig +++ X))) ex := by
  have hor : B256.or 0 sevm.value = 0 := by rw [hvalue]; decide
  have hsel' : Sevm.dataWord sevm 0 >>> B256.toNat 224 = sel := hsel
  func_run (10) [0, 0, sel]
  simpa only [Nat.add_sub_cancel, prepend] using hX

end Arms

/-! ## The selector words -/

namespace Word

theorem pauseDuration : selector "pauseDuration" [] = (0x0526679c : B256) := by decide +kernel
theorem maxPauseDuration : selector "MAX_PAUSE_DURATION" [] = (0x2799657d : B256) := by
  decide +kernel
theorem admin : selector "ADMIN" [] = (0x2a0acc6a : B256) := by decide +kernel
theorem registerPauser :
    selector "registerPauser" [.address, .address] = (0x338d93fc : B256) := by decide +kernel
theorem heartbeat : selector "heartbeat" [] = (0x3defb962 : B256) := by decide +kernel
theorem getPauser : selector "getPauser" [.address] = (0x5280237a : B256) := by decide +kernel
theorem getPausables : selector "getPausables" [] = (0x54720ecd : B256) := by decide +kernel
theorem heartbeatInterval : selector "heartbeatInterval" [] = (0x561a4fac : B256) := by
  decide +kernel
theorem setHeartbeatInterval :
    selector "setHeartbeatInterval" [.uint256] = (0x71a99c22 : B256) := by decide +kernel
theorem pause : selector "pause" [.address] = (0x76a67a51 : B256) := by decide +kernel
theorem minPauseDuration : selector "MIN_PAUSE_DURATION" [] = (0x76c810b5 : B256) := by
  decide +kernel
theorem maxHeartbeatInterval : selector "MAX_HEARTBEAT_INTERVAL" [] = (0x879f32f6 : B256) := by
  decide +kernel
theorem getPausableCount : selector "getPausableCount" [.address] = (0x8cd80ba0 : B256) := by
  decide +kernel
theorem minHeartbeatInterval : selector "MIN_HEARTBEAT_INTERVAL" [] = (0x8dd54ee7 : B256) := by
  decide +kernel
theorem heartbeatExpiry : selector "heartbeatExpiry" [.address] = (0xc427909e : B256) := by
  decide +kernel
theorem setPauseDuration : selector "setPauseDuration" [.uint256] = (0xc9387332 : B256) := by
  decide +kernel
theorem isPauserLive : selector "isPauserLive" [.address] = (0xd10ea321 : B256) := by
  decide +kernel

end Word

/-! ## Event words

The event topics are `signatureHash` words too: a walk that pushes one, or a
premise that asks for one to be nonzero, would evaluate a keccak in the
elaborator.  Each fact is kernel-checked once here. -/

theorem heartbeatUpdatedEvent_pushCost : pushCost heartbeatUpdatedEvent.toBytes.sig = 3 :=
  pushCost_of_ne_zero (by decide +kernel)

theorem pauseDurationUpdatedEvent_pushCost :
    pushCost pauseDurationUpdatedEvent.toBytes.sig = 3 :=
  pushCost_of_ne_zero (by decide +kernel)

theorem pauserSetEvent_pushCost : pushCost pauserSetEvent.toBytes.sig = 3 :=
  pushCost_of_ne_zero (by decide +kernel)

theorem pauseTriggeredEvent_pushCost :
    pushCost pauseTriggeredEvent.toBytes.sig = 3 :=
  pushCost_of_ne_zero (by decide +kernel)

/-- The pause callback's two selectors are pushed like event words. -/
theorem isPausedSelector_pushCost : pushCost isPausedSelector.toBytes.sig = 3 :=
  pushCost_of_ne_zero (by decide +kernel)

theorem pauseForSelector_pushCost : pushCost pauseForSelector.toBytes.sig = 3 :=
  pushCost_of_ne_zero (by decide +kernel)

theorem heartbeatIntervalUpdatedEvent_ne_zero : heartbeatIntervalUpdatedEvent ≠ 0 := by
  decide +kernel

/-- Decide a closed comparison between selector words of the table: rewrite each
`selector "…" […]` to its numeral first, so `decide` never evaluates a keccak. -/
macro "selector_words_decide" : tactic =>
  `(tactic| (simp only [
    Word.pauseDuration, Word.maxPauseDuration, Word.admin, Word.registerPauser,
    Word.heartbeat, Word.getPauser, Word.getPausables, Word.heartbeatInterval,
    Word.setHeartbeatInterval, Word.pause, Word.minPauseDuration,
    Word.maxHeartbeatInterval, Word.getPausableCount, Word.minHeartbeatInterval,
    Word.heartbeatExpiry, Word.setPauseDuration, Word.isPauserLive]) <;> decide)

/-- The dispatch table with numeral keys. -/
theorem funcs_eq_words (dp : DeployParams) : funcs dp =
    [ ((0x0526679c : B256), pauseDuration), ((0x2799657d : B256), maxPauseDuration dp),
      ((0x2a0acc6a : B256), admin dp), ((0x338d93fc : B256), registerPauser dp),
      ((0x3defb962 : B256), heartbeat), ((0x5280237a : B256), getPauser),
      ((0x54720ecd : B256), getPausables), ((0x561a4fac : B256), heartbeatInterval),
      ((0x71a99c22 : B256), setHeartbeatInterval dp), ((0x76a67a51 : B256), pause),
      ((0x76c810b5 : B256), minPauseDuration dp), ((0x879f32f6 : B256), maxHeartbeatInterval dp),
      ((0x8cd80ba0 : B256), getPausableCount), ((0x8dd54ee7 : B256), minHeartbeatInterval dp),
      ((0xc427909e : B256), heartbeatExpiry), ((0xc9387332 : B256), setPauseDuration dp),
      ((0xd10ea321 : B256), isPauserLive) ] := by
  rw [funcs, Word.pauseDuration, Word.maxPauseDuration, Word.admin, Word.registerPauser,
    Word.heartbeat, Word.getPauser, Word.getPausables, Word.heartbeatInterval,
    Word.setHeartbeatInterval, Word.pause, Word.minPauseDuration, Word.maxHeartbeatInterval,
    Word.getPausableCount, Word.minHeartbeatInterval, Word.heartbeatExpiry,
    Word.setPauseDuration, Word.isPauserLive]

/-! ## The whole dispatcher -/

/-- Exact `Func`-level gas of `runtimeMain` from entry to the selected body, per
table index: guard and `fsig` 37, a taken pivot 23 and a fallen-through one 22, a
missed entry 22, a matched non-final entry 25 and a matched final entry 20. -/
def runtimeDispatchCost (k : Fin 17) : Nat :=
  [108, 130, 152, 174, 191, 107, 129, 151, 168, 107, 129, 151, 168, 106, 128, 150, 167].getD
    k 0

/-- The exact public dispatcher, for any table index: from the entry state with
an empty stack and empty memory to the selected body, over any function table
`fs` and any body outcome. -/
theorem runtimeMain_dispatch_runCompiledTo (dp : DeployParams) (k : Fin 17)
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {sg : StateGasMeter} {ex : Execution} {G : Nat}
    (h_push0 : sevm.benvStat.rules.op.push0 = true)
    (h_shifts : sevm.benvStat.rules.op.shifts = true) (hvalue : sevm.value = 0)
    (hlt : sevm.data.length.toB256 <? 4 = 0)
    (hsel : Sevm.selector sevm = ((funcs dp).getD k (0, .revert)).1)
    (hbody : Func.RunCompiledTo fs sevm (base.setMach ⟨[], Mem.empty, G, sg⟩)
      ((funcs dp).getD k (0, .revert)).2 ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + runtimeDispatchCost k, sg⟩)
      (runtimeMain dp) ex := by
  unfold runtimeMain hybridDispatchWith
  fin_cases k <;>
    simp only [funcs_eq_words, runtimeDispatchCost, List.getD_cons_zero, List.getD_cons_succ,
      List.take, List.drop, firstSelector, List.head?, Option.map, Option.getD] at hsel hbody ⊢
  all_goals
    generalize pauseDuration = b0, maxPauseDuration dp = b1, admin dp = b2,
      registerPauser dp = b3, heartbeat = b4, getPauser = b5, getPausables = b6,
      heartbeatInterval = b7, setHeartbeatInterval dp = b8, pause = b9,
      minPauseDuration dp = b10, maxHeartbeatInterval dp = b11, getPausableCount = b12,
      minHeartbeatInterval dp = b13, heartbeatExpiry = b14, setPauseDuration dp = b15,
      isPauserLive = b16 at hbody ⊢
    refine entryGuard_runCompiledTo h_push0 h_shifts hvalue hlt hsel ?_
    repeat
      first
      | exact linearLast_hit_runCompiledTo (by decide) (by decide) hbody
      | exact linearEntry_hit_runCompiledTo (by decide) (by decide) hbody
      | refine splitDispatch_left_runCompiledTo (by decide) (by decide) (by decide) ?_
      | refine splitDispatch_right_runCompiledTo (by decide) (by decide) (by decide) ?_
      | refine linearEntry_miss_runCompiledTo (by decide) (by decide) (by decide) ?_

/-- The emitted runtime, entered at pc 0, crosses its dispatcher to the selected
body for any table index and any body outcome. -/
theorem runtime_dispatch_runCompiledTo (dp : DeployParams) (k : Fin 17)
    {sevm : Sevm} {base : Devm} {ex : Execution} {G g : Nat}
    (h_push0 : sevm.benvStat.rules.op.push0 = true)
    (h_shifts : sevm.benvStat.rules.op.shifts = true) (hvalue : sevm.value = 0)
    (hlt : sevm.data.length.toB256 <? 4 = 0)
    (hsel : Sevm.selector sevm = ((funcs dp).getD k (0, .revert)).1)
    (hgas : g = G + runtimeDispatchCost k + gJumpdest)
    (hbody : Func.RunCompiledTo (runtimeMain dp :: aux) sevm
      (base.setMach ⟨[], Mem.empty, G, base.stateGas⟩)
      ((funcs dp).getD k (0, .revert)).2 ex) :
    Prog.RunCompiledTo sevm (base.setMach ⟨[], Mem.empty, g, base.stateGas⟩)
      (runtime dp) ex := by
  refine Prog.runCompiledTo_intro (G := G + runtimeDispatchCost k)
    (by simp only [Devm.gasLeft_setMach, hgas]) rfl ?_
  rw [runtime_eq_mk]
  simpa only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach,
    Devm.stateGas_setMach] using
    runtimeMain_dispatch_runCompiledTo dp k h_push0 h_shifts hvalue hlt hsel hbody

/-- `runtime_dispatch_runCompiledTo` for a successful body. -/
theorem runtime_dispatch_runCompiled (dp : DeployParams) (k : Fin 17)
    {sevm : Sevm} {base post : Devm} {G g : Nat}
    (h_push0 : sevm.benvStat.rules.op.push0 = true)
    (h_shifts : sevm.benvStat.rules.op.shifts = true) (hvalue : sevm.value = 0)
    (hlt : sevm.data.length.toB256 <? 4 = 0)
    (hsel : Sevm.selector sevm = ((funcs dp).getD k (0, .revert)).1)
    (hgas : g = G + runtimeDispatchCost k + gJumpdest)
    (hbody : Func.RunCompiled (runtimeMain dp :: aux) sevm
      (base.setMach ⟨[], Mem.empty, G, base.stateGas⟩)
      ((funcs dp).getD k (0, .revert)).2 post) :
    Prog.RunCompiled sevm (base.setMach ⟨[], Mem.empty, g, base.stateGas⟩)
      (runtime dp) post := by
  rcases runtime_dispatch_runCompiledTo dp k h_push0 h_shifts hvalue hlt hsel hgas
      (Func.RunCompiledTo.of_runCompiled hbody) with ⟨mid, hburn, hrun⟩
  exact ⟨mid, hburn, Func.RunCompiled.of_runCompiledTo_ok hrun⟩

end LidoCircuitBreaker

end Blanc
