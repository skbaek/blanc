import Blanc.ExecutionKeptFacts
import Blanc.ExecutionKeptChain
import Blanc.LadderBase

/-!
# Kept-frame value: never falls, and covers the kept values (O37 sizing draft)

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`.

**Status.** Sizing draft written without Lean elaboration under the run's
no-elaboration constraint. Every `sorry` carries a `-- DRAFT:` comment giving
the leaf's route and an estimated line count from a comparable existing proof
that was actually read. The master compiles this file and clears them.

**What this is.** The neutral `Exec` fold O37 needs, over kept (settled) frames
only: nothing here names `rawNodes`, `rawFrames`, a gas amount, or a frame that
did not commit. `Exec.kept_bal_neverFalls` says the account's balance never
falls across one kept run; `Exec.kept_bal_ge_keptPaid` says it additionally
covers the values the kept frames carried in. Both induct over
`Exec.retained_induction` with the code premise threaded down by
`Blanc.Exec.Deriv.ParentStep.codePreserve`, exactly as `Exec.keptAt_entry`
does. The at-code frame law is a premise, discharged per contract by
`frame_keeps_balances` (`Blanc/Lift/BuilderRequest/Surplus.lean`, W18, merged).
The foreign cases are the new work: balance twins of the storage twins in
`Blanc/ExecutionKeptFrames.lean`.

**Reuse.** `Exec.keptAt`, `Exec.retained_induction`, `Execution.committedPost`,
`Execution.commits`, `Devm.getBal`, `SumNof`, `KeptFork`,
`Blanc.Exec.Deriv.ParentStep.codePreserve`, `Evm.step_spawn_inv`,
`Xinst.step_spawn_form` are reused, not redefined. Nothing here is
contract-specific, so at the green boundary this module is a SHARED candidate
(`scripts/check-layering.py` registration plus a `docs/COMMON_API.md` entry are
left to the compiling run: this run edits no existing file).
-/

namespace Blanc

open Jaune ExecutionTrace

/-- The values the frames kept at `a` carried in, one per kept frame. -/
def Exec.keptPaid (a : Adr) {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) : Nat :=
  ((Exec.keptAt a run).map fun f => f.sevm.value.toNat).sum

/-- **Never falls across one kept run.** At an account holding nondelegating
code, with the world-sum bound at every derivation and the at-code frame law,
a committed run leaves the account no poorer. The sum premise is universal on
purpose: the compiling run weakens it to endpoint-plus-preservation. -/
theorem Exec.kept_bal_neverFalls {C : ByteArray} {a : Adr} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution} (run : Exec pc sevm pre out)
    (committed : Execution.commits out = true) (code : pre.getCode a = C)
    (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C)
    (sums : ∀ {q : Nat} {s : Sevm} {d : Devm} {o : Execution},
      Exec q s d o → SumNof d.state.bal)
    (at_code : ∀ {q : Nat} {s : Sevm} {d e : Devm}, s.currentTarget = a →
      s.code = C → Exec q s d (.ok e) → (e.getBal a).toNat = (d.getBal a).toNat) :
    (pre.getBal a).toNat ≤ ((Execution.committedPost out committed).getBal a).toNat := by
  revert code
  refine Exec.retained_induction
    (P := fun _ sevm pre out run => pre.getCode a = C →
      ∀ {post : Devm}, out = .ok post → (pre.getBal a).toNat ≤ (post.getBal a).toNat)
    ?_ ?_ ?_ ?_ ?_ run committed
  · intro pc sevm pre out step _ _ code post heq
    -- DRAFT: halt case. `cases out` with `Exec.keptAt, List.not_mem_nil`; the
    -- `.ok` subcase is `Linst`-halt balance stasis, the balance twin of
    -- `Evm.step_halt_getStor` (ExecutionKeptFrames.lean:213, ~30 lines read).
    -- Estimated 20-40 lines.
    sorry
  · intro pc sevm pre pc' post out step next ih code post' heq
    -- DRAFT: continue case. Balance twin of
    -- `Ninst.foreignNone_getStor_eq_neutral` (ExecutionKeptFrames.lean:151,
    -- ~20 lines read) at a foreign target, else `at_code` at `a`; `sums`
    -- covers the credit arithmetic. Estimated 20-40 lines.
    sorry
  · intro pc sevm pre frame resume pc' result post out step enter child resumed next ih code post' heq
    -- DRAFT: settled-child case. `Evm.step_spawn_inv` plus `Xinst.step_spawn_form`
    -- (ExecutionKeptFrames.lean:79, read) for the handoff; `Resume.run` hands
    -- the child's state to the parent (precedent `resume_createAmsterdam_state`,
    -- ExecutionKeptFrames.lean:20, ~30 lines read); child IH below, `ih`-style
    -- continuation above; the at-`a` child contributes itself via `at_code`.
    -- Estimated 40-80 lines.
    sorry
  · intro pc sevm pre frame resume pc' childEvm raw post out step enter child resumed next settles childIH nextIH code post' heq
    -- DRAFT: committed-spawn case. As the settled-child case, plus the entry
    -- credit is zero here (no value moves on resume) and the rolled-back
    -- sibling contributes nothing (`Exec.keptAt, dite_eq_right rolled`,
    -- pattern read in `Exec.keptAt_caller_ne`, ExecutionKeptChain.lean:396).
    -- The rollback-restores clause needs the balance twin of
    -- `ProcessMessage.rollback_of_error` (name unverified: the compiling run
    -- pins it in Jaune's `MessageExecution`). Estimated 40-80 lines.
    sorry
  · intro pc sevm pre frame resume pc' childEvm raw post out step enter child resumed next rolled nextIH code post' heq
    -- DRAFT: rolled-back case. `Exec.keptAt, dite_eq_right rolled,
    -- List.nil_append` (pattern read at ExecutionKeptChain.lean:396): the
    -- child contributes nothing and the state is restored, so this is the
    -- continuation IH alone. Estimated 15-30 lines.
    sorry

/-- **Covers the kept values.** Under the never-falls premises, with every kept
frame's caller away from the account, the post balance covers the pre balance
plus every kept frame's carried value. The caller premise excludes self-calls,
whose value moves from the account to itself. -/
theorem Exec.kept_bal_ge_keptPaid {C : ByteArray} {a : Adr} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution} (run : Exec pc sevm pre out)
    (committed : Execution.commits out = true) (code : pre.getCode a = C)
    (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C)
    (sums : ∀ {q : Nat} {s : Sevm} {d : Devm} {o : Execution},
      Exec q s d o → SumNof d.state.bal)
    (at_code : ∀ {q : Nat} {s : Sevm} {d e : Devm}, s.currentTarget = a →
      s.code = C → Exec q s d (.ok e) → (e.getBal a).toNat = (d.getBal a).toNat)
    (callers : ∀ f ∈ Exec.keptAt a run, f.sevm.caller ≠ a) :
    (pre.getBal a).toNat + Exec.keptPaid a run ≤
      ((Execution.committedPost out committed).getBal a).toNat := by
  revert code callers
  refine Exec.retained_induction
    (P := fun _ sevm pre out run => pre.getCode a = C →
      (∀ f ∈ Exec.keptAt a run, f.sevm.caller ≠ a) →
      ∀ {post : Devm}, out = .ok post →
        (pre.getBal a).toNat + Exec.keptPaid a run ≤ (post.getBal a).toNat)
    ?_ ?_ ?_ ?_ ?_ run committed
  · intro pc sevm pre out step _ _ code callers post heq
    -- DRAFT: halt case. No kept frames (`Exec.keptAt, List.not_mem_nil`), so
    -- `keptPaid` is `0` and this is the never-falls halt leaf above.
    -- Estimated 10-20 lines.
    sorry
  · intro pc sevm pre pc' post out step next ih code callers post' heq
    -- DRAFT: continue case. No kept frame starts here; thread `callers`
    -- through `Exec.keptAt` rewrite (pattern read at
    -- ExecutionKeptChain.lean:354) into the continuation IH.
    -- Estimated 15-30 lines.
    sorry
  · intro pc sevm pre frame resume pc' result post out step enter child resumed next ih code callers post' heq
    -- DRAFT: settled-child case. Split `callers` and `keptPaid` over
    -- `List.mem_append` (pattern read at ExecutionKeptChain.lean:376); the
    -- at-`a` child contributes its carried value by the entry-credit clause
    -- (caller `≠ a`, value lands in `a`: balance twin of
    -- `benvAfterTransfer_ok_getStor`, read in ExecutionKeptFrames.lean:266;
    -- the value-credit form is unwritten). Needs `of_state_transfer_sum`
    -- (LadderBase.lean:317, statement read) under `sums`. Estimated 60-100
    -- lines; this is the critical-path leaf with the foreign-call twin.
    sorry
  · intro pc sevm pre frame resume pc' childEvm raw post out step enter child resumed next settles childIH nextIH code callers post' heq
    -- DRAFT: committed-spawn case. As above on both sides; the at-`a` spawn
    -- itself contributes via `at_code` (equality, so the credit arithmetic
    -- still telescopes). Estimated 40-80 lines.
    sorry
  · intro pc sevm pre frame resume pc' childEvm raw post out step enter child resumed next rolled nextIH code post' heq
    -- DRAFT: rolled-back case. Same `dite_eq_right rolled` reduction as the
    -- never-falls rolled leaf; `keptPaid` of `[] ++ rest` is `rest`'s.
    -- Estimated 15-30 lines.
    sorry

end Blanc
