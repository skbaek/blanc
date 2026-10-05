import Blanc.Lift.StaticCall
import Jaune.MessageExecution

/-!
# A callee that fails on every input

`revertingCode` is the three-byte runtime `PUSH0 PUSH0 REVERT`. Every frame that starts at
program counter zero over it ends in an error, whatever its machine state, calldata or gas:
each `PUSH0` either charges `G_base` and continues or halts out of gas, and the closing
`REVERT` never returns `.ok` (`revertingCode_exec_error`).

Consequently no ordinary message whose code is `revertingCode` and whose code address is not
a precompile settles cleanly (`processMessage_not_clean_of_reverting`), and no static child
message to an account holding that code answers (`not_staticAnswered_of_reverting`). The
second fact is the one a caller's `STATICCALL` inversion (`ri_staticcall`) consumes: a set
success flag there is exactly a `StaticAnswered` witness.

Two step-level facts serve later queries and calls: any successful instruction step keeps
`revertingCode` installed (`revertingCode_kept`, since no step rewrites nonempty code), and a
`CALL` to it never leaves the success flag (`call_flag_ne_one_of_reverting`).

These are adverse-callee facts at EVM altitude: universal over the child's derivation, with a
concrete callee code. Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-- `PUSH0 PUSH0 REVERT`: revert with empty return data on every input. -/
def revertingCode : ByteArray := ⟨#[0x5f, 0x5f, 0xfd]⟩

/-- A non-spawning step that is an `Execution` outcome either halts the whole derivation with
that error or continues it at the next counter. -/
theorem Exec.ofExecution_inv {pc pc' : Nat} {sevm : Sevm} {devm : Devm} {ex raw : Execution}
    (run : Exec pc sevm devm raw) (step : Evm.step ⟨pc, sevm, devm⟩ = Step.ofExecution pc' ex) :
    (∃ e, raw = .error e) ∨ ∃ d, Nonempty (Exec pc' sevm d raw) := by
  cases ex with
  | error e => exact .inl ⟨e, run.halt_inv step⟩
  | ok d =>
    refine .inr ⟨d, ?_⟩
    cases run with
    | halt h => rw [step] at h; cases h
    | cont h next => rw [step] at h; cases h; exact ⟨next⟩
    | doneErr h _ _ => rw [step] at h; cases h
    | doneOk h _ _ _ => rw [step] at h; cases h
    | runErr h _ _ _ => rw [step] at h; cases h
    | runOk h _ _ _ _ => rw [step] at h; cases h

/-- Every frame at `revertingCode`, started at program counter zero, ends in an error. -/
theorem revertingCode_exec_error {sevm : Sevm} {devm : Devm} {raw : Execution}
    (codeEq : sevm.code = revertingCode) (run : Exec 0 sevm devm raw) :
    ∃ e, raw = .error e := by
  have at0 : Ninst.At sevm.code 0 (.push [] (by decide)) := by rw [codeEq]; rfl
  have at1 : Ninst.At sevm.code 1 (.push [] (by decide)) := by rw [codeEq]; rfl
  have at2 : Linst.At sevm.code 2 .revert := by rw [codeEq]; rfl
  rcases Exec.ofExecution_inv run (by rw [Evm.step_next at0, Ninst.step_push]) with
    done | ⟨d1, ⟨run1⟩⟩
  · exact done
  change Exec 1 sevm d1 raw at run1
  rcases Exec.ofExecution_inv run1 (by rw [Evm.step_next at1, Ninst.step_push]) with
    done | ⟨d2, ⟨run2⟩⟩
  · exact done
  change Exec 2 sevm d2 raw at run2
  rw [run2.last_inv at2]
  cases ran : Linst.run sevm d2 .revert with
  | error e => exact ⟨e, rfl⟩
  | ok post =>
    simp only [Linst.run] at ran
    rcases Except.bind_eq_ok ran with ⟨_, _, ran⟩
    rcases Except.bind_eq_ok ran with ⟨_, _, ran⟩
    rcases Except.bind_eq_ok ran with ⟨_, _, ran⟩
    contradiction

/-- An ordinary message over `revertingCode`, whose code address is not a precompile, never
settles cleanly: a failed transfer settles as an error, and an entered frame runs the code. -/
theorem processMessage_not_clean_of_reverting {msg : Msg} {xl : Xlot} {child : Devm} {t : Adr}
    (codeAddress : msg.codeAddress = some t) (codeEq : msg.code = revertingCode)
    (notPrecompile : ¬ msg.benv.stat.rules.isPrecomp t) (filled : xl.Filled)
    (process : ProcessMessage msg xl (.ok child)) :
    ¬ child.error.isSome = false := by
  intro clean
  cases transfer : msg.benvAfterTransfer with
  | error e =>
    have enter : (Frame.ofCall msg).enter =
        .done ((Frame.ofCall msg).settleMsg (.error e)) := by
      unfold Frame.enter Frame.ofCall
      rw [transfer]
    unfold ProcessMessage RunFrame at process
    rw [enter] at process
    cases process.2
  | ok benv =>
    have stat := benvAfterTransfer_stat transfer
    have enter := MessageExecution.frameEnter_eq_run_afterTransfer_of_notPrecompile msg benv t
      transfer codeAddress (by rw [stat]; exact notPrecompile)
    unfold ProcessMessage RunFrame at process
    rw [enter] at process
    obtain ⟨raw, slot, settled⟩ := process
    subst slot
    obtain ⟨run⟩ := filled
    obtain ⟨e, rawEq⟩ := revertingCode_exec_error (codeEq := codeEq) run
    have commits := Frame.raw_commits_of_settlementCommits
      (ProcessMessage.settlementCommits_of_some_ok_clean
        (pc := 0) (sevm := initSevm (msg.withBenv benv)) (pre := initDevm (msg.withBenv benv))
        (by unfold ProcessMessage RunFrame; rw [enter]; exact ⟨raw, rfl, settled⟩) clean)
    rw [rawEq] at commits
    cases commits

/-- No static child message to an account holding `revertingCode`, outside the precompile
range, answers: the code is not a delegation designator, so the child runs it. -/
theorem not_staticAnswered_of_reverting {sevm : Sevm} {b : Devm} {t : Adr} {input out : Bytes}
    (codeEq : b.getCode t = revertingCode) (notPrecompile : ¬ sevm.benvStat.rules.isPrecomp t) :
    ¬ StaticAnswered sevm b t input out := by
  rintro ⟨_, child, xl, dp, na, code, gas, _, delegation, filled, process, clean, _⟩
  rcases delegation with ⟨_, naEq, codeIs, dpEq⟩ | ⟨d, designated, _, _, _⟩
  · subst naEq codeIs dpEq
    exact processMessage_not_clean_of_reverting rfl codeEq notPrecompile filled process clean
  · rw [codeEq] at designated
    cases designated

/-- Any successful instruction step keeps `revertingCode` where it is installed: the code is
nonempty, and no step ever rewrites nonempty code (`Ninst.codePreserve_effectRec`). -/
theorem revertingCode_kept {sevm : Sevm} {pre post : Devm} {n : Ninst} {t : Adr}
    (run : Ninst.Run sevm pre n post) (codeEq : pre.getCode t = revertingCode) :
    post.getCode t = revertingCode := by
  have kept := Ninst.effect_of_effectRec codePreserve_refl_trans.1 codePreserve_refl_trans.2
    Ninst.codePreserve_effectRec Jinst.codePreserve_effect Linst.codePreserve_effect n run t
    (by rw [codeEq, ByteArray.toList_eq_toList_data]; decide)
  rw [kept, codeEq]

/-- A `CALL` to an account holding `revertingCode`, outside the precompile range, never leaves
the success flag `1`: either no child is entered, or the entered child runs the code and
cannot settle cleanly. -/
theorem call_flag_ne_one_of_reverting {sevm : Sevm} {b d : Devm} {S T : List B256} {M : Mem}
    {G : Nat} {g c v ii is oi os : B256}
    (codeEq : b.getCode c.toAdr = revertingCode)
    (notPrecompile : ¬ sevm.benvStat.rules.isPrecomp c.toAdr)
    (hfork : CoveredFork sevm.benvStat.fork)
    (h : Ninst.Run sevm (St b (g :: c :: v :: ii :: is :: oi :: os :: S) M G) (.exec .call) d) :
    d.stack ≠ 1 :: T := by
  intro stack
  have operands : (g :: c :: v :: ii :: is :: oi :: os :: S) <<+
      (St b (g :: c :: v :: ii :: is :: oi :: os :: S) M G).stack := by
    simpa only [List.append_nil, St.stack] using
      (pref_append (g :: c :: v :: ii :: is :: oi :: os :: S) [])
  rcases of_run_call_val_with_depth_frame operands h hfork with failed | entered
  · rw [stack] at failed
    exact absurd (pref_head_unique failed.1 (pref_append [1] T)) (by decide)
  · obtain ⟨_, child, xl, dp, na, code, _, _, _, _, _, _, _, _, _, delegation, filled, process,
      clean, _⟩ := entered
    rcases delegation with ⟨_, naEq, codeIs, dpEq⟩ | ⟨e, designated, _, _, _⟩
    · subst naEq codeIs dpEq
      exact processMessage_not_clean_of_reverting rfl codeEq notPrecompile filled process clean
    · change getDelegatedCodeAddress (b.getCode c.toAdr) = some e at designated
      rw [codeEq] at designated
      cases designated

end Blanc.Lift
