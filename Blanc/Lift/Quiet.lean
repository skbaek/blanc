import Blanc.Lift.Silent
import Blanc.StaticCallStorage
import Blanc.CompiledFixedInvariance

/-!
# Storage- and log-quiet synthetic trees

`SFunc.silent` (`Silent.lean`) keeps the whole persistent world but excludes every call, so a
view that calls a precompile (the beacon deposit contract's `get_deposit_root`) is not silent.
What such a view does keep is every account's storage and the log list: a `STATICCALL` cannot
write storage or emit a log in any frame it reaches.  `SFunc.quiet` is that weaker property
(no `SSTORE`, no `LOG`, the only call `STATICCALL`), `QuietSet` its closure over entries, and
`SFunc.Run.world_of_quiet` the frame theorem, proved here from two per-step facts
(`Ninst.world_of_quiet`, `Linst.world_of_ok`), which are frozen segments.

Nothing here mentions a contract.
-/

namespace Jaune

/-- A nonterminal instruction that neither writes storage nor emits a log in any frame it
reaches: no `SSTORE`, no `LOG`, and among the calls only `STATICCALL`. -/
def Ninst.quiet : Ninst → Bool
  | .reg .sstore => false
  | .reg (.log _) => false
  | .reg _ => true
  | .exec x => x == .staticcall
  | .push _ _ => true
  | .dupn _ => true
  | .swapn _ => true
  | .exchange _ => true

end Jaune

namespace Blanc.Lift

open Jaune
open scoped LogOutputHinv

lemma Ninst.dupn_logs {imm : UInt8} {sevm : Sevm} {pre post : Devm}
    (run : Ninst.Run sevm pre (.dupn imm) post) : post.logs = pre.logs := by
  rcases run with ⟨xl, -, pc, hrun⟩
  simp only [Ninst.StepRun, Ninst.step_dupn, Step.run_ofExecution] at hrun
  obtain ⟨rfl, hstep⟩ := hrun
  split at hstep
  · rcases Except.bind_eq_ok hstep.symm with ⟨d1, h1, h2⟩
    have hb := (Devm.burn_of_chargeGas h1).logs
    split at h2
    · cases h2
    · split at h2
      · cases h2
      · have hp := (Devm.push_of_push h2).logs
        rw [← hp, hb]
  · cases hstep

lemma Ninst.swapn_logs {imm : UInt8} {sevm : Sevm} {pre post : Devm}
    (run : Ninst.Run sevm pre (.swapn imm) post) : post.logs = pre.logs := by
  rcases run with ⟨xl, -, pc, hrun⟩
  simp only [Ninst.StepRun, Ninst.step_swapn, Step.run_ofExecution] at hrun
  obtain ⟨rfl, hstep⟩ := hrun
  split at hstep
  · rcases Except.bind_eq_ok hstep.symm with ⟨d1, h1, h2⟩
    have hb := (Devm.burn_of_chargeGas h1).logs
    split at h2
    · cases h2
    · split at h2
      · cases h2
      · injection h2 with h2
        rw [← h2]
        exact hb.symm
  · cases hstep

lemma Ninst.exchange_logs {imm : UInt8} {sevm : Sevm} {pre post : Devm}
    (run : Ninst.Run sevm pre (.exchange imm) post) : post.logs = pre.logs := by
  rcases run with ⟨xl, -, pc, hrun⟩
  simp only [Ninst.StepRun, Ninst.step_exchange, Step.run_ofExecution] at hrun
  obtain ⟨rfl, hstep⟩ := hrun
  split at hstep
  · rcases Except.bind_eq_ok hstep.symm with ⟨d1, h1, h2⟩
    have hb := (Devm.burn_of_chargeGas h1).logs
    split at h2
    · cases h2
    · split at h2
      · cases h2
      · injection h2 with h2
        rw [← h2]
        exact hb.symm
  · cases hstep

lemma Rinst.preserves_logs {pc : Nat} {sevm : Sevm} {pre post : Devm} {r : Rinst}
    (hr : ∀ n, r ≠ .log n)
    (run : Rinst.run ⟨pc, sevm, pre⟩ r = .ok post) : post.logs = pre.logs := by
  cases r
  all_goals try (solve | intro n; contradiction | contradiction)
  all_goals try exact (Rinst.Hinv.inv run).symm
  all_goals simp only [Rinst.run, Rinst.runCore] at run
  all_goals with_reducible first
    | exact (Devm.diffBurn_of_applyBinary run).choose_spec.choose_spec.logs.symm
    | exact (Devm.diffBurn_of_applyTernary run).choose_spec.choose_spec.choose_spec.logs.symm
    | exact (Devm.diffBurn_of_applyUnary run).choose_spec.logs.symm
    | exact (Devm.pushBurn_of_pushItem run).logs.symm
  all_goals sorry

-- SEGMENT: ninstWorldOfQuiet
/-- **A quiet step keeps every storage map and the log list.**

Proof sketch.  `.reg r`: storage by `Rinst.preserves_stor` (`r ≠ sstore`); logs by a case split
on `r` — every non-`LOG` `Rinst.run` is a `liftMach…` combinator or a charge-and-push that leaves
`Meta.logs` alone (the `Rinst.*_runCore_instructionFrame` family in `CommonProofs.lean` fixes
all fields but `logs`; strengthen it to `logs` for the non-`LOG` cases).  `.exec .staticcall`:
storage by `Ninst.staticcall_inv_getStor_exact`; logs by the same induction as
`StaticCallStorage.lean` (a static frame's `LOG` cannot complete, and a child's logs are
merged only on success).  `push`/`dupn`/`swapn`/`exchange`: the `effectRec_of_instructionFrame`
lemmas used in `Silent.lean`, with `R := logs` and `getStor`. -/
theorem Ninst.world_of_quiet {sevm : Sevm} {pre post : Devm} {n : Ninst}
    (hfork : CoveredFork sevm.benvStat.fork) (hn : n.quiet = true)
    (run : Ninst.Run sevm pre n post) :
    Devm.getStor post = Devm.getStor pre ∧ post.logs = pre.logs := by
  cases n with
  | push bytes bound =>
      exact ⟨(Ninst.Hinv.inv (f := Devm.getStor) run).symm,
             (Ninst.Hinv.inv (f := Devm.logs) run).symm⟩
  | dupn imm =>
      rcases run with ⟨xl, -, pc, hrun⟩
      have hxl : xl = .none := by
        simp only [Ninst.StepRun, Ninst.step_dupn, Step.run_ofExecution] at hrun
        exact hrun.1
      subst hxl
      have frame := Ninst.dupn_instructionFrame_effectRec (xl := .none) trivial hrun
      exact ⟨(funext (Devm.InstructionFrame.getStor frame)).symm,
             Ninst.dupn_logs ⟨.none, trivial, pc, hrun⟩⟩
  | swapn imm =>
      rcases run with ⟨xl, -, pc, hrun⟩
      have hxl : xl = .none := by
        simp only [Ninst.StepRun, Ninst.step_swapn, Step.run_ofExecution] at hrun
        exact hrun.1
      subst hxl
      have frame := Ninst.swapn_instructionFrame_effectRec (xl := .none) trivial hrun
      exact ⟨(funext (Devm.InstructionFrame.getStor frame)).symm,
             Ninst.swapn_logs ⟨.none, trivial, pc, hrun⟩⟩
  | exchange imm =>
      rcases run with ⟨xl, -, pc, hrun⟩
      have hxl : xl = .none := by
        simp only [Ninst.StepRun, Ninst.step_exchange, Step.run_ofExecution] at hrun
        exact hrun.1
      subst hxl
      have frame := Ninst.exchange_instructionFrame_effectRec (xl := .none) trivial hrun
      exact ⟨(funext (Devm.InstructionFrame.getStor frame)).symm,
             Ninst.exchange_logs ⟨.none, trivial, pc, hrun⟩⟩
  | exec x => sorry
  | reg r => sorry

-- SEGMENT: linstWorldOfOk
/-- **A successful terminal other than `SELFDESTRUCT` keeps every storage map and the log
list.**

Proof sketch.  `Linst.run_instructionFrame` (`Silent.lean`'s `linst_state_of_silent`) gives the
world; `STOP`/`RETURN` set only the output and `REVERT` has no successful run (unfold
`Linst.run`). -/
theorem Linst.world_of_ok {sevm : Sevm} {pre post : Devm} {l : Linst}
    (hl : l ≠ .selfdestruct) (run : Linst.Run sevm pre l (.ok post)) :
    Devm.getStor post = Devm.getStor pre ∧ post.logs = pre.logs := by
  cases l with
  | stop =>
      have hf := Linst.run_instructionFrame sevm pre .stop (by simp)
      rw [run] at hf
      exact ⟨funext (fun a => (hf.getStor a).symm), (Linst.Hinv.inv run).symm⟩
  | return_ =>
      have hf := Linst.run_instructionFrame sevm pre .return_ (by simp)
      rw [run] at hf
      exact ⟨funext (fun a => (hf.getStor a).symm), (Linst.Hinv.inv run).symm⟩
  | revert =>
      simp only [Linst.Run, Linst.run] at run
      cases h : pre.popToNat with
      | error e => simp [h] at run
      | ok x =>
        cases h2 : x.2.popToNat with
        | error e => simp [h, h2] at run
        | ok y =>
          cases h3 : chargeGas (y.2.extCost [(x.1, y.1)]) y.2 with
          | error e => simp [h, h2, h3] at run
          | ok d => simp [h, h2, h3] at run
  | selfdestruct => exact (hl rfl).elim

/-- A synthetic tree whose instructions are quiet and whose terminals are not
`SELFDESTRUCT`. -/
def SFunc.quiet : SFunc → Bool
  | .branch f g => f.quiet && g.quiet
  | .branchTo f _ => f.quiet
  | .last l => l != .selfdestruct
  | .next n f => n.quiet && f.quiet
  | .dest f => f.quiet
  | .jump _ => true
  | .callNext _ f => f.quiet
  | .ret => true
  | .undefined => true

/-- `S` is closed under the entries referenced by its members, and all of them are quiet. -/
def QuietSet (fs : List SFunc) (S : List Nat) : Bool :=
  S.all fun k => match fs[k]? with
    | some g => g.quiet && g.refs.all (· ∈ S)
    | none => false

theorem PopBurn.world {ws : List B256} {a b : Devm} (h : Devm.PopBurn ws a b) :
    Devm.getStor b = Devm.getStor a ∧ b.logs = a.logs :=
  ⟨funext fun x => Devm.PopBurn.getStor h x, h.logs.symm⟩

theorem Burn.world {a b : Devm} (h : Devm.Burn a b) :
    Devm.getStor b = Devm.getStor a ∧ b.logs = a.logs := by
  refine ⟨funext fun x => ?_, h.logs.symm⟩
  exact getStor_eq_of_state_eq h.state.symm x

/-- **The quiet frame theorem**: a run of a quiet tree whose gotos and calls stay in a
`QuietSet` keeps every storage map and the log list. -/
theorem SFunc.Run.world_of_quiet {fs : List SFunc} {S : List Nat}
    (hS : QuietSet fs S = true) {sevm : Sevm} (hfork : CoveredFork sevm.benvStat.fork)
    {devm : Devm} {f : SFunc} {o : Outcome}
    (hf : f.quiet = true) (hrefs : f.refs.all (· ∈ S) = true)
    (run : SFunc.Run fs sevm devm f o) :
    Devm.getStor (Outcome.devm o) = Devm.getStor devm ∧ (Outcome.devm o).logs = devm.logs := by
  have closed : ∀ {k g}, k ∈ S → fs[k]? = some g →
      g.quiet = true ∧ g.refs.all (· ∈ S) = true := by
    intro k g hk hget
    have h := (List.all_eq_true.mp hS) k hk
    rw [hget] at h
    simpa using h
  have tr : ∀ {a b c : Devm}, (Devm.getStor c = Devm.getStor b ∧ c.logs = b.logs) →
      (Devm.getStor b = Devm.getStor a ∧ b.logs = a.logs) →
      Devm.getStor c = Devm.getStor a ∧ c.logs = a.logs :=
    fun h1 h2 => ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
  induction run with
  | zero d pop run ih =>
      simp only [SFunc.quiet, Bool.and_eq_true] at hf
      simp only [SFunc.refs, List.all_append, Bool.and_eq_true] at hrefs
      exact tr (ih hf.1 hrefs.1) (PopBurn.world pop)
  | succ d w hnz pop run ih =>
      simp only [SFunc.quiet, Bool.and_eq_true] at hf
      simp only [SFunc.refs, List.all_append, Bool.and_eq_true] at hrefs
      exact tr (ih hf.2 hrefs.2) (PopBurn.world pop)
  | toZero d pop run ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      exact tr (ih hf hrefs.2) (PopBurn.world pop)
  | toSucc d w hnz lookup pop run ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      have ht := closed (of_decide_eq_true hrefs.1) lookup
      exact tr (ih ht.1 ht.2) (PopBurn.world pop)
  | last hrun =>
      exact Linst.world_of_ok (by simpa [SFunc.quiet] using hf) hrun
  | next hrun run ih =>
      simp only [SFunc.quiet, Bool.and_eq_true] at hf
      exact tr (ih hf.2 hrefs) (Ninst.world_of_quiet hfork hf.1 hrun)
  | dest burn run ih =>
      exact tr (ih hf hrefs) (Burn.world burn)
  | jump d lookup pop run ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      have ht := closed (of_decide_eq_true hrefs.1) lookup
      exact tr (ih ht.1 ht.2) (PopBurn.world pop)
  | ret d pop =>
      exact PopBurn.world pop
  | callHalt d lookup pop run ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      have ht := closed (of_decide_eq_true hrefs.1) lookup
      exact tr (ih ht.1 ht.2) (PopBurn.world pop)
  | callRet d lookup pop run tail ihRun ihTail =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      have ht := closed (of_decide_eq_true hrefs.1) lookup
      simp only [SFunc.quiet] at hf
      exact tr (ihTail hf hrefs.2) (tr (ihRun ht.1 ht.2) (PopBurn.world pop))

end Blanc.Lift
