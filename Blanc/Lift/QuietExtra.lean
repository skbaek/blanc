import Blanc.Lift.Silent
import Blanc.StaticCallStorage
import Blanc.CompiledFixedInvariance
import Blanc.Lift.Quiet

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

end Jaune

namespace Blanc.Lift

open Jaune
open scoped LogOutputHinv

/-! ## Log-list equality through an instruction

`Devm.LogsEq` is the relation "same log list".  The walk below keeps the
instruction's entry machine `d` fixed and carries, for the machine reached so far,
the equation `x.logs = d.logs`; each primitive (all `liftMach`-family or meta-only
updates other than `addLog`) extends that equation, so one combinator set proves
`Execution.Rel Devm.LogsEq` for every non-`LOG` regular instruction. -/

namespace LogsWalk

end LogsWalk

open _root_.Lean _root_.Lean.Meta _root_.Lean.Elab _root_.Lean.Elab.Tactic in
/-! ## Log-list shape of a recursive instruction

`Xinst.ShapeCovered` (`CommonProofs.lean`) keeps only the instruction frame of the machine
handed to the generic call or create, which does not fix the log list.  `Xinst.ShapeLogs`
is the same covered-fork decomposition with the log list in place of the frame. -/

namespace ShapeLogs

end ShapeLogs

/-! ## Log lists across a message frame -/

/-! ## Static execution keeps the log list -/

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
  | .pcAt _ f => f.quiet
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
    (hS : QuietSet fs S = true) {sevm : Sevm} (hfork : ShanghaiOnwards sevm.benvStat.fork)
    {devm : Devm} {f : SFunc} {o : Outcome}
    (hf : f.quiet = true) (hrefs : f.refs.all (· ∈ S) = true)
    (run : SFunc.Run fs sevm devm f o) :
    Devm.getStor (Outcome.devm o) = Devm.getStor devm ∧ (Outcome.devm o).logs = devm.logs := by
  have closed : ∀ {k g}, k ∈ S → fs[k]? = some g →
      g.quiet = true ∧ g.refs.all (· ∈ S) = true := by
    intro k g hk hget
    have h := (List.all_eq_true.mp hS) k hk
    rw [hget] at h
    simpa only [List.all_eq_true, decide_eq_true_eq, Bool.and_eq_true] using h
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
      exact Linst.world_of_ok (by simpa only [ne_eq, quiet, bne_iff_ne] using hf) hrun
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
  | pcAt hrun _ run ih =>
      simp only [SFunc.quiet] at hf
      simp only [SFunc.refs] at hrefs
      exact tr (ih hf hrefs) (Ninst.world_of_quiet (n := .reg .pc) hfork rfl hrun)

end Blanc.Lift
