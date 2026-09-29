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

/-! ## Log-list equality through an instruction

`Devm.LogsEq` is the relation "same log list".  The walk below keeps the
instruction's entry machine `d` fixed and carries, for the machine reached so far,
the equation `x.logs = d.logs`; each primitive (all `liftMach`-family or meta-only
updates other than `addLog`) extends that equation, so one combinator set proves
`Execution.Rel Devm.LogsEq` for every non-`LOG` regular instruction. -/

/-- The two machines carry the same log list. -/
def Devm.LogsEq (a b : Devm) : Prop := a.logs = b.logs

namespace LogsWalk

lemma ofMach {x : Devm} {e : Execution} (h : Execution.Rel Devm.MachFrame x e) :
    Execution.Rel Devm.LogsEq x e := by
  cases e <;> exact h.logs

lemma ofMachP {α : Type} {x : Devm} {o : Except (EvmError × Devm) (α × Devm)}
    (h : Outcome.Rel Prod.snd Prod.snd Devm.MachFrame x o) :
    Outcome.Rel Prod.snd Prod.snd Devm.LogsEq x o := by
  cases o <;> exact h.logs

/-- Close a walk on a sub-execution related to the current machine. -/
lemma leaf {d x : Devm} {e : Execution} (hx : x.logs = d.logs)
    (h : Execution.Rel Devm.LogsEq x e) : Execution.Rel Devm.LogsEq d e := by
  cases e <;> exact hx.symm.trans h

lemma ok {d x : Devm} (hx : x.logs = d.logs) :
    Execution.Rel Devm.LogsEq d (.ok x) := hx.symm

lemma err {d : Devm} {e : EvmError × Devm} (hx : e.2.logs = d.logs) :
    Execution.Rel Devm.LogsEq d (.error e) := hx.symm

lemma bindE {d x : Devm} {e : Execution} {f : Devm → Execution}
    (hx : x.logs = d.logs) (h : Execution.Rel Devm.LogsEq x e)
    (hf : ∀ y : Devm, y.logs = d.logs → Execution.Rel Devm.LogsEq d (f y)) :
    Execution.Rel Devm.LogsEq d (e >>= f) := by
  cases e with
  | error e => exact hx.symm.trans h
  | ok y => exact hf y ((Eq.trans hx.symm h).symm)

lemma bindP {α : Type} {d x : Devm} {o : Except (EvmError × Devm) (α × Devm)}
    {f : α × Devm → Execution}
    (hx : x.logs = d.logs) (h : Outcome.Rel Prod.snd Prod.snd Devm.LogsEq x o)
    (hf : ∀ (v : α) (y : Devm), y.logs = d.logs →
      Execution.Rel Devm.LogsEq d (f (v, y))) :
    Execution.Rel Devm.LogsEq d (o >>= f) := by
  cases o with
  | error e => exact hx.symm.trans h
  | ok p => exact hf p.1 p.2 ((Eq.trans hx.symm h).symm)

lemma bindU {d x : Devm} {u : Except (EvmError × Devm) Unit} {f : Unit → Execution}
    (hx : x.logs = d.logs) (hu : ∀ e, u = .error e → e.2.logs = x.logs)
    (hf : Execution.Rel Devm.LogsEq d (f ())) :
    Execution.Rel Devm.LogsEq d (u >>= f) := by
  cases u with
  | error e => exact ((hu e rfl).trans hx).symm
  | ok v => exact hf

lemma bindOk {α : Type} {d : Devm} {a : α} {f : α → Execution}
    (h : Execution.Rel Devm.LogsEq d (f a)) :
    Execution.Rel Devm.LogsEq d ((Except.ok a : Except (EvmError × Devm) α) >>= f) := h

lemma bindErr {α : Type} {d : Devm} {e : EvmError × Devm} {f : α → Execution}
    (h : e.2.logs = d.logs) :
    Execution.Rel Devm.LogsEq d ((Except.error e : Except (EvmError × Devm) α) >>= f) :=
  h.symm

lemma bindSnd {α : Type} {d x : Devm} {o : Except (EvmError × Devm) (α × Devm)}
    {f : Devm → Execution}
    (hx : x.logs = d.logs) (h : Outcome.Rel Prod.snd Prod.snd Devm.LogsEq x o)
    (hf : ∀ y : Devm, y.logs = d.logs → Execution.Rel Devm.LogsEq d (f y)) :
    Execution.Rel Devm.LogsEq d ((o <&> Prod.snd) >>= f) := by
  cases o with
  | error e => exact hx.symm.trans h
  | ok p => exact hf p.2 ((Eq.trans hx.symm h).symm)

lemma assert_err {p : Prop} [Decidable p] {err : EvmError × Devm} :
    ∀ e, Except.assert p err = .error e → e.2.logs = err.2.logs := by
  intro e h
  unfold Except.assert at h
  split at h
  · cases h
  · cases h; rfl

lemma assertDynamic_err {sevm : Sevm} {x : Devm} :
    ∀ e, assertDynamic sevm x = .error e → e.2.logs = x.logs :=
  assert_err

lemma pop (x : Devm) : Outcome.Rel Prod.snd Prod.snd Devm.LogsEq x x.pop :=
  ofMachP (Devm.pop_machFrame x)

lemma popToNat (x : Devm) :
    Outcome.Rel Prod.snd Prod.snd Devm.LogsEq x x.popToNat :=
  ofMachP (Devm.popToNat_machFrame x)

lemma popToAdr (x : Devm) :
    Outcome.Rel Prod.snd Prod.snd Devm.LogsEq x x.popToAdr :=
  ofMachP (Devm.popToAdr_machFrame x)

lemma popN (x : Devm) (n : Nat) :
    Outcome.Rel Prod.snd Prod.snd Devm.LogsEq x (x.popN n) :=
  ofMachP (Devm.popN_machFrame x n)

lemma push (v : B256) (x : Devm) : Execution.Rel Devm.LogsEq x (x.push v) :=
  ofMach (Devm.push_machFrame v x)

lemma pushItem (v : B256) (c : Nat) (x : Devm) :
    Execution.Rel Devm.LogsEq x (Jaune.pushItem v c x) :=
  ofMach (pushItem_machFrame v c x)

lemma chargeGas (c : Nat) (x : Devm) :
    Execution.Rel Devm.LogsEq x (Jaune.chargeGas c x) :=
  ofMach (chargeGas_machFrame c x)

lemma chargeStateGas (c : Nat) (x : Devm) :
    Execution.Rel Devm.LogsEq x (Jaune.chargeStateGas c x) :=
  ofMach (liftMachExecution_machFrame (Mach.chargeStateGas c) x)

lemma applyUnary (f : B256 → B256) (c : Nat) (x : Devm) :
    Execution.Rel Devm.LogsEq x (Jaune.applyUnary f c x) :=
  ofMach (applyUnary_machFrame f c x)

lemma applyBinary (f : B256 → B256 → B256) (c : Nat) (x : Devm) :
    Execution.Rel Devm.LogsEq x (Jaune.applyBinary f c x) :=
  ofMach (applyBinary_machFrame f c x)

lemma applyTernary (f : B256 → B256 → B256 → B256) (c : Nat) (x : Devm) :
    Execution.Rel Devm.LogsEq x (Jaune.applyTernary f c x) :=
  ofMach (applyTernary_machFrame f c x)

lemma balance (rules : ForkRules) (x : Devm) :
    Execution.Rel Devm.LogsEq x
      (liftMachMetaWorldExecution (Rinst.balanceCore rules) x) := by
  have hcore : Outcome.Rel (fun e => e.2.2.logs) (fun v => v.2.2.logs) Eq x.meta.logs
      (Rinst.balanceCore rules x.world x.mach x.meta) := by
    unfold Rinst.balanceCore
    split
    · rfl
    · dsimp only
      split
      · split <;> rfl
      · split <;> split <;> split <;> rfl
  unfold liftMachMetaWorldExecution liftMachMetaExecution liftMachMeta
    Footprint.toExecution Footprint.liftOutcome
  dsimp only
  rcases h : Rinst.balanceCore rules x.world x.mach x.meta with ⟨err, view⟩ | ⟨v, view⟩ <;>
    rw [h] at hcore <;> exact hcore

/-- The meta-only and machine-only pure updates that leave the log list alone. -/
theorem addAccessedAddress_logs (x : Devm) (a : Adr) :
    (addAccessedAddress x a).logs = x.logs := rfl
theorem addAccessedStorageKey_logs (x : Devm) (a : Adr) (k : B256) :
    (addAccessedStorageKey x a k).logs = x.logs := rfl
theorem memWrite_logs (x : Devm) (i : Nat) (v : Bytes) :
    (x.memWrite i v).logs = x.logs := rfl
theorem memExtends_logs (x : Devm) (r : List (Nat × Nat)) :
    (x.memExtends r).logs = x.logs := rfl
theorem withStack_logs (x : Devm) (s : List B256) : (x.withStack s).logs = x.logs := rfl
theorem withReturnData_logs (x : Devm) (r : Bytes) :
    (x.withReturnData r).logs = x.logs := rfl
theorem withGasLeft_logs (x : Devm) (g : Nat) : (x.withGasLeft g).logs = x.logs := rfl
theorem setTransVal_logs (x : Devm) (a : Adr) (k v : B256) :
    (x.setTransVal a k v).logs = x.logs := rfl
theorem balReadStorage_logs (rules : ForkRules) (a : Adr) (k : B256) (x : Devm) :
    (x.balReadStorage rules a k).logs = x.logs := by
  unfold Devm.balReadStorage Meta.readStorage; split <;> rfl

end LogsWalk

/-- Close a log-list side goal `x.logs = d.logs` from the walk's carried equations. -/
syntax "logs_close" : tactic
macro_rules
  | `(tactic| logs_close) => `(tactic| first
      | assumption
      | rfl
      | (simp only [LogsWalk.addAccessedAddress_logs, LogsWalk.addAccessedStorageKey_logs,
          LogsWalk.memWrite_logs, LogsWalk.memExtends_logs, LogsWalk.withStack_logs,
          LogsWalk.withReturnData_logs, LogsWalk.withGasLeft_logs, LogsWalk.setTransVal_logs,
          LogsWalk.balReadStorage_logs, Devm.balReadAccount_logs, Devm.memRead_logs, *]
         <;> done))

/-- Discharge the walk's pending `?hx` side goal. -/
macro "logs_hx" : tactic => `(tactic| (case hx => logs_close))

/-- Enter a bind continuation: introduce its value, machine and carried equation. -/
macro "logs_enter" : tactic => `(tactic| (intro _ _ _; try dsimp only))

/-- Enter a bind continuation on an execution: its machine and carried equation. -/
macro "logs_enterE" : tactic => `(tactic| (intro _ _; try dsimp only))

/-- Close the goal with a sub-execution lemma `t` for the current machine. -/
macro "logs_leaf " t:term : tactic =>
  `(tactic| (refine LogsWalk.leaf ?hx $t; (case hx => logs_close)))

/-- Enter a bind whose first computation, related by `t`, returns a value and a machine. -/
macro "logs_bindP " t:term : tactic =>
  `(tactic| (refine LogsWalk.bindP ?hx $t ?_; logs_hx; logs_enter))

/-- Enter a bind whose first computation, related by `t`, is an execution. -/
macro "logs_bindE " t:term : tactic =>
  `(tactic| (refine LogsWalk.bindE ?hx $t ?_; logs_hx; logs_enterE))

/-- Enter a bind whose first computation is `x.pop` with its value dropped. -/
macro "logs_bindSnd" : tactic =>
  `(tactic| (refine LogsWalk.bindSnd ?hx (LogsWalk.pop _) ?_; logs_hx; logs_enterE))

/-- Enter a bind past a unit-valued check whose failure keeps the machine `t` is about. -/
macro "logs_bindU " t:term : tactic =>
  `(tactic| (refine LogsWalk.bindU ?hx $t ?_; (case hx => logs_close)))

open _root_.Lean _root_.Lean.Meta _root_.Lean.Elab _root_.Lean.Elab.Tactic in
/-- One step of the log walk on a goal `Execution.Rel Devm.LogsEq d e`, chosen by the head
symbol of `e` (or, for a bind, of its first computation), so that no alternative is tried
by unification. -/
elab "logs_step" : tactic => do
  let tgt ← instantiateMVars (← getMainTarget)
  let args := tgt.getAppArgs
  unless tgt.isAppOf ``Execution.Rel && args.size == 3 do
    throwError "logs_step: not an `Execution.Rel` goal"
  let e := args[2]!
  let run (stx : TacticM (TSyntax `tactic)) : TacticM Unit := do evalTactic (← stx)
  if e.isAppOfArity ``Bind.bind 6 then
    match (e.getArg! 4).getAppFn.constName? with
    | some ``Except.ok => run `(tactic| (refine LogsWalk.bindOk ?_; try dsimp only))
    | some ``Except.error =>
        run `(tactic| (refine LogsWalk.bindErr ?hx; (case hx => logs_close)))
    | some ``Devm.pop => run `(tactic| logs_bindP (LogsWalk.pop _))
    | some ``Devm.popToNat => run `(tactic| logs_bindP (LogsWalk.popToNat _))
    | some ``Devm.popToAdr => run `(tactic| logs_bindP (LogsWalk.popToAdr _))
    | some ``Devm.popN => run `(tactic| logs_bindP (LogsWalk.popN _ _))
    | some ``Jaune.chargeGas => run `(tactic| logs_bindE (LogsWalk.chargeGas _ _))
    | some ``Jaune.chargeStateGas => run `(tactic| logs_bindE (LogsWalk.chargeStateGas _ _))
    | some ``Devm.push => run `(tactic| logs_bindE (LogsWalk.push _ _))
    | some ``Functor.mapRev => run `(tactic| logs_bindSnd)
    | some ``Jaune.assertDynamic => run `(tactic| logs_bindU LogsWalk.assertDynamic_err)
    | some ``Except.assert => run `(tactic| logs_bindU LogsWalk.assert_err)
    | _ => run `(tactic| split)
  else
    match e.getAppFn.constName? with
    | some ``Devm.push => run `(tactic| logs_leaf (LogsWalk.push _ _))
    | some ``Jaune.pushItem => run `(tactic| logs_leaf (LogsWalk.pushItem _ _ _))
    | some ``Jaune.chargeGas => run `(tactic| logs_leaf (LogsWalk.chargeGas _ _))
    | some ``Jaune.chargeStateGas => run `(tactic| logs_leaf (LogsWalk.chargeStateGas _ _))
    | some ``Jaune.applyUnary => run `(tactic| logs_leaf (LogsWalk.applyUnary _ _ _))
    | some ``Jaune.applyBinary => run `(tactic| logs_leaf (LogsWalk.applyBinary _ _ _))
    | some ``Jaune.applyTernary => run `(tactic| logs_leaf (LogsWalk.applyTernary _ _ _))
    | some ``Jaune.liftMachMetaWorldExecution =>
        run `(tactic| logs_leaf (LogsWalk.balance _ _))
    | some ``Except.ok => run `(tactic| (refine LogsWalk.ok ?hx; (case hx => logs_close)))
    | some ``Except.error => run `(tactic| (refine LogsWalk.err ?hx; (case hx => logs_close)))
    | _ => run `(tactic| split)

/-- **Every regular instruction other than `LOG` and `SSTORE` keeps the log list**, on
both outcomes: one log walk over every `Rinst.runCore` arm. -/
theorem Rinst.logsEffect {r : Rinst} (hr : ∀ n, r ≠ .log n) (hs : r ≠ .sstore) :
    Rinst.Effect Devm.LogsEq r := by
  intro pc sevm pre out hrun
  subst hrun
  cases r
  case log n => exact absurd rfl (hr n)
  case sstore => exact absurd rfl hs
  all_goals simp only [Rinst.run, Rinst.runCore]
  all_goals repeat' logs_step

/-- A successful regular instruction other than `LOG` keeps the log list. -/
theorem Rinst.logs_of_ok {r : Rinst} (hr : ∀ n, r ≠ .log n) {pc : Nat} {sevm : Sevm}
    {pre post : Devm} (run : Rinst.run ⟨pc, sevm, pre⟩ r = .ok post) :
    post.logs = pre.logs := by
  by_cases hs : r = .sstore
  · subst hs
    exact (Rinst.Hinv.inv (f := Devm.logs) run).symm
  · exact (Rinst.logsEffect hr hs run).symm

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

/-! ## Log-list shape of a recursive instruction

`Xinst.ShapeCovered` (`CommonProofs.lean`) keeps only the instruction frame of the machine
handed to the generic call or create, which does not fix the log list.  `Xinst.ShapeLogs`
is the same covered-fork decomposition with the log list in place of the frame. -/

/-- On a covered fork an executable step either finishes with an execution that keeps the
log list, or hands a machine with the entry log list to a generic call, or (only when
`creates` holds) to a generic create. -/
def Xinst.ShapeLogs (sevm : Sevm) (devm : Devm) (creates : Prop) (s : XStep) : Prop :=
  (∃ ex, s = .done ex ∧ Execution.Rel Devm.LogsEq devm ex) ∨
  (creates ∧ ∃ d endowment newAddress mi ms, d.logs = devm.logs ∧
      s = genericCreate.step sevm d endowment newAddress mi ms) ∨
  (∃ d gas value caller target codeAddress stv isSt ii isz oi osz code dp,
      d.logs = devm.logs ∧
      s = genericCall.step sevm d gas value caller target codeAddress stv isSt
        ii isz oi osz code dp)

namespace ShapeLogs

lemma error {c : Prop} {sevm : Sevm} {devm : Devm} {err : EvmError × Devm}
    (h : err.2.logs = devm.logs) :
    Xinst.ShapeLogs sevm devm c (XStep.ofExcept (.error err)) :=
  Or.inl ⟨_, rfl, h.symm⟩

lemma create {c : Prop} {sevm : Sevm} {devm d : Devm} {endowment : B256} {newAddress : Adr}
    {mi ms : Nat} (hc : c) (hf : d.logs = devm.logs) :
    Xinst.ShapeLogs sevm devm c (genericCreate.step sevm d endowment newAddress mi ms) :=
  Or.inr (Or.inl ⟨hc, d, endowment, newAddress, mi, ms, hf, rfl⟩)

lemma call {c : Prop} {sevm : Sevm} {devm d : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv isSt : Bool} {ii isz oi osz : Nat}
    {code : ByteArray} {dp : Bool} (hf : d.logs = devm.logs) :
    Xinst.ShapeLogs sevm devm c
      (genericCall.step sevm d gas value caller target codeAddress stv isSt
        ii isz oi osz code dp) :=
  Or.inr (Or.inr ⟨d, gas, value, caller, target, codeAddress, stv, isSt, ii, isz, oi,
    osz, code, dp, hf, rfl⟩)

lemma bind {c : Prop} {sevm : Sevm} {devm d : Devm} {α : Type}
    {x : Except (EvmError × Devm) (α × Devm)}
    {f : α × Devm → Except (EvmError × Devm) XStep}
    (hd : d.logs = devm.logs) (hx : Outcome.Rel Prod.snd Prod.snd Devm.LogsEq d x)
    (hf : ∀ (v : α) (d' : Devm), d'.logs = devm.logs →
      Xinst.ShapeLogs sevm devm c (XStep.ofExcept (f ⟨v, d'⟩))) :
    Xinst.ShapeLogs sevm devm c (XStep.ofExcept (x >>= f)) := by
  rcases x with e | ⟨v, d'⟩
  · exact error (Eq.trans hx.symm hd)
  · exact hf v d' (Eq.trans hx.symm hd)

lemma bindE {c : Prop} {sevm : Sevm} {devm d : Devm} {x : Execution}
    {f : Devm → Except (EvmError × Devm) XStep}
    (hd : d.logs = devm.logs) (hx : Execution.Rel Devm.LogsEq d x)
    (hf : ∀ d' : Devm, d'.logs = devm.logs →
      Xinst.ShapeLogs sevm devm c (XStep.ofExcept (f d'))) :
    Xinst.ShapeLogs sevm devm c (XStep.ofExcept (x >>= f)) := by
  rcases x with e | d'
  · exact error (Eq.trans hx.symm hd)
  · exact hf d' (Eq.trans hx.symm hd)

lemma assert {c : Prop} {sevm : Sevm} {devm : Devm} {p : Prop} [Decidable p]
    {err : EvmError × Devm} {f : Unit → Except (EvmError × Devm) XStep}
    (herr : err.2.logs = devm.logs)
    (hf : Xinst.ShapeLogs sevm devm c (XStep.ofExcept (f ()))) :
    Xinst.ShapeLogs sevm devm c (XStep.ofExcept (Except.assert p err >>= f)) := by
  unfold Except.assert
  split
  · exact hf
  · exact error herr

lemma shortfall {c : Prop} {sevm : Sevm} {devm d : Devm} {stipend : Nat}
    (hf : d.logs = devm.logs) :
    Xinst.ShapeLogs sevm devm c
      (XStep.ofExcept
        (d.push 0 >>= fun d' =>
          .ok (XStep.done (.ok ((d'.withReturnData []).withGasLeft
            (d'.gasLeft + stipend)))))) := by
  refine bindE hf (LogsWalk.push 0 d) fun d' hf' => ?_
  exact Or.inl ⟨_, rfl, hf'.symm⟩

lemma shortfall' {c : Prop} {sevm : Sevm} {devm d : Devm} {stipend : Nat}
    (hf : d.logs = devm.logs) :
    Xinst.ShapeLogs sevm devm c
      (XStep.ofExcept
        (d.push 0 >>= fun d' =>
          .ok (XStep.done (.ok ((d'.withGasLeft
            (d'.gasLeft + stipend)).withReturnData []))))) := by
  refine bindE hf (LogsWalk.push 0 d) fun d' hf' => ?_
  exact Or.inl ⟨_, rfl, hf'.symm⟩

lemma delegation {gas : GasSchedule} {devm x : Devm} {adr : Adr} {dp : Bool} {na : Adr}
    {code : ByteArray} {dg : Nat} {d : Devm}
    (hx : x.logs = devm.logs)
    (hdel : gas.accessDelegation x adr = ⟨dp, na, code, dg, d⟩) :
    d.logs = devm.logs := by
  have h := GasSchedule.accessDelegation_logs (gas := gas) (devm := x) (adr := adr)
  rw [hdel] at h
  exact h.trans hx

end ShapeLogs

/-- **Every executable instruction on a covered fork has a log-list shape.** -/
lemma Xinst.step_shapeLogs (sevm : Sevm) (devm : Devm) (x : Xinst)
    (hfork : CoveredFork sevm.benvStat.fork) :
    Xinst.ShapeLogs sevm devm (x = .create ∨ x = .create2) (Xinst.step sevm devm x) := by
  have hsg : sevm.benvStat.rules.stateGas = none := hfork.rules_stateGas_none
  cases x with
  | create =>
    simp only [Xinst.step, hsg]
    refine ShapeLogs.bind rfl (LogsWalk.pop devm) fun _ d1 h1 => ?_
    refine ShapeLogs.bind h1 (LogsWalk.popToNat d1) fun _ d2 h2 => ?_
    refine ShapeLogs.bind h2 (LogsWalk.popToNat d2) fun _ d3 h3 => ?_
    refine ShapeLogs.bindE h3 (LogsWalk.chargeGas _ d3) fun d4 h4 => ?_
    exact ShapeLogs.create (Or.inl trivial) h4
  | create2 =>
    simp only [Xinst.step, hsg]
    refine ShapeLogs.bind rfl (LogsWalk.pop devm) fun _ d1 h1 => ?_
    refine ShapeLogs.bind h1 (LogsWalk.popToNat d1) fun _ d2 h2 => ?_
    refine ShapeLogs.bind h2 (LogsWalk.popToNat d2) fun _ d3 h3 => ?_
    refine ShapeLogs.bind h3 (LogsWalk.pop d3) fun _ d4 h4 => ?_
    refine ShapeLogs.bindE h4 (LogsWalk.chargeGas _ d4) fun d5 h5 => ?_
    exact ShapeLogs.create (Or.inr trivial) h5
  | call =>
    simp only [Xinst.step, hsg]
    refine ShapeLogs.bind rfl (LogsWalk.pop devm) fun _ d1 h1 => ?_
    refine ShapeLogs.bind h1 (LogsWalk.popToAdr d1) fun callee d2 h2 => ?_
    refine ShapeLogs.bind h2 (LogsWalk.pop d2) fun _ d3 h3 => ?_
    refine ShapeLogs.bind h3 (LogsWalk.popToNat d3) fun _ d4 h4 => ?_
    refine ShapeLogs.bind h4 (LogsWalk.popToNat d4) fun _ d5 h5 => ?_
    refine ShapeLogs.bind h5 (LogsWalk.popToNat d5) fun _ d6 h6 => ?_
    refine ShapeLogs.bind h6 (LogsWalk.popToNat d6) fun _ d7 h7 => ?_
    dsimp only
    rcases hdel : sevm.benvStat.rules.gas.accessDelegation
        (addAccessedAddress d7 callee) callee with ⟨dpv, na, cd, dagc, d8⟩
    have h8 := ShapeLogs.delegation (x := addAccessedAddress d7 callee) h7 hdel
    refine ShapeLogs.bindE h8 (LogsWalk.chargeGas _ d8) fun d9 h9 => ?_
    refine ShapeLogs.assert h9 ?_
    split
    · exact ShapeLogs.shortfall h9
    · exact ShapeLogs.call h9
  | callcode =>
    simp only [Xinst.step, hsg]
    refine ShapeLogs.bind rfl (LogsWalk.pop devm) fun _ d1 h1 => ?_
    refine ShapeLogs.bind h1 (LogsWalk.popToAdr d1) fun cadr d2 h2 => ?_
    refine ShapeLogs.bind h2 (LogsWalk.pop d2) fun _ d3 h3 => ?_
    refine ShapeLogs.bind h3 (LogsWalk.popToNat d3) fun _ d4 h4 => ?_
    refine ShapeLogs.bind h4 (LogsWalk.popToNat d4) fun _ d5 h5 => ?_
    refine ShapeLogs.bind h5 (LogsWalk.popToNat d5) fun _ d6 h6 => ?_
    refine ShapeLogs.bind h6 (LogsWalk.popToNat d6) fun _ d7 h7 => ?_
    dsimp only
    rcases hdel : sevm.benvStat.rules.gas.accessDelegation
        (addAccessedAddress d7 cadr) cadr with ⟨dpv, na, cd, dagc, d8⟩
    have h8 := ShapeLogs.delegation (x := addAccessedAddress d7 cadr) h7 hdel
    refine ShapeLogs.bindE h8 (LogsWalk.chargeGas _ d8) fun d9 h9 => ?_
    split
    · exact ShapeLogs.shortfall' h9
    · exact ShapeLogs.call h9
  | delegatecall =>
    simp only [Xinst.step, hsg]
    refine ShapeLogs.bind rfl (LogsWalk.pop devm) fun _ d1 h1 => ?_
    refine ShapeLogs.bind h1 (LogsWalk.popToAdr d1) fun cadr d2 h2 => ?_
    refine ShapeLogs.bind h2 (LogsWalk.popToNat d2) fun _ d3 h3 => ?_
    refine ShapeLogs.bind h3 (LogsWalk.popToNat d3) fun _ d4 h4 => ?_
    refine ShapeLogs.bind h4 (LogsWalk.popToNat d4) fun _ d5 h5 => ?_
    refine ShapeLogs.bind h5 (LogsWalk.popToNat d5) fun _ d6 h6 => ?_
    dsimp only
    rcases hdel : sevm.benvStat.rules.gas.accessDelegation
        (addAccessedAddress d6 cadr) cadr with ⟨dpv, na, cd, dagc, d7⟩
    have h7 := ShapeLogs.delegation (x := addAccessedAddress d6 cadr) h6 hdel
    refine ShapeLogs.bindE h7 (LogsWalk.chargeGas _ d7) fun d8 h8 => ?_
    exact ShapeLogs.call h8
  | staticcall =>
    simp only [Xinst.step, hsg]
    refine ShapeLogs.bind rfl (LogsWalk.pop devm) fun _ d1 h1 => ?_
    refine ShapeLogs.bind h1 (LogsWalk.popToAdr d1) fun tgt d2 h2 => ?_
    refine ShapeLogs.bind h2 (LogsWalk.popToNat d2) fun _ d3 h3 => ?_
    refine ShapeLogs.bind h3 (LogsWalk.popToNat d3) fun _ d4 h4 => ?_
    refine ShapeLogs.bind h4 (LogsWalk.popToNat d4) fun _ d5 h5 => ?_
    refine ShapeLogs.bind h5 (LogsWalk.popToNat d5) fun _ d6 h6 => ?_
    dsimp only
    rcases hdel : sevm.benvStat.rules.gas.accessDelegation
        (addAccessedAddress d6 tgt) tgt with ⟨dpv, na, cd, dagc, d7⟩
    have h7 := ShapeLogs.delegation (x := addAccessedAddress d6 tgt) h6 hdel
    refine ShapeLogs.bindE h7 (LogsWalk.chargeGas _ d7) fun d8 h8 => ?_
    exact ShapeLogs.call h8

/-! ## Log lists across a message frame -/

/-- A frame entered under rules without state gas starts with no logs. -/
theorem initDevm_logs {msg : Msg} (hsg : msg.benv.stat.rules.stateGas = none) :
    (initDevm msg).logs = [] := by
  unfold initDevm Devm.logs
  dsimp only
  rw [hsg]

/-- The log hypothesis a recursive step needs about its child: a committing child
execution ends with its entry log list. -/
def Xlot.KeepsLogs : Xlot → Prop
  | .none => True
  | .some ⟨cevm, raw⟩ => ∀ c : Execution.commits raw = true,
      (Execution.committedPost raw c).logs = cevm.dyna.logs

/-- **A clean call-frame child carries no logs** when its fork has no state gas and its
interpreted body, if any, keeps its entry log list: the frame starts with none, a
precompile adds none, and settlement returns a clean body unchanged. -/
theorem ProcessMessage.clean_logs {msg : Msg} {xl : Xlot} {child : Devm}
    (hsg : msg.benv.stat.rules.stateGas = none)
    (run : ProcessMessage msg xl (.ok child)) (hclean : child.error.isSome = false)
    (body : Xlot.KeepsLogs xl) : child.logs = [] := by
  obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp run
  obtain ⟨evm2, rfl, hcase⟩ := processMessage.settle_ok_cases hset.symm
  have hclean' : ¬ child.error.isSome = true := by simp [hclean]
  have hc : evm2 = child := by
    rcases hcase with ⟨herr, hrb⟩ | ⟨_, h⟩
    · exfalso
      apply hclean'
      rw [← hrb]
      exact herr
    · exact h
  subst hc
  unfold FrameBody at hbody
  rcases hbt : msg.benvAfterTransfer with e | benv <;> simp only [hbt] at hbody
  · cases hbody.2
  have hsg' : (msg.withBenv benv).benv.stat.rules.stateGas = none :=
    (Msg.benvAfterTransfer_ok_stateGas hbt).trans hsg
  try unfold ExecuteCode at hbody
  rcases hent : executeCode.enter (msg.withBenv benv) with evm | raw <;>
    simp only [hent] at hbody
  · obtain ⟨raw, hxl, hr⟩ := hbody
    have hraw := exec_ok_of_handleError hr.symm hclean'
    subst hraw hxl
    have hevm : evm = initEvm (msg.withBenv benv) := by
      unfold executeCode.enter at hent
      split at hent
      · cases hent; rfl
      · split at hent
        · cases hent
        · cases hent; rfl
    have hkeep := body (by
      cases h : evm2.error <;> simp_all [Execution.commits])
    change evm2.logs = evm.dyna.logs at hkeep
    rw [hkeep, hevm]
    exact initDevm_logs hsg'
  · obtain ⟨-, hr⟩ := hbody
    have hraw := exec_ok_of_handleError hr.symm hclean'
    unfold executeCode.enter at hent
    split at hent
    · cases hent
    · split at hent
      · cases hent
        unfold executePrecomp applyPrecompResult at hraw
        split at hraw
        · cases hraw
        · cases hraw
          exact initDevm_logs hsg'
      · cases hent

/-- **A successful generic call keeps the caller's log list** on a fork without state
gas, given that the interpreted child, if any, keeps its entry log list. -/
theorem GenericCall.logs_of_ok {sevm : Sevm} {d post : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv isSt : Bool} {ii isz oi osz : Nat}
    {code : ByteArray} {dp : Bool} {xl : Xlot}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (run : XStep.Run (genericCall.step sevm d gas value caller target codeAddress stv isSt
      ii isz oi osz code dp) xl (.ok post))
    (body : Xlot.KeepsLogs xl) : post.logs = d.logs := by
  unfold genericCall.step at run
  split at run
  · rcases hp : (d.withReturnData []).withGasLeft ((d.withReturnData []).gasLeft + gas)
        |>.push 0 with e | d' <;>
      simp only [hp, XStep.ofExcept, bind, Except.bind, XStep.Run] at run
    · cases run.2
    · obtain ⟨-, hpost⟩ := run
      cases hpost
      exact (Devm.push_of_push hp).logs.symm
  · obtain ⟨r, hframe, hres⟩ := run
    rcases r with e | child
    · exact (Resume.call_run_error hres.symm).elim
    have hlogs := Resume.call_logs hres.symm
    by_cases herr : child.error.isSome = true
    · simp only [herr, ↓reduceIte] at hlogs
      exact hlogs
    · rw [Bool.not_eq_true] at herr
      simp only [herr, Bool.false_eq_true, ↓reduceIte] at hlogs
      have hnil := ProcessMessage.clean_logs (msg := callMsg sevm (d.withReturnData []) gas
        value caller target codeAddress stv isSt _ code dp) hsg hframe
        (by simpa using herr) body
      rw [hlogs, hnil, List.append_nil]
      rfl

/-- A generic create cannot succeed in a static frame: `assertDynamic` precedes every
successful exit. -/
theorem GenericCreate.not_ok_of_static {sevm : Sevm} {d post : Devm} {endowment : B256}
    {newAddress : Adr} {mi ms : Nat} {xl : Xlot} (hs : sevm.isStatic = true)
    (run : XStep.Run (genericCreate.step sevm d endowment newAddress mi ms) xl
      (.ok post)) : False := by
  unfold genericCreate.step at run
  simp only [Bind.bind, Except.bind, Except.assert, assertDynamic, hs] at run
  repeat' split at run
  all_goals simp_all [XStep.ofExcept, XStep.Run]

/-- **A successful executable instruction keeps the log list** on a covered fork, given
that its interpreted child, if any, keeps its entry log list.  A create is excluded by a
static frame; the call family needs nothing more. -/
theorem Xinst.logs_of_ok {sevm : Sevm} {pre post : Devm} {x : Xinst} {xl : Xlot}
    (hfork : CoveredFork sevm.benvStat.fork) (hx : sevm.isStatic = true ∨ x = .staticcall)
    (run : Xinst.Run sevm pre x xl (.ok post)) (body : Xlot.KeepsLogs xl) :
    post.logs = pre.logs := by
  unfold Xinst.Run at run
  rcases Xinst.step_shapeLogs sevm pre x hfork with ⟨ex, hs, hex⟩ |
    ⟨hc, d, e, na, mi, ms, hd, hs⟩ |
    ⟨d, g, v, c, t, ca, stv, isSt, ii, isz, oi, osz, code, dp, hd, hs⟩ <;> rw [hs] at run
  · obtain ⟨-, hpost⟩ := run
    subst hpost
    exact hex.symm
  · exfalso
    rcases hx with hst | rfl
    · exact GenericCreate.not_ok_of_static hst run
    · rcases hc with h | h <;> cases h
  · exact (GenericCall.logs_of_ok hfork.rules_stateGas_none run body).trans hd

/-! ## Static execution keeps the log list -/

/-- `LOG` cannot succeed in a static frame. -/
theorem Rinst.log_not_ok_of_static {pc : Nat} {sevm : Sevm} {pre post : Devm} {n : Fin 5}
    (hs : sevm.isStatic = true) (run : Rinst.run ⟨pc, sevm, pre⟩ (.log n) = .ok post) :
    False := by
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨_, _, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨_, _, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨_, _, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨_, _, run₄⟩
  rcases Except.bind_eq_ok run₄ with ⟨_, hassert, _⟩
  simp [assertDynamic, Except.assert, hs] at hassert

/-- `SELFDESTRUCT` cannot succeed in a static frame of a covered fork. -/
theorem Linst.selfdestruct_not_ok_of_static {sevm : Sevm} {pre post : Devm}
    (hfork : CoveredFork sevm.benvStat.fork) (hs : sevm.isStatic = true)
    (run : Linst.Run sevm pre .selfdestruct (.ok post)) : False := by
  have hsg : sevm.benvStat.rules.stateGas = none := hfork.rules_stateGas_none
  simp only [Linst.Run, Linst.run, hsg] at run
  rcases Except.bind_eq_ok run with ⟨_, _, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨_, _, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨_, _, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨_, _, run₄⟩
  rcases Except.bind_eq_ok run₄ with ⟨_, _, run₅⟩
  rcases Except.bind_eq_ok run₅ with ⟨_, hassert, _⟩
  simp [assertDynamic, Except.assert, hs] at hassert

/-- `REVERT` never succeeds. -/
theorem Linst.revert_not_ok {sevm : Sevm} {pre post : Devm}
    (run : Linst.Run sevm pre .revert (.ok post)) : False := by
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

/-- A successful jump keeps the log list. -/
theorem Jinst.logs_of_ok {evm : Evm} {j : Jinst} {pc : Nat} {post : Devm}
    (run : Jinst.run evm j = .ok (pc, post)) : post.logs = evm.dyna.logs := by
  cases j <;> simp only [Jinst.run, Jinst.runCore] at run
  · rcases Except.bind_eq_ok run with ⟨⟨_, d1⟩, h1, run₁⟩
    rcases Except.bind_eq_ok run₁ with ⟨d2, h2, run₂⟩
    rcases Except.bind_eq_ok run₂ with ⟨_, _, run₃⟩
    cases run₃
    exact (Devm.burn_of_chargeGas h2).logs.symm.trans (Devm.pop_of_pop h1).logs.symm
  · rcases Except.bind_eq_ok run with ⟨⟨_, d1⟩, h1, run₁⟩
    rcases Except.bind_eq_ok run₁ with ⟨⟨_, d2⟩, h2, run₂⟩
    rcases Except.bind_eq_ok run₂ with ⟨d3, h3, run₃⟩
    have hp : d3 = post := by
      split at run₃
      · cases run₃; rfl
      · unfold Except.assert at run₃
        split at run₃
        · cases run₃; rfl
        · cases run₃
    subst hp
    exact ((Devm.burn_of_chargeGas h3).logs.symm.trans (Devm.pop_of_pop h2).logs.symm).trans
      (Devm.pop_of_pop h1).logs.symm
  · rcases Except.bind_eq_ok run with ⟨d1, h1, run₁⟩
    cases run₁
    exact (Devm.burn_of_chargeGas h1).logs.symm

/-- One successful same-frame driver step of a static frame on a covered fork keeps the
log list. -/
private theorem staticStep_cont_logs
    {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' post)
    (static : sevm.isStatic = true) (hfork : CoveredFork sevm.benvStat.fork) :
    post.logs = pre.logs := by
  cases decoded : Evm.getInst ⟨pc, sevm, pre⟩ with
  | none =>
      unfold Evm.step at step
      rw [decoded] at step
      cases step
  | some instruction =>
      cases instruction with
      | last last =>
          rw [Evm.step_last decoded] at step
          cases step
      | jump jumpInst =>
          rw [Evm.step_jump decoded] at step
          cases jumpEq : Jinst.run ⟨pc, sevm, pre⟩ jumpInst with
          | error error =>
              rw [jumpEq] at step
              cases step
          | ok pair =>
              rcases pair with ⟨actualPc, actualPost⟩
              rw [jumpEq] at step
              cases step
              exact Jinst.logs_of_ok jumpEq
      | next instruction =>
          have nstep : Ninst.step ⟨pc, sevm, pre⟩ instruction = .cont pc' post := by
            rw [← Evm.step_next decoded]
            exact step
          have pcEq : pc' = pc + instruction.size := Ninst.step_cont_pc nstep
          subst pc'
          have nrun : Ninst.StepRun pc sevm pre instruction .none (.ok post) := by
            unfold Ninst.StepRun
            rw [nstep]
            exact ⟨rfl, rfl⟩
          cases instruction with
          | push bytes bound =>
              exact (Ninst.Hinv.inv (f := Devm.logs)
                (show Ninst.Run sevm pre (.push bytes bound) post from
                  ⟨.none, trivial, pc, nrun⟩)).symm
          | exec executable =>
              exact Xinst.logs_of_ok hfork (Or.inl static) (XStep.run_toStep.mp nrun) trivial
          | dupn imm => exact Ninst.dupn_logs ⟨.none, trivial, pc, nrun⟩
          | swapn imm => exact Ninst.swapn_logs ⟨.none, trivial, pc, nrun⟩
          | exchange imm => exact Ninst.exchange_logs ⟨.none, trivial, pc, nrun⟩
          | reg regular =>
              have rrun : Rinst.run ⟨pc, sevm, pre⟩ regular = .ok post :=
                (Step.run_ofExecution.mp nrun).2.symm
              by_cases hlog : ∃ n, regular = .log n
              · rcases hlog with ⟨n, rfl⟩
                exact (Rinst.log_not_ok_of_static static rrun).elim
              · exact Rinst.logs_of_ok (fun n h => hlog ⟨n, h⟩) rrun

/-- A successfully halted node of a static frame on a covered fork keeps the log list. -/
private theorem staticHalt_logs
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .halt out)
    (static : sevm.isStatic = true) (hfork : CoveredFork sevm.benvStat.fork) :
    ∀ post, out = .ok post → post.logs = pre.logs := by
  intro post hout
  subst hout
  cases decoded : Evm.getInst ⟨pc, sevm, pre⟩ with
  | none =>
      unfold Evm.step at step
      rw [decoded] at step
      cases step
  | some instruction =>
      cases instruction with
      | next next =>
          rw [Evm.step_next decoded] at step
          exact (Ninst.step_ne_halt_ok step).elim
      | jump jumpInst =>
          rw [Evm.step_jump decoded] at step
          cases jumpEq : Jinst.run ⟨pc, sevm, pre⟩ jumpInst <;>
            rw [jumpEq] at step <;> cases step
      | last last =>
          rw [Evm.step_last decoded] at step
          have run : Linst.Run sevm pre last (.ok post) := Step.halt.inj step
          change post.logs = pre.logs
          cases last with
          | stop => exact (Linst.Hinv.inv run).symm
          | return_ => exact (Linst.Hinv.inv run).symm
          | revert => exact (Linst.revert_not_ok run).elim
          | selfdestruct =>
              exact (Linst.selfdestruct_not_ok_of_static hfork static run).elim

/-- A log fact about every successful outcome holds for the committed post. -/
private theorem Execution.committedPost_logs_of_ok {out : Execution} {pre : Devm}
    (h : ∀ post, out = .ok post → post.logs = pre.logs) (committed : Execution.commits out = true) :
    (Execution.committedPost out committed).logs = pre.logs := by
  cases out with
  | error _ => simp [Execution.commits] at committed
  | ok post => exact h post rfl

/-- **Static execution keeps the log list.**  A successful execution (`.ok post`, committing
or not) of a static frame on a covered fork ends with exactly its entry log list: `LOG`
cannot complete in a static frame, every other step keeps the list, and every child is
static and merges its (empty) log list only on success. -/
theorem Exec.logs_eq_of_static_ok
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (static : sevm.isStatic = true)
    (hfork : CoveredFork sevm.benvStat.fork) :
    ∀ post, out = .ok post → post.logs = pre.logs := by
  induction run with
  | halt step => exact staticHalt_logs step static hfork
  | cont step _ ih =>
      intro post hout
      exact (ih static hfork post hout).trans (staticStep_cont_logs step static hfork)
  | doneErr _ _ _ => intro post hout; cases hout
  | @doneOk _ nodeSevm nodePre _ _ _ _ nodePost _ step enter resumeRun _ ih =>
      intro post hout
      rcases Evm.step_spawn_inv step with ⟨x, _, spawn, _⟩
      have xrun : Xinst.Run nodeSevm nodePre x .none (.ok nodePost) := by
        unfold Xinst.Run XStep.Run
        rw [spawn]
        exact ⟨_, RunFrame.of_done enter, resumeRun.symm⟩
      exact (ih static hfork post hout).trans
        (Xinst.logs_of_ok hfork (Or.inl static) xrun trivial)
  | runErr _ _ _ _ _ => intro post hout; cases hout
  | runOk step enter _ resumeRun _ childIH nextIH =>
      intro post hout
      rcases Evm.step_spawn_inv step with ⟨x, _, spawn, _⟩
      have xrun := (show Xinst.Run _ _ x (.some ⟨_, _⟩) (.ok _) by
        unfold Xinst.Run XStep.Run
        rw [spawn]
        exact ⟨_, RunFrame.of_run enter, resumeRun.symm⟩)
      have childStatic := Evm.step_run_isStatic step enter static
      have childFork := Evm.step_spawn_child_fork step enter hfork
      exact (nextIH static hfork post hout).trans
        (Xinst.logs_of_ok hfork (Or.inl static) xrun
          (fun childCommitted => Execution.committedPost_logs_of_ok
            (childIH childStatic childFork) childCommitted))

/-- **Static execution keeps the log list**, committed form: a committing execution of a
static frame on a covered fork ends with exactly its entry log list
(`Exec.logs_eq_of_static_ok`). -/
theorem Exec.logs_committedPost_eq_of_static
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (static : sevm.isStatic = true)
    (committed : Execution.commits out = true)
    (hfork : CoveredFork sevm.benvStat.fork) :
    (Execution.committedPost out committed).logs = pre.logs :=
  Execution.committedPost_logs_of_ok (Exec.logs_eq_of_static_ok run static hfork) committed

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
  | exec x =>
      have hx : x = .staticcall := by simpa [Ninst.quiet] using hn
      subst hx
      refine ⟨(Ninst.staticcall_inv_getStor_exact hfork run).symm, ?_⟩
      rcases run with ⟨slot, filled, pc, stepRun⟩
      have xrun : Xinst.Run sevm pre .staticcall slot (.ok post) := by
        simpa only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.Run] using stepRun
      have body : Xlot.KeepsLogs slot := by
        cases slot with
        | none => trivial
        | some child =>
            rcases child with ⟨cevm, out⟩
            rcases filled with ⟨childRun⟩
            rcases XStep.Run.some_inv xrun with ⟨frame, resume, spawn, enter, -⟩
            have childStatic : cevm.sta.isStatic = true :=
              (Frame.enter_run_isStatic enter).trans
                (Xinst.step_staticcall_spawn_isStatic spawn)
            exact fun committed => Exec.logs_committedPost_eq_of_static childRun childStatic
              committed (Xinst.Run.some_child_fork xrun hfork)
      exact Xinst.logs_of_ok hfork (Or.inr rfl) xrun body
  | reg r =>
      have hs : r ≠ .sstore := by
        rintro rfl
        simp [Ninst.quiet] at hn
      have hr : ∀ n, r ≠ .log n := by
        rintro n rfl
        simp [Ninst.quiet] at hn
      rcases of_run_reg run with ⟨pc, rrun⟩
      exact ⟨(Rinst.preserves_stor hs rrun).symm, Rinst.logs_of_ok hr rrun⟩

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
  | pcAt hrun _ run ih =>
      simp only [SFunc.quiet] at hf
      simp only [SFunc.refs] at hrefs
      exact tr (ih hf hrefs) (Ninst.world_of_quiet (n := .reg .pc) hfork rfl hrun)

end Blanc.Lift
