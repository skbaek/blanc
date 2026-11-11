import Batteries.Tactic.OpenPrivate
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

open private resume_callAmsterdam_state from Blanc.LadderBase

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
      repeat' split
      all_goals rfl
  unfold liftMachMetaWorldExecution liftMachMetaExecution liftMachMeta
    Footprint.toExecution Footprint.liftOutcome
  dsimp only
  rcases h : Rinst.balanceCore rules x.world x.mach x.meta with ⟨err, view⟩ | ⟨v, view⟩ <;>
    rw [h] at hcore <;> exact hcore

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
      | (simp only [addAccessedAddress_logs, addAccessedStorageKey_logs,
          Devm.memWrite_logs, Devm.memExtends_logs, Devm.withStack_logs,
          Devm.withReturnData_logs, Devm.withGasLeft_logs, Devm.setTransVal_logs,
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

/-- On a fork from Shanghai on an executable step either finishes with an execution that keeps the
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

private abbrev logsBalances (d : Devm) := (d.logs, d.getBal)

/-- Concrete observations of the same selected instruction prefix; old log consumers
project this structure without assuming a balance invariant for their child. -/
private def Xinst.ShapePair (sevm : Sevm) (devm : Devm) (x : Xinst) (s : XStep) : Prop :=
  (∃ ex, s = .done ex ∧ Execution.Rel (fun a b => logsBalances a = logsBalances b) devm ex) ∨
  ((x = .create ∨ x = .create2) ∧
    ∃ (state : Option StateGasRules), ∃ d endowment newAddress mi ms,
      sevm.benvStat.rules.stateGas = state ∧ logsBalances d = logsBalances devm ∧
      (state = none ∨ sevm.isStatic = false) ∧
      s = match state with
        | none => genericCreate.step sevm d endowment newAddress mi ms
        | some state => genericCreateAmsterdam.step sevm state d endowment newAddress mi ms) ∨
  (∃ (state : Option StateGasRules), ∃ d gas reservoir value caller target codeAddress
      stv isSt ii isz oi osz code dp charged insufficient,
    sevm.benvStat.rules.stateGas = state ∧ logsBalances d = logsBalances devm ∧
    ((sevm.isStatic = true ∨ x = .staticcall) →
      stv = false ∨ value = 0 ∨ caller = target) ∧
    s = match state with
      | none => genericCall.step sevm d gas value caller target codeAddress stv isSt
          ii isz oi osz code dp
      | some state => genericCallAmsterdam.step sevm state d gas reservoir value caller
          target codeAddress stv isSt ii isz oi osz code dp charged insufficient)

namespace PairShape

private lemma frame {a b : Devm} (world : Devm.InstructionFrame a b)
    (logs : b.logs = a.logs) : logsBalances b = logsBalances a :=
  Prod.ext logs (funext (getBal_eq_of_state_eq world.state.symm))

private lemma mach {a b : Devm} (h : Devm.MachFrame a b) :
    logsBalances a = logsBalances b :=
  Prod.ext h.logs (funext (getBal_eq_of_state_eq h.state))

private lemma ofMach {d : Devm} {out : Execution}
    (h : Execution.Rel Devm.MachFrame d out) :
    Execution.Rel (fun a b => logsBalances a = logsBalances b) d out := by
  cases out <;> exact mach h

private lemma ofMachP {α : Type} {d : Devm} {out : Except (EvmError × Devm) (α × Devm)}
    (h : Outcome.Rel Prod.snd Prod.snd Devm.MachFrame d out) :
    Outcome.Rel Prod.snd Prod.snd (fun a b => logsBalances a = logsBalances b) d out := by
  cases out <;> exact mach h

private lemma error {s : Sevm} {d : Devm} {x : Xinst} {e : EvmError × Devm}
    (h : logsBalances e.2 = logsBalances d) : Xinst.ShapePair s d x (XStep.ofExcept (.error e)) :=
  Or.inl ⟨_, rfl, h.symm⟩

private lemma bind {s : Sevm} {d base : Devm} {x : Xinst} {α : Type}
    {out : Except (EvmError × Devm) (α × Devm)}
    {next : α × Devm → Except (EvmError × Devm) XStep}
    (basePair : logsBalances base = logsBalances d)
    (step : Outcome.Rel Prod.snd Prod.snd (fun a b => logsBalances a = logsBalances b) base out)
    (tail : ∀ v b, logsBalances b = logsBalances d →
      Xinst.ShapePair s d x (XStep.ofExcept (next (v, b)))) :
    Xinst.ShapePair s d x (XStep.ofExcept (out >>= next)) := by
  cases out with
  | error e => exact error (step.symm.trans basePair)
  | ok pair => exact tail pair.1 pair.2 (step.symm.trans basePair)

private lemma bindE {s : Sevm} {d base : Devm} {x : Xinst} {out : Execution}
    {next : Devm → Except (EvmError × Devm) XStep}
    (basePair : logsBalances base = logsBalances d)
    (step : Execution.Rel (fun a b => logsBalances a = logsBalances b) base out)
    (tail : ∀ b, logsBalances b = logsBalances d → Xinst.ShapePair s d x (XStep.ofExcept (next b))) :
    Xinst.ShapePair s d x (XStep.ofExcept (out >>= next)) := by
  cases out with
  | error e => exact error (step.symm.trans basePair)
  | ok b => exact tail b (step.symm.trans basePair)

private lemma assert {s : Sevm} {d : Devm} {x : Xinst} {p : Prop} [Decidable p]
    {e : EvmError × Devm} {next : Unit → Except (EvmError × Devm) XStep}
    (pair : logsBalances e.2 = logsBalances d)
    (tail : p → Xinst.ShapePair s d x (XStep.ofExcept (next ()))) :
    Xinst.ShapePair s d x (XStep.ofExcept (Except.assert p e >>= next)) := by
  unfold Except.assert
  split
  · exact tail (by assumption)
  · exact error pair

private lemma create {s : Sevm} {d base : Devm} {x : Xinst}
    {state : Option StateGasRules} {endowment : B256} {address : Adr} {mi ms : Nat}
    (kind : x = .create ∨ x = .create2) (lane : s.benvStat.rules.stateGas = state)
    (pair : logsBalances base = logsBalances d)
    (dynamic : state = none ∨ s.isStatic = false) : Xinst.ShapePair s d x
      (match state with
      | none => genericCreate.step s base endowment address mi ms
      | some state => genericCreateAmsterdam.step s state base endowment address mi ms) :=
  by
    cases state with
    | none => exact Or.inr (Or.inl ⟨kind, none, base, endowment, address, mi, ms, lane, pair, dynamic, rfl⟩)
    | some state =>
      exact Or.inr (Or.inl ⟨kind, some state, base, endowment, address, mi, ms, lane, pair, dynamic, rfl⟩)

private lemma call {s : Sevm} {d base : Devm} {x : Xinst} {state : Option StateGasRules}
    {gas reservoir : Nat} {value : B256} {caller target address : Adr} {stv isSt : Bool}
    {ii isz oi osz : Nat} {code : ByteArray} {dp charged insufficient : Bool}
    (lane : s.benvStat.rules.stateGas = state) (pair : logsBalances base = logsBalances d)
    (quiet : (s.isStatic = true ∨ x = .staticcall) →
      stv = false ∨ value = 0 ∨ caller = target) : Xinst.ShapePair s d x
      (match state with
      | none => genericCall.step s base gas value caller target address stv isSt ii isz oi osz code dp
      | some state => genericCallAmsterdam.step s state base gas reservoir value caller target
          address stv isSt ii isz oi osz code dp charged insufficient) :=
  by
    cases state with
    | none => exact Or.inr (Or.inr ⟨none, base, gas, reservoir, value, caller, target, address,
        stv, isSt, ii, isz, oi, osz, code, dp, charged, insufficient, lane, pair, quiet, rfl⟩)
    | some state => exact Or.inr (Or.inr ⟨some state, base, gas, reservoir, value, caller,
        target, address, stv, isSt, ii, isz, oi, osz, code, dp, charged, insufficient,
        lane, pair, quiet, rfl⟩)

private lemma memExtends {d : Devm} {windows : List (Nat × Nat)} :
    logsBalances (d.memExtends windows) = logsBalances d :=
  frame (Devm.memExtends_instructionFrame _ _) (Devm.memExtends_logs _ _)

private lemma access {d : Devm} {a : Adr} :
    logsBalances (addAccessedAddress d a) = logsBalances d :=
  frame (addAccessedAddress_instructionFrame _ _) rfl

private lemma readAccount {rules : ForkRules} {d : Devm} {a : Adr} :
    logsBalances (d.balReadAccount rules a) = logsBalances d :=
  frame (Devm.balReadAccount_instructionFrame _ _ _) (Devm.balReadAccount_logs _ _ _)

private lemma delegation {rules : ForkRules} {d : Devm} {a : Adr} :
    logsBalances (rules.accessDelegation d a).2.2.2.2 = logsBalances d := by
  apply frame (ForkRules.accessDelegation_instructionFrame _ _ _)
  unfold ForkRules.accessDelegation
  split
  · exact GasSchedule.accessDelegation_logs
  · rfl

private lemma completeDelegation {d : Devm} {enabled : Bool} {a : Adr} :
    logsBalances (completeDelegationAccess d enabled a).2 = logsBalances d := by
  apply frame (completeDelegationAccess_instructionFrame _ _ _)
  cases enabled <;> rfl

private lemma pop (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd (fun a b => logsBalances a = logsBalances b) d d.pop := ofMachP (Devm.pop_machFrame d)
private lemma popToNat (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd (fun a b => logsBalances a = logsBalances b) d d.popToNat := ofMachP (Devm.popToNat_machFrame d)
private lemma popToAdr (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd (fun a b => logsBalances a = logsBalances b) d d.popToAdr := ofMachP (Devm.popToAdr_machFrame d)
private lemma push (v : B256) (d : Devm) :
    Execution.Rel (fun a b => logsBalances a = logsBalances b) d (d.push v) := ofMach (Devm.push_machFrame v d)
private lemma chargeGas (cost : Nat) (d : Devm) :
    Execution.Rel (fun a b => logsBalances a = logsBalances b) d (Jaune.chargeGas cost d) := ofMach (chargeGas_machFrame cost d)
private lemma chargeStateGas (cost : Nat) (d : Devm) :
    Execution.Rel (fun a b => logsBalances a = logsBalances b) d (Jaune.chargeStateGas cost d) :=
  ofMach (liftMachExecution_machFrame (Mach.chargeStateGas cost) d)

private lemma shortfall {s : Sevm} {d base : Devm} {x : Xinst} {stipend : Nat}
    (pair : logsBalances base = logsBalances d) : Xinst.ShapePair s d x
      (XStep.ofExcept (base.push 0 >>= fun next => .ok (.done (.ok
        ((next.withReturnData []).withGasLeft (next.gasLeft + stipend)))))) := by
  refine bindE pair (push 0 base) fun next kept => ?_
  exact Or.inl ⟨_, rfl, kept.symm⟩

private lemma shortfall' {s : Sevm} {d base : Devm} {x : Xinst} {stipend : Nat}
    (pair : logsBalances base = logsBalances d) : Xinst.ShapePair s d x
      (XStep.ofExcept (base.push 0 >>= fun next => .ok (.done (.ok
        ((next.withGasLeft (next.gasLeft + stipend)).withReturnData []))))) := by
  refine bindE pair (push 0 base) fun next kept => ?_
  exact Or.inl ⟨_, rfl, kept.symm⟩

private lemma callRouting {s : Sevm} {value : B256} {target : Adr}
    (passed : (!s.isStatic) = true ∨ value = 0) :
    (s.isStatic = true ∨ Xinst.call = .staticcall) →
      true = false ∨ value = 0 ∨ s.currentTarget = target := by
  intro selected
  rcases selected with static | impossible
  · rcases passed with dynamic | zero
    · simp only [static, Bool.not_true, Bool.false_eq_true] at dynamic
    · exact Or.inr (Or.inl zero)
  · cases impossible

private lemma oldLogs {s : Sevm} {d : Devm} {x : Xinst} {step : XStep}
    (lane : s.benvStat.rules.stateGas = none) (shape : Xinst.ShapePair s d x step) :
    Xinst.ShapeLogs s d (x = .create ∨ x = .create2) step := by
  rcases shape with ⟨ex, step, pair⟩ | ⟨kind, state, base, val, target, mi, ms, selected, pair, _, step⟩ |
    ⟨state, base, gas, reservoir, val, caller, target, address, stv, isSt, ii, isz, oi, osz,
      code, dp, charged, insufficient, selected, pair, _, step⟩
  · refine Or.inl ⟨ex, step, ?_⟩
    cases ex <;> exact congrArg Prod.fst pair
  · have none : state = none := selected.symm.trans lane
    rw [none] at step
    exact Or.inr (Or.inl ⟨kind, base, val, target, mi, ms, congrArg Prod.fst pair, step⟩)
  · have none : state = none := selected.symm.trans lane
    rw [none] at step
    exact Or.inr (Or.inr ⟨base, gas, val, caller, target, address, stv, isSt, ii, isz, oi, osz,
      code, dp, congrArg Prod.fst pair, step⟩)

end PairShape

/-- One structural opcode decomposition supplies both old log callbacks and the
new concrete pair callbacks, without requiring either child observation here. -/
private theorem Xinst.step_shapePair (sevm : Sevm) (devm : Devm) (x : Xinst) :
    Xinst.ShapePair sevm devm x (Xinst.step sevm devm x) := by
  cases x with
  | create =>
    simp only [Xinst.step]
    cases lane : sevm.benvStat.rules.stateGas with
    | none =>
      refine PairShape.bind rfl (PairShape.pop devm) fun _ d1 h1 => ?_
      refine PairShape.bind h1 (PairShape.popToNat d1) fun _ d2 h2 => ?_
      refine PairShape.bind h2 (PairShape.popToNat d2) fun _ d3 h3 => ?_
      refine PairShape.bindE h3 (PairShape.chargeGas _ d3) fun next kept => ?_
      exact PairShape.create (Or.inl rfl) lane (PairShape.memExtends.trans kept) (Or.inl rfl)
    | some state =>
      refine PairShape.assert rfl fun dynamic => ?_
      refine PairShape.bind rfl (PairShape.pop devm) fun _ d1 h1 => ?_
      refine PairShape.bind h1 (PairShape.popToNat d1) fun _ d2 h2 => ?_
      refine PairShape.bind h2 (PairShape.popToNat d2) fun _ d3 h3 => ?_
      refine PairShape.bindE h3 (PairShape.chargeGas _ d3) fun next kept => ?_
      refine PairShape.assert kept fun _ => ?_
      exact PairShape.create (Or.inl rfl) lane (PairShape.memExtends.trans kept) (Or.inr (by cases h : sevm.isStatic <;> simp_all only [Bool.not_true, Bool.false_eq_true]))
  | create2 =>
    simp only [Xinst.step]
    split
    · cases lane : sevm.benvStat.rules.stateGas with
      | none =>
        refine PairShape.bind rfl (PairShape.pop devm) fun _ d1 h1 => ?_
        refine PairShape.bind h1 (PairShape.popToNat d1) fun _ d2 h2 => ?_
        refine PairShape.bind h2 (PairShape.popToNat d2) fun _ d3 h3 => ?_
        refine PairShape.bind h3 (PairShape.pop d3) fun _ d4 h4 => ?_
        refine PairShape.bindE h4 (PairShape.chargeGas _ d4) fun next kept => ?_
        exact PairShape.create (Or.inr rfl) lane (PairShape.memExtends.trans kept) (Or.inl rfl)
      | some state =>
        refine PairShape.assert rfl fun dynamic => ?_
        refine PairShape.bind rfl (PairShape.pop devm) fun _ d1 h1 => ?_
        refine PairShape.bind h1 (PairShape.popToNat d1) fun _ d2 h2 => ?_
        refine PairShape.bind h2 (PairShape.popToNat d2) fun _ d3 h3 => ?_
        refine PairShape.bind h3 (PairShape.pop d3) fun _ d4 h4 => ?_
        refine PairShape.bindE h4 (PairShape.chargeGas _ d4) fun next kept => ?_
        refine PairShape.assert kept fun _ => ?_
        exact PairShape.create (Or.inr rfl) lane (PairShape.memExtends.trans kept) (Or.inr (by cases h : sevm.isStatic <;> simp_all only [Bool.not_true, Bool.false_eq_true]))
    · exact PairShape.error rfl
  | call =>
    simp only [Xinst.step]
    cases lane : sevm.benvStat.rules.stateGas with
    | none =>
      refine PairShape.bind rfl (PairShape.pop devm) fun _ d1 h1 => ?_
      refine PairShape.bind h1 (PairShape.popToAdr d1) fun target d2 h2 => ?_
      refine PairShape.bind h2 (PairShape.pop d2) fun value d3 h3 => ?_
      refine PairShape.bind h3 (PairShape.popToNat d3) fun _ d4 h4 => ?_
      refine PairShape.bind h4 (PairShape.popToNat d4) fun _ d5 h5 => ?_
      refine PairShape.bind h5 (PairShape.popToNat d5) fun _ d6 h6 => ?_
      refine PairShape.bind h6 (PairShape.popToNat d6) fun _ d7 h7 => ?_
      dsimp only
      let access : Devm := match sevm.benvStat.rules.access with
        | .eip2929 => addAccessedAddress d7 target
        | .flat _ => d7
      have accessed : logsBalances access = logsBalances devm := by
        dsimp only [access]
        split
        · exact PairShape.access.trans h7
        · exact h7
      let base := (sevm.benvStat.rules.accessDelegation access target).2.2.2.2
      have prePair : logsBalances base = logsBalances devm :=
        PairShape.delegation.trans accessed
      refine PairShape.bindE prePair (PairShape.chargeGas _ base) fun charged kept => ?_
      refine PairShape.assert kept fun passed => ?_
      split
      · exact PairShape.shortfall (PairShape.memExtends.trans kept)
      · exact PairShape.call (reservoir := 0) (charged := false) (insufficient := false)
          lane (PairShape.memExtends.trans kept) (PairShape.callRouting passed)
    | some state =>
      refine PairShape.bind rfl (PairShape.pop devm) fun _ d1 h1 => ?_
      refine PairShape.bind h1 (PairShape.popToAdr d1) fun target d2 h2 => ?_
      refine PairShape.bind h2 (PairShape.pop d2) fun value d3 h3 => ?_
      refine PairShape.bind h3 (PairShape.popToNat d3) fun _ d4 h4 => ?_
      refine PairShape.bind h4 (PairShape.popToNat d4) fun _ d5 h5 => ?_
      refine PairShape.bind h5 (PairShape.popToNat d5) fun _ d6 h6 => ?_
      refine PairShape.bind h6 (PairShape.popToNat d6) fun _ d7 h7 => ?_
      dsimp only
      refine PairShape.assert h7 fun passed => ?_
      refine PairShape.assert h7 fun _ => ?_
      let accessed := addAccessedAddress d7 target
      let delegate := sevm.benvStat.rules.delegationCost accessed target
      let read1 := accessed.balReadAccount sevm.benvStat.rules target
      have first : logsBalances read1 = logsBalances devm :=
        PairShape.readAccount.trans (PairShape.access.trans h7)
      refine PairShape.assert first fun _ => ?_
      let read2 := read1.balReadAccount sevm.benvStat.rules delegate.2.1
      let completed := completeDelegationAccess read2 delegate.1 delegate.2.1
      have prePair : logsBalances completed.2 = logsBalances devm :=
        PairShape.completeDelegation.trans (PairShape.readAccount.trans first)
      refine PairShape.bindE prePair (PairShape.chargeGas _ completed.2) fun charged kept => ?_
      split
      · refine PairShape.bindE kept (PairShape.chargeStateGas _ charged) fun stored storageKept => ?_
        refine PairShape.bindE storageKept (PairShape.chargeGas _ stored) fun sent sentKept => ?_
        exact PairShape.call lane (PairShape.memExtends.trans sentKept) (PairShape.callRouting passed)
      · simp only [Except.bind_ok]
        refine PairShape.bindE kept (PairShape.chargeGas _ charged) fun sent sentKept => ?_
        exact PairShape.call lane (PairShape.memExtends.trans sentKept) (PairShape.callRouting passed)
  | callcode =>
    simp only [Xinst.step]
    cases lane : sevm.benvStat.rules.stateGas with
    | none =>
      refine PairShape.bind rfl (PairShape.pop devm) fun _ d1 h1 => ?_
      refine PairShape.bind h1 (PairShape.popToAdr d1) fun target d2 h2 => ?_
      refine PairShape.bind h2 (PairShape.pop d2) fun value d3 h3 => ?_
      refine PairShape.bind h3 (PairShape.popToNat d3) fun _ d4 h4 => ?_
      refine PairShape.bind h4 (PairShape.popToNat d4) fun _ d5 h5 => ?_
      refine PairShape.bind h5 (PairShape.popToNat d5) fun _ d6 h6 => ?_
      refine PairShape.bind h6 (PairShape.popToNat d6) fun _ d7 h7 => ?_
      dsimp only
      let access : Devm := match sevm.benvStat.rules.access with
        | .eip2929 => addAccessedAddress d7 target
        | .flat _ => d7
      have accessed : logsBalances access = logsBalances devm := by
        dsimp only [access]
        split
        · exact PairShape.access.trans h7
        · exact h7
      let base := (sevm.benvStat.rules.accessDelegation access target).2.2.2.2
      have prePair : logsBalances base = logsBalances devm :=
        PairShape.delegation.trans accessed
      refine PairShape.bindE prePair (PairShape.chargeGas _ base) fun charged kept => ?_
      split
      · exact PairShape.shortfall' (PairShape.memExtends.trans kept)
      · exact PairShape.call (reservoir := 0) (charged := false) (insufficient := false)
          lane (PairShape.memExtends.trans kept) ((fun _ => Or.inr (Or.inr rfl)))
    | some state =>
      refine PairShape.bind rfl (PairShape.pop devm) fun _ d1 h1 => ?_
      refine PairShape.bind h1 (PairShape.popToAdr d1) fun target d2 h2 => ?_
      refine PairShape.bind h2 (PairShape.pop d2) fun value d3 h3 => ?_
      refine PairShape.bind h3 (PairShape.popToNat d3) fun _ d4 h4 => ?_
      refine PairShape.bind h4 (PairShape.popToNat d4) fun _ d5 h5 => ?_
      refine PairShape.bind h5 (PairShape.popToNat d5) fun _ d6 h6 => ?_
      refine PairShape.bind h6 (PairShape.popToNat d6) fun _ d7 h7 => ?_
      dsimp only
      refine PairShape.assert h7 fun _ => ?_
      let accessed := addAccessedAddress d7 target
      let delegate := sevm.benvStat.rules.delegationCost accessed target
      let read1 := accessed.balReadAccount sevm.benvStat.rules target
      have first : logsBalances read1 = logsBalances devm :=
        PairShape.readAccount.trans (PairShape.access.trans h7)
      refine PairShape.assert first fun _ => ?_
      let read2 := read1.balReadAccount sevm.benvStat.rules delegate.2.1
      let completed := completeDelegationAccess read2 delegate.1 delegate.2.1
      have prePair : logsBalances completed.2 = logsBalances devm :=
        PairShape.completeDelegation.trans (PairShape.readAccount.trans first)
      refine PairShape.bindE prePair (PairShape.chargeGas _ completed.2) fun charged kept => ?_
      exact PairShape.call lane (PairShape.memExtends.trans kept) (fun _ => Or.inr (Or.inr rfl))
  | delegatecall =>
    simp only [Xinst.step]
    cases lane : sevm.benvStat.rules.stateGas with
    | none =>
      refine PairShape.bind rfl (PairShape.pop devm) fun _ d1 h1 => ?_
      refine PairShape.bind h1 (PairShape.popToAdr d1) fun target d2 h2 => ?_
      refine PairShape.bind h2 (PairShape.popToNat d2) fun _ d3 h3 => ?_
      refine PairShape.bind h3 (PairShape.popToNat d3) fun _ d4 h4 => ?_
      refine PairShape.bind h4 (PairShape.popToNat d4) fun _ d5 h5 => ?_
      refine PairShape.bind h5 (PairShape.popToNat d5) fun _ d6 h6 => ?_
      dsimp only
      let access : Devm := match sevm.benvStat.rules.access with
        | .eip2929 => addAccessedAddress d6 target
        | .flat _ => d6
      have accessed : logsBalances access = logsBalances devm := by
        dsimp only [access]
        split
        · exact PairShape.access.trans h6
        · exact h6
      let base := (sevm.benvStat.rules.accessDelegation access target).2.2.2.2
      have prePair : logsBalances base = logsBalances devm :=
        PairShape.delegation.trans accessed
      refine PairShape.bindE prePair (PairShape.chargeGas _ base) fun charged kept => ?_
      exact PairShape.call (reservoir := 0) (charged := false) (insufficient := false)
        lane (PairShape.memExtends.trans kept) (fun _ => Or.inl rfl)
    | some state =>
      refine PairShape.bind rfl (PairShape.pop devm) fun _ d1 h1 => ?_
      refine PairShape.bind h1 (PairShape.popToAdr d1) fun target d2 h2 => ?_
      refine PairShape.bind h2 (PairShape.popToNat d2) fun _ d3 h3 => ?_
      refine PairShape.bind h3 (PairShape.popToNat d3) fun _ d4 h4 => ?_
      refine PairShape.bind h4 (PairShape.popToNat d4) fun _ d5 h5 => ?_
      refine PairShape.bind h5 (PairShape.popToNat d5) fun _ d6 h6 => ?_
      dsimp only
      refine PairShape.assert h6 fun _ => ?_
      let accessed := addAccessedAddress d6 target
      let delegate := sevm.benvStat.rules.delegationCost accessed target
      let read1 := accessed.balReadAccount sevm.benvStat.rules target
      have first : logsBalances read1 = logsBalances devm :=
        PairShape.readAccount.trans (PairShape.access.trans h6)
      refine PairShape.assert first fun _ => ?_
      let read2 := read1.balReadAccount sevm.benvStat.rules delegate.2.1
      let completed := completeDelegationAccess read2 delegate.1 delegate.2.1
      have prePair : logsBalances completed.2 = logsBalances devm :=
        PairShape.completeDelegation.trans (PairShape.readAccount.trans first)
      refine PairShape.bindE prePair (PairShape.chargeGas _ completed.2) fun charged kept => ?_
      exact PairShape.call lane (PairShape.memExtends.trans kept) (fun _ => Or.inl rfl)
  | staticcall =>
    simp only [Xinst.step]
    cases lane : sevm.benvStat.rules.stateGas with
    | none =>
      refine PairShape.bind rfl (PairShape.pop devm) fun _ d1 h1 => ?_
      refine PairShape.bind h1 (PairShape.popToAdr d1) fun target d2 h2 => ?_
      refine PairShape.bind h2 (PairShape.popToNat d2) fun _ d3 h3 => ?_
      refine PairShape.bind h3 (PairShape.popToNat d3) fun _ d4 h4 => ?_
      refine PairShape.bind h4 (PairShape.popToNat d4) fun _ d5 h5 => ?_
      refine PairShape.bind h5 (PairShape.popToNat d5) fun _ d6 h6 => ?_
      dsimp only
      let access : Devm := match sevm.benvStat.rules.access with
        | .eip2929 => addAccessedAddress d6 target
        | .flat _ => d6
      have accessed : logsBalances access = logsBalances devm := by
        dsimp only [access]
        split
        · exact PairShape.access.trans h6
        · exact h6
      let base := (sevm.benvStat.rules.accessDelegation access target).2.2.2.2
      have prePair : logsBalances base = logsBalances devm :=
        PairShape.delegation.trans accessed
      refine PairShape.bindE prePair (PairShape.chargeGas _ base) fun charged kept => ?_
      exact PairShape.call (reservoir := 0) (charged := false) (insufficient := false)
        lane (PairShape.memExtends.trans kept) (fun _ => Or.inr (Or.inl rfl))
    | some state =>
      refine PairShape.bind rfl (PairShape.pop devm) fun _ d1 h1 => ?_
      refine PairShape.bind h1 (PairShape.popToAdr d1) fun target d2 h2 => ?_
      refine PairShape.bind h2 (PairShape.popToNat d2) fun _ d3 h3 => ?_
      refine PairShape.bind h3 (PairShape.popToNat d3) fun _ d4 h4 => ?_
      refine PairShape.bind h4 (PairShape.popToNat d4) fun _ d5 h5 => ?_
      refine PairShape.bind h5 (PairShape.popToNat d5) fun _ d6 h6 => ?_
      dsimp only
      refine PairShape.assert h6 fun _ => ?_
      let accessed := addAccessedAddress d6 target
      let delegate := sevm.benvStat.rules.delegationCost accessed target
      let read1 := accessed.balReadAccount sevm.benvStat.rules target
      have first : logsBalances read1 = logsBalances devm :=
        PairShape.readAccount.trans (PairShape.access.trans h6)
      refine PairShape.assert first fun _ => ?_
      let read2 := read1.balReadAccount sevm.benvStat.rules delegate.2.1
      let completed := completeDelegationAccess read2 delegate.1 delegate.2.1
      have prePair : logsBalances completed.2 = logsBalances devm :=
        PairShape.completeDelegation.trans (PairShape.readAccount.trans first)
      refine PairShape.bindE prePair (PairShape.chargeGas _ completed.2) fun charged kept => ?_
      exact PairShape.call lane (PairShape.memExtends.trans kept) (fun _ => Or.inr (Or.inl rfl))

/-- Compatibility projection of the same structural routing proof. -/
lemma Xinst.step_shapeLogs_noStateGas (sevm : Sevm) (devm : Devm) (x : Xinst)
    {b : Bool} {a : AccessSchedule}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hdel : sevm.benvStat.rules.delegationEnabled = b)
    (hacc : sevm.benvStat.rules.access = a) :
    Xinst.ShapeLogs sevm devm (x = .create ∨ x = .create2) (Xinst.step sevm devm x) := by
  cases hdel
  cases hacc
  exact PairShape.oldLogs hsg (Xinst.step_shapePair sevm devm x)

/-- **Every executable instruction on a fork from Shanghai on has a log-list shape.** -/
lemma Xinst.step_shapeLogs (sevm : Sevm) (devm : Devm) (x : Xinst)
    (hfork : ShanghaiOnwards sevm.benvStat.fork) :
    Xinst.ShapeLogs sevm devm (x = .create ∨ x = .create2) (Xinst.step sevm devm x) :=
  Xinst.step_shapeLogs_noStateGas sevm devm x hfork.rules_stateGas_none
    rfl
    hfork.rules_access

/-! ## Log lists across a message frame -/

/-- A frame entered under rules without state gas starts with no logs. -/
theorem initDevm_logs {msg : Msg} (hsg : msg.benv.stat.rules.stateGas = none) :
    (initDevm msg).logs = [] := by
  unfold initDevm Devm.logs
  dsimp only
  rw [hsg]

/-- Zero, disabled and self transfers emit no entry log, on either meter lane. -/
theorem initDevm_logs_of_staticTransfer {msg : Msg}
    (quiet : msg.shouldTransferValue = false ∨ msg.value = 0 ∨
      msg.caller = msg.currentTarget) : (initDevm msg).logs = [] := by
  unfold initDevm Devm.logs
  dsimp only
  split
  · rfl
  · rcases quiet with off | zero | self
    · simp only [off, Bool.false_eq_true, ↓reduceIte]
    · simp only [Devm.emitTransferLog, zero, or_true, ↓reduceIte, ite_self]
    · simp only [Devm.emitTransferLog, self, eq_self, true_or, ↓reduceIte, ite_self]

/-- A successful self payment restores balances even when account normalization changes storage. -/
theorem Msg.benvAfterTransfer_balances_of_staticTransfer {msg : Msg} {entry : Benv}
    (quiet : msg.shouldTransferValue = false ∨ msg.value = 0 ∨
      msg.caller = msg.currentTarget)
    (transfer : msg.benvAfterTransfer = .ok entry) :
    entry.state.bal = msg.benv.state.bal := by
  by_cases moves : msg.shouldTransferValue = true ∧ msg.value ≠ 0
  · have self : msg.caller = msg.currentTarget := quiet.resolve_left
      (fun off => Bool.noConfusion (off.symm.trans moves.1)) |>.resolve_left moves.2
    obtain ⟨mid, debit, rfl⟩ := of_benvAfterTransfer moves.1 moves.2 transfer
    obtain ⟨_, rfl⟩ := State.of_subBal debit
    change (msg.benv.state.setBal msg.caller
      (msg.benv.state.bal msg.caller - msg.value) |>.addBal msg.currentTarget msg.value).bal = _
    rw [← self]
    funext a
    by_cases same : msg.caller = a
    · subst a
      simp only [State.bal, State.addBal, State.setBal_get_self, Acct.clearIfEmpty_bal,
        Acct.withBal, B256.sub_add_cancel]
    · simp only [State.bal, State.addBal, State.setBal_get_ne same]
  · rw [benvAfterTransfer_eq_of_not_transfer moves transfer]

/-- The log hypothesis a recursive step needs about its child: a committing child
execution ends with its entry log list. -/
def Xlot.KeepsLogs : Xlot → Prop
  | .none => True
  | .some ⟨cevm, raw⟩ => ∀ c : Execution.commits raw = true,
      (Execution.committedPost raw c).logs = cevm.dyna.logs

/-- A clean settled call exposes its actual interpreted source or native entry observation. -/
theorem ProcessMessage.clean_pair_source {msg : Msg} {xl : Xlot} {child : Devm}
    (run : ProcessMessage msg xl (.ok child)) (clean : child.error.isSome = false) :
    ∃ entry : Benv, msg.benvAfterTransfer = .ok entry ∧
      ((∃ raw : Devm, xl = .some ⟨initEvm (msg.withBenv entry), .ok raw⟩ ∧
          Execution.commits (.ok raw) = true ∧
          (child.logs, child.getBal) = (raw.logs, raw.getBal)) ∨
        (child.logs, child.getBal) =
          ((initDevm (msg.withBenv entry)).logs, (initDevm (msg.withBenv entry)).getBal)) := by
  obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp run
  obtain ⟨evm2, rfl, hcase⟩ := processMessage.settle_ok_cases hset.symm
  have hclean : ¬ child.error.isSome = true := by
    simp only [clean, Bool.false_eq_true, not_false_eq_true]
  have hc : (child.logs, child.getBal) = (evm2.logs, evm2.getBal) ∧
      child.error = evm2.error := by
    rcases hcase with ⟨herr, hrb⟩ | ⟨_, h⟩
    · exfalso
      apply hclean
      rw [← hrb]
      exact herr
    · subst h
      constructor <;> (unfold Devm.recordTouch; split <;> rfl)
  replace hclean : ¬ evm2.error.isSome = true := by
    rw [← hc.2]
    exact hclean
  unfold FrameBody at hbody
  rcases transfer : msg.benvAfterTransfer with error | entry <;>
    simp only [transfer] at hbody
  · cases hbody.2
  refine ⟨entry, rfl, ?_⟩
  try unfold ExecuteCode at hbody
  rcases entered : executeCode.enter (msg.withBenv entry) with evm | raw <;>
    simp only [entered] at hbody
  · obtain ⟨raw, slot, handled⟩ := hbody
    have actual := exec_ok_of_handleError handled.symm hclean
    subst actual slot
    have initial : evm = initEvm (msg.withBenv entry) := by
      unfold executeCode.enter at entered
      split at entered
      · cases entered; rfl
      · split at entered
        · cases entered
        · cases entered; rfl
    refine Or.inl ⟨evm2, ?_, ?_, hc.1⟩
    · rw [initial]
    · cases error : evm2.error <;>
        simp_all only [Execution.commits, Option.isNone_none, Option.isSome_some,
          Bool.true_eq_false]
  · obtain ⟨_, handled⟩ := hbody
    have actual := exec_ok_of_handleError handled.symm hclean
    unfold executeCode.enter at entered
    split at entered
    · cases entered
    · split at entered
      · cases entered
        unfold executePrecomp applyPrecompResult at actual
        split at actual
        · cases actual
        · cases actual
          exact Or.inr hc.1
      · cases entered

/-- Clean child observations, with actual transfer and rollback routed before projection. -/
theorem ProcessMessage.clean_logs_balances {msg : Msg} {xl : Xlot} {child : Devm}
    (quiet : msg.shouldTransferValue = false ∨ msg.value = 0 ∨
      msg.caller = msg.currentTarget)
    (run : ProcessMessage msg xl (.ok child)) (clean : child.error.isSome = false)
    (body : ∀ (evm : Evm) (raw : Execution), xl = .some ⟨evm, raw⟩ →
      ∀ committed : Execution.commits raw = true,
        ((Execution.committedPost raw committed).logs,
          (Execution.committedPost raw committed).getBal) = (evm.dyna.logs, evm.dyna.getBal)) :
    child.logs = [] ∧ child.getBal = msg.benv.state.bal := by
  obtain ⟨entry, transfer, interpreted | native⟩ := clean_pair_source run clean
  · obtain ⟨raw, slot, committed, source⟩ := interpreted
    have kept := body _ _ slot committed
    have pair := source.trans kept
    refine ⟨?_, ?_⟩
    · exact (congrArg Prod.fst pair).trans (initDevm_logs_of_staticTransfer quiet)
    · exact (congrArg Prod.snd pair).trans
        (Msg.benvAfterTransfer_balances_of_staticTransfer quiet transfer)
  · exact ⟨(congrArg Prod.fst native).trans (initDevm_logs_of_staticTransfer quiet),
      (congrArg Prod.snd native).trans
        (Msg.benvAfterTransfer_balances_of_staticTransfer quiet transfer)⟩

/-- Actual failed message settlement restores the saved balances before caller incorporation. -/
theorem ProcessMessage.failed_balances {msg : Msg} {xl : Xlot} {child : Devm}
    (run : ProcessMessage msg xl (.ok child)) (failed : child.error.isSome = true) :
    child.getBal = msg.benv.state.bal := by
  obtain ⟨_, _, settled⟩ := ProcessMessage.iff_body.mp run
  obtain ⟨raw, _, restored | clean⟩ := processMessage.settle_ok_cases settled.symm
  · rw [← restored.2]
    funext a
    unfold Devm.getBal Devm.getAcct Devm.recordTouch
    split <;> rfl
  · have error : child.error = raw.error := by
      rw [← clean.2]
      unfold Devm.recordTouch
      split <;> rfl
    exact (clean.1 (error ▸ failed)).elim

/-- Amsterdam's guarded call resume has the same concrete log/balance observation as its child. -/
theorem Resume.callAmsterdam_logs_balances {state : StateGasRules} {parent child post : Devm}
    {oi os : Nat} {charged : Bool}
    (run : (Resume.callAmsterdam state parent oi os charged).run (.ok child) = .ok post) :
    (post.logs, post.getBal) =
      ((if child.error.isSome then parent.logs else parent.logs ++ child.logs), child.getBal) := by
  apply Prod.ext
  · have finish : ∀ d : Devm,
        d.logs = (if child.error.isSome then parent.logs else parent.logs ++ child.logs) →
        ∀ flag : B256, (d.push flag >>= fun d' => .ok (d'.memWrite oi (child.output.take os))) =
          .ok post → post.logs =
            (if child.error.isSome then parent.logs else parent.logs ++ child.logs) := by
      intro d logs flag done
      obtain ⟨pushed, push, done⟩ := Except.bind_eq_ok done
      cases done
      exact (Devm.push_of_push push).logs.symm.trans logs
    unfold Resume.run liftToExecution at run
    dsimp only [bind, Except.bind, Except.assert] at run
    by_cases failed : child.error.isSome = true
    · rw [ite_eq_left failed] at run
      by_cases settled : child.AmsterdamFailedChildSettled
      · rw [ite_eq_left settled] at run
        dsimp only at run
        by_cases paid : charged = true
        · rw [ite_eq_left paid] at run
          exact finish _ (by rw [ite_eq_left failed]; rfl) _ run
        · rw [ite_eq_right paid] at run
          exact finish _ (by rw [ite_eq_left failed]; rfl) _ run
      · rw [ite_eq_right settled] at run
        cases run
    · rw [ite_eq_right failed] at run
      by_cases uncommitted : child.AmsterdamChildUncommitted
      · rw [ite_eq_left uncommitted] at run
        dsimp only at run
        exact finish _ (by rw [ite_eq_right failed]; rfl) _ run
      · rw [ite_eq_right uncommitted] at run
        cases run
  · exact funext (getBal_eq_of_state_eq (resume_callAmsterdam_state run))

/-- Ordinary call resumption projects the already proved state and log observations. -/
theorem Resume.call_logs_balances {parent child post : Devm} {oi os : Nat}
    (run : (Resume.call parent oi os).run (.ok child) = .ok post) :
    (post.logs, post.getBal) =
      ((if child.error.isSome then parent.logs else parent.logs ++ child.logs), child.getBal) :=
  Prod.ext (Resume.call_logs run) (funext (getBal_eq_of_state_eq (Resume.call_state run)))

/-- The actual call frame and either selected resume preserve the caller's concrete observation. -/
theorem ProcessMessage.resume_call_logs_balances
    {state : Option StateGasRules} {sevm : Sevm} {parent post : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv isSt : Bool} {ii isz oi osz : Nat}
    {code : ByteArray} {dp charged : Bool} {grant : Nat} {xl : Xlot}
    {raw : Except (EvmError × State × AdrSet × Tra) Devm}
    (quiet : stv = false ∨ value = 0 ∨ caller = target)
    (frame : ProcessMessage
      { callMsg sevm parent gas value caller target codeAddress stv isSt
          (parent.memory.data.sliceD ii isz 0) code dp with stateGasGrant := grant } xl raw)
    (resume : (match state with
      | none => Resume.call parent oi osz
      | some state => Resume.callAmsterdam state parent oi osz charged).run raw = .ok post)
    (body : ∀ (evm : Evm) (raw : Execution), xl = .some ⟨evm, raw⟩ →
      ∀ committed : Execution.commits raw = true,
        ((Execution.committedPost raw committed).logs,
          (Execution.committedPost raw committed).getBal) = (evm.dyna.logs, evm.dyna.getBal)) :
    (post.logs, post.getBal) = (parent.logs, parent.getBal) := by
  cases raw with
  | error error =>
    cases state <;> simp only [Resume.run, liftToExecution, bind, Except.bind] at resume
    all_goals cases resume
  | ok child =>
    have pair : (post.logs, post.getBal) =
        ((if child.error.isSome then parent.logs else parent.logs ++ child.logs), child.getBal) := by
      cases state with
      | none => exact Resume.call_logs_balances resume
      | some state => exact Resume.callAmsterdam_logs_balances resume
    by_cases failed : child.error.isSome = true
    · rw [ite_eq_left failed] at pair
      exact pair.trans (Prod.ext rfl (ProcessMessage.failed_balances frame failed))
    · have clean : child.error.isSome = false := Bool.eq_false_iff.mpr failed
      obtain ⟨logs, balances⟩ := ProcessMessage.clean_logs_balances quiet frame clean body
      rw [ite_eq_right failed, logs, List.append_nil, balances] at pair
      exact pair

/-- A selected ordinary or Amsterdam generic call preserves logs and balances when its
actual value transfer is disabled, zero or self-directed. -/
theorem GenericCall.logs_balances_of_staticTransfer
    {state : Option StateGasRules} {sevm : Sevm} {pre post : Devm} {gas reservoir : Nat}
    {value : B256} {caller target codeAddress : Adr} {stv isSt : Bool} {ii isz oi osz : Nat}
    {code : ByteArray} {dp charged insufficient : Bool} {xl : Xlot}
    (quiet : stv = false ∨ value = 0 ∨ caller = target)
    (run : XStep.Run (match state with
      | none => genericCall.step sevm pre gas value caller target codeAddress stv isSt
          ii isz oi osz code dp
      | some state => genericCallAmsterdam.step sevm state pre gas reservoir value
          caller target codeAddress stv isSt ii isz oi osz code dp charged insufficient)
      xl (.ok post))
    (body : ∀ (evm : Evm) (raw : Execution), xl = .some ⟨evm, raw⟩ →
      ∀ committed : Execution.commits raw = true,
        ((Execution.committedPost raw committed).logs,
          (Execution.committedPost raw committed).getBal) = (evm.dyna.logs, evm.dyna.getBal)) :
    (post.logs, post.getBal) = (pre.logs, pre.getBal) := by
  have preflight : ∀ d : Devm, (d.logs, d.getBal) = (pre.logs, pre.getBal) →
      XStep.Run (XStep.ofExcept (do
        let pushed ← d.push 0
        pure (.done (.ok pushed)))) xl (.ok post) →
      (post.logs, post.getBal) = (pre.logs, pre.getBal) := by
    intro d pair done
    rcases pushed : d.push 0 with error | next <;>
      simp only [pushed, XStep.ofExcept, bind, Except.bind, XStep.Run] at done
    · cases done.2
    · obtain ⟨_, done⟩ := done
      cases done
      exact (Prod.ext (Devm.push_of_push pushed).logs.symm
        (funext (getBal_eq_of_state_eq (Devm.push_of_push pushed).state.symm))).trans pair
  cases state with
  | none =>
    simp only [genericCall.step] at run
    split at run
    · refine preflight _ ?_ run
      rfl
    · obtain ⟨raw, frame, resume⟩ := run
      exact ProcessMessage.resume_call_logs_balances (state := none) (grant := 0) (charged := false)
        (parent := pre.withReturnData []) quiet frame resume.symm body
  | some state =>
    simp only [genericCallAmsterdam.step] at run
    split at run
    · cases charged <;>
        simp only [Bool.false_eq_true, ↓reduceIte] at run
      all_goals (refine preflight _ ?_ run; rfl)
    · obtain ⟨raw, frame, resume⟩ := run
      exact ProcessMessage.resume_call_logs_balances (state := some state) (grant := reservoir)
        (parent := pre.withReturnData []) quiet frame resume.symm body

/-- **A clean call-frame child carries no logs** when its fork has no state gas and its
interpreted body, if any, keeps its entry log list. -/
theorem ProcessMessage.clean_logs {msg : Msg} {xl : Xlot} {child : Devm}
    (hsg : msg.benv.stat.rules.stateGas = none)
    (run : ProcessMessage msg xl (.ok child)) (hclean : child.error.isSome = false)
    (body : Xlot.KeepsLogs xl) : child.logs = [] := by
  obtain ⟨entry, transfer, interpreted | native⟩ := clean_pair_source run hclean
  · have noGas : (msg.withBenv entry).benv.stat.rules.stateGas = none :=
      (Msg.benvAfterTransfer_ok_stateGas transfer).trans hsg
    obtain ⟨raw, slot, committed, source⟩ := interpreted
    rw [slot] at body
    exact ((congrArg Prod.fst source).trans (body committed)).trans (initDevm_logs noGas)
  · have noGas : (msg.withBenv entry).benv.stat.rules.stateGas = none :=
      (Msg.benvAfterTransfer_ok_stateGas transfer).trans hsg
    exact (congrArg Prod.fst native).trans (initDevm_logs noGas)

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
        (by simpa only [Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] using herr) body
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
  all_goals simp_all only [XStep.Run, XStep.ofExcept, ExceptT.stM_eq, reduceCtorEq, and_false, ite_eq_left_iff, not_le, imp_false, not_lt, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Except.error.injEq]

/-- **A successful executable instruction keeps the log list** on a fork from Shanghai on, given
that its interpreted child, if any, keeps its entry log list.  A create is excluded by a
static frame; the call family needs nothing more. -/
theorem Xinst.logs_of_ok {sevm : Sevm} {pre post : Devm} {x : Xinst} {xl : Xlot}
    (hfork : ShanghaiOnwards sevm.benvStat.fork) (hx : sevm.isStatic = true ∨ x = .staticcall)
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

/-- The same routing shape yields concrete log/balance preservation when its actual child does. -/
theorem Xinst.static_logs_balances_of_ok {sevm : Sevm} {pre post : Devm}
    {x : Xinst} {xl : Xlot}
    (selected : sevm.isStatic = true ∨ x = .staticcall)
    (run : Xinst.Run sevm pre x xl (.ok post))
    (body : ∀ (evm : Evm) (raw : Execution), xl = .some ⟨evm, raw⟩ →
      ∀ committed : Execution.commits raw = true,
        ((Execution.committedPost raw committed).logs,
          (Execution.committedPost raw committed).getBal) = (evm.dyna.logs, evm.dyna.getBal)) :
    (post.logs, post.getBal) = (pre.logs, pre.getBal) := by
  unfold Xinst.Run at run
  rcases Xinst.step_shapePair sevm pre x with ⟨ex, step, pair⟩ |
    ⟨kind, state, base, val, target, mi, ms, _, pair, dynamic, step⟩ |
    ⟨state, base, gas, reservoir, val, caller, target, address, stv, isSt, ii, isz, oi, osz,
      code, dp, charged, insufficient, _, pair, quiet, step⟩ <;> rw [step] at run
  · obtain ⟨_, actual⟩ := run
    cases actual
    exact pair.symm
  · exfalso
    have static : sevm.isStatic = true := by
      rcases selected with static | rfl
      · exact static
      · rcases kind with impossible | impossible <;> cases impossible
    rcases dynamic with rfl | forbidden
    · exact GenericCreate.not_ok_of_static static run
    · exact Bool.noConfusion (forbidden.symm.trans static)
  · cases state with
    | none =>
      exact (GenericCall.logs_balances_of_staticTransfer (state := none)
        (reservoir := reservoir) (charged := charged) (insufficient := insufficient)
        (quiet selected) run body).trans pair
    | some state =>
      exact (GenericCall.logs_balances_of_staticTransfer (state := some state)
        (quiet selected) run body).trans pair

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
  simp only [assertDynamic, Except.assert, hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    reduceCtorEq] at hassert

/-- Both meter lanes enforce the actual static SELFDESTRUCT guard. -/
private theorem Linst.selfdestruct_not_ok_of_static_any {sevm : Sevm} {pre post : Devm}
    (hs : sevm.isStatic = true)
    (run : Linst.Run sevm pre .selfdestruct (.ok post)) : False := by
  cases lane : sevm.benvStat.rules.stateGas with
  | none =>
    simp only [Linst.Run, Linst.run, lane] at run
    rcases Except.bind_eq_ok run with ⟨_, _, run₁⟩
    rcases Except.bind_eq_ok run₁ with ⟨_, _, run₂⟩
    rcases Except.bind_eq_ok run₂ with ⟨_, _, run₃⟩
    rcases Except.bind_eq_ok run₃ with ⟨_, _, run₄⟩
    rcases Except.bind_eq_ok run₄ with ⟨_, _, run₅⟩
    rcases Except.bind_eq_ok run₅ with ⟨_, hassert, _⟩
    simp only [assertDynamic, Except.assert, hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      reduceCtorEq] at hassert
  | some state =>
    simp only [Linst.Run, Linst.run, lane, assertDynamic, Except.assert, hs,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, Except.bind_error, reduceCtorEq] at run

/-- `SELFDESTRUCT` cannot succeed in a static frame of a fork from Shanghai on. -/
theorem Linst.selfdestruct_not_ok_of_static {sevm : Sevm} {pre post : Devm}
    (hfork : ShanghaiOnwards sevm.benvStat.fork) (hs : sevm.isStatic = true)
    (run : Linst.Run sevm pre .selfdestruct (.ok post)) : False := by
  have _ := hfork.rules_stateGas_none
  exact Linst.selfdestruct_not_ok_of_static_any hs run

/-- `REVERT` never succeeds. -/
theorem Linst.revert_not_ok {sevm : Sevm} {pre post : Devm}
    (run : Linst.Run sevm pre .revert (.ok post)) : False := by
  simp only [Linst.Run, Linst.run] at run
  cases h : pre.popToNat with
  | error e => simp only [h, Except.bind_error, reduceCtorEq] at run
  | ok x =>
    cases h2 : x.2.popToNat with
    | error e => simp only [h, Except.bind_ok, h2, Except.bind_error, reduceCtorEq] at run
    | ok y =>
      cases h3 : chargeGas (y.2.extCost [(x.1, y.1)]) y.2 with
      | error e => simp only [h, Except.bind_ok, h2, h3, Except.bind_error, reduceCtorEq] at run
      | ok d => simp only [h, Except.bind_ok, h2, h3, reduceCtorEq] at run

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

/-- One successful same-frame driver step of a static frame on a fork from Shanghai on keeps the
log list. -/
private theorem staticStep_cont_pair
    {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' post)
    (static : sevm.isStatic = true) :
    logsBalances post = logsBalances pre := by
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
              have frame := Jinst.run_instructionFrame ⟨pc, sevm, pre⟩ jumpInst
              rw [jumpEq] at frame
              exact PairShape.frame frame (Jinst.logs_of_ok jumpEq)
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
              exact Prod.ext (Ninst.Hinv.inv (f := Devm.logs)
                (show Ninst.Run sevm pre (.push bytes bound) post from
                  ⟨.none, trivial, pc, nrun⟩)).symm
                (Ninst.Hinv.inv (f := Devm.getBal)
                  (show Ninst.Run sevm pre (.push bytes bound) post from
                    ⟨.none, trivial, pc, nrun⟩)).symm
          | exec executable =>
              exact Xinst.static_logs_balances_of_ok (Or.inl static)
                (XStep.run_toStep.mp nrun) (by intro _ _ impossible; cases impossible)
          | dupn imm =>
              exact PairShape.frame (Ninst.dupn_instructionFrame_effectRec (xl := .none) trivial nrun)
                (Ninst.dupn_logs ⟨.none, trivial, pc, nrun⟩)
          | swapn imm =>
              exact PairShape.frame (Ninst.swapn_instructionFrame_effectRec (xl := .none) trivial nrun)
                (Ninst.swapn_logs ⟨.none, trivial, pc, nrun⟩)
          | exchange imm =>
              exact PairShape.frame (Ninst.exchange_instructionFrame_effectRec (xl := .none) trivial nrun)
                (Ninst.exchange_logs ⟨.none, trivial, pc, nrun⟩)
          | reg regular =>
              have rrun : Rinst.run ⟨pc, sevm, pre⟩ regular = .ok post :=
                (Step.run_ofExecution.mp nrun).2.symm
              by_cases hlog : ∃ n, regular = .log n
              · rcases hlog with ⟨n, rfl⟩
                exact (Rinst.log_not_ok_of_static static rrun).elim
              · exact Prod.ext (Rinst.logs_of_ok (fun n h => hlog ⟨n, h⟩) rrun)
                  (Rinst.preserves_bal rrun).symm

/-- A successfully halted node of a static frame on a fork from Shanghai on keeps the log list. -/
private theorem staticHalt_pair
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .halt out)
    (static : sevm.isStatic = true) :
    ∀ post, out = .ok post → logsBalances post = logsBalances pre := by
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
          change logsBalances post = logsBalances pre
          cases last with
          | stop =>
              exact Prod.ext (Linst.Hinv.inv (f := Devm.logs) (g := Devm.logs) run).symm
                (Linst.Hinv.inv (f := Devm.getBal) (g := Devm.getBal) run).symm
          | return_ =>
              exact Prod.ext (Linst.Hinv.inv (f := Devm.logs) (g := Devm.logs) run).symm
                (Linst.Hinv.inv (f := Devm.getBal) (g := Devm.getBal) run).symm
          | revert => exact (Linst.revert_not_ok run).elim
          | selfdestruct =>
              exact (Linst.selfdestruct_not_ok_of_static_any static run).elim

/-- A log fact about every successful outcome holds for the committed post. -/
private theorem Execution.committedPost_logs_of_ok {out : Execution} {pre : Devm}
    (h : ∀ post, out = .ok post → post.logs = pre.logs) (committed : Execution.commits out = true) :
    (Execution.committedPost out committed).logs = pre.logs := by
  cases out with
  | error _ => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post => exact h post rfl

/-- Successful concrete observations determine the actual committed post. -/
private theorem Execution.committedPost_pair_of_ok {out : Execution} {pre : Devm}
    (h : ∀ post, out = .ok post → logsBalances post = logsBalances pre)
    (committed : Execution.commits out = true) :
    logsBalances (Execution.committedPost out committed) = logsBalances pre := by
  cases out with
  | error _ => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post => exact h post rfl

/-- A successful static execution preserves its concrete log/balance observation on either meter
lane. The original child run supplies the recursive premise at the actual filled slot. -/
theorem Exec.static_logs_balances_of_ok
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (static : sevm.isStatic = true)
    :
    ∀ post, out = .ok post → (post.logs, post.getBal) = (pre.logs, pre.getBal) := by
  induction run with
  | halt step => exact staticHalt_pair step static
  | cont step _ ih =>
      intro post hout
      exact (ih static post hout).trans (staticStep_cont_pair step static)
  | doneErr _ _ _ => intro post hout; cases hout
  | @doneOk _ nodeSevm nodePre _ _ _ _ nodePost _ step enter resumeRun _ ih =>
      intro post hout
      rcases Evm.step_spawn_inv step with ⟨x, _, spawn, _⟩
      have xrun : Xinst.Run nodeSevm nodePre x .none (.ok nodePost) := by
        unfold Xinst.Run XStep.Run
        rw [spawn]
        exact ⟨_, RunFrame.of_done enter, resumeRun.symm⟩
      exact (ih static post hout).trans
        (Xinst.static_logs_balances_of_ok (Or.inl static) xrun
          (by intro _ _ impossible; cases impossible))
  | runErr _ _ _ _ _ => intro post hout; cases hout
  | runOk step enter _ resumeRun _ childIH nextIH =>
      intro post hout
      rcases Evm.step_spawn_inv step with ⟨x, _, spawn, _⟩
      have xrun := (show Xinst.Run _ _ x (.some ⟨_, _⟩) (.ok _) by
        unfold Xinst.Run XStep.Run
        rw [spawn]
        exact ⟨_, RunFrame.of_run enter, resumeRun.symm⟩)
      have childStatic := Evm.step_run_isStatic step enter static
      exact (nextIH static post hout).trans
        (Xinst.static_logs_balances_of_ok (Or.inl static) xrun (by
          intro child raw slot committed
          cases slot
          exact Execution.committedPost_pair_of_ok (childIH childStatic) committed))

/-- An actual successful STATICCALL preserves logs and every account balance on either meter lane.
Its original filled child is discharged by the single static execution induction. -/
theorem Ninst.staticcall_logs_balances_any {sevm : Sevm} {pre post : Devm}
    (run : Ninst.Run sevm pre (.exec .staticcall) post) :
    (post.logs, post.getBal) = (pre.logs, pre.getBal) := by
  rcases run with ⟨slot, filled, pc, stepRun⟩
  have xrun : Xinst.Run sevm pre .staticcall slot (.ok post) := by
    simpa only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.Run] using stepRun
  apply Xinst.static_logs_balances_of_ok (Or.inr rfl) xrun
  intro child raw actual committed
  cases actual
  rcases filled with ⟨childRun⟩
  rcases XStep.Run.some_inv xrun with ⟨frame, resume, spawn, enter, _⟩
  have childStatic := (Frame.enter_run_isStatic enter).trans
    (Xinst.step_staticcall_spawn_isStatic spawn)
  exact Execution.committedPost_pair_of_ok
    (Exec.static_logs_balances_of_ok childRun childStatic) committed

/-- Compatibility projection from the single all-fork static execution induction. -/
theorem Exec.logs_eq_of_static_ok
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (static : sevm.isStatic = true)
    (hfork : ShanghaiOnwards sevm.benvStat.fork) :
    ∀ post, out = .ok post → post.logs = pre.logs := by
  have _ := hfork.rules_stateGas_none
  intro post actual
  exact congrArg Prod.fst (Exec.static_logs_balances_of_ok run static post actual)

/-- **Static execution keeps the log list**, committed form: a committing execution of a
static frame on a fork from Shanghai on ends with exactly its entry log list
(`Exec.logs_eq_of_static_ok`). -/
theorem Exec.logs_committedPost_eq_of_static
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (static : sevm.isStatic = true)
    (committed : Execution.commits out = true)
    (hfork : ShanghaiOnwards sevm.benvStat.fork) :
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
    (hfork : ShanghaiOnwards sevm.benvStat.fork) (hn : n.quiet = true)
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
      have hx : x = .staticcall := by simpa only [Ninst.quiet, beq_iff_eq] using hn
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
              committed (Xinst.Run.some_child_shanghaiOnwards xrun hfork)
      exact Xinst.logs_of_ok hfork (Or.inr rfl) xrun body
  | reg r =>
      have hs : r ≠ .sstore := by
        rintro rfl
        simp only [Ninst.quiet, Bool.false_eq_true] at hn
      have hr : ∀ n, r ≠ .log n := by
        rintro n rfl
        simp only [Ninst.quiet, Bool.false_eq_true] at hn
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
      have hf := Linst.run_instructionFrame sevm pre .stop (by simp only [ne_eq, reduceCtorEq,
        not_false_eq_true])
      rw [run] at hf
      exact ⟨funext (fun a => (hf.getStor a).symm), (Linst.Hinv.inv run).symm⟩
  | return_ =>
      have hf := Linst.run_instructionFrame sevm pre .return_ (by simp only [ne_eq, reduceCtorEq,
        not_false_eq_true])
      rw [run] at hf
      exact ⟨funext (fun a => (hf.getStor a).symm), (Linst.Hinv.inv run).symm⟩
  | revert =>
      simp only [Linst.Run, Linst.run] at run
      cases h : pre.popToNat with
      | error e => simp only [h, Except.bind_error, reduceCtorEq] at run
      | ok x =>
        cases h2 : x.2.popToNat with
        | error e => simp only [h, Except.bind_ok, h2, Except.bind_error, reduceCtorEq] at run
        | ok y =>
          cases h3 : chargeGas (y.2.extCost [(x.1, y.1)]) y.2 with
          | error e => simp only [h, Except.bind_ok, h2, h3, Except.bind_error, reduceCtorEq] at run
          | ok d => simp only [h, Except.bind_ok, h2, h3, reduceCtorEq] at run
  | selfdestruct => exact (hl rfl).elim

end Blanc.Lift
