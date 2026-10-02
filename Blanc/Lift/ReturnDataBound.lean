import Blanc.ExecutionTraceCalldata
import Blanc.Lift.PrecompileOutputBound

/-!
# Return-data bounds from interpreter producers

The ordinary-code theory tracks the enclosing output independently of child
return-data. Actual frame entry, bounded child input and precompile producers
compose through settlement to bound the full returndata of CALL and STATICCALL.
-/

namespace Blanc.Lift.ReturnDataBound

open Jaune

private abbrev OutputEq (a b : Devm) : Prop := a.output = b.output

private theorem outputEq_trans : TransitiveRel OutputEq :=
  fun _ _ _ hab hbc => hab.trans hbc

private theorem ofMach {a b : Devm} {out : Execution}
    (hab : a.output = b.output) (h : Execution.Rel Devm.MachFrame b out) :
    Execution.Rel OutputEq a out := by
  cases out <;> exact hab.trans h.output

private theorem ofMachPair {α : Type} {a b : Devm}
    {out : Except (EvmError × Devm) (α × Devm)}
    (hab : a.output = b.output)
    (h : Outcome.Rel Prod.snd Prod.snd Devm.MachFrame b out) :
    Outcome.Rel Prod.snd Prod.snd OutputEq a out := by
  cases out <;> exact hab.trans h.output

private theorem bindPair {α : Type} {d : Devm}
    {out : Except (EvmError × Devm) (α × Devm)} {f : α × Devm → Execution}
    (h : Outcome.Rel Prod.snd Prod.snd OutputEq d out)
    (hf : ∀ v d, Execution.Rel OutputEq d (f (v, d))) :
    Execution.Rel OutputEq d (out >>= f) := by
  cases out with
  | error e => exact h
  | ok p => exact Execution.Rel.trans_left outputEq_trans h (hf p.1 p.2)

private theorem bindOutcome {α β : Type} {d : Devm} {get : α → Devm}
    {result : β → Devm} {out : Except (EvmError × Devm) α}
    {f : α → Except (EvmError × Devm) β}
    (h : Outcome.Rel Prod.snd get OutputEq d out)
    (hf : ∀ a, Outcome.Rel Prod.snd result OutputEq (get a) (f a)) :
    Outcome.Rel Prod.snd result OutputEq d (out >>= f) := by
  cases out with
  | error e => exact h
  | ok a =>
      have hk := hf a
      cases hfa : f a <;> rw [hfa] at hk
      all_goals simpa only [Except.bind_ok, hfa, Outcome.Rel] using h.trans hk

private theorem mapSnd {α : Type} {d : Devm}
    {out : Except (EvmError × Devm) (α × Devm)}
    (h : Outcome.Rel Prod.snd Prod.snd OutputEq d out) :
    Execution.Rel OutputEq d (out <&> Prod.snd) := by
  cases out <;> exact h

private theorem balance_output (rules : ForkRules) (d : Devm) :
    Execution.Rel OutputEq d
      (liftMachMetaWorldExecution (Rinst.balanceCore rules) d) := by
  have core : Outcome.Rel (fun e => e.2.2.output) (fun v => v.2.2.output)
      Eq d.meta.output (Rinst.balanceCore rules d.world d.mach d.meta) := by
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
  rcases h : Rinst.balanceCore rules d.world d.mach d.meta with ⟨_, _⟩ | ⟨_, _⟩
    <;> rw [h] at core <;> exact core

private theorem memWrite_output (d : Devm) (i : Nat) (v : Bytes) :
    (d.memWrite i v).output = d.output := rfl

private theorem setStorVal_output (d : Devm) (a : Adr) (k v : B256) :
    (d.setStorVal a k v).output = d.output := rfl

private theorem refund_output (d : Devm) (n : Int) :
    (d.withRefundCounter n).output = d.output := rfl

private theorem accessAddress_output (d : Devm) (a : Adr) :
    (addAccessedAddress d a).output = d.output := rfl

private theorem accessStorage_output (d : Devm) (a : Adr) (k : B256) :
    (addAccessedStorageKey d a k).output = d.output := rfl

private theorem subBalance_output (d : Devm) (a : Adr) (v : B256) :
    Execution.Rel OutputEq d ((d.subBal a v).toExcept
      (.internal (.invariant (.text "InsufficientBalanceError")), d)) := by
  simp only [Devm.subBal, State.subBal]
  split <;> rfl

private theorem delegation_output (g : GasSchedule) (d : Devm) (a : Adr) :
    (g.accessDelegation d a).2.2.2.2.output = d.output := by
  unfold GasSchedule.accessDelegation
  dsimp only
  split <;> rfl

private theorem extends_output (d : Devm) (regions : List (Nat × Nat)) :
    (d.memExtends regions).output = d.output := rfl

private theorem nonce_output (d : Devm) (a : Adr) :
    (d.incrNonce a).output = d.output := rfl

macro "output_pure" : tactic => `(tactic|
  (first | rfl | (simp only [id_eq, delegation_output, extends_output, nonce_output, refund_output, accessAddress_output, memWrite_output, setStorVal_output, Devm.memRead, Mem.read, Devm.setTransVal, Devm.addLog, Devm.withStack, Devm.withMemory, Devm.balReadAccount_output, Devm.balReadStorage_output] <;> rfl) | ((try simp only [refund_output]); split <;> simp only [accessAddress_output, accessStorage_output, Devm.balReadAccount_output, Devm.balReadStorage_output] <;> rfl)))

open _root_.Lean _root_.Lean.Meta _root_.Lean.Elab _root_.Lean.Elab.Tactic in
/-- Deterministic monadic walk. Every simplifier invocation lists its equations. -/
elab "output_step" : tactic => do
  let target ← instantiateMVars (← getMainTarget)
  let args := target.getAppArgs
  unless target.isAppOf ``Execution.Rel && args.size == 3 do
    throwError "output_step: expected an output-preservation relation"
  let e := args[2]!
  let run (s : TacticM (TSyntax `tactic)) : TacticM Unit := do withoutRecover <| evalTactic (← s)
  if e.isAppOfArity ``Bind.bind 6 then
    match (e.getArg! 4).getAppFn.constName? with
    | some ``Devm.pop => run `(tactic|
        (refine bindPair
          (ofMachPair ?inputEq (Devm.pop_machFrame _)) ?_; (case inputEq => output_pure); intro _ _; try dsimp only))
    | some ``Devm.popToNat => run `(tactic|
        (refine bindPair
          (ofMachPair ?inputEq (Devm.popToNat_machFrame _)) ?_; (case inputEq => output_pure); intro _ _; try dsimp only))
    | some ``Devm.popToAdr => run `(tactic|
        (refine bindPair
          (ofMachPair ?inputEq (Devm.popToAdr_machFrame _)) ?_; (case inputEq => output_pure); intro _ _; try dsimp only))
    | some ``Devm.popN => run `(tactic|
        (refine bindPair
          (ofMachPair ?inputEq (Devm.popN_machFrame _ _)) ?_; (case inputEq => output_pure); intro _ _; try dsimp only))
    | some ``Devm.push => run `(tactic|
        (refine Execution.Rel.bind outputEq_trans (ofMach ?inputEq (Devm.push_machFrame _ _)) ?_; (case inputEq => output_pure); intro _))
    | some ``Jaune.chargeGas => run `(tactic|
        (refine Execution.Rel.bind outputEq_trans
          (ofMach ?inputEq (chargeGas_machFrame _ _)) ?_; (case inputEq => output_pure); intro _))
    | some ``Except.ok => run `(tactic| dsimp only [Except.bind_ok])
    | some ``Except.error => run `(tactic| (change _ = _; output_pure))
    | some ``Functor.mapRev => run `(tactic|
        (refine Execution.Rel.bind outputEq_trans
          (mapSnd (ofMachPair ?inputEq (Devm.pop_machFrame _))) ?_; (case inputEq => output_pure); intro _))
    | some ``Jaune.assertDynamic => run `(tactic|
        (simp only [assertDynamic, Except.assert]; split))
    | some ``Except.assert => run `(tactic| (simp only [Except.assert]; split))
    | some ``Option.toExcept => run `(tactic| (refine Execution.Rel.bind outputEq_trans (subBalance_output _ _ _) ?_; intro _))
    | _ => run `(tactic| split)
  else
    match e.getAppFn.constName? with
    | some ``Devm.push => run `(tactic| (refine ofMach ?_ (Devm.push_machFrame _ _); output_pure))
    | some ``Jaune.pushItem => run `(tactic| (refine ofMach ?_ (pushItem_machFrame _ _ _); output_pure))
    | some ``Jaune.chargeGas => run `(tactic| (refine ofMach ?_ (chargeGas_machFrame _ _); output_pure))
    | some ``Jaune.applyUnary => run `(tactic| (refine ofMach ?_ (applyUnary_machFrame _ _ _); output_pure))
    | some ``Jaune.applyBinary => run `(tactic| (refine ofMach ?_ (applyBinary_machFrame _ _ _); output_pure))
    | some ``Jaune.applyTernary => run `(tactic| (refine ofMach ?_ (applyTernary_machFrame _ _ _); output_pure))
    | some ``Jaune.liftMachMetaWorldExecution => run `(tactic| exact balance_output _ _)
    | some ``Except.ok => run `(tactic| (change _ = _; output_pure))
    | some ``Except.error => run `(tactic| (change _ = _; output_pure))
    | _ => run `(tactic| split)

/-- Every regular instruction preserves enclosing output on both outcomes. -/
theorem regular_output {pc : Nat} {sevm : Sevm} {pre : Devm} (r : Rinst)
    (hsg : sevm.benvStat.rules.stateGas = none) :
    Execution.Rel (fun a b => a.output = b.output) pre
      (Rinst.run ⟨pc, sevm, pre⟩ r) := by
  cases r
  all_goals simp only [Rinst.run, Rinst.runCore, hsg]
  all_goals repeat' output_step

open _root_.Lean _root_.Lean.Meta _root_.Lean.Elab _root_.Lean.Elab.Tactic in
elab "jump_output_step" : tactic => do
  let target ← instantiateMVars (← getMainTarget)
  let e := target.getAppArgs.back!
  let run (s : TacticM (TSyntax `tactic)) : TacticM Unit := do
    withoutRecover <| evalTactic (← s)
  if e.isAppOfArity ``Bind.bind 6 then
    match (e.getArg! 4).getAppFn.constName? with
    | some ``Devm.pop => run `(tactic|
        (refine bindOutcome (ofMachPair rfl (Devm.pop_machFrame _)) ?_; intro p; rcases p with ⟨v, d⟩; dsimp only))
    | some ``Jaune.chargeGas => run `(tactic|
        (refine bindOutcome (ofMach rfl (chargeGas_machFrame _ _)) ?_; intro d))
    | some ``Except.ok => run `(tactic| dsimp only [Except.bind_ok])
    | some ``Except.error => run `(tactic| (change _ = _; rfl))
    | some ``Except.assert => run `(tactic| (simp only [Except.assert]; split))
    | _ => run `(tactic| split)
  else
    match e.getAppFn.constName? with
    | some ``Except.ok => run `(tactic| (change _ = _; rfl))
    | some ``Except.error => run `(tactic| (change _ = _; rfl))
    | _ => run `(tactic| split)

/-- Jumps preserve the enclosing output on both outcomes. -/
theorem jump_output {pc : Nat} {sevm : Sevm} {pre : Devm} (j : Jinst) :
    Outcome.Rel Prod.snd Prod.snd OutputEq pre (Jinst.run ⟨pc, sevm, pre⟩ j) := by
  cases j
  all_goals simp only [Jinst.run, Jinst.runCore]
  all_goals repeat' jump_output_step

/-- Ordinary terminal output is inherited or produced by a word-sized read. -/
def OutputProvenance (a b : Devm) : Prop :=
  a.output = b.output ∨ b.output.length < 2 ^ 256

private theorem outputProvenance_of_eq {a : Devm} {out : Execution}
    (h : Execution.Rel OutputEq a out) :
    Execution.Rel OutputProvenance a out := by
  cases out <;> exact Or.inl h

/-- RETURN and REVERT take their full output size from a popped word. -/
theorem last_output {sevm : Sevm} {pre : Devm} (l : Linst)
    (hsg : sevm.benvStat.rules.stateGas = none) :
    Execution.Rel OutputProvenance pre (Linst.run sevm pre l) := by
  cases l with
  | stop => exact Or.inl rfl
  | selfdestruct =>
      apply outputProvenance_of_eq
      simp only [Linst.run, hsg]
      repeat' output_step
  | return_ | revert =>
      simp only [Linst.run, Devm.popToNat_def, Bind.bind, Except.bind,
        Functor.mapRev, Functor.map, Except.map, Prod.mapFst, Prod.map]
      rcases hp1 : pre.pop with e | ⟨i, d1⟩ <;> dsimp only [id_eq]
      · have he := ofMachPair rfl (Devm.pop_machFrame pre)
        rw [hp1] at he
        exact Or.inl he
      · have h1 := ofMachPair rfl (Devm.pop_machFrame pre)
        rw [hp1] at h1
        rcases hp2 : d1.pop with e | ⟨n, d2⟩ <;> try dsimp only [id_eq]
        · have he := ofMachPair rfl (Devm.pop_machFrame d1)
          rw [hp2] at he
          exact Or.inl (h1.trans he)
        · have h2 := ofMachPair rfl (Devm.pop_machFrame d1)
          rw [hp2] at h2
          rcases hg : chargeGas (d2.extCost [(i.toNat, n.toNat)]) d2 with e | d3 <;> try dsimp only [id_eq]
          · have he := ofMach rfl (chargeGas_machFrame (d2.extCost [(i.toNat, n.toNat)]) d2)
            rw [hg] at he
            exact Or.inl (h1.trans (h2.trans he))
          · simp only [Execution.Rel, Outcome.Rel, OutputProvenance, id_eq]
            right
            change (d3.memRead i.toNat n.toNat).1.length < 2 ^ 256
            rw [Devm.memRead_fst]
            simp only [Mem.read, Blanc.ExecutionTrace.Array.sliceD_length]
            exact B256.toNat_lt n

/-- The normal CREATE resume preserves parent output, including error outcomes. -/
theorem create_resume_output (parent : Devm) (a : Adr)
    (r : Except (EvmError × State × AdrSet × Tra) Devm) :
    Execution.Rel OutputEq parent ((Resume.create parent a).run r) := by
  cases r <;> simp only [Resume.run, liftToExecution, Except.bind_ok, Except.bind_error]
  all_goals repeat' output_step

/-- The normal CALL resume preserves parent output, including error outcomes. -/
theorem call_resume_output (parent : Devm) (oi os : Nat)
    (r : Except (EvmError × State × AdrSet × Tra) Devm) :
    Execution.Rel OutputEq parent ((Resume.call parent oi os).run r) := by
  cases r <;> simp only [Resume.run, liftToExecution, Except.bind_ok, Except.bind_error]
  all_goals repeat' output_step

private def StepOutput (pre : Devm) : XStep → Prop
  | .done out => Execution.Rel OutputEq pre out
  | .spawn _ rsm => ∀ r, Execution.Rel OutputEq pre (rsm.run r)

private theorem stepOutput_trans {a b : Devm} {s : XStep}
    (hab : OutputEq a b) (h : StepOutput b s) : StepOutput a s := by
  cases s with
  | done out => exact Execution.Rel.trans_left outputEq_trans hab h
  | spawn f rsm => intro r; exact Execution.Rel.trans_left outputEq_trans hab (h r)

private theorem stepOutput_bind {α : Type} {d : Devm} {get : α → Devm}
    {out : Except (EvmError × Devm) α} {f : α → Except (EvmError × Devm) XStep}
    (h : Outcome.Rel Prod.snd get OutputEq d out)
    (hf : ∀ a, StepOutput (get a) (XStep.ofExcept (f a))) :
    StepOutput d (XStep.ofExcept (out >>= f)) := by
  cases out with
  | error e => exact h
  | ok a => exact stepOutput_trans h (hf a)


open _root_.Lean _root_.Lean.Meta _root_.Lean.Elab _root_.Lean.Elab.Tactic in
elab "spawn_output_step" : tactic => do
  withoutRecover <| evalTactic (← `(tactic| try dsimp only [id_eq]))
  let target ← instantiateMVars (← getMainTarget)
  unless target.isAppOf ``StepOutput do throwError "expected StepOutput"
  let e := target.getAppArgs.back!
  let run (s : TacticM (TSyntax `tactic)) : TacticM Unit := do
    withoutRecover <| evalTactic (← s)
  if e.isAppOfArity ``XStep.ofExcept 1 then
    let out := e.getArg! 0
    if out.isAppOfArity ``Bind.bind 6 then
      match (out.getArg! 4).getAppFn.constName? with
      | some ``Devm.pop => run `(tactic|
          (refine stepOutput_bind (ofMachPair ?inputEq (Devm.pop_machFrame _)) ?_; (case inputEq => output_pure); intro p; rcases p with ⟨v, d⟩; try dsimp only))
      | some ``Devm.popToNat => run `(tactic|
          (refine stepOutput_bind (ofMachPair ?inputEq (Devm.popToNat_machFrame _)) ?_; (case inputEq => output_pure); intro p; rcases p with ⟨v, d⟩; try dsimp only))
      | some ``Devm.popToAdr => run `(tactic|
          (refine stepOutput_bind (ofMachPair ?inputEq (Devm.popToAdr_machFrame _)) ?_; (case inputEq => output_pure); intro p; rcases p with ⟨v, d⟩; try dsimp only))
      | some ``Jaune.chargeGas => run `(tactic|
          (refine stepOutput_bind (ofMach ?inputEq (chargeGas_machFrame _ _)) ?_; (case inputEq => output_pure); intro d))
      | some ``Devm.push => run `(tactic|
          (refine stepOutput_bind (ofMach ?inputEq (Devm.push_machFrame _ _)) ?_; (case inputEq => output_pure); intro d))
      | some ``Except.assert => run `(tactic| (simp only [Except.assert]; split))
      | some ``Jaune.assertDynamic => run `(tactic| (simp only [assertDynamic, Except.assert]; split))
      | some ``Except.ok => run `(tactic| dsimp only [Except.bind_ok])
      | some ``Except.error => run `(tactic| (change _ = _; output_pure))
      | _ => run `(tactic| split)
    else
      match out.getAppFn.constName? with
      | some ``Pure.pure => run `(tactic| dsimp only [Pure.pure, Except.pure, XStep.ofExcept])
      | some ``Except.ok => run `(tactic| dsimp only [XStep.ofExcept])
      | some ``Except.error => run `(tactic| (change _ = _; output_pure))
      | _ => run `(tactic| split)
  else
    match e.getAppFn.constName? with
    | some ``Jaune.genericCall.step => run `(tactic| (unfold genericCall.step; split))
    | some ``Jaune.genericCreate.step => run `(tactic| unfold genericCreate.step)
    | some ``XStep.done => run `(tactic| (change Execution.Rel OutputEq _ _; repeat' output_step))
    | some ``XStep.spawn => run `(tactic|
        (intro r; first | (refine Execution.Rel.trans_left outputEq_trans ?_ (call_resume_output _ _ _ r); output_pure) | (refine Execution.Rel.trans_left outputEq_trans ?_ (create_resume_output _ _ r); output_pure)))
    | _ => run `(tactic| split)

/-- A spawning opcode preserves its enclosing output through every normal resume. -/
private theorem spawn_output {sevm : Sevm} {pre : Devm} (x : Xinst)
    (hsg : sevm.benvStat.rules.stateGas = none) : StepOutput pre (Xinst.step sevm pre x) := by
  cases x
  all_goals simp only [Xinst.step, hsg]
  all_goals repeat' spawn_output_step

private def DriverOutput (pre : Devm) : Step → Prop
  | .halt out => Execution.Rel OutputProvenance pre out
  | .cont _ d => OutputEq pre d
  | .spawn _ rsm _ => ∀ r, Execution.Rel OutputEq pre (rsm.run r)

private theorem ofExecution_output {pre : Devm} {out : Execution} (pc : Nat)
    (h : Execution.Rel OutputEq pre out) : DriverOutput pre (Step.ofExecution pc out) := by
  cases out with
  | error e => exact Or.inl h
  | ok d => exact h

private theorem ofJump_output {pre : Devm} {out : Except (EvmError × Devm) (Nat × Devm)}
    (h : Outcome.Rel Prod.snd Prod.snd OutputEq pre out) :
    DriverOutput pre (Step.ofJump out) := by
  cases out with
  | error e => exact Or.inl h
  | ok p => exact h

private theorem toStep_output {pre : Devm} {s : XStep} (pc : Nat)
    (h : StepOutput pre s) : DriverOutput pre (XStep.toStep pc s) := by
  cases s with
  | done out => exact ofExecution_output pc h
  | spawn f rsm => exact h

private theorem driver_output {pc : Nat} {sevm : Sevm} {pre : Devm}
    (hsg : sevm.benvStat.rules.stateGas = none) :
    DriverOutput pre (Evm.step ⟨pc, sevm, pre⟩) := by
  unfold Evm.step
  split
  · exact Or.inl rfl
  · rename_i n _
    cases n
    case reg r hgi => exact ofExecution_output _ (regular_output r hsg)
    case exec x hgi => exact toStep_output _ (spawn_output x hsg)
    all_goals simp only [Ninst.step]
    all_goals apply ofExecution_output
    all_goals repeat' output_step
  · exact ofJump_output (jump_output _)
  · exact last_output _ hsg

private theorem provenance_left_eq {a b : Devm} {out : Execution}
    (hab : OutputEq a b) (h : Execution.Rel OutputProvenance b out) :
    Execution.Rel OutputProvenance a out := by
  cases out <;> rcases h with h | h
  all_goals first | exact Or.inl (hab.trans h) | exact Or.inr h

/-- Ordinary execution inherits its initial output or produces a word-sized result.
The arbitrary initial output is deliberately not assumed to be short. -/
theorem exec_output {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (cr : Exec pc sevm pre out) (hsg : sevm.benvStat.rules.stateGas = none) :
    Execution.Rel OutputProvenance pre out := by
  induction cr with
  | @halt pc sevm devm ex hs =>
      have h := driver_output (pc := pc) (pre := devm) hsg
      rw [hs] at h
      exact h
  | @cont pc sevm devm pc2 devm2 ex hs cr ih =>
      have h := driver_output (pc := pc) (pre := devm) hsg
      rw [hs] at h
      exact provenance_left_eq h (ih hsg)
  | @doneErr pc sevm devm f rsm pc2 r e hs he hr =>
      have h := driver_output (pc := pc) (pre := devm) hsg
      rw [hs] at h
      have ho := h r
      rw [hr] at ho
      exact Or.inl ho
  | @doneOk pc sevm devm f rsm pc2 r devm2 ex hs he hr cr ih =>
      have h := driver_output (pc := pc) (pre := devm) hsg
      rw [hs] at h
      have ho := h r
      rw [hr] at ho
      exact provenance_left_eq ho (ih hsg)
  | @runErr pc sevm devm f rsm pc2 cevm raw e hs he child hr ih =>
      have h := driver_output (pc := pc) (pre := devm) hsg
      rw [hs] at h
      have ho := h (f.settle raw)
      rw [hr] at ho
      exact Or.inl ho
  | @runOk pc sevm devm f rsm pc2 cevm raw devm2 ex hs he child hr cr ihchild ih =>
      have h := driver_output (pc := pc) (pre := devm) hsg
      rw [hs] at h
      have ho := h (f.settle raw)
      rw [hr] at ho
      exact provenance_left_eq ho (ih hsg)

private def SuccessfulOutputBound : Except (EvmError × State × AdrSet × Tra) Devm → Prop
  | .error _ => True
  | .ok d => d.output.length < 2^256

private theorem output_of_seed_bound {pre : Devm} {raw : Execution}
    (hs : pre.output.length < 2^256) (hp : Execution.Rel OutputProvenance pre raw) :
    Execution.Rel (fun _ d => d.output.length < 2^256) pre raw := by
  cases raw <;> change List.length _ < 2^256
  all_goals rcases hp with he | hb
  · rw [← he]; exact hs
  · exact hb
  · rw [← he]; exact hs
  · exact hb

private theorem handleError_output {pre : Devm} {raw : Execution}
    (h : Execution.Rel (fun _ d => d.output.length < 2^256) pre raw) :
    SuccessfulOutputBound (executeCode.handleError raw) := by
  cases raw with
  | ok d => exact h
  | error e =>
    rcases e with ⟨reason, d⟩
    cases reason
    · exact (show (0 : Nat) < 2^256 from by decide)
    · exact h
    · exact True.intro
    · exact True.intro

private theorem process_settle_output (msg : Msg)
    (r : Except (EvmError × State × AdrSet × Tra) Devm)
    (h : SuccessfulOutputBound r) : SuccessfulOutputBound (processMessage.settle msg r) := by
  cases r with
  | error e => exact True.intro
  | ok d =>
    unfold processMessage.settle
    dsimp only [bind, Except.bind]
    split <;> exact h

private theorem executeCode_output {msg : Msg} {xl : Xlot}
    {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (hf : xl.Filled) (hc : ExecuteCode msg xl r)
    (hsg : msg.benv.stat.rules.stateGas = none) (hi : msg.data.length < 2^256) :
    SuccessfulOutputBound r := by
  cases xl with
  | none =>
    unfold ExecuteCode at hc
    cases he : executeCode.enter msg with
    | inl evm =>
      rw [he] at hc
      obtain ⟨raw, hxl, _⟩ := hc
      cases hxl
    | inr raw =>
      rw [he] at hc
      rw [hc.2, hsg, executeCode.handleErrorWith_none]
      obtain ⟨adr, rfl⟩ := executeCode.enter_inr he
      exact handleError_output
        (PrecompileOutputBound.executePrecomp_output (initEvm msg) adr hi (by change (0 : Nat) < 2^256; decide))
  | some v =>
    rcases v with ⟨evm, raw⟩
    obtain ⟨he, hr⟩ := ExecuteCode.some_inv hc
    obtain ⟨cr⟩ := hf
    subst evm
    rw [hr, hsg, executeCode.handleErrorWith_none]
    exact handleError_output (output_of_seed_bound (by change (0 : Nat) < 2^256; decide) (exec_output cr hsg))

/-- A real retained message call produces short output, including normally
settled REVERT and exceptional-halt children. Its ordinary seed is initialized
by the interpreter, and its precompile input is the actual message data. -/
theorem processMessage_output {msg : Msg} {xl : Xlot} {child : Devm}
    (hf : xl.Filled) (hm : ProcessMessage msg xl (.ok child))
    (hsg : msg.benv.stat.rules.stateGas = none) (hi : msg.data.length < 2^256) :
    child.output.length < 2^256 := by
  obtain ⟨r0, hb, hs⟩ := ProcessMessage.iff_body.mp hm
  have hp : SuccessfulOutputBound (.ok child) := by
    rw [hs]
    apply process_settle_output
    unfold FrameBody at hb
    cases ht : msg.benvAfterTransfer with
    | error e =>
      rw [ht] at hb
      rw [hb.2]
      exact True.intro
    | ok benv =>
      rw [ht] at hb
      apply executeCode_output hf hb
      · change benv.stat.rules.stateGas = none
        rw [Msg.benvAfterTransfer_ok_stateGas ht]
        exact hsg
      · exact hi
  exact hp

private def CallShape : XStep → Prop
  | .done ex => ∀ post, ex = .ok post → post.returnData = []
  | .spawn f rsm => ∃ msg parent oi os,
      f = Frame.ofCall msg ∧ rsm = Resume.call parent oi os

private theorem callShape_bind {α : Type} {out : Except (EvmError × Devm) α}
    {f : α → Except (EvmError × Devm) XStep}
    (hf : ∀ a, out = .ok a → CallShape (XStep.ofExcept (f a))) :
    CallShape (XStep.ofExcept (out >>= f)) := by
  cases out with
  | error e => intro post he; cases he
  | ok a => exact hf a rfl

open _root_.Lean _root_.Lean.Meta _root_.Lean.Elab _root_.Lean.Elab.Tactic in
elab "call_shape_step" : tactic => do
  withoutRecover <| evalTactic (← `(tactic| try dsimp only [id_eq]))
  let target ← instantiateMVars (← getMainTarget)
  unless target.isAppOf ``CallShape do throwError "expected CallShape"
  let e := target.getAppArgs.back!
  let run (s : TacticM (TSyntax `tactic)) : TacticM Unit := do
    withoutRecover <| evalTactic (← s)
  if e.isAppOfArity ``XStep.ofExcept 1 then
    let out := e.getArg! 0
    if out.isAppOfArity ``Bind.bind 6 then
      match (out.getArg! 4).getAppFn.constName? with
      | some ``Except.assert => run `(tactic| (simp only [Except.assert]; split))
      | some ``Pure.pure => run `(tactic| dsimp only [Pure.pure, Except.pure, Except.bind_ok])
      | some ``Except.ok => run `(tactic| dsimp only [Except.bind_ok])
      | some ``Except.error => run `(tactic| (intro post he; cases he))
      | _ => run `(tactic| (apply callShape_bind; intro value hvalue))
    else
      match out.getAppFn.constName? with
      | some ``Pure.pure => run `(tactic| dsimp only [Pure.pure, Except.pure, XStep.ofExcept])
      | some ``Except.ok => run `(tactic| dsimp only [XStep.ofExcept])
      | some ``Except.error => run `(tactic| (intro post he; cases he))
      | _ => run `(tactic| split)
  else
    match e.getAppFn.constName? with
    | some ``Jaune.genericCall.step => run `(tactic| (unfold genericCall.step; split))
    | some ``XStep.done =>
      run `(tactic| (intro post he; cases he))
      try run `(tactic| rfl)
      catch _ => withMainContext do
        for decl in ← getLCtx do
          let ty ← instantiateMVars decl.type
          if ty.isAppOfArity ``Eq 3 && (ty.getArg! 1).isAppOf ``Devm.push then
            let hp := mkIdent decl.userName
            run `(tactic| (rw [← (Devm.push_of_push $hp).returnData]; rfl))
            return
        throwError "expected the retained successful push equation"
    | some ``XStep.spawn => run `(tactic| exact ⟨_, _, _, _, rfl, rfl⟩)
    | _ => run `(tactic| split)

private theorem call_shape {sevm : Sevm} {pre : Devm} {x : Xinst}
    (hx : x = .call ∨ x = .staticcall)
    (hsg : sevm.benvStat.rules.stateGas = none) : CallShape (Xinst.step sevm pre x) := by
  rcases hx with rfl | rfl
  all_goals simp only [Xinst.step, hsg]
  all_goals repeat' call_shape_step

private theorem call_xstep_returnData_length_lt
    {sevm : Sevm} {pre post : Devm} {x : Xinst} {xl : Xlot}
    (hx : x = .call ∨ x = .staticcall) (hsg : sevm.benvStat.rules.stateGas = none)
    (hf : xl.Filled) (hrun : XStep.Run (Xinst.step sevm pre x) xl (.ok post)) :
    post.returnData.length < 2^256 := by
  have hs := call_shape (pre := pre) hx hsg
  cases he : Xinst.step sevm pre x with
  | done ex =>
    rw [he] at hs hrun
    have hret := hs post hrun.2.symm
    rw [hret]
    decide
  | spawn f rsm =>
    have hi := Blanc.ExecutionTrace.Xinst.step_spawn_inner_data_length_lt hsg he
    have hstat := Xinst.step_spawn_benvStat he
    rw [he] at hs hrun
    obtain ⟨msg, parent, oi, os, rfl, rfl⟩ := hs
    obtain ⟨r, hm, hr⟩ := hrun
    cases r with
    | error e =>
      unfold Resume.run liftToExecution at hr
      dsimp only [bind, Except.bind] at hr
      cases hr
    | ok child =>
      have ho := processMessage_output hf hm (by
        change msg.benv.stat = sevm.benvStat at hstat
        rw [hstat]
        exact hsg) hi
      rw [Resume.call_returnData hr.symm]
      exact ho

/-- Actual CALL/STATICCALL steps install short full returndata. The bound comes
from the retained child producer and includes normally settled failed children,
independently of the caller's requested output-copy window. -/
theorem call_step_returnData_length_lt
    {pc : Nat} {sevm : Sevm} {pre post : Devm} {x : Xinst} {xl : Xlot}
    (hx : x = .call ∨ x = .staticcall) (hsg : sevm.benvStat.rules.stateGas = none)
    (hf : xl.Filled) (hrun : Ninst.StepRun pc sevm pre (.exec x) xl (.ok post)) :
    post.returnData.length < 2^256 := by
  rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep] at hrun
  exact call_xstep_returnData_length_lt hx hsg hf hrun

/-- A successful actual CALL result has short full returndata on covered forks. -/
theorem call_returnData_length_lt {sevm : Sevm} {pre post : Devm}
    (hrun : Ninst.Run sevm pre Ninst.call post) (hfork : CoveredFork sevm.benvStat.fork) :
    post.returnData.length < 2^256 := by
  obtain ⟨xl, hf, pc, hr⟩ := hrun
  exact call_step_returnData_length_lt (Or.inl rfl) hfork.rules_stateGas_none hf hr

/-- A successful actual STATICCALL result has short full returndata on covered forks. -/
theorem staticcall_returnData_length_lt {sevm : Sevm} {pre post : Devm}
    (hrun : Ninst.Run sevm pre Ninst.staticcall post) (hfork : CoveredFork sevm.benvStat.fork) :
    post.returnData.length < 2^256 := by
  obtain ⟨xl, hf, pc, hr⟩ := hrun
  exact call_step_returnData_length_lt (Or.inr rfl) hfork.rules_stateGas_none hf hr

end Blanc.Lift.ReturnDataBound
