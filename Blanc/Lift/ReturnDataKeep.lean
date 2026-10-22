import Blanc.Lift.Silent

/-!
# Regular instructions keep the return-data buffer

Only the call and create instructions (`Xinst`) install return data; every regular
instruction (`Rinst`) leaves `Devm.returnData` alone, on both outcomes
(`regular_returnData`), and so does a successful regular step (`Ninst.Run.reg_returnData`).
The walk is the one `Blanc/Lift/ReturnDataBound.lean` runs for the enclosing output, with
the return-data projection.  Contract-neutral.
-/

namespace Blanc.Lift.ReturnDataKeep

open Jaune

private theorem balReadAccount_rd {rules : ForkRules} {a : Adr} {devm : Devm} :
    (Devm.balReadAccount rules a devm).returnData = devm.returnData := by
  unfold Devm.balReadAccount Meta.readAccount; split <;> rfl

private theorem balReadStorage_rd {rules : ForkRules} {a : Adr} {k : B256} {devm : Devm} :
    (Devm.balReadStorage rules a k devm).returnData = devm.returnData := by
  unfold Devm.balReadStorage Meta.readStorage; split <;> rfl

private abbrev RdEq (a b : Devm) : Prop := a.returnData = b.returnData

private theorem rdEq_trans : TransitiveRel RdEq :=
  fun _ _ _ hab hbc => hab.trans hbc

private theorem ofMach {a b : Devm} {out : Execution}
    (hab : a.returnData = b.returnData) (h : Execution.Rel Devm.MachFrame b out) :
    Execution.Rel RdEq a out := by
  cases out <;> exact hab.trans h.returnData

private theorem ofMachPair {α : Type} {a b : Devm}
    {out : Except (EvmError × Devm) (α × Devm)}
    (hab : a.returnData = b.returnData)
    (h : Outcome.Rel Prod.snd Prod.snd Devm.MachFrame b out) :
    Outcome.Rel Prod.snd Prod.snd RdEq a out := by
  cases out <;> exact hab.trans h.returnData

private theorem bindPair {α : Type} {d : Devm}
    {out : Except (EvmError × Devm) (α × Devm)} {f : α × Devm → Execution}
    (h : Outcome.Rel Prod.snd Prod.snd RdEq d out)
    (hf : ∀ v d, Execution.Rel RdEq d (f (v, d))) :
    Execution.Rel RdEq d (out >>= f) := by
  cases out with
  | error e => exact h
  | ok p => exact Execution.Rel.trans_left rdEq_trans h (hf p.1 p.2)

private theorem mapSnd {α : Type} {d : Devm}
    {out : Except (EvmError × Devm) (α × Devm)}
    (h : Outcome.Rel Prod.snd Prod.snd RdEq d out) :
    Execution.Rel RdEq d (out <&> Prod.snd) := by
  cases out <;> exact h

private theorem balance_rd (rules : ForkRules) (d : Devm) :
    Execution.Rel RdEq d
      (liftMachMetaWorldExecution (Rinst.balanceCore rules) d) := by
  have core : Outcome.Rel (fun e => e.2.2.returnData) (fun v => v.2.2.returnData)
      Eq d.meta.returnData (Rinst.balanceCore rules d.world d.mach d.meta) := by
    unfold Rinst.balanceCore
    dsimp only
    repeat' split
    all_goals rfl
  unfold liftMachMetaWorldExecution liftMachMetaExecution liftMachMeta
    Footprint.toExecution Footprint.liftOutcome
  dsimp only
  rcases h : Rinst.balanceCore rules d.world d.mach d.meta with ⟨_, _⟩ | ⟨_, _⟩
    <;> rw [h] at core <;> exact core

private theorem memWrite_rd (d : Devm) (i : Nat) (v : Bytes) :
    (d.memWrite i v).returnData = d.returnData := rfl

private theorem setStorVal_rd (d : Devm) (a : Adr) (k v : B256) :
    (d.setStorVal a k v).returnData = d.returnData := rfl

private theorem refund_rd (d : Devm) (n : Int) :
    (d.withRefundCounter n).returnData = d.returnData := rfl

private theorem accessAddress_rd (d : Devm) (a : Adr) :
    (addAccessedAddress d a).returnData = d.returnData := rfl

private theorem accessStorage_rd (d : Devm) (a : Adr) (k : B256) :
    (addAccessedStorageKey d a k).returnData = d.returnData := rfl

private theorem subBalance_rd (d : Devm) (a : Adr) (v : B256) :
    Execution.Rel RdEq d ((d.subBal a v).toExcept
      (.internal (.invariant (.text "InsufficientBalanceError")), d)) := by
  simp only [Devm.subBal, State.subBal]
  split <;> rfl

private theorem delegation_rd (g : GasSchedule) (d : Devm) (a : Adr) :
    (g.accessDelegation d a).2.2.2.2.returnData = d.returnData := by
  unfold GasSchedule.accessDelegation
  dsimp only
  split <;> rfl

private theorem extends_rd (d : Devm) (regions : List (Nat × Nat)) :
    (d.memExtends regions).returnData = d.returnData := rfl

private theorem nonce_rd (d : Devm) (a : Adr) :
    (d.incrNonce a).returnData = d.returnData := rfl

macro "rd_pure" : tactic => `(tactic|
  (first | rfl | (simp only [id_eq, delegation_rd, extends_rd, nonce_rd, refund_rd, accessAddress_rd, memWrite_rd, setStorVal_rd, Devm.memRead, Mem.read, Devm.setTransVal, Devm.addLog, Devm.withStack, Devm.withMemory, balReadAccount_rd, balReadStorage_rd] <;> rfl) | ((try simp only [refund_rd]); (repeat' split) <;> (first | rfl | (simp only [accessAddress_rd, accessStorage_rd, balReadAccount_rd, balReadStorage_rd] <;> rfl)))))

open _root_.Lean _root_.Lean.Meta _root_.Lean.Elab _root_.Lean.Elab.Tactic in
/-- Deterministic monadic walk. Every simplifier invocation lists its equations. -/
elab "rd_step" : tactic => do
  let target ← instantiateMVars (← getMainTarget)
  let args := target.getAppArgs
  unless target.isAppOf ``Execution.Rel && args.size == 3 do
    throwError "rd_step: expected a return-data preservation relation"
  let e := args[2]!
  let run (s : TacticM (TSyntax `tactic)) : TacticM Unit := do withoutRecover <| evalTactic (← s)
  if e.isAppOfArity ``Bind.bind 6 then
    match (e.getArg! 4).getAppFn.constName? with
    | some ``Devm.pop => run `(tactic|
        (refine bindPair
          (ofMachPair ?inputEq (Devm.pop_machFrame _)) ?_; (case inputEq => rd_pure); intro _ _; try dsimp only))
    | some ``Devm.popToNat => run `(tactic|
        (refine bindPair
          (ofMachPair ?inputEq (Devm.popToNat_machFrame _)) ?_; (case inputEq => rd_pure); intro _ _; try dsimp only))
    | some ``Devm.popToAdr => run `(tactic|
        (refine bindPair
          (ofMachPair ?inputEq (Devm.popToAdr_machFrame _)) ?_; (case inputEq => rd_pure); intro _ _; try dsimp only))
    | some ``Devm.popN => run `(tactic|
        (refine bindPair
          (ofMachPair ?inputEq (Devm.popN_machFrame _ _)) ?_; (case inputEq => rd_pure); intro _ _; try dsimp only))
    | some ``Devm.push => run `(tactic|
        (refine Execution.Rel.bind rdEq_trans (ofMach ?inputEq (Devm.push_machFrame _ _)) ?_; (case inputEq => rd_pure); intro _))
    | some ``Jaune.chargeGas => run `(tactic|
        (refine Execution.Rel.bind rdEq_trans
          (ofMach ?inputEq (chargeGas_machFrame _ _)) ?_; (case inputEq => rd_pure); intro _))
    | some ``Except.ok => run `(tactic| dsimp only [Except.bind_ok])
    | some ``Except.error => run `(tactic| (change _ = _; rd_pure))
    | some ``Functor.mapRev => run `(tactic|
        (refine Execution.Rel.bind rdEq_trans
          (mapSnd (ofMachPair ?inputEq (Devm.pop_machFrame _))) ?_; (case inputEq => rd_pure); intro _))
    | some ``Jaune.assertDynamic => run `(tactic|
        (simp only [assertDynamic, Except.assert]; split))
    | some ``Except.assert => run `(tactic| (simp only [Except.assert]; split))
    | some ``Option.toExcept => run `(tactic| (refine Execution.Rel.bind rdEq_trans (subBalance_rd _ _ _) ?_; intro _))
    | _ => run `(tactic| split)
  else
    match e.getAppFn.constName? with
    | some ``Devm.push => run `(tactic| (refine ofMach ?_ (Devm.push_machFrame _ _); rd_pure))
    | some ``Jaune.pushItem => run `(tactic| (refine ofMach ?_ (pushItem_machFrame _ _ _); rd_pure))
    | some ``Jaune.chargeGas => run `(tactic| (refine ofMach ?_ (chargeGas_machFrame _ _); rd_pure))
    | some ``Jaune.applyUnary => run `(tactic| (refine ofMach ?_ (applyUnary_machFrame _ _ _); rd_pure))
    | some ``Jaune.applyBinary => run `(tactic| (refine ofMach ?_ (applyBinary_machFrame _ _ _); rd_pure))
    | some ``Jaune.applyTernary => run `(tactic| (refine ofMach ?_ (applyTernary_machFrame _ _ _); rd_pure))
    | some ``Jaune.liftMachMetaWorldExecution => run `(tactic| exact balance_rd _ _)
    | some ``Except.ok => run `(tactic| (change _ = _; rd_pure))
    | some ``Except.error => run `(tactic| (change _ = _; rd_pure))
    | _ => run `(tactic| split)

/-- **Every regular instruction keeps the return-data buffer**, on both outcomes. -/
theorem regular_returnData {pc : Nat} {sevm : Sevm} {pre : Devm} (r : Rinst)
    (hsg : sevm.benvStat.rules.stateGas = none) :
    Execution.Rel (fun a b => a.returnData = b.returnData) pre
      (Rinst.run ⟨pc, sevm, pre⟩ r) := by
  cases r
  all_goals simp only [Rinst.run, Rinst.runCore, hsg]
  all_goals repeat' rd_step

/-- A successful regular step keeps the return-data buffer. -/
theorem Ninst.Run.reg_returnData {sevm : Sevm} {d d' : Devm} {r : Rinst}
    (hsg : sevm.benvStat.rules.stateGas = none) (run : Ninst.Run sevm d (.reg r) d') :
    d'.returnData = d.returnData := by
  rcases run with ⟨xl, -, pc, hrun⟩
  simp only [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at hrun
  have h := regular_returnData (pc := pc) (pre := d) r hsg
  rw [← hrun.2] at h
  exact h.symm

end Blanc.Lift.ReturnDataKeep
