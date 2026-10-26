import Blanc.ExecDeterminism
import Blanc.ExecutionTrace

/-! Uniqueness of actual retained traces from their deterministic inputs. -/

namespace Blanc.ExecutionTrace

open Jaune

theorem RetainedXlot.eq_of_same {xl : Xlot}
    (left right : RetainedXlot xl) : left = right := by
  cases left <;> cases right <;> simp_all only [ExceptT.stM_eq, ExecutionTrace.RetainedXlot.some.injEq]
  apply Exec.unique

/-- A filled retained slot satisfying the deterministic frame wrapper is
uniquely indexed, even though `RunFrame` itself existentially names the raw
child outcome. -/
theorem RetainedXlot.index_eq_of_runFrame
    {f : Jaune.Frame}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    {leftSlot rightSlot : Xlot}
    (leftRetained : RetainedXlot leftSlot)
    (rightRetained : RetainedXlot rightSlot)
    (leftRun : RunFrame f leftSlot out)
    (rightRun : RunFrame f rightSlot out) : leftSlot = rightSlot := by
  cases henter : f.enter with
  | done settled =>
      simp only [RunFrame, henter] at leftRun rightRun
      exact leftRun.1.trans rightRun.1.symm
  | run evm =>
      simp only [RunFrame, henter] at leftRun rightRun
      rcases leftRun with ⟨leftOut, rfl, _⟩
      rcases rightRun with ⟨rightOut, rfl, _⟩
      cases leftRetained with
      | some leftExec =>
          cases rightRetained with
          | some rightExec =>
              rw [Exec.result_unique leftExec rightExec]

theorem ProcessMessageTrace.eq_of_same
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (left right : ProcessMessageTrace msg out) : left = right := by
  rcases left with ⟨leftSlot, leftRetained, leftRun⟩
  rcases right with ⟨rightSlot, rightRetained, rightRun⟩
  change RunFrame (Jaune.Frame.ofCall msg) leftSlot out at leftRun
  change RunFrame (Jaune.Frame.ofCall msg) rightSlot out at rightRun
  have hslot := RetainedXlot.index_eq_of_runFrame
    leftRetained rightRetained leftRun rightRun
  subst rightSlot
  have hretained := RetainedXlot.eq_of_same leftRetained rightRetained
  subst rightRetained
  rfl

theorem ProcessCreateMessageTrace.eq_of_same
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (left right : ProcessCreateMessageTrace msg out) : left = right := by
  rcases left with ⟨leftSlot, leftRetained, leftRun⟩
  rcases right with ⟨rightSlot, rightRetained, rightRun⟩
  change RunFrame (Jaune.Frame.ofCreate msg) leftSlot out at leftRun
  change RunFrame (Jaune.Frame.ofCreate msg) rightSlot out at rightRun
  have hslot := RetainedXlot.index_eq_of_runFrame
    leftRetained rightRetained leftRun rightRun
  subst rightSlot
  have hretained := RetainedXlot.eq_of_same leftRetained rightRetained
  subst rightRetained
  rfl

theorem MessageCallTrace.toResult
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) :
    processMessageCall msg = .ok (state, out) :=
  Blanc.ExecutionTrace.MessageCallTrace.result trace

theorem MessageCallTrace.index_eq_of_same_input
    {msg : Msg} {leftState rightState : State}
    {leftOut rightOut : MsgCallOutput}
    (left : MessageCallTrace msg leftState leftOut)
    (right : MessageCallTrace msg rightState rightOut) :
    leftState = rightState ∧ leftOut = rightOut := by
  have hpair : (leftState, leftOut) = (rightState, rightOut) :=
    Except.ok.inj (left.toResult.symm.trans right.toResult)
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

theorem MessageCallTrace.eq_of_same
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (left right : MessageCallTrace msg state out) : left = right := by
  cases left with
  | createCollision ltarget lcollision _ =>
      cases right with
      | createCollision => rfl
      | createRun _ rcollision =>
          rw [lcollision] at rcollision
          cases rcollision
      | callRun rtarget =>
          rw [ltarget] at rtarget
          cases rtarget
  | createRun ltarget lcollision levm lcore ltrace _ =>
      cases right with
      | createCollision _ rcollision =>
          rw [lcollision] at rcollision
          cases rcollision
      | createRun _ _ revm rcore rtrace =>
          have hevm : levm = revm := Except.ok.inj (lcore.symm.trans rcore)
          subst hevm
          rw [ProcessCreateMessageTrace.eq_of_same ltrace rtrace]
      | callRun rtarget =>
          rw [ltarget] at rtarget
          cases rtarget
  | callRun ltarget ldelegated lrefund ldelegation lexec lexecEq levm lcore ltrace _ =>
      cases right with
      | createCollision rtarget =>
          rw [ltarget] at rtarget
          cases rtarget
      | createRun rtarget =>
          rw [ltarget] at rtarget
          cases rtarget
      | callRun _ rdelegated rrefund rdelegation rexec rexecEq revm rcore rtrace =>
          have hdelegation : (ldelegated, lrefund) = (rdelegated, rrefund) :=
            Except.ok.inj (ldelegation.symm.trans rdelegation)
          cases hdelegation
          subst lexecEq
          subst rexecEq
          have hevm : levm = revm := Except.ok.inj (lcore.symm.trans rcore)
          subst hevm
          rw [ProcessMessageTrace.eq_of_same ltrace rtrace]

theorem MessageCallTrace.index_eq_and_heq_of_same_input
    {msg : Msg} {leftState rightState : State}
    {leftOut rightOut : MsgCallOutput}
    (left : MessageCallTrace msg leftState leftOut)
    (right : MessageCallTrace msg rightState rightOut) :
    leftState = rightState ∧ leftOut = rightOut ∧ HEq left right := by
  rcases MessageCallTrace.index_eq_of_same_input left right with
    ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, heq_of_eq (MessageCallTrace.eq_of_same left right)⟩

theorem TransactionTrace.index_eq_of_same_input
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {leftState rightState : State}
    {leftBout rightBout : BlockOutput}
    (left : TransactionTrace benv bout tx index leftState leftBout)
    (right : TransactionTrace benv bout tx index rightState rightBout) :
    leftState = rightState ∧ leftBout = rightBout := by
  have hpair : (leftState, leftBout) = (rightState, rightBout) :=
    Except.ok.inj (left.result.symm.trans right.result)
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

theorem TransactionTrace.eq_of_same
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (left right : TransactionTrace benv bout tx index state bout') :
    left = right := by
  obtain ⟨vs, ig, fl, sd, gp, bh, bg, db, msg, ms, mo,
    lval, lchk, ldeb, lprep, lmsg, lres, lsender⟩ := left
  obtain ⟨vs', ig', fl', sd', gp', bh', bg', db', msg', ms', mo',
    rval, rchk, rdeb, rprep, rmsg, rres, rsender⟩ := right
  have hvs : vs = vs' := Except.ok.inj (lsender.symm.trans rsender)
  subst hvs
  have hval := Except.ok.inj (lval.symm.trans rval)
  simp only [Prod.mk.injEq] at hval
  obtain ⟨rfl, rfl⟩ := hval
  have hchk := Except.ok.inj (lchk.symm.trans rchk)
  simp only [Prod.mk.injEq] at hchk
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hchk
  have hdb := Option.some.inj (ldeb.symm.trans rdeb)
  subst hdb
  have hmsg := Except.ok.inj (lprep.symm.trans rprep)
  subst hmsg
  obtain ⟨hms, hmo, hheq⟩ :=
    MessageCallTrace.index_eq_and_heq_of_same_input lmsg rmsg
  subst hms
  subst hmo
  cases eq_of_heq hheq
  rfl

theorem TransactionTrace.index_eq_and_heq_of_same_input
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {leftState rightState : State}
    {leftBout rightBout : BlockOutput}
    (left : TransactionTrace benv bout tx index leftState leftBout)
    (right : TransactionTrace benv bout tx index rightState rightBout) :
    leftState = rightState ∧ leftBout = rightBout ∧ HEq left right := by
  rcases TransactionTrace.index_eq_of_same_input left right with
    ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, heq_of_eq (TransactionTrace.eq_of_same left right)⟩

theorem ApplyTransactionsTrace.toRun
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout
      finalBenv finalBout) :
    applyTransactions txs benv bout = .ok (finalBenv, finalBout) := by
  induction trace with
  | nil => rfl
  | cons head tail ih =>
      simp only [applyTransactions]
      rw [head.result]
      exact ih

theorem ApplyTransactionsTrace.index_eq_of_same_input
    {txs : List (Nat × Tx)} {benv : Benv} {bout : BlockOutput}
    {leftBenv rightBenv : Benv} {leftBout rightBout : BlockOutput}
    (left : ApplyTransactionsTrace txs benv bout leftBenv leftBout)
    (right : ApplyTransactionsTrace txs benv bout rightBenv rightBout) :
    leftBenv = rightBenv ∧ leftBout = rightBout := by
  have hpair : (leftBenv, leftBout) = (rightBenv, rightBout) :=
    Except.ok.inj (left.toRun.symm.trans right.toRun)
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

theorem ApplyTransactionsTrace.eq_of_same
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (left right : ApplyTransactionsTrace txs benv bout
      finalBenv finalBout) : left = right := by
  induction left with
  | nil =>
      cases right
      rfl
  | cons leftHead leftTail ih =>
      cases right with
      | cons rightHead rightTail =>
          rcases TransactionTrace.index_eq_and_heq_of_same_input
            leftHead rightHead with ⟨rfl, rfl, hhead⟩
          cases hhead
          rw [ih rightTail]

/-- Reassemble two actual transaction spines at their common environment. -/
def ApplyTransactionsTrace.append
    {xs ys : List (Nat × Tx)} {benv middle finalBenv : Benv}
    {bout middleBout finalBout : BlockOutput}
    (left : ApplyTransactionsTrace xs benv bout middle middleBout)
    (right : ApplyTransactionsTrace ys middle middleBout finalBenv finalBout) :
    ApplyTransactionsTrace (xs ++ ys) benv bout finalBenv finalBout :=
  match left with
  | .nil .. => right
  | .cons head tail => .cons head (tail.append right)

end Blanc.ExecutionTrace
