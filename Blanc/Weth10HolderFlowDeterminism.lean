import Blanc.ExecDeterminism
import Blanc.Weth10HolderFlow

namespace Blanc

open Jaune

namespace Weth10

theorem RetainedXlot.eq_of_same {xl : Xlot}
    (left right : RetainedXlot xl) : left = right := by
  cases left <;> cases right <;> simp_all
  apply Exec.unique

instance RetainedXlot.instSubsingleton {xl : Xlot} :
    Subsingleton (RetainedXlot xl) :=
  ⟨RetainedXlot.eq_of_same⟩

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

instance ProcessMessageTrace.instSubsingleton
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm} :
    Subsingleton (ProcessMessageTrace msg out) :=
  ⟨ProcessMessageTrace.eq_of_same⟩

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

instance ProcessCreateMessageTrace.instSubsingleton
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm} :
    Subsingleton (ProcessCreateMessageTrace msg out) :=
  ⟨ProcessCreateMessageTrace.eq_of_same⟩

theorem MessageCallTrace.toResult
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) :
    processMessageCall msg = .ok (state, out) := by
  cases trace <;> assumption

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
  cases left <;> cases right <;> simp_all <;>
    aesop (add safe forward ProcessMessageTrace.eq_of_same)
      (add safe forward ProcessCreateMessageTrace.eq_of_same)

theorem MessageCallTrace.index_eq_and_heq_of_same_input
    {msg : Msg} {leftState rightState : State}
    {leftOut rightOut : MsgCallOutput}
    (left : MessageCallTrace msg leftState leftOut)
    (right : MessageCallTrace msg rightState rightOut) :
    leftState = rightState ∧ leftOut = rightOut ∧ HEq left right := by
  rcases MessageCallTrace.index_eq_of_same_input left right with
    ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, heq_of_eq (MessageCallTrace.eq_of_same left right)⟩

instance MessageCallTrace.instSubsingleton
    {msg : Msg} {state : State} {out : MsgCallOutput} :
    Subsingleton (MessageCallTrace msg state out) :=
  ⟨MessageCallTrace.eq_of_same⟩

theorem SystemMessageTrace.index_eq_of_same_input
    {benv : Benv} {target : Adr} {data : Bytes}
    {leftState rightState : State} {leftOut rightOut : MsgCallOutput}
    (left : SystemMessageTrace benv target data leftState leftOut)
    (right : SystemMessageTrace benv target data rightState rightOut) :
    leftState = rightState ∧ leftOut = rightOut := by
  have hpair : (leftState, leftOut) = (rightState, rightOut) :=
    Except.ok.inj (left.run.symm.trans right.run)
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

theorem SystemMessageTrace.eq_of_same
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (left right : SystemMessageTrace benv target data state out) :
    left = right := by
  rcases left with ⟨leftMessage, leftRun⟩
  rcases right with ⟨rightMessage, rightRun⟩
  have hmessage := MessageCallTrace.eq_of_same leftMessage rightMessage
  subst rightMessage
  rfl

theorem SystemMessageTrace.index_eq_and_heq_of_same_input
    {benv : Benv} {target : Adr} {data : Bytes}
    {leftState rightState : State} {leftOut rightOut : MsgCallOutput}
    (left : SystemMessageTrace benv target data leftState leftOut)
    (right : SystemMessageTrace benv target data rightState rightOut) :
    leftState = rightState ∧ leftOut = rightOut ∧ HEq left right := by
  rcases SystemMessageTrace.index_eq_of_same_input left right with
    ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, heq_of_eq (SystemMessageTrace.eq_of_same left right)⟩

instance SystemMessageTrace.instSubsingleton
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput} :
    Subsingleton (SystemMessageTrace benv target data state out) :=
  ⟨SystemMessageTrace.eq_of_same⟩

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
  cases left
  cases right
  simp_all
  aesop (add safe forward MessageCallTrace.index_eq_and_heq_of_same_input)

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

instance TransactionTrace.instSubsingleton
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput} :
    Subsingleton (TransactionTrace benv bout tx index state bout') :=
  ⟨TransactionTrace.eq_of_same⟩

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

theorem ApplyTransactionsTrace.index_eq_and_heq_of_same_input
    {txs : List (Nat × Tx)} {benv : Benv} {bout : BlockOutput}
    {leftBenv rightBenv : Benv} {leftBout rightBout : BlockOutput}
    (left : ApplyTransactionsTrace txs benv bout leftBenv leftBout)
    (right : ApplyTransactionsTrace txs benv bout rightBenv rightBout) :
    leftBenv = rightBenv ∧ leftBout = rightBout ∧ HEq left right := by
  rcases ApplyTransactionsTrace.index_eq_of_same_input left right with
    ⟨rfl, rfl⟩
  exact ⟨rfl, rfl,
    heq_of_eq (ApplyTransactionsTrace.eq_of_same left right)⟩

instance ApplyTransactionsTrace.instSubsingleton
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput} :
    Subsingleton (ApplyTransactionsTrace txs benv bout
      finalBenv finalBout) :=
  ⟨ApplyTransactionsTrace.eq_of_same⟩

theorem RequestsTrace.index_eq_of_same_input
    {benv : Benv} {bout : BlockOutput}
    {leftState rightState : State}
    {leftBout rightBout : BlockOutput}
    (left : RequestsTrace benv bout leftState leftBout)
    (right : RequestsTrace benv bout rightState rightBout) :
    leftState = rightState ∧ leftBout = rightBout := by
  have hpair : (leftState, leftBout) = (rightState, rightBout) :=
    Except.ok.inj (left.run.symm.trans right.run)
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

theorem RequestsTrace.eq_of_same
    {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (left right : RequestsTrace benv bout state bout') : left = right := by
  cases left
  cases right
  simp_all
  aesop (add safe forward SystemMessageTrace.index_eq_and_heq_of_same_input)

theorem RequestsTrace.index_eq_and_heq_of_same_input
    {benv : Benv} {bout : BlockOutput}
    {leftState rightState : State}
    {leftBout rightBout : BlockOutput}
    (left : RequestsTrace benv bout leftState leftBout)
    (right : RequestsTrace benv bout rightState rightBout) :
    leftState = rightState ∧ leftBout = rightBout ∧ HEq left right := by
  rcases RequestsTrace.index_eq_of_same_input left right with
    ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, heq_of_eq (RequestsTrace.eq_of_same left right)⟩

instance RequestsTrace.instSubsingleton
    {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput} :
    Subsingleton (RequestsTrace benv bout state bout') :=
  ⟨RequestsTrace.eq_of_same⟩

theorem AppliedBodyTrace.index_eq_of_same_input
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {leftState rightState : State}
    {leftBout rightBout : BlockOutput}
    (left : AppliedBodyTrace benv txs wds leftState leftBout)
    (right : AppliedBodyTrace benv txs wds rightState rightBout) :
    leftState = rightState ∧ leftBout = rightBout := by
  have hpair : (leftState, leftBout) = (rightState, rightBout) :=
    Except.ok.inj (left.run.symm.trans right.run)
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

theorem AppliedBodyTrace.eq_of_same
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (left right : AppliedBodyTrace benv txs wds state bout) :
    left = right := by
  rcases left with ⟨leftRun, leftBeaconState, leftBeaconOut, leftBeacon,
    leftLastHash, leftLastHashRun, leftHistoryState, leftHistoryOut,
    leftHistory, leftDecodedTxs, leftDecodeRun, leftTransactionBenv,
    leftTransactionBout, leftTransactions, leftRequests⟩
  rcases right with ⟨rightRun, rightBeaconState, rightBeaconOut, rightBeacon,
    rightLastHash, rightLastHashRun, rightHistoryState, rightHistoryOut,
    rightHistory, rightDecodedTxs, rightDecodeRun, rightTransactionBenv,
    rightTransactionBout, rightTransactions, rightRequests⟩
  rcases SystemMessageTrace.index_eq_of_same_input leftBeacon rightBeacon with
    ⟨hBeaconState, hBeaconOut⟩
  subst rightBeaconState
  subst rightBeaconOut
  have hBeacon := SystemMessageTrace.eq_of_same leftBeacon rightBeacon
  subst rightBeacon
  have hLastHash : leftLastHash = rightLastHash :=
    Except.ok.inj (leftLastHashRun.symm.trans rightLastHashRun)
  subst rightLastHash
  rcases SystemMessageTrace.index_eq_of_same_input leftHistory rightHistory with
    ⟨hHistoryState, hHistoryOut⟩
  subst rightHistoryState
  subst rightHistoryOut
  have hHistory := SystemMessageTrace.eq_of_same leftHistory rightHistory
  subst rightHistory
  have hDecodedTxs : leftDecodedTxs = rightDecodedTxs :=
    Except.ok.inj (leftDecodeRun.symm.trans rightDecodeRun)
  subst rightDecodedTxs
  rcases ApplyTransactionsTrace.index_eq_of_same_input
    leftTransactions rightTransactions with
    ⟨hTransactionBenv, hTransactionBout⟩
  subst rightTransactionBenv
  subst rightTransactionBout
  have hTransactions :=
    ApplyTransactionsTrace.eq_of_same leftTransactions rightTransactions
  subst rightTransactions
  have hRequests := RequestsTrace.eq_of_same leftRequests rightRequests
  subst rightRequests
  rfl

instance AppliedBodyTrace.instSubsingleton
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput} :
    Subsingleton (AppliedBodyTrace benv txs wds state bout) :=
  ⟨AppliedBodyTrace.eq_of_same⟩

/-- For fixed endpoints, the applied block determines all retained replay and
flow data. -/
theorem AccountedBlock.eq_of_block_eq
    {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {pre post : BlockChain}
    (left right : AccountedBlock cfg dp ca pre post)
    (hblock : left.block = right.block) : left = right := by
  cases left
  cases right
  simp_all
  aesop (add safe forward AppliedBodyTrace.eq_of_same)

theorem AccountedBlock.observations_eq_of_block_eq
    {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {pre post : BlockChain}
    (left right : AccountedBlock cfg dp ca pre post)
    (hblock : left.block = right.block) :
    left.observations = right.observations := by
  rw [AccountedBlock.eq_of_block_eq left right hblock]

private theorem append_singleton_eq_append_singleton
    {α : Type} {leftPrefix rightPrefix : List α} {leftLast rightLast : α}
    (h : leftPrefix ++ [leftLast] = rightPrefix ++ [rightLast]) :
    leftPrefix = rightPrefix ∧ leftLast = rightLast := by
  have reversed : leftLast :: leftPrefix.reverse =
      rightLast :: rightPrefix.reverse := by
    simpa using congrArg List.reverse h
  exact ⟨List.reverse_injective (List.cons.inj reversed).2,
    (List.cons.inj reversed).1⟩

/-- Replaying the same block list from a fixed checkpoint has a unique
endpoint. -/
theorem AccountedHistory.endpoint_eq_of_appliedBlocks_eq
    {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint leftFuture rightFuture : BlockChain}
    (left : AccountedHistory cfg dp ca checkpoint leftFuture)
    (right : AccountedHistory cfg dp ca checkpoint rightFuture)
    (hblocks : left.appliedBlocks = right.appliedBlocks) :
    leftFuture = rightFuture := by
  induction left generalizing rightFuture with
  | refl hcfg hctx hid =>
      cases right with
      | refl => rfl
      | step prior accounted =>
          simp [AccountedHistory.appliedBlocks] at hblocks
  | step prior leftBlock ih =>
      cases right with
      | refl =>
          simp [AccountedHistory.appliedBlocks] at hblocks
      | step rightPrior rightBlock =>
          change prior.appliedBlocks ++ [leftBlock.block] =
            rightPrior.appliedBlocks ++ [rightBlock.block] at hblocks
          rcases append_singleton_eq_append_singleton hblocks with
            ⟨hprior, hblock⟩
          have hcurrent := ih rightPrior hprior
          have hsame := congrArg₂
            (stateTransitionUsing cfg)
            hcurrent hblock
          exact Except.ok.inj
            (leftBlock.transition.symm.trans
              (hsame.trans rightBlock.transition))

theorem AccountedHistory.flowObservations_eq_of_appliedBlocks_eq
    {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (left right : AccountedHistory cfg dp ca checkpoint future)
    (hblocks : left.appliedBlocks = right.appliedBlocks) :
    left.flowObservations = right.flowObservations := by
  induction left with
  | refl hcfg hctx hid =>
      cases right with
      | refl => rfl
      | step prior accounted =>
          simp [AccountedHistory.appliedBlocks] at hblocks
  | step prior leftBlock ih =>
      cases right with
      | refl =>
          simp [AccountedHistory.appliedBlocks] at hblocks
      | step rightPrior rightBlock =>
          change prior.appliedBlocks ++ [leftBlock.block] =
            rightPrior.appliedBlocks ++ [rightBlock.block] at hblocks
          rcases append_singleton_eq_append_singleton hblocks with
            ⟨hprior, hblock⟩
          have hcurrent :=
            AccountedHistory.endpoint_eq_of_appliedBlocks_eq
              prior rightPrior hprior
          cases hcurrent
          have hprefix := ih rightPrior hprior
          have hlast :=
            AccountedBlock.observations_eq_of_block_eq
              leftBlock rightBlock hblock
          simp only [AccountedHistory.flowObservations]
          rw [hprefix, hlast]

theorem AccountedHistory.weth10Flow_eq_of_appliedBlocks_eq
    {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (history₁ history₂ :
      AccountedHistory cfg dp ca checkpoint future)
    (hblocks : history₁.appliedBlocks = history₂.appliedBlocks) :
    history₁.weth10Flow u = history₂.weth10Flow u := by
  unfold AccountedHistory.weth10Flow
  rw [AccountedHistory.flowObservations_eq_of_appliedBlocks_eq
    history₁ history₂ hblocks]

end Weth10

end Blanc
