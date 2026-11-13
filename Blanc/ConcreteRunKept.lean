import Blanc.ConcreteRun
import Blanc.ExecutionKeptValue
import Blanc.Lift.LedgerFootprint

/-!
Continuing prefixes do not add retained frames. This relates the original
`ConcreteRun.Exec.ofStepN` derivation to the kept frames of its supplied tail.
-/

namespace Blanc.ConcreteRun

open Jaune

/-- Extending an actual execution by a continuing prefix keeps exactly the
frames kept by that execution, at any observed address and on any outcome. -/
theorem Exec.keptAt_ofStepN (a : Adr) (n : Nat) {evm evm' : Evm} {out : Execution}
    (h : stepN n evm = some evm') (run : Jaune.Exec evm'.pc evm'.sta evm'.dyna out) :
    Blanc.Exec.keptAt a (Exec.ofStepN n h run) = Blanc.Exec.keptAt a run := by
  induction n generalizing evm with
  | zero =>
      simp only [stepN, Option.some.injEq] at h
      subst evm'
      rfl
  | succ n ih =>
      cases hs : Evm.step evm with
      | cont pc devm =>
          have tail : stepN n ⟨pc, evm.sta, devm⟩ = some evm' := by
            simpa only [stepN, hs] using h
          have same := Blanc.Exec.unique (Exec.ofStepN (n + 1) h run)
            (Jaune.Exec.cont hs (Exec.ofStepN n tail run))
          rw [same, Blanc.Exec.keptAt]
          exact ih tail
      | halt result => simp only [stepN, hs, reduceCtorEq] at h
      | spawn frame resume pc => simp only [stepN, hs, reduceCtorEq] at h

/-- Reconstruct the original interpreter derivations at exactly the entries
chosen by the original message preparation. No message result is assumed. -/
def deriveEntries (depth : Nat) (msg : Msg) :
    Option {rs : List Blanc.Root //
      rs.map (fun r => (r.frame, r.evm)) = (Blanc.messageEntry msg).toList} :=
  match entered : Blanc.messageEntry msg with
  | none => some ⟨[], by rfl⟩
  | some (frame, evm) => do
      let ⟨raw, run⟩ ← derive depth evm
      let root : Blanc.Root := ⟨frame, evm, raw, run⟩
      pure ⟨[root], by rfl⟩

/-- The actual result of a message, with all its interpreter roots. -/
structure MessageResult (msg : Msg) where
  state : State
  output : MsgCallOutput
  roots : List Blanc.Root
  sound : Blanc.MessageRoots msg state output roots

/-- Execute the original dispatch, then reconstruct its derivations. This
repeats interpreter work; it does not replace the original message semantics. -/
def deriveMessage (depth : Nat) (msg : Msg) : Option (MessageResult msg) :=
  match called : processMessageCall msg with
  | .error _ => none
  | .ok (state, output) => do
      let ⟨roots, entries⟩ ← deriveEntries depth msg
      pure ⟨state, output, roots, called, entries⟩

open Blanc ExecutionTrace

/-- Retain the beacon call's computed entries. Its actual result determines
the message result in the proof; no chosen root enters computation. -/
def deriveBeaconRoots (depth : Nat) (benv : Benv) (st : State) (bal : BalBuilder)
    (h : beaconRootsCall benv.stat.rules benv = .ok (st, bal)) :
    Option {rs : List Root // PreCall benv.stat.rules.sys.beaconRoots benv
      beaconRootsAddress benv.stat.parentBeaconBlockRoot.toBytes st rs} := do
  if on : benv.stat.rules.sys.beaconRoots = true then
    let ⟨roots, entries⟩ ← deriveEntries depth
      (systemTransactionMessage benv beaconRootsAddress benv.stat.parentBeaconBlockRoot.toBytes)
    pure ⟨roots, by
      obtain ⟨old, hold⟩ := exists_beaconRoots h
      simp only [PreCall, on] at hold ⊢
      obtain ⟨out, called, -⟩ := hold
      exact ⟨out, called, entries⟩⟩
  else
    pure ⟨[], by
      obtain ⟨old, hold⟩ := exists_beaconRoots h
      simp only [PreCall, on] at hold ⊢
      exact ⟨hold.1, True.intro⟩⟩

/-- Retain the history-storage call's computed entries on its actual message. -/
def deriveHistoryRoots (depth : Nat) (benv : Benv) (st : State) (bal bal' : BalBuilder)
    (h : historyStorageCall benv.stat.rules benv bal = .ok (st, bal')) :
    Option {rs : List Root // PreCall benv.stat.rules.sys.historyStorage benv
      historyStorageAddress (historyData benv) st rs} := do
  if on : benv.stat.rules.sys.historyStorage = true then
    let ⟨roots, entries⟩ ← deriveEntries depth
      (systemTransactionMessage benv historyStorageAddress (historyData benv))
    pure ⟨roots, by
      obtain ⟨old, hold⟩ := exists_historyRoots (historyData benv) rfl h
      simp only [PreCall, on] at hold ⊢
      obtain ⟨out, called, -⟩ := hold
      exact ⟨out, called, entries⟩⟩
  else
    pure ⟨[], by
      obtain ⟨old, hold⟩ := exists_historyRoots (historyData benv) rfl h
      simp only [PreCall, on] at hold ⊢
      exact ⟨hold.1, True.intro⟩⟩

/-- A computed pre-execution stage and its original call certificates. -/
structure PreResult (benv : Benv) where
  state : State
  bal : BalBuilder
  roots : List Root
  sound : PreRoots benv state bal roots

/-- Replay both original pre-execution calls, retaining their actual roots. -/
def derivePre (depth : Nat) (benv : Benv) : Option (PreResult benv) := do
  match beacon : beaconRootsCall benv.stat.rules benv with
  | .error _ => none
  | .ok (stBeacon, beaconBal) =>
      let ⟨beaconRoots, hb⟩ ← deriveBeaconRoots depth benv stBeacon beaconBal beacon
      match history : historyStorageCall benv.stat.rules (benv.withState stBeacon) beaconBal with
      | .error _ => none
      | .ok (st, bal) =>
          let ⟨historyRoots, hh⟩ ← deriveHistoryRoots depth (benv.withState stBeacon) st beaconBal bal history
          pure ⟨st, bal, beaconRoots ++ historyRoots,
            stBeacon, beaconBal, beaconRoots, historyRoots, beacon, hb, history, hh, rfl⟩

/-- A computed transaction and its original message roots. -/
structure TransactionResult (benv : Benv) (bout : BlockOutput) (tx : Tx) (index : Nat) where
  state : State
  output : BlockOutput
  sender : Adr
  roots : List Root
  sound : TransactionRoots benv bout tx index state output sender roots

/-- Replay the original transaction, then reconstruct only its actual message's
entries. Sender/message equality is justified by the original transaction spine. -/
def deriveTransaction (depth : Nat) (benv : Benv) (bout : BlockOutput) (tx : Tx) (index : Nat) :
    Option (TransactionResult benv bout tx index) := do
  match called : processTransaction benv bout tx index with
  | .error _ => none
  | .ok (st, out) =>
      match prepared : transactionMessage benv bout tx index with
      | .error _ => none
      | .ok (sender, msg) =>
          let ⟨roots, entries⟩ ← deriveEntries depth msg
          pure ⟨st, out, sender, roots, called, by
            obtain ⟨sender', old, -, msg', messageState, messageOut, hp, hm, -⟩ := exists_transactionRoots called
            have same := Except.ok.inj (prepared.symm.trans hp)
            cases same
            exact ⟨msg, messageState, messageOut, prepared, hm, entries⟩⟩

/-- A computed transaction fold, retaining actual senders and message roots. -/
structure TransactionsResult (txs : List (Nat × Tx)) (benv : Benv) (bout : BlockOutput) where
  final : Benv
  output : BlockOutput
  senders : List (Adr × Tx)
  roots : List Root
  sound : TransactionsRoots txs benv bout final output senders roots

/-- Replay the original transactions in order; failure discards the suffix and
does not return a successful prefix certificate. -/
def deriveTransactions (depth : Nat) : (txs : List (Nat × Tx)) → (benv : Benv) → (bout : BlockOutput) →
    Option (TransactionsResult txs benv bout)
  | [], benv, bout => some ⟨benv, bout, [], [], .nil _ _⟩
  | (index, tx) :: rest, benv, bout => do
      let head ← deriveTransaction depth benv bout tx index
      let tail ← deriveTransactions depth rest (benv.withState head.state) head.output
      pure ⟨tail.final, tail.output, (head.sender, tx) :: tail.senders, head.roots ++ tail.roots,
        .cons head.sound tail.sound⟩

/-- A computed request fold and all of its checked-call roots. -/
structure RequestsResult (idx : Nat) (contracts : List (UInt8 × Adr))
    (benv : Benv) (acc : List Bytes) (bal : BalBuilder) where
  state : State
  requests : List Bytes
  finalBal : BalBuilder
  steps : List RequestStep
  sound : RequestRoots idx contracts benv acc bal state requests finalBal steps

/-- Replay the original checked request calls, retaining every actual message
entry and threading the original request accumulator and access-list builder. -/
def deriveRequests (depth idx : Nat) : (contracts : List (UInt8 × Adr)) →
    (benv : Benv) → (acc : List Bytes) → (bal : BalBuilder) →
    Option (RequestsResult idx contracts benv acc bal)
  | [], benv, acc, bal => some ⟨benv.state, acc, bal, [], .nil _ _ _⟩
  | (type, target) :: rest, benv, acc, bal => do
      match called : processCheckedSystemTransaction benv target [] with
      | .error _ => none
      | .ok (post, out) =>
          let ⟨roots, entries⟩ ← deriveEntries depth (systemTransactionMessage benv target [])
          let message : MessageRoots (systemTransactionMessage benv target []) post out roots := by
            obtain ⟨-, old, hm, -⟩ := exists_systemRoots called
            exact ⟨hm, entries⟩
          let step : RequestStep := ⟨type, target, post, out, roots⟩
          let tail ← deriveRequests depth idx rest (benv.withState post) (acc ++ step.bytes)
            (requestBal idx benv bal target post out)
          pure ⟨tail.state, tail.requests, tail.finalBal, step :: tail.steps,
            .cons called message tail.sound⟩

/-- The request pass's computed result, including all checked system calls. -/
structure RequestPassResult (benv : Benv) (bout : BlockOutput) where
  state : State
  output : BlockOutput
  steps : List RequestStep
  sound : RequestPass benv bout state output steps

/-- Follow the original request-enable flag, deposit parser and contract list. -/
def deriveRequestPass (depth : Nat) (benv : Benv) (bout : BlockOutput) :
    Option (RequestPassResult benv bout) := do
  if on : benv.stat.rules.header.requestsHash = true then
    match parsed : parseDepositRequests bout with
    | .error _ => none
    | .ok deposits =>
        let result ← deriveRequests depth (bout.receiptKeys.length + 1) benv.stat.rules.requests benv
          (seedRequests bout deposits) bout.bal
        pure ⟨result.state, {bout with requests := result.requests, bal := result.finalBal}, result.steps, by
          simp only [RequestPass, on]
          exact ⟨deposits, result.requests, result.finalBal, parsed, result.sound, rfl⟩⟩
  else
    pure ⟨benv.state, bout, [], by simp only [RequestPass, on]; exact ⟨True.intro, True.intro, True.intro⟩⟩

/-- An actual original body result, with all stages' computed interpreter roots. -/
structure BodyResult (benv : Benv) (txs : List (Bytes ⊕ Tx)) (ommers : List Header)
    (wds : List Withdrawal) where
  state : State
  output : BlockOutput
  run : BodyRun
  sound : BodyRoots benv txs ommers wds state output run

/-- Execute the original body and reconstruct its actual pre-call, transaction
and request roots. Every original call and interpreter branch must succeed.
Proof-only existence lemmas identify message results; all retained root data
comes from `deriveEntries`, with no choice operation in this computation. -/
def deriveBody (depth : Nat) (benv : Benv) (txs : List (Bytes ⊕ Tx)) (ommers : List Header)
    (wds : List Withdrawal) : Option (BodyResult benv txs ommers wds) := do
  match applied : applyBody benv txs ommers wds with
  | .error _ => none
  | .ok (state, output) =>
      let pre ← derivePre depth benv
      match decoded : txs.mapM (decodeTx benv.stat.rules) with
      | .error _ => none
      | .ok transactions =>
          let tx ← deriveTransactions depth transactions.putIndex (benv.withState pre.state)
            {BlockOutput.init with bal := pre.bal}
          let withdrawals := withdrawalsPass benv.stat.rules tx.final tx.output wds
          let requests ← deriveRequestPass depth (tx.final.withState withdrawals.1) withdrawals.2
          let run : BodyRun := ⟨pre.state, pre.bal, pre.roots, tx.final, tx.output, tx.senders, tx.roots,
            requests.steps⟩
          pure ⟨state, output, run,
            applied, pre.sound, ⟨transactions, decoded, tx.sound⟩,
            ⟨requests.state, requests.output, requests.sound⟩⟩

/-- Execute the original configured transition and compute the exact retained
block certificate. Coverage is tested at its actual selected fork. -/
def deriveKept (depth : Nat) (cfg : ChainConfig) (parent : BlockChain) (block : Block) :
    Option (Σ post : BlockChain,
      {b : KeptBlock // b.parent = parent ∧ b.block = block ∧ KeptStep cfg b post}) := do
  match transitioned : stateTransitionUsing cfg parent block with
  | .error _ => none
  | .ok post =>
      match selected : cfg.forkAt block.header.number block.header.timestamp with
      | .error _ => none
      | .ok fork =>
          letI : Decidable (KeptFork fork) := by unfold KeptFork; infer_instance
          if kept : KeptFork fork then do
            let body ← deriveBody depth (initBenv fork parent block.header) block.txs block.ommers block.wds
            have stateEq : body.state = post.state := by
              obtain ⟨f, st, out, hf, -, hb, hp⟩ := exists_configuredBody_of_transition transitioned
              have same := Except.ok.inj (hf.symm.trans selected)
              subst f
              have eq := Prod.mk.inj (Except.ok.inj (body.sound.applied.symm.trans hb))
              rw [hp]
              exact eq.1
            pure ⟨post, ⟨⟨parent, block, fork, body.output, body.run⟩, rfl, rfl,
              transitioned, selected, kept,
              ⟨by rw [← stateEq]; exact body.sound.applied,
                body.sound.pre, body.sound.transactions, body.sound.requests⟩⟩⟩
          else none

/-- Decide each root's original world-sum premise over stored account keys. -/
def rootsFitDecidable (rs : List Root) : Decidable (RootsFit rs) := by
  letI (root : Root) : Decidable (SumNof root.frame.outer.benv.state.bal) :=
    State.sumNofDecidable root.frame.outer.benv.state
  unfold RootsFit
  infer_instance

/-- Decide the original withdrawal-credit bounds along their actual state updates. -/
def wdsFitDecidable (a : Adr) : (st : State) → (wds : List Withdrawal) → Decidable (WdsFit a st wds)
  | _, [] => isTrue True.intro
  | st, wd :: rest =>
      letI := wdsFitDecidable a (st.addBal wd.recipient (wd.amount * (10 ^ 9).toB256)) rest
      show Decidable ((_ → _) ∧ _) from inferInstance

/-- A sufficient tip-credit check: transactions cannot credit their tip at an
address different from their fee recipient. This does not assert the converse. -/
theorem tipsFit_of_coinbase_ne (a : Adr) (txs : List (Nat × Tx)) (benv : Benv) (bout : BlockOutput)
    (away : benv.stat.coinbase ≠ a) : TipsFit a txs benv bout := by
  induction txs generalizing benv bout with
  | nil => exact True.intro
  | cons pair rest ih =>
      obtain ⟨index, tx⟩ := pair
      refine ⟨?_, fun st out _ => ih (benv.withState st) out away⟩
      intro sender msg messageState messageOut refund tip state output _ _ _ _ same
      exact (away same).elim

/-- Retain actual body roots only when their original world-sum bound holds. -/
def deriveBodyFit (depth : Nat) (benv : Benv) (txs : List (Bytes ⊕ Tx)) (ommers : List Header)
    (wds : List Withdrawal) :
    Option {result : BodyResult benv txs ommers wds // RootsFit result.run.roots} := do
  let result ← deriveBody depth benv txs ommers wds
  letI := rootsFitDecidable result.run.roots
  if fits : RootsFit result.run.roots then pure ⟨result, fits⟩ else none

/-- All finite exclusions over a body's computed roots and recovered senders. -/
def BodyExcludes (a : Adr) (run : BodyRun) : Prop :=
  NoSenderAt a run.senders ∧ NoAuthorityAt a run.senders ∧ NoCreateAt a run.roots

/-- Decide the original sender, authorization and retained-create exclusions. -/
def bodyExcludesDecidable (a : Adr) (run : BodyRun) : Decidable (BodyExcludes a run) := by
  unfold BodyExcludes NoSenderAt NoAuthorityAt NoCreateAt
  infer_instance

/-- The exact per-body credit premise used by `HistoryCreditsFit`. -/
def BodyCreditsFit (a : Adr) (benv : Benv) (txs : List (Bytes ⊕ Tx)) (wds : List Withdrawal)
    (run : BodyRun) : Prop :=
  (∀ decoded, txs.mapM (decodeTx benv.stat.rules) = .ok decoded →
    TipsFit a decoded.putIndex (benv.withState run.preState) {BlockOutput.init with bal := run.preBal}) ∧
  WdsFit a run.txEnv.state wds

/-- Check original withdrawal credits and prove the tip premise when the fee
recipient is elsewhere. A rejected address may still satisfy the premise:
this is deliberately a sufficient checker rather than a complete decider. -/
def checkBodyCredits (a : Adr) (benv : Benv) (txs : List (Bytes ⊕ Tx)) (wds : List Withdrawal)
    (run : BodyRun) : Option {_u : Unit // BodyCreditsFit a benv txs wds run} :=
  letI := wdsFitDecidable a run.txEnv.state wds
  if away : benv.stat.coinbase ≠ a then
    if fits : WdsFit a run.txEnv.state wds then
      some ⟨(), fun decoded _ => tipsFit_of_coinbase_ne a decoded.putIndex
        (benv.withState run.preState) {BlockOutput.init with bal := run.preBal} away, fits⟩
    else none
  else none

end Blanc.ConcreteRun
