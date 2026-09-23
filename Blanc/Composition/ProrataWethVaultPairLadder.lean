-- ProrataWethVaultPairLadder.lean : the pair's wrapper ladder, message root to configured history.

import Blanc.Composition.ProrataWethVaultPairReplay
import Blanc.ExecutionAccountingLadder   -- §4 generic additions (fallback: leaf-local, §4)
import Blanc.ExecutionTransactionEffects
import Blanc.ExecutionBodyEffects
import Blanc.ExecutionHistoryEffects

/-!
# The pair's wrapper ladder

`Exec.corePairReplay` classifies one interpreter execution rooted at a frame that satisfies the pair frame
invariant and the root envelope.  This module climbs from there to a whole configured history, one rung per
wrapper Jaune retains — message, CREATE, message-call wrapper, transaction, transaction list, system message,
request calls, direct withdrawals, block body, configured block, configured history — in the order of
`Blanc/ProrataAccounting{Exec,Transaction,Body,History}.lean` and of the generic `ExecutionAccountingLadder`.

It is a separate ladder, not an instance of the generic one, for three material reasons (the ladder design's
§6): the boundary reads two storages, the invariant is not one `ContractSpec`'s, and the replay is
provenance-indexed.  What it carries instead is `PairWorldInv`: both contracts' state invariants, where the
vault's share ledger — whose `ContractSpec` preservation is conditional on the WETH configuration — is carried
by the replay itself (`PairReplay.conserved`), and the vault's code by the code-only spec
`pairVaultCodeSpec`, whose preservation is unconditional.  Neither pair account ever originates a retained root
message (`pair_root_caller_ne_vault`), and neither can be the target of a non-colliding CREATE
(`PairMsgInv.createCollision`): those two facts are the whole root envelope.
-/

namespace Blanc.Composition.ProrataWethVault

open Jaune
open _root_.Blanc.ExecutionTrace

/-! ## 1. Replays with an admissibility predicate -/

/-- A record emitted inside block `blockIndex`. -/
def PairInBlock {vault : Adr} (blockIndex : Nat) (r : PairStepRecord vault) : Prop :=
  r.provenance.blockIndex = blockIndex


theorem PairReplayBetween.toWith {vault : Adr} {blockIndex : Nat}
    {transactionIndex : Option Nat} {framePath : List Nat} {pre post : PairBoundary}
    (replay : PairReplayBetween vault blockIndex transactionIndex framePath pre post) :
    PairReplayWith vault (PairProvenanceOk blockIndex transactionIndex framePath) pre post :=
  replay

theorem PairReplayBetween.inBlock {vault : Adr} {blockIndex : Nat}
    {transactionIndex : Option Nat} {framePath : List Nat} {pre post : PairBoundary}
    (replay : PairReplayBetween vault blockIndex transactionIndex framePath pre post) :
    PairReplayWith vault (PairInBlock blockIndex) pre post :=
  replay.toWith.mono fun _ ok => ok.block

/-- A faithful replay re-graded: weaken the admissibility half and enlarge the frame universe. -/
theorem PairReplayWith.faithfulLift {vault : Adr} {p q : PairStepRecord vault → Prop}
    {F G : List Exec.Deriv} {pre post : PairBoundary}
    (weaken : ∀ r, p r → q r) (sub : ∀ d ∈ F, d ∈ G)
    (replay : PairReplayWith vault (fun r => p r ∧ PairStepRecord.OwnIn vault F r) pre post) :
    PairReplayWith vault (fun r => q r ∧ PairStepRecord.OwnIn vault G r) pre post :=
  replay.mono fun r h => ⟨weaken r h.1, h.2.mono sub⟩

/-! ## 2. The share ledger rides in the replay -/

/-- Every classified step keeps the vault's share ledger conserved: an operation by its retained evidence,
the other two because they fix the vault's storage outright. -/
theorem PairStep.conserved {vault : Adr} {before after : State}
    (step : PairStep vault before after)
    (conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot (before.getStor vault)) :
    LedgerConserved Blanc.ProrataWethVault.supplySlot (after.getStor vault) := by
  cases step with
  | operation t evidence =>
      have entry : Devm.getStor t.entry vault = before.getStor vault :=
        congrArg (fun w : State => w.getStor vault) t.preState
      have exit : Devm.getStor t.exit vault = after.getStor vault :=
        congrArg (fun w : State => w.getStor vault) t.postState
      have pre : LedgerConserved Blanc.ProrataWethVault.supplySlot
          (Devm.getStor t.entry vault) := by
        rw [entry]
        exact conserved
      have post := evidence.preserves_conserved pre
      rwa [exit] at post
  | authorizedDebit call foreign owner pair moved vaultKept =>
      rw [vaultKept]
      exact conserved
  | silent caller vaultKept rowKept =>
      rw [vaultKept]
      exact conserved
-- new; the operation arm is `FourQuoteShareEvidence.preserves_conserved` (Accounting.lean:1309).

/-- A connected replay carries the ledger from its first boundary to its last. -/
theorem PairReplay.conserved {vault : Adr} {pre post : PairBoundary}
    {steps : List (PairStepRecord vault)} (replay : PairReplay vault pre steps post)
    (conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot pre.vault) :
    LedgerConserved Blanc.ProrataWethVault.supplySlot post.vault := by
  induction replay with
  | nil boundary => exact conserved
  | @cons pre mid post record steps preEq postEq tail ih =>
      apply ih
      rw [← postEq]
      rw [← preEq] at conserved
      exact record.step.conserved conserved
-- induction shape of H:96–100.

theorem PairReplayWith.conserved {vault : Adr} {ok : PairStepRecord vault → Prop}
    {pre post : PairBoundary} (replay : PairReplayWith vault ok pre post)
    (conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot pre.vault) :
    LedgerConserved Blanc.ProrataWethVault.supplySlot post.vault := by
  obtain ⟨steps, stepsReplay, -⟩ := replay
  exact stepsReplay.conserved conserved

/-! ## 3. The threaded invariant -/

/-- The code half of the vault's storage-only spec.  `vaultSpec.Preserves` does not exist — the rely rung
needs the WETH configuration — but this spec's does, trivially, and it is all the generic transports need to
carry the vault's code and its not-created side condition. -/
abbrev pairVaultCodeSpec : ContractSpec :=
  ContractSpec.ofStorageOnly Blanc.ProrataWethVault.vault (fun _ => True)

theorem pairVaultCodeSpec_preserves (vault : Adr) : pairVaultCodeSpec.Preserves vault :=
  fun _ _ _ _ _ _ _ => ⟨trivial, trivial⟩

/-- The code half and the ledger are the vault's whole state invariant. -/
theorem vaultStateInv_of_code {vault : Adr} {w : State}
    (code : pairVaultCodeSpec.StateInv vault w)
    (conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot (w.getStor vault)) :
    Blanc.ProrataWethVault.vaultSpec.StateInv vault w :=
  ⟨code.code, trivial, conserved⟩

/-- What a pair history carries from settled world to settled world, unconditionally.  `PairStable` adds the
backing numbers, which a history carries only under D9 (design §3.3.6). -/
structure PairWorldInv (vaultAddr : Adr) (w : State) : Prop where
  vault : Blanc.ProrataWethVault.vaultSpec.StateInv vaultAddr w
  weth : wethSpec.StateInv wethAccount w
  distinct : wethAccount ≠ vaultAddr
  vaultNotSystem : vaultAddr ≠ systemAddress
  wethNotSystem : wethAccount ≠ systemAddress

namespace PairWorldInv

variable {vault : Adr} {w : State}

theorem vaultCode (h : PairWorldInv vault w) : pairVaultCodeSpec.StateInv vault w :=
  ⟨h.vault.code, trivial, trivial⟩

theorem conserved (h : PairWorldInv vault w) :
    LedgerConserved Blanc.ProrataWethVault.supplySlot (w.getStor vault) :=
  h.vault.inv

theorem sumNof (h : PairWorldInv vault w) : sum w.bal < 2 ^ 256 :=
  h.weth.side

end PairWorldInv

/-- The block-environment form: both accounts not yet created in this block, and WETH not a precompile
under the block's rules. -/
structure PairBenvInv (vault : Adr) (benv : Benv) : Prop where
  world : PairWorldInv vault benv.state
  vaultNotCreated : vault ∉ benv.createdAccounts
  wethNotCreated : wethAccount ∉ benv.createdAccounts
  wethNonprecompile : benv.stat.rules.isPrecomp wethAccount = false

/-- The one transport every rung above the message uses: both code invariants by the generic ladder, the
ledger by the rung's own replay, the rules by the rung's own statics. -/
theorem PairBenvInv.transport {vault : Adr} {benv benv' : Benv}
    (inv : PairBenvInv vault benv)
    (code : pairVaultCodeSpec.BenvInv vault benv')
    (weth : wethSpec.BenvInv wethAccount benv')
    (rules : benv'.stat.rules = benv.stat.rules)
    (conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot
      (benv'.state.getStor vault)) :
    PairBenvInv vault benv' :=
  ⟨⟨vaultStateInv_of_code code.state conserved, weth.state, inv.world.distinct,
      inv.world.vaultNotSystem, inv.world.wethNotSystem⟩,
    code.ca, weth.ca, by rw [rules]; exact inv.wethNonprecompile⟩

theorem PairBenvInv.afterTransaction {vault : Adr} {benv : Benv} {bout : BlockOutput}
    {tx : Tx} {index : Nat} {state : State} {bout' : BlockOutput}
    (inv : PairBenvInv vault benv) (trace : TransactionTrace benv bout tx index state bout')
    {ok : PairStepRecord vault → Prop}
    (replay : PairReplayWith vault ok (PairBoundary.ofState vault benv.state)
      (PairBoundary.ofState vault state)) :
    PairBenvInv vault (benv.withState state) :=
  inv.transport
    (trace.benvInv (pairVaultCodeSpec_preserves vault) inv.world.sumNof
      ⟨inv.world.vaultCode, inv.vaultNotCreated⟩)
    (trace.benvInv (wethSpec_preserves wethAccount) inv.world.sumNof
      ⟨inv.world.weth, inv.wethNotCreated⟩)
    rfl (replay.conserved inv.world.conserved)
-- PB:40–41 (`head.benvInv …`), twice, plus the replay.

theorem PairBenvInv.afterSystem {vault : Adr} {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (inv : PairBenvInv vault benv) (trace : SystemMessageTrace benv target data state out)
    {ok : PairStepRecord vault → Prop}
    (replay : PairReplayWith vault ok (PairBoundary.ofState vault benv.state)
      (PairBoundary.ofState vault state)) :
    PairBenvInv vault (benv.withState state) :=
  inv.transport
    (trace.benvInv (pairVaultCodeSpec_preserves vault) ⟨inv.world.vaultCode, inv.vaultNotCreated⟩)
    (trace.benvInv (wethSpec_preserves wethAccount) ⟨inv.world.weth, inv.wethNotCreated⟩)
    rfl (replay.conserved inv.world.conserved)
-- PB:104–106 / 183–188.

theorem PairBenvInv.afterTransactions {vault : Adr} {txs : List (Nat × Tx)}
    {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (inv : PairBenvInv vault benv)
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    {ok : PairStepRecord vault → Prop}
    (replay : PairReplayWith vault ok (PairBoundary.ofState vault benv.state)
      (PairBoundary.ofState vault finalBenv.state)) :
    PairBenvInv vault finalBenv :=
  inv.transport
    (trace.benvInv (pairVaultCodeSpec_preserves vault) inv.world.sumNof
      ⟨inv.world.vaultCode, inv.vaultNotCreated⟩)
    (trace.benvInv (wethSpec_preserves wethAccount) inv.world.sumNof
      ⟨inv.world.weth, inv.wethNotCreated⟩)
    (by rw [trace.stat_eq]) (replay.conserved inv.world.conserved)
-- PB:192–194; `stat_eq` is §4 (G+2).

theorem PairBenvInv.afterWithdrawals {vault : Adr} {benv : Benv} {wds : List Withdrawal}
    (inv : PairBenvInv vault benv)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256) :
    PairBenvInv vault (benv.withState (processWithdrawalsState benv.state wds)) :=
  inv.transport
    (benvInv_processWithdrawalsState ⟨inv.world.vaultCode, inv.vaultNotCreated⟩ bound)
    (benvInv_processWithdrawalsState ⟨inv.world.weth, inv.wethNotCreated⟩ bound)
    rfl
    (by
      show LedgerConserved _ ((processWithdrawalsState benv.state wds).getStor vault)
      rw [processWithdrawalsState_getStor_eq]
      exact inv.world.conserved)
-- PB:209; `processWithdrawalsState_getStor_eq` is §4 (G+3).

theorem PairWorldInv.afterHistory {vault : Adr} {cfg : ChainConfig}
    {checkpoint current : BlockChain}
    (inv : PairWorldInv vault checkpoint.state)
    (history : ConfiguredHistoryTrace cfg checkpoint current)
    {ok : PairStepRecord vault → Prop}
    (replay : PairReplayWith vault ok (PairBoundary.ofState vault checkpoint.state)
      (PairBoundary.ofState vault current.state)) :
    PairWorldInv vault current.state :=
  ⟨vaultStateInv_of_code (history.stateInv (pairVaultCodeSpec_preserves vault) inv.vaultCode)
      (replay.conserved inv.conserved),
    history.stateInv (wethSpec_preserves wethAccount) inv.weth,
    inv.distinct, inv.vaultNotSystem, inv.wethNotSystem⟩
-- PH:78 (`prior.stateInv …`), twice, plus the replay.

/-! ## 4. Message readiness, the root envelope and the CREATE-collision arm -/

/-- What every message-level rung needs of a retained message: both contracts' message invariants, the
configuration's rules fact, and the root envelope. -/
structure PairMsgInv (vaultAddr : Adr) (msg : Msg) : Prop where
  vault : Blanc.ProrataWethVault.vaultSpec.MsgInv vaultAddr msg
  weth : wethSpec.MsgInv wethAccount msg
  distinct : wethAccount ≠ vaultAddr
  wethNonprecompile : msg.benv.stat.rules.isPrecomp wethAccount = false
  callerNotVault : msg.caller ≠ vaultAddr
  callerNotWeth : msg.caller ≠ wethAccount

/-- A message that is about to run: an actual call, or a CREATE at an address that is neither pair
account. -/
structure PairMessageReady (vaultAddr : Adr) (msg : Msg) : Prop extends PairMsgInv vaultAddr msg where
  codeOrForeign : msg.target.isNone = false ∨
    (msg.currentTarget ≠ vaultAddr ∧ msg.currentTarget ≠ wethAccount)

/-- **The CREATE-collision arm.**  A CREATE aimed at either pair account collides: both hold non-empty
compiled code, and `messageCreateCollision` tests the target's code before anything runs. -/
theorem PairMsgInv.createCollision {vault : Adr} {msg : Msg} (ready : PairMsgInv vault msg)
    (target : msg.currentTarget = vault ∨ msg.currentTarget = wethAccount) :
    messageCreateCollision msg = true := by
  cases test : messageCreateCollision msg with
  | true => rfl
  | false =>
      rcases target with hit | hit
      · exact absurd hit (ready.vault.state.ne_of_messageCreateCollision_false test)
      · exact absurd hit (ready.weth.state.ne_of_messageCreateCollision_false test)
-- PT:44–50 / G:312–318, at two accounts.

/-- The retained root messages of a pair history: a transaction's prepared message and a system
transaction's message.  Direct withdrawals open no message frame; request calls are system messages; every
nested frame is classified inside the core. -/
inductive PairRootMessage (vault : Adr) : Msg → Prop
  | transaction {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
      {state : State} {bout' : BlockOutput}
      (trace : TransactionTrace benv bout tx index state bout')
      (inv : PairBenvInv vault benv) : PairRootMessage vault trace.msg
  | system {benv : Benv} (target : Adr) (data : Bytes) (inv : PairBenvInv vault benv) :
      PairRootMessage vault (systemTransactionMessage benv target data)

/-- **The root envelope.**  No retained root message of a pair history is sent by either pair account: a
checked transaction sender is never an installed contract (EIP-3607 in `checkTransaction`), and a system
message is sent by `systemAddress`, which neither account is.  Nested frames derive the same fact from their
parent inside the core (`History.lean:643–664`, and `:848–856` for the `withdraw` callback), so no premise of
this shape survives into any rung. -/
theorem pair_root_caller_ne_vault {vault : Adr} {msg : Msg}
    (root : PairRootMessage vault msg) :
    msg.caller ≠ vault ∧ msg.caller ≠ wethAccount := by
  cases root with
  | transaction trace inv =>
      rw [trace.msg_caller]
      exact ⟨trace.sender_ne inv.world.vault inv.vaultNotCreated,
        trace.sender_ne inv.world.weth inv.wethNotCreated⟩
  | system target data inv =>
      rw [systemTransactionMessage_caller]
      exact ⟨fun hit => inv.world.vaultNotSystem hit.symm,
        fun hit => inv.world.wethNotSystem hit.symm⟩
-- design §3.3.4; `sender_ne` ExecutionTransactionEffects:31, `msg_caller` §4 (G+1).

/-! ## 5. The message root -/

/-- **The message-root corollary, faithful.**  As `Exec.pairReplay_of_messageRoot`, and every owned
allowance invocation is the visit of a raw frame root of the message's own derivation. -/
theorem Exec.pairReplay_of_messageRootFaithful {vault : Adr} {msg : Msg} {entry : Benv}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (transfer : msg.benvAfterTransfer = .ok entry)
    (evmEq : (⟨pc, sevm, pre⟩ : Evm) = initEvm (msg.withBenv entry))
    (committed : Execution.commits out = true)
    (ready : PairMessageReady vault msg)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    PairReplayWith vault
      (fun r => PairProvenanceOk blockIndex transactionIndex [] r ∧
        PairStepRecord.OwnIn vault (Exec.rawFrameRoots run) r)
      (PairBoundary.ofState vault pre.state)
      (PairBoundary.ofState vault (Execution.committedPost out committed).state) := by
  have vaultPre := ContractSpec.Pre.of_inv_benvAfterTransfer
    ready.vault.ne ready.vault.val0 transfer ready.vault.state
  have wethPre := ContractSpec.Pre.of_inv_benvAfterTransfer
    ready.weth.ne ready.weth.val0 transfer ready.weth.state
  have pcEq := congrArg Evm.pc evmEq
  have sevmEq := congrArg Evm.sta evmEq
  have preEq := congrArg Evm.dyna evmEq
  dsimp only [initEvm] at pcEq sevmEq preEq
  subst pc
  subst sevm
  subst pre
  have targetEq : ∀ {a : Adr},
      (initSevm (msg.withBenv entry)).currentTarget = a → msg.currentTarget = a := by
    intro a hit
    simpa [initSevm, Msg.withBenv] using hit
  -- both programs, at `pc = 0`
  have vaultAt : Prog.At Blanc.ProrataWethVault.vault vault 0
      (initSevm (msg.withBenv entry)) (initDevm (msg.withBenv entry)) := by
    refine ⟨vaultPre.code, fun hit => ⟨?_, rfl⟩⟩
    rcases ready.codeOrForeign with call | ⟨vaultNe, -⟩
    · exact ready.vault.code call (targetEq hit)
    · exact absurd (targetEq hit) vaultNe
  have wethAt : Prog.At Blanc.weth wethAccount 0
      (initSevm (msg.withBenv entry)) (initDevm (msg.withBenv entry)) := by
    refine ⟨wethPre.code, fun hit => ⟨?_, rfl⟩⟩
    rcases ready.codeOrForeign with call | ⟨-, wethNe⟩
    · exact ready.weth.code call (targetEq hit)
    · exact absurd (targetEq hit) wethNe
  -- the configuration, from the stable statics the message carries
  have config : DirectWethConfiguration vault (initSevm (msg.withBenv entry))
      (initDevm (msg.withBenv entry)) := by
    refine ⟨ready.distinct, ?_, ?_⟩
    · show (msg.withBenv entry).benv.stat.rules.isPrecomp wethAccount = false
      rw [show (msg.withBenv entry).benv = entry from rfl, benvAfterTransfer_stat transfer]
      exact ready.wethNonprecompile
    · exact Option.some.inj (wethPre.code.trans Blanc.wethCode_compile)
  have inv : PairFrameInv vault (initSevm (msg.withBenv entry))
      (initDevm (msg.withBenv entry)) :=
    ⟨⟨⟨vaultPre, fun _ => Mem.wf_empty⟩, config, fun hit => (vaultAt.2 hit).1⟩,
      wethPre, fun _ => ⟨rfl, rfl⟩⟩
  -- the envelope
  have vaultDirect : (initSevm (msg.withBenv entry)).currentTarget = vault →
      (initSevm (msg.withBenv entry)).codeAddress = some vault ∧
        (initSevm (msg.withBenv entry)).caller ≠ vault := by
    intro hit
    refine ⟨?_, by simpa [initSevm, Msg.withBenv] using ready.callerNotVault⟩
    rcases ready.codeOrForeign with call | ⟨vaultNe, -⟩
    · simpa [initSevm, Msg.withBenv] using ready.vault.codeAddress call (targetEq hit)
    · exact absurd (targetEq hit) vaultNe
  have wethDirect : (initSevm (msg.withBenv entry)).currentTarget = wethAccount →
      (initSevm (msg.withBenv entry)).codeAddress = some wethAccount ∧
        (initSevm (msg.withBenv entry)).caller ≠ vault ∧
        (initSevm (msg.withBenv entry)).caller ≠ wethAccount := by
    intro hit
    refine ⟨?_, by simpa [initSevm, Msg.withBenv] using ready.callerNotVault,
      by simpa [initSevm, Msg.withBenv] using ready.callerNotWeth⟩
    rcases ready.codeOrForeign with call | ⟨-, wethNe⟩
    · simpa [initSevm, Msg.withBenv] using ready.weth.codeAddress call (targetEq hit)
    · exact absurd (targetEq hit) wethNe
  have core := Exec.corePairReplay vault 0 (initSevm (msg.withBenv entry))
    (initDevm (msg.withBenv entry)) out run wethAt
  exact core run committed vaultAt wethAt inv vaultDirect wethDirect
    blockIndex transactionIndex [] 0
-- PX:560–621 (`prorataAccountingReplay_of_messageRoot`) with two programs; the configuration clause is
-- Pair.lean:504–507; `wethFresh` is `Frame.enter_run_fresh`'s `⟨rfl, rfl⟩` (ExecutionFrameEntry:25).

/-- **The message-root corollary.**  The pair core at the exact EVM root a successful message entry selects:
every premise of `Exec.CorePairReplay` is discharged from the message's readiness. -/
theorem Exec.pairReplay_of_messageRoot {vault : Adr} {msg : Msg} {entry : Benv}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (transfer : msg.benvAfterTransfer = .ok entry)
    (evmEq : (⟨pc, sevm, pre⟩ : Evm) = initEvm (msg.withBenv entry))
    (committed : Execution.commits out = true)
    (ready : PairMessageReady vault msg)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    PairReplayBetween vault blockIndex transactionIndex []
      (PairBoundary.ofState vault pre.state)
      (PairBoundary.ofState vault (Execution.committedPost out committed).state) :=
  (Exec.pairReplay_of_messageRootFaithful run transfer evmEq committed ready blockIndex
    transactionIndex).mono fun _ h => h.1

/-! ## 6. Rungs R1–R3: message, CREATE, message-call wrapper

Each rung Rk has a faithful twin `…Faithful`: the same replay, whose records also witness every owned
allowance invocation among the rung's own raw frames.  The published rung is its projection. -/

/-- **R1, faithful.** -/
theorem retainedProcessMessagePairReplayFaithful {vault : Adr} {msg : Msg} {post : Devm}
    (trace : ProcessMessageTrace msg (.ok post))
    (ready : PairMessageReady vault msg)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    PairReplayWith vault
      (fun r => PairProvenanceOk blockIndex transactionIndex [] r ∧
        PairStepRecord.OwnIn vault trace.rawFrames r)
      (PairBoundary.ofState vault msg.benv.state) (PairBoundary.ofState vault post.state) := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none =>
      have storage := _root_.Blanc.ExecutionTrace.ProcessMessage.none_ok_getStor_eq process
      exact PairReplayWith.nil_of_eq
        (PairBoundary.ofState_eq (congrFun storage vault) (congrFun storage wethAccount))
  | @some pc sevm pre out run =>
      show PairReplayWith vault
        (fun r => PairProvenanceOk blockIndex transactionIndex [] r ∧
          PairStepRecord.OwnIn vault (Exec.rawFrameRoots run) r) _ _
      apply (pairCarrierWith vault
        (fun r => PairProvenanceOk blockIndex transactionIndex [] r ∧
          PairStepRecord.OwnIn vault (Exec.rawFrameRoots run) r)).processMessage_of_body process
        ready.weth.ne ready.weth.val0 ready.weth.state.side
      intro committed
      have enter := (RunFrame.some_inv process).1
      rcases Frame.enter_run_inv enter with ⟨entry, transfer, evmEq⟩
      exact Exec.pairReplay_of_messageRootFaithful run transfer evmEq committed ready
        blockIndex transactionIndex

/-- **R1.**  One retained CALL message. -/
theorem retainedProcessMessagePairReplay {vault : Adr} {msg : Msg} {post : Devm}
    (trace : ProcessMessageTrace msg (.ok post))
    (ready : PairMessageReady vault msg)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    PairReplayBetween vault blockIndex transactionIndex []
      (PairBoundary.ofState vault msg.benv.state) (PairBoundary.ofState vault post.state) :=
  (retainedProcessMessagePairReplayFaithful trace ready blockIndex transactionIndex).mono
    fun _ h => h.1
-- PX:623–658 / G:150–176; the no-slot arm is whole-world storage silence (no credit law).

/-- **R1c, faithful.** -/
theorem retainedProcessCreateMessagePairReplayFaithful {vault : Adr} {msg : Msg} {post : Devm}
    (trace : ProcessCreateMessageTrace msg (.ok post))
    (ready : PairMsgInv vault msg)
    (targetNone : msg.target.isNone = true)
    (vaultNe : msg.currentTarget ≠ vault) (wethNe : msg.currentTarget ≠ wethAccount)
    (fresh : msg.benv.state.getStor msg.currentTarget = .empty)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    PairReplayWith vault
      (fun r => PairProvenanceOk blockIndex transactionIndex [] r ∧
        PairStepRecord.OwnIn vault trace.rawFrames r)
      (PairBoundary.ofState vault msg.benv.state) (PairBoundary.ofState vault post.state) := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none =>
      have storage :=
        _root_.Blanc.ExecutionTrace.ProcessCreateMessage.none_ok_getStor_eq_of_empty
          process fresh
      exact PairReplayWith.nil_of_eq
        (PairBoundary.ofState_eq (congrFun storage vault) (congrFun storage wethAccount))
  | @some pc sevm pre out run =>
      show PairReplayWith vault
        (fun r => PairProvenanceOk blockIndex transactionIndex [] r ∧
          PairStepRecord.OwnIn vault (Exec.rawFrameRoots run) r) _ _
      apply (pairCarrierWith vault
        (fun r => PairProvenanceOk blockIndex transactionIndex [] r ∧
          PairStepRecord.OwnIn vault (Exec.rawFrameRoots run) r)).processCreateMessage_of_body
        process ready.weth.ne ready.weth.val0 fresh ready.weth.state.side
      intro committed
      have preparedNe : ∀ {a : Adr}, msg.currentTarget ≠ a →
          (processCreateMessage.msg msg).currentTarget ≠ a := by
        intro a ne hit
        exact ne (by simpa [processCreateMessage.msg, Msg.withBenv] using hit)
      have preparedReady : PairMessageReady vault (processCreateMessage.msg msg) :=
        { vault := ready.vault.processCreateMessage_msg targetNone vaultNe
          weth := ready.weth.processCreateMessage_msg targetNone wethNe
          distinct := ready.distinct
          wethNonprecompile := by
            simpa [processCreateMessage.msg, Msg.withBenv, addCreatedAccount,
              Benv.setStor, Benv.incrNonce] using ready.wethNonprecompile
          callerNotVault := by
            simpa [processCreateMessage.msg, Msg.withBenv] using ready.callerNotVault
          callerNotWeth := by
            simpa [processCreateMessage.msg, Msg.withBenv] using ready.callerNotWeth
          codeOrForeign := Or.inr ⟨preparedNe vaultNe, preparedNe wethNe⟩ }
      have enter := (RunFrame.some_inv process).1
      rcases Frame.enter_run_inv enter with ⟨entry, transfer, evmEq⟩
      exact Exec.pairReplay_of_messageRootFaithful run transfer evmEq committed preparedReady
        blockIndex transactionIndex

/-- **R1c.**  One retained CREATE constructor at an address that is neither pair account. -/
theorem retainedProcessCreateMessagePairReplay {vault : Adr} {msg : Msg} {post : Devm}
    (trace : ProcessCreateMessageTrace msg (.ok post))
    (ready : PairMsgInv vault msg)
    (targetNone : msg.target.isNone = true)
    (vaultNe : msg.currentTarget ≠ vault) (wethNe : msg.currentTarget ≠ wethAccount)
    (fresh : msg.benv.state.getStor msg.currentTarget = .empty)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    PairReplayBetween vault blockIndex transactionIndex []
      (PairBoundary.ofState vault msg.benv.state) (PairBoundary.ofState vault post.state) :=
  (retainedProcessCreateMessagePairReplayFaithful trace ready targetNone vaultNe wethNe fresh
    blockIndex transactionIndex).mono fun _ h => h.1
-- PX:660–714 / G:179–221; `processCreateMessage_msg` for both specs is exactly what keeps the vault's and
-- WETH's storage out of the prepared message's `setStor currentTarget .empty`.

/-- **R2, faithful.** -/
theorem retainedMessageCallPairReplayFaithful {vault : Adr} {msg : Msg} {state : State}
    {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (ready : PairMsgInv vault msg)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    PairReplayWith vault
      (fun r => PairProvenanceOk blockIndex transactionIndex [] r ∧
        PairStepRecord.OwnIn vault trace.rawFrames r)
      (PairBoundary.ofState vault msg.benv.state) (PairBoundary.ofState vault state) := by
  cases trace with
  | createCollision targetNone collision result =>
      have stateEq :=
        processMessageCall_createCollision_state_eq targetNone collision result
      exact PairReplayWith.nil_of_eq (by rw [stateEq])
  | createRun targetNone collision evm core inner result =>
      have vaultNe : msg.currentTarget ≠ vault := fun hit =>
        Bool.noConfusion ((ready.createCollision (.inl hit)).symm.trans collision)
      have wethNe : msg.currentTarget ≠ wethAccount := fun hit =>
        Bool.noConfusion ((ready.createCollision (.inr hit)).symm.trans collision)
      have fresh := messageCreateCollision_false_getStor_eq_empty collision
      have boundary := congrArg (PairBoundary.ofState vault)
        (processMessageCall_createRun_state_eq targetNone collision core result)
      rw [boundary]
      exact retainedProcessCreateMessagePairReplayFaithful inner ready targetNone vaultNe wethNe
        fresh blockIndex transactionIndex
  | callRun targetSome delegated refund delegation execMsg execMsgEq evm core inner result =>
      subst execMsgEq
      have stateEq :=
        processMessageCall_callRun_state_eq targetSome delegation rfl core result
      have execReady : PairMessageReady vault (messageCallExecutionMessage delegated) :=
        { vault := (ready.vault.of_messageCallDelegation delegation).messageCallExecutionMessage
          weth := (ready.weth.of_messageCallDelegation delegation).messageCallExecutionMessage
          distinct := ready.distinct
          wethNonprecompile := by
            rw [messageCallExecutionMessage_benv_stat, messageCallDelegation_benv_stat delegation]
            exact ready.wethNonprecompile
          callerNotVault := by
            rw [messageCallExecutionMessage_caller_eq, messageCallDelegation_caller_eq delegation]
            exact ready.callerNotVault
          callerNotWeth := by
            rw [messageCallExecutionMessage_caller_eq, messageCallDelegation_caller_eq delegation]
            exact ready.callerNotWeth
          codeOrForeign := Or.inl (by
            rw [messageCallExecutionMessage_target_eq, messageCallDelegation_target_eq delegation]
            exact targetSome) }
      have storEq : (messageCallExecutionMessage delegated).benv.state.getStor =
          msg.benv.state.getStor := by
        rw [messageCallExecutionMessage_getStor_eq, messageCallDelegation_getStor_eq delegation]
      have boundary := congrArg (PairBoundary.ofState vault) stateEq
      rw [boundary, ← PairBoundary.ofState_eq (congrFun storEq vault)
        (congrFun storEq wethAccount)]
      exact retainedProcessMessagePairReplayFaithful inner execReady blockIndex transactionIndex

/-- **R2.**  The settled message-call wrapper: create collision, CREATE run, EIP-7702-normalised call. -/
theorem retainedMessageCallPairReplay {vault : Adr} {msg : Msg} {state : State}
    {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (ready : PairMsgInv vault msg)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    PairReplayBetween vault blockIndex transactionIndex []
      (PairBoundary.ofState vault msg.benv.state) (PairBoundary.ofState vault state) :=
  (retainedMessageCallPairReplayFaithful trace ready blockIndex transactionIndex).mono
    fun _ h => h.1
-- PX:717–779 / G:225–295; the createRun arm replaces `codeOrForeign` by the collision derivation (§5).

/-! ## 7. Rung R3: one transaction -/

/-- **R3, faithful.** -/
theorem retainedTransactionPairReplayFaithful {vault : Adr} {benv : Benv} {bout : BlockOutput}
    {tx : Tx} {index : Nat} {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (inv : PairBenvInv vault benv)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    PairReplayWith vault
      (fun r => PairProvenanceOk blockIndex transactionIndex [] r ∧
        PairStepRecord.OwnIn vault trace.rawFrames r)
      (PairBoundary.ofState vault benv.state) (PairBoundary.ofState vault state) := by
  rcases trace.exists_stateChronology with ⟨chronology⟩
  -- (1) nonce bump and up-front debit: storage-silent everywhere
  have debitBoundary : PairBoundary.ofState vault trace.msg.benv.state =
      PairBoundary.ofState vault benv.state := by
    rw [prepareMessage_benv trace.prepared]
    show PairBoundary.ofState vault trace.debitState = _
    exact PairBoundary.ofState_eq trace.debitState_getStor_eq trace.debitState_getStor_eq
  -- (2) the envelope and the prepared message, by R2
  have envelope := pair_root_caller_ne_vault (.transaction trace inv)
  have ready : PairMsgInv vault trace.msg :=
    { vault := trace.msgInv inv.world.vault inv.vaultNotCreated
      weth := trace.msgInv inv.world.weth inv.wethNotCreated
      distinct := inv.world.distinct
      wethNonprecompile := by
        rw [prepareMessage_benv trace.prepared]
        exact inv.wethNonprecompile
      callerNotVault := envelope.1
      callerNotWeth := envelope.2 }
  have messageReplay :=
    retainedMessageCallPairReplayFaithful trace.message ready blockIndex transactionIndex
  rw [debitBoundary] at messageReplay
  -- (3), (4) the two gas credits move balances only
  have settled : PairBoundary.ofState vault (trace.coinbaseState chronology.refundCounter) =
      PairBoundary.ofState vault trace.messageState :=
    PairBoundary.ofState_eq
      ((getStor_addBal _ vault _ _).trans (getStor_addBal _ vault _ _))
      ((getStor_addBal _ wethAccount _ _).trans (getStor_addBal _ wethAccount _ _))
  -- (5) the deletion fold names neither pair account
  have vaultKept := foldl_destroyAccount_get_eq
    (state := trace.coinbaseState chronology.refundCounter)
    (trace.accountsToDelete_ne (pairVaultCodeSpec_preserves vault)
      inv.world.vaultCode inv.vaultNotCreated)
  have wethKept := foldl_destroyAccount_get_eq
    (state := trace.coinbaseState chronology.refundCounter)
    (trace.accountsToDelete_ne (wethSpec_preserves wethAccount)
      inv.world.weth inv.wethNotCreated)
  have finalBoundary : PairBoundary.ofState vault state =
      PairBoundary.ofState vault trace.messageState := by
    have finalState : PairBoundary.ofState vault state =
        PairBoundary.ofState vault
          (trace.messageOut.accountsToDelete.toList.foldl destroyAccount
            (trace.coinbaseState chronology.refundCounter)) :=
      congrArg (PairBoundary.ofState vault) chronology.finalState_eq
    exact (finalState.trans
      (PairBoundary.ofState_eq (congrArg Acct.stor vaultKept)
        (congrArg Acct.stor wethKept))).trans settled
  rw [finalBoundary]
  exact messageReplay

/-- **R3.**  One whole retained transaction.  It moves the pair's boundary only through its message: the
nonce bump, fee debit, refund and coinbase credit move balances, and the deletion fold names neither pair
account. -/
theorem retainedTransactionPairReplay {vault : Adr} {benv : Benv} {bout : BlockOutput}
    {tx : Tx} {index : Nat} {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (inv : PairBenvInv vault benv)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    PairReplayBetween vault blockIndex transactionIndex []
      (PairBoundary.ofState vault benv.state) (PairBoundary.ofState vault state) :=
  (retainedTransactionPairReplayFaithful trace inv blockIndex transactionIndex).mono
    fun _ h => h.1
-- PT:76–146 / G:333–393.  No `settlement_sum_bounds`, no `ofAddBal`: the boundary has no balance.  No
-- G3' split: R2 owns the create-at-account case.

/-! ## 8. Rungs R4–R7: transaction list, system message, requests, withdrawals, body -/

/-- **R4, faithful.** -/
theorem retainedTransactionListPairReplayFaithful {vault : Adr} {txs : List (Nat × Tx)}
    {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (inv : PairBenvInv vault benv) (blockIndex : Nat) :
    PairReplayWith vault
      (fun r => PairInBlock blockIndex r ∧ PairStepRecord.OwnIn vault trace.rawFrames r)
      (PairBoundary.ofState vault benv.state) (PairBoundary.ofState vault finalBenv.state) := by
  induction trace with
  | nil => exact PairReplayWith.nil_of_eq rfl
  | @cons index tx txs benv bout txState txBout finalBenv finalBout head tail ih =>
      have headReplay := retainedTransactionPairReplayFaithful head inv blockIndex (some index)
      exact (headReplay.faithfulLift (fun _ ok => ok.block)
          (fun d member => List.mem_append.mpr (Or.inl member))).append
        ((ih (inv.afterTransaction head headReplay)).faithfulLift (fun _ ok => ok)
          (fun d member => List.mem_append.mpr (Or.inr member)))

/-- **R4.**  A retained transaction list; each record keeps its own transaction position. -/
theorem retainedTransactionListPairReplay {vault : Adr} {txs : List (Nat × Tx)}
    {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (inv : PairBenvInv vault benv) (blockIndex : Nat) :
    PairReplayWith vault (PairInBlock blockIndex)
      (PairBoundary.ofState vault benv.state) (PairBoundary.ofState vault finalBenv.state) :=
  (retainedTransactionListPairReplayFaithful trace inv blockIndex).mono fun _ h => h.1
-- PB:21–45 / G:396–422.

/-- **R5, faithful.** -/
theorem retainedSystemMessagePairReplayFaithful {vault : Adr} {benv : Benv} {target : Adr}
    {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (inv : PairBenvInv vault benv) (blockIndex : Nat) :
    PairReplayWith vault
      (fun r => PairProvenanceOk blockIndex none [] r ∧
        PairStepRecord.OwnIn vault trace.rawFrames r)
      (PairBoundary.ofState vault benv.state) (PairBoundary.ofState vault state) := by
  have envelope := pair_root_caller_ne_vault (.system target data inv)
  have ready : PairMsgInv vault (systemTransactionMessage benv target data) :=
    { vault := systemTransactionMessage_msgInv inv.world.vault inv.vaultNotCreated
      weth := systemTransactionMessage_msgInv inv.world.weth inv.wethNotCreated
      distinct := inv.world.distinct
      wethNonprecompile := inv.wethNonprecompile
      callerNotVault := envelope.1
      callerNotWeth := envelope.2 }
  have replay := retainedMessageCallPairReplayFaithful trace.message ready blockIndex none
  rw [systemTransactionMessage_benv_state] at replay
  exact replay

/-- **R5.**  One retained system message.  No `target ≠ systemAddress` side condition: the envelope is
the two pair accounts' own separation from `systemAddress`. -/
theorem retainedSystemMessagePairReplay {vault : Adr} {benv : Benv} {target : Adr}
    {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (inv : PairBenvInv vault benv) (blockIndex : Nat) :
    PairReplayBetween vault blockIndex none []
      (PairBoundary.ofState vault benv.state) (PairBoundary.ofState vault state) :=
  (retainedSystemMessagePairReplayFaithful trace inv blockIndex).mono fun _ h => h.1
-- PB:58–84 / G:425–451, minus `systemNe`.

/-- **R6, faithful.** -/
theorem retainedRequestsPairReplayFaithful {vault : Adr} {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (inv : PairBenvInv vault benv) (blockIndex : Nat) :
    PairReplayWith vault
      (fun r => PairProvenanceOk blockIndex none [] r ∧
        PairStepRecord.OwnIn vault trace.rawFrames r)
      (PairBoundary.ofState vault benv.state) (PairBoundary.ofState vault state) := by
  have withdrawalReplay :=
    retainedSystemMessagePairReplayFaithful trace.withdrawal inv blockIndex
  have withdrawalInv := inv.afterSystem trace.withdrawal withdrawalReplay
  have consolidationReplay :=
    retainedSystemMessagePairReplayFaithful trace.consolidation withdrawalInv blockIndex
  have boundary := congrArg (PairBoundary.ofState vault)
    (RequestsTrace.state_eq_consolidationState trace)
  rw [boundary]
  exact (withdrawalReplay.faithfulLift (fun _ ok => ok)
      (fun d member => List.mem_append.mpr (Or.inl member))).append
    (consolidationReplay.faithfulLift (fun _ ok => ok)
      (fun d member => List.mem_append.mpr (Or.inr member)))

/-- **R6.**  The two checked request calls. -/
theorem retainedRequestsPairReplay {vault : Adr} {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (inv : PairBenvInv vault benv) (blockIndex : Nat) :
    PairReplayBetween vault blockIndex none []
      (PairBoundary.ofState vault benv.state) (PairBoundary.ofState vault state) :=
  (retainedRequestsPairReplayFaithful trace inv blockIndex).mono fun _ h => h.1
-- PB:89–112 / G:454–480.

/-- **R6w.**  The direct consensus withdrawals: balance credits only, so no record and no bound. -/
theorem retainedDirectWithdrawalPairReplay (vault : Adr) (pre : State)
    (wds : List Withdrawal) (blockIndex : Nat) :
    PairReplayBetween vault blockIndex none []
      (PairBoundary.ofState vault pre)
      (PairBoundary.ofState vault (processWithdrawalsState pre wds)) :=
  PairReplayBetween.nil_of_eq (PairBoundary.ofState_eq
    (processWithdrawalsState_getStor_eq vault pre wds)
    (processWithdrawalsState_getStor_eq wethAccount pre wds))
-- replaces PB:123–146 / G:483–501 (per-credit `ofAddBal` induction) by one storage equation.

/-- **R7, faithful.** -/
theorem retainedBodyPairReplayFaithful {vault : Adr} {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (inv : PairBenvInv vault benv)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256) (blockIndex : Nat) :
    PairReplayWith vault
      (fun r => PairInBlock blockIndex r ∧ PairStepRecord.OwnIn vault trace.rawFrames r)
      (PairBoundary.ofState vault benv.state) (PairBoundary.ofState vault state) := by
  -- (1) beacon roots
  have beaconReplay := retainedSystemMessagePairReplayFaithful trace.beacon inv blockIndex
  have beaconInv := inv.afterSystem trace.beacon beaconReplay
  -- (2) history storage
  have historyReplay :=
    retainedSystemMessagePairReplayFaithful trace.history beaconInv blockIndex
  have historyInv := beaconInv.afterSystem trace.history historyReplay
  -- (3) the transaction list, by R4
  have txReplay :=
    retainedTransactionListPairReplayFaithful trace.transactions historyInv blockIndex
  have txInv := historyInv.afterTransactions trace.transactions txReplay
  -- (4) direct withdrawals: no record
  have wdReplay : PairReplayWith vault
      (fun r => PairInBlock blockIndex r ∧ PairStepRecord.OwnIn vault trace.rawFrames r)
      (PairBoundary.ofState vault trace.transactionBenv.state)
      (PairBoundary.ofState vault (processWithdrawalsState trace.transactionBenv.state wds)) :=
    PairReplayWith.nil_of_eq (PairBoundary.ofState_eq
      (processWithdrawalsState_getStor_eq vault trace.transactionBenv.state wds)
      (processWithdrawalsState_getStor_eq wethAccount trace.transactionBenv.state wds))
  have wdInv := txInv.afterWithdrawals (trace.transactionBound bound)
  -- (5) request calls, by R6
  have requestReplay := retainedRequestsPairReplayFaithful trace.requests wdInv blockIndex
  have sub : ∀ {F : List Exec.Deriv}, (∀ d ∈ F, d ∈ trace.rawFrames) →
      ∀ {p : PairStepRecord vault → Prop}, (∀ r, p r → PairInBlock blockIndex r) →
      ∀ {pre post : PairBoundary},
        PairReplayWith vault (fun r => p r ∧ PairStepRecord.OwnIn vault F r) pre post →
        PairReplayWith vault
          (fun r => PairInBlock blockIndex r ∧ PairStepRecord.OwnIn vault trace.rawFrames r)
          pre post :=
    fun {_} inside {_} weaken {_ _} replay => replay.faithfulLift weaken inside
  exact (sub (fun d member => by simp [AppliedBodyTrace.rawFrames, member])
      (fun _ ok => ok.block) beaconReplay).append
    ((sub (fun d member => by simp [AppliedBodyTrace.rawFrames, member])
      (fun _ ok => ok.block) historyReplay).append
    ((sub (fun d member => by simp [AppliedBodyTrace.rawFrames, member])
      (fun _ ok => ok) txReplay).append
    (wdReplay.append
      (sub (fun d member => by simp [AppliedBodyTrace.rawFrames, member])
        (fun _ ok => ok.block) requestReplay))))

/-- **R7.**  A whole successful block body, in `applyBody` order. -/
theorem retainedBodyPairReplay {vault : Adr} {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (inv : PairBenvInv vault benv)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256) (blockIndex : Nat) :
    PairReplayWith vault (PairInBlock blockIndex)
      (PairBoundary.ofState vault benv.state) (PairBoundary.ofState vault state) :=
  (retainedBodyPairReplayFaithful trace inv bound blockIndex).mono fun _ h => h.1
-- PB:163–222 / G:504–572; `transactionBound` is §4 (G+4), the inline `txBound` of PB:190–198 / G:548–556.

/-! ## 9. Rungs R8–R9, the root, and the stable boundary of a history -/

/-- **R8, faithful.** -/
theorem retainedConfiguredBlockPairReplayFaithful {vault : Adr} {cfg : ChainConfig}
    {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post)
    (inv : PairWorldInv vault pre.state)
    (wethNonprecompile : trace.rules.isPrecomp wethAccount = false)
    (blockIndex : Nat) :
    PairReplayWith vault
      (fun r => PairInBlock blockIndex r ∧ PairStepRecord.OwnIn vault trace.rawFrames r)
      (PairBoundary.ofState vault pre.state) (PairBoundary.ofState vault post.state) := by
  have benvInv : PairBenvInv vault (initBenv trace.fork pre trace.block.header) :=
    ⟨trace.openingState ▸ inv, trace.not_mem_openingCreatedAccounts vault,
      trace.not_mem_openingCreatedAccounts wethAccount, wethNonprecompile⟩
  have replay :=
    retainedBodyPairReplayFaithful trace.bodyTrace benvInv trace.openingBound blockIndex
  have postBoundary := congrArg (PairBoundary.ofState vault) trace.postState
  have openingBoundary := congrArg (PairBoundary.ofState vault) trace.openingState
  rw [postBoundary]
  rw [openingBoundary] at replay
  exact replay

/-- **R8.**  A whole configured block.  The rules fact is the schedule's, at the block's own rules. -/
theorem retainedConfiguredBlockPairReplay {vault : Adr} {cfg : ChainConfig}
    {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post)
    (inv : PairWorldInv vault pre.state)
    (wethNonprecompile : trace.rules.isPrecomp wethAccount = false)
    (blockIndex : Nat) :
    PairReplayWith vault (PairInBlock blockIndex)
      (PairBoundary.ofState vault pre.state) (PairBoundary.ofState vault post.state) :=
  (retainedConfiguredBlockPairReplayFaithful trace inv wethNonprecompile blockIndex).mono
    fun _ h => h.1
-- PH:30–46 / G:576–589.

/-- **R9, faithful.**  Each block's records carry that block's header number, and every owned
allowance invocation is a visit of the history's own raw frames. -/
theorem retainedConfiguredHistoryPairReplayFaithful {vault : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint future)
    (inv : PairWorldInv vault checkpoint.state)
    (schedule : ∀ {timestamp : Nat} {rules : ForkRules},
      cfg.rulesAt timestamp = .ok rules → rules.isPrecomp wethAccount = false) :
    PairReplayWith vault (fun r => PairStepRecord.OwnIn vault history.rawFrames r)
      (PairBoundary.ofState vault checkpoint.state)
      (PairBoundary.ofState vault future.state) := by
  induction history with
  | refl hcfg hctx hid => exact PairReplayWith.nil_of_eq rfl
  | step prior block ih =>
      have current := inv.afterHistory prior ih
      exact (ih.mono fun _ own => own.mono fun d member =>
          List.mem_append.mpr (Or.inl member)).append
        ((retainedConfiguredBlockPairReplayFaithful block current
          (schedule block.rulesAt) block.block.header.number).mono fun _ h =>
            h.2.mono fun d member => List.mem_append.mpr (Or.inr member))

/-- **R9.**  A whole configured history.  The pair invariant is carried block to block by the generic
transports and the replay itself; each block's records carry that block's header number. -/
theorem retainedConfiguredHistoryPairReplay {vault : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint future)
    (inv : PairWorldInv vault checkpoint.state)
    (schedule : ∀ {timestamp : Nat} {rules : ForkRules},
      cfg.rulesAt timestamp = .ok rules → rules.isPrecomp wethAccount = false) :
    PairReplayWith vault (fun _ => True)
      (PairBoundary.ofState vault checkpoint.state)
      (PairBoundary.ofState vault future.state) :=
  (retainedConfiguredHistoryPairReplayFaithful history inv schedule).mono fun _ _ => trivial
-- PH:63–80 / G:593–606.

/-- The post-installation root carries the pair invariant. -/
theorem PairWorldInv.of_root {cfg : ChainConfig} {deployed : BlockChain} {vault : Adr}
    (root : PairRoot cfg deployed vault) : PairWorldInv vault deployed.state := by
  refine ⟨⟨root.vaultInstalled, trivial, ?_⟩, ⟨?_, root.sumNof, ?_⟩, root.distinct,
    root.vaultNotSystem, root.wethNotSystem⟩
  · exact LedgerConserved.of_get_eq_zero (fun key => by rw [root.vaultEmpty]; rfl)
  · rw [root.wethInstalled, wethSpec_prog_eq, Blanc.wethCode_compile]
  · show balSum (deployed.state.getStor wethAccount) + (0 : B256).toNat ≤
      (deployed.state.bal wethAccount).toNat
    have rest : Stor.rest (deployed.state.getStor wethAccount) = fun _ => (0 : B256) := by
      rw [root.wethEmpty]
      funext key
      rfl
    rw [balSum, sum, rest, sumBelow_zero]
    exact Nat.zero_le _
-- Pair.lean:145–162 without the rules; the solvency lines follow LedgerConservation.lean:213 (§9 D-d).

/-- The pair history from its root: the whole configured continuation replays. -/
theorem pair_history_replay {cfg : ChainConfig} {deployed future : BlockChain} {vault : Adr}
    (root : PairRoot cfg deployed vault)
    (history : ConfiguredHistoryTrace cfg deployed future) :
    PairReplayWith vault (fun _ => True)
      (PairBoundary.ofState vault deployed.state) (PairBoundary.ofState vault future.state) :=
  retainedConfiguredHistoryPairReplay history (PairWorldInv.of_root root)
    (fun rulesAt => (root.notPrecompile rulesAt).2)

/-- Every configured continuation of the root carries the pair invariant, unconditionally. -/
theorem PairWorldInv.of_history {cfg : ChainConfig} {deployed future : BlockChain}
    {vault : Adr} (root : PairRoot cfg deployed vault)
    (history : ConfiguredHistoryTrace cfg deployed future) :
    PairWorldInv vault future.state :=
  (PairWorldInv.of_root root).afterHistory history (pair_history_replay root history)

/-- **`PairStable` of a history.**  Everything but the two backing numbers is unconditional; those two are
the premises, because only D9 carries `supply ≤ offset · row` (design §3.3.6), and the supply cap's
preservation needs supply-slot facts the share operations do not yet export (§7). -/
theorem PairStable.of_history {cfg : ChainConfig} {deployed future : BlockChain}
    {vault : Adr} (root : PairRoot cfg deployed vault)
    (history : ConfiguredHistoryTrace cfg deployed future)
    {timestamp : Nat} {rules : ForkRules} (rulesAt : cfg.rulesAt timestamp = .ok rules)
    (capped : supplyN (future.state.getStor vault) ≤ Blanc.ProrataWethVault.maxSupplyN)
    (backing : supplyN (future.state.getStor vault) ≤
      Blanc.ProrataWethVault.offsetN *
        (Stor.rest (future.state.getStor wethAccount) vault).toNat) :
    PairStable vault rules future.state := by
  have world := PairWorldInv.of_history root history
  obtain ⟨vaultPrecomp, wethPrecomp⟩ := root.notPrecompile rulesAt
  exact ⟨world.vault.code, Option.some.inj (world.weth.code.trans Blanc.wethCode_compile),
    world.distinct, root.vaultNonzero, vaultPrecomp, wethPrecomp,
    ⟨world.conserved, capped, backing⟩, world.weth.side, world.weth.inv⟩

end Blanc.Composition.ProrataWethVault
