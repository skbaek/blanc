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

/-- A connected pair replay whose records all satisfy `ok`.  `PairReplayBetween b t fp` is the instance
`ok = PairProvenanceOk b t fp`. -/
def PairReplayWith (vault : Adr) (ok : PairStepRecord vault → Prop)
    (pre post : PairBoundary) : Prop :=
  ∃ steps, PairReplay vault pre steps post ∧ ∀ r ∈ steps, ok r

/-- A record emitted inside block `blockIndex`. -/
def PairInBlock {vault : Adr} (blockIndex : Nat) (r : PairStepRecord vault) : Prop :=
  r.provenance.blockIndex = blockIndex

namespace PairReplayWith

variable {vault : Adr} {ok ok' : PairStepRecord vault → Prop}

theorem nil_of_eq {pre post : PairBoundary} (eq : post = pre) :
    PairReplayWith vault ok pre post :=
  ⟨[], PairReplay.nil_of_eq eq, by simp⟩
-- H:270–272 at a general predicate.

theorem append {pre mid post : PairBoundary}
    (first : PairReplayWith vault ok pre mid) (second : PairReplayWith vault ok mid post) :
    PairReplayWith vault ok pre post := by
  obtain ⟨left, leftReplay, leftOk⟩ := first
  obtain ⟨right, rightReplay, rightOk⟩ := second
  refine ⟨left ++ right, leftReplay.append rightReplay, fun r member => ?_⟩
  rcases List.mem_append.mp member with inLeft | inRight
  · exact leftOk r inLeft
  · exact rightOk r inRight
-- H:274–283 at a general predicate (K1 note §9 D-d).

theorem mono {pre post : PairBoundary} (weaken : ∀ r, ok r → ok' r)
    (replay : PairReplayWith vault ok pre post) : PairReplayWith vault ok' pre post := by
  obtain ⟨steps, stepsReplay, stepsOk⟩ := replay
  exact ⟨steps, stepsReplay, fun r member => weaken r (stepsOk r member)⟩

end PairReplayWith

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

end Blanc.Composition.ProrataWethVault
