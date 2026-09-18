-- ProrataWethVaultHistory.lean : the pair history carrier and its interpreter core.

import Blanc.Composition.ProrataWethVaultEnvironment
import Blanc.Composition.ProrataWethVaultAccounting
import Blanc.ProrataRealizedAccounting
import Blanc.Composition.ProrataWethVaultRely
import Blanc.Composition.ProrataWethVaultLedgerVisits

namespace Blanc.Composition.ProrataWethVault

open Jaune

/-- The pair's replay boundary: the two storages the pair reads.  Balances are not in it; WETH
solvency rides in the frame invariant, not in the replay. -/
structure PairBoundary where
  /-- The vault's storage. -/
  vault : Stor
  /-- WETH's storage, at `wethAccount`. -/
  weth : Stor

/-- The pair boundary of an ordinary world state. -/
def PairBoundary.ofState (vault : Adr) (w : State) : PairBoundary :=
  ⟨w.getStor vault, w.getStor wethAccount⟩

/-- One classified pair step.  Emitted only by a frame at the vault or at WETH; a foreign
instruction segment moves no boundary and emits nothing.  `silent` is a WETH-frame class. -/
inductive PairStep (vault : Adr) : State → State → Type
  /-- A vault-frame share operation: a four-quote transition with its share evidence. -/
  | operation {before after : State} (t : FourQuote.FourQuoteTransition vault before after)
      (evidence : FourQuote.FourQuoteShareEvidence t.operation) : PairStep vault before after
  /-- A WETH spend of the vault's allowance by a caller other than the vault: the vault's WETH row moves by `Transfer` and vault storage is unchanged. -/
  | authorizedDebit {before after : State} (call : WethAllowanceInvocation)
      (foreign : call.sevm.caller ≠ vault)
      (owner : Sevm.argWord call.sevm 0 = vault.toB256)
      (pair : call.pair? = some (vault.toB256, call.sevm.caller.toB256))
      (moved : Transfer (Stor.rest (before.getStor wethAccount)) vault
        (Sevm.argWord call.sevm 2) (Sevm.argWord call.sevm 1).toAdr
        (Stor.rest (after.getStor wethAccount)))
      (vaultKept : after.getStor vault = before.getStor vault) : PairStep vault before after
  /-- A WETH-frame step by `caller` that leaves vault storage and the vault's WETH row unchanged. -/
  | silent {before after : State} (caller : Adr)
      (vaultKept : after.getStor vault = before.getStor vault)
      (rowKept : Stor.rest (after.getStor wethAccount) vault =
        Stor.rest (before.getStor wethAccount) vault) : PairStep vault before after

/-- The caller of the frame that emitted the step. -/
def PairStep.caller {vault : Adr} {before after : State} : PairStep vault before after → Adr
  | .operation t _ => t.sevm.caller
  | .authorizedDebit call _ _ _ _ _ => call.sevm.caller
  | .silent caller _ _ => caller

/-- One emitted step with its real endpoint states, the allowance invocation it is or contains
(`own`), that invocation's storage links, the non-address silence of a step that is none, and
its provenance, whose actor is the emitting frame's caller. -/
structure PairStepRecord (vault : Adr) where
  /-- The state where the step starts. -/
  before : State
  /-- The state where the step ends. -/
  after : State
  /-- The classified step between `before` and `after`. -/
  step : PairStep vault before after
  /-- The WETH allowance invocation the step is or contains, if any. -/
  own : Option WethAllowanceInvocation
  /-- An owned invocation's WETH storage matches the record's endpoints, and a vault-called one carries vault-staged calldata. -/
  linked : ∀ call, own = some call →
    call.pre.state.getStor wethAccount = before.getStor wethAccount ∧
    call.post.state.getStor wethAccount = after.getStor wethAccount ∧
    (call.sevm.caller = vault → VaultStagedCalldata call)
  /-- A step owning no invocation leaves every non-address WETH storage key unchanged. -/
  quiet : own = none → ∀ key, ¬ ValidAdr key →
    (after.getStor wethAccount).get key = (before.getStor wethAccount).get key
  /-- An `authorizedDebit` step owns its own invocation. -/
  debitOwn : ∀ call f o p m k, step = .authorizedDebit call f o p m k → own = some call
  /-- The step's accounting provenance. -/
  provenance : Blanc.Prorata.ProrataAccountingProvenance
  /-- The provenance actor is the emitting frame's caller. -/
  actor : provenance.actor = some step.caller

/-- The allowance ledger of a history: the invocations its records own, in order. -/
def PairStepRecord.ledger (steps : List (PairStepRecord vault)) : List WethAllowanceInvocation :=
  steps.filterMap (·.own)

/-- A connected pair history: consecutive records meet at equal pair boundaries. -/
inductive PairReplay (vault : Adr) : PairBoundary → List (PairStepRecord vault) → PairBoundary → Prop
  /-- The empty history replays a boundary to itself. -/
  | nil (b : PairBoundary) : PairReplay vault b [] b
  /-- Prepend a record whose endpoint boundaries are `pre` and `mid` to a history from `mid` to `post`. -/
  | cons {pre mid post : PairBoundary} (record : PairStepRecord vault) {steps}
      (preEq : PairBoundary.ofState vault record.before = pre)
      (postEq : PairBoundary.ofState vault record.after = mid)
      (tail : PairReplay vault mid steps post) : PairReplay vault pre (record :: steps) post

namespace PairReplay

/-- Equal boundaries replay with no record. -/
theorem nil_of_eq {vault : Adr} {pre post : PairBoundary}
    (eq : post = pre) : PairReplay vault pre [] post := by
  rw [eq]
  exact .nil pre

/-- One record replays between its own endpoints. -/
theorem singleton {vault : Adr} (record : PairStepRecord vault) :
    PairReplay vault (PairBoundary.ofState vault record.before) [record]
      (PairBoundary.ofState vault record.after) := by
  exact .cons record rfl rfl (.nil _)

/-- Histories compose. -/
theorem append {vault : Adr} {pre mid post : PairBoundary}
    {left right : List (PairStepRecord vault)}
    (before : PairReplay vault pre left mid)
    (after : PairReplay vault mid right post) :
    PairReplay vault pre (left ++ right) post := by
  induction before with
  | nil boundary =>
      simpa using after
  | @cons pre mid post record steps preEq postEq tail ih =>
      simpa using PairReplay.cons record preEq postEq (ih after)

/-- The ledger of a composed history is the composed ledger. -/
theorem ledger_append {vault : Adr} {xs ys : List (PairStepRecord vault)} :
    PairStepRecord.ledger (xs ++ ys) =
      PairStepRecord.ledger xs ++ PairStepRecord.ledger ys := by
  simp [PairStepRecord.ledger]

end PairReplay

/-- A connected pair replay whose records all satisfy `ok`.  `PairReplayBetween b t fp` is the instance
`ok = PairProvenanceOk b t fp`. -/
def PairReplayWith (vault : Adr) (ok : PairStepRecord vault → Prop)
    (pre post : PairBoundary) : Prop :=
  ∃ steps, PairReplay vault pre steps post ∧ ∀ r ∈ steps, ok r

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

/-- A record's owned call is the visit of some frame in `frames`. -/
def PairStepRecord.OwnIn (vault : Adr) (frames : List Exec.Deriv)
    (r : PairStepRecord vault) : Prop :=
  ∀ call, r.own = some call → ∃ d ∈ frames, d.pairVisit? vault = some call.visit

/-- Ownership witnesses survive enlarging the frame universe. -/
theorem PairStepRecord.OwnIn.mono {vault : Adr} {F G : List Exec.Deriv}
    {r : PairStepRecord vault} (sub : ∀ d ∈ F, d ∈ G) :
    r.OwnIn vault F → r.OwnIn vault G := by
  intro own call owned
  obtain ⟨d, member, visit⟩ := own call owned
  exact ⟨d, sub d member, visit⟩

/-! ## The frame invariant and the motive -/

/-- The frame invariant carried across every frame of a pair execution: the vault's rely
invariant, WETH's solvency precondition, and a fresh entry whenever the frame is WETH's own. -/
structure PairFrameInv (vault : Adr) (sevm : Sevm) (pre : Devm) : Prop where
  vault : VaultFrameInv vault sevm pre
  weth : wethSpec.Pre wethAccount sevm pre
  wethFresh : sevm.currentTarget = wethAccount → Exec.FreshEntry sevm pre

/-- A record's provenance names the transaction and sits at or below the emitting frame path. -/
structure PairProvenanceOk {vault : Adr} (blockIndex : Nat) (transactionIndex : Option Nat)
    (framePath : List Nat) (r : PairStepRecord vault) : Prop where
  block : r.provenance.blockIndex = blockIndex
  tx : r.provenance.transactionIndex = transactionIndex
  path : framePath <+: r.provenance.framePath

/-- The conclusion of the pair core: a connected replay between two boundaries whose records all
carry admissible provenance. -/
def PairReplayBetween (vault : Adr) (blockIndex : Nat) (transactionIndex : Option Nat)
    (framePath : List Nat) (pre post : PairBoundary) : Prop :=
  ∃ steps, PairReplay vault pre steps post ∧
    ∀ r ∈ steps, PairProvenanceOk blockIndex transactionIndex framePath r

/-- Proof-indexed committed pair replay for one interpreter suffix.  Every record carries
admissible provenance, and every allowance invocation it owns is the visit of a raw frame root of
the suffix's own derivation. -/
def Exec.CorePairReplay (vault : Adr) (pc : Nat) (sevm : Sevm) (pre : Devm)
    (out : Execution) : Prop :=
  ∀ (run : Exec pc sevm pre out) (committed : Execution.commits out = true),
    Prog.At Blanc.ProrataWethVault.vault vault pc sevm pre →
    Prog.At Blanc.weth wethAccount pc sevm pre →
    PairFrameInv vault sevm pre →
    (sevm.currentTarget = vault → sevm.codeAddress = some vault ∧ sevm.caller ≠ vault) →
    (sevm.currentTarget = wethAccount → sevm.codeAddress = some wethAccount ∧
      sevm.caller ≠ vault ∧ sevm.caller ≠ wethAccount) →
    ∀ (blockIndex : Nat) (transactionIndex : Option Nat) (framePath : List Nat)
      (_nextChild : Nat),
      PairReplayWith vault
        (fun r => PairProvenanceOk blockIndex transactionIndex framePath r ∧
          PairStepRecord.OwnIn vault (Exec.rawFrameRoots run) r)
        (PairBoundary.ofState vault pre.state)
        (PairBoundary.ofState vault (Execution.committedPost out committed).state)

/-- The core's conclusion without its frame witnesses. -/
theorem Exec.CorePairReplay.toBetween {vault : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} {run : Exec pc sevm pre out} {committed : Execution.commits out = true}
    {blockIndex : Nat} {transactionIndex : Option Nat} {framePath : List Nat}
    (replay : PairReplayWith vault
      (fun r => PairProvenanceOk blockIndex transactionIndex framePath r ∧
        PairStepRecord.OwnIn vault (Exec.rawFrameRoots run) r)
      (PairBoundary.ofState vault pre.state)
      (PairBoundary.ofState vault (Execution.committedPost out committed).state)) :
    PairReplayBetween vault blockIndex transactionIndex framePath
      (PairBoundary.ofState vault pre.state)
      (PairBoundary.ofState vault (Execution.committedPost out committed).state) :=
  replay.mono fun _ h => h.1

/-! ## The three segment hypotheses -/

/-- **Segment hypothesis (vault frame).**  A committed compiled vault run entered by a caller
other than the vault is a provenance-tagged replay between its own endpoints.  A record owns an
invocation only under `deposit` or `mint`, and that invocation's visit is the inbound
`transferFrom` the frame stages: caller the vault, owner the frame's caller, WETH's storage at the
frame's entry. -/
def VaultFramePairSegment (vault : Adr) : Prop :=
  ∀ {sevm : Sevm} {pre post : Devm},
    Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post →
    sevm.currentTarget = vault → sevm.codeAddress = some vault → sevm.caller ≠ vault →
    PairFrameInv vault sevm pre →
    ∀ provenance : Blanc.Prorata.ProrataAccountingProvenance,
      provenance.actor = some sevm.caller →
      ∃ steps : List (PairStepRecord vault),
        PairReplay vault (PairBoundary.ofState vault pre.state) steps
          (PairBoundary.ofState vault post.state) ∧
        ∀ r ∈ steps, r.provenance = provenance ∧
          ∀ call, r.own = some call →
            (Sevm.selector sevm = selector "deposit" [.uint256, .address] ∨
              Sevm.selector sevm = selector "mint" [.uint256, .address]) ∧
            call.visit = ⟨false, vault, sevm.caller.toB256, Devm.getStor pre wethAccount⟩

/-- The classifier at a committed exact vault `deposit`/`mint` frame root: the inbound
`transferFrom` visit it stages. -/
theorem pairVisit?_vaultFrame {vault : Adr} {d : Exec.Deriv}
    (commits : Execution.commits d.exn = true) (pcZero : d.pc = 0)
    (target : d.sevm.currentTarget = vault) (distinct : wethAccount ≠ vault)
    (direct : d.sevm.codeAddress = some vault)
    (code : some d.sevm.code.toList = Blanc.ProrataWethVault.vault.compile)
    (selected : Sevm.selector d.sevm = selector "deposit" [.uint256, .address] ∨
      Sevm.selector d.sevm = selector "mint" [.uint256, .address]) :
    d.pairVisit? vault =
      some ⟨false, vault, d.sevm.caller.toB256, Devm.getStor d.devm wethAccount⟩ := by
  have wethNe : d.sevm.currentTarget ≠ wethAccount := by
    rw [target]
    exact fun equal => distinct equal.symm
  unfold Exec.Deriv.pairVisit?
  rw [if_neg (fun h => wethNe h.2.2.1),
    if_pos ⟨commits, pcZero, target, direct, code, selected⟩]

/-- The classifier at a committed exact WETH frame root that is an allowance invocation's own
frame: that invocation's visit. -/
theorem pairVisit?_wethFrame {vault : Adr} {d : Exec.Deriv} (call : WethAllowanceInvocation)
    (commits : Execution.commits d.exn = true) (pcZero : d.pc = 0)
    (target : d.sevm.currentTarget = wethAccount)
    (direct : d.sevm.codeAddress = some wethAccount)
    (code : some d.sevm.code.toList = Blanc.weth.compile)
    (sevmEq : call.sevm = d.sevm) (preEq : call.pre = d.devm) :
    d.pairVisit? vault = some call.visit := by
  have selected := call.selected
  rw [sevmEq] at selected
  unfold Exec.Deriv.pairVisit?
  rw [if_pos ⟨commits, pcZero, target, direct, code⟩]
  cases approval : call.approval with
  | false =>
      rw [approval] at selected
      simp only [Bool.false_eq_true, ↓reduceIte] at selected
      have distinct : selector "transferFrom" [.address, .address, .uint256] ≠
          selector "approve" [.address, .uint256] := by decide +kernel
      have notApprove : Sevm.selector d.sevm ≠ selector "approve" [.address, .uint256] :=
        fun equal => distinct (selected.symm.trans equal)
      rw [if_neg notApprove, if_pos selected]
      simp only [WethAllowanceInvocation.visit, approval, sevmEq, preEq]
  | true =>
      rw [approval] at selected
      simp only [↓reduceIte] at selected
      rw [if_pos selected]
      simp only [WethAllowanceInvocation.visit, approval, sevmEq, preEq]

/-- A record witnessed among a foreign continuation's raw roots is witnessed among its raw
descendants: the continuation's own root classifies to nothing. -/
theorem PairStepRecord.OwnIn.of_foreignRoot {vault : Adr} {r : PairStepRecord vault}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} {run : Exec pc sevm pre out}
    {G : List Exec.Deriv}
    (vaultNe : sevm.currentTarget ≠ vault) (wethNe : sevm.currentTarget ≠ wethAccount)
    (sub : ∀ d ∈ Exec.rawFrameDescendants run, d ∈ G)
    (own : r.OwnIn vault (Exec.rawFrameRoots run)) : r.OwnIn vault G := by
  intro call owned
  obtain ⟨d, member, visit⟩ := own call owned
  simp only [Exec.rawFrameRoots, List.mem_cons] at member
  rcases member with rfl | member
  · rw [Exec.Deriv.pairVisit?_eq_none_of_foreign (vault := vault) wethNe vaultNe] at visit
    cases visit
  · exact ⟨d, sub d member, visit⟩

private theorem vault_pcFree' : Prog.pcFree Blanc.ProrataWethVault.vault = true := by
  decide +kernel

/-- The vault branch of every structural handler: a frame at the vault is at `pc = 0`, so the
whole run is one compiled vault run and the vault segment classifies it. -/
theorem Exec.CorePairReplay.vaultFrame {vault : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (vaultSeg : VaultFramePairSegment vault)
    (target : sevm.currentTarget = vault) :
    Exec.CorePairReplay vault pc sevm pre out := by
  intro run committed vaultAt _ inv vaultDirect _ blockIndex transactionIndex framePath _
  cases out with
  | error error => simp [Execution.commits] at committed
  | ok post =>
      obtain ⟨code, pcZero⟩ := vaultAt.2 target
      subst pcZero
      have compiled := Prog.runCompiled_of_exec sevm pre _ post vault_pcFree' run code
      obtain ⟨direct, callerNe⟩ := vaultDirect target
      rcases vaultSeg compiled target direct callerNe inv
          ⟨blockIndex, transactionIndex, framePath, some sevm.caller⟩ rfl with
        ⟨steps, replay, tagged⟩
      refine ⟨steps, replay, fun r member => ?_⟩
      obtain ⟨tag, owned⟩ := tagged r member
      refine ⟨⟨by rw [tag], by rw [tag], by rw [tag]⟩, fun call own => ?_⟩
      obtain ⟨selected, visit⟩ := owned call own
      refine ⟨⟨0, sevm, pre, .ok post, run⟩, Exec.mem_rawFrameRoots_self run, ?_⟩
      rw [visit]
      exact pairVisit?_vaultFrame committed rfl target inv.vault.config.distinct direct code selected

/-- **Segment hypothesis (WETH frame, every class but `withdraw`).**  A committed compiled WETH
run whose selector is not `withdraw(uint256)` — a view, `approve`, `deposit`, `transfer` or
`transferFrom` — entered by a caller that is neither the vault nor WETH is a provenance-tagged
replay between its own endpoints.  Its donation arm builds `FourQuoteShareEvidence.credit` in the
generalised shape, from `vaultKept` alone.  A record owns an invocation only over the frame's own
endpoints. -/
def WethFramePairSegment (vault : Adr) : Prop :=
  ∀ {sevm : Sevm} {pre post : Devm},
    Prog.RunCompiled sevm pre Blanc.weth post →
    sevm.currentTarget = wethAccount → sevm.codeAddress = some wethAccount →
    sevm.caller ≠ vault → sevm.caller ≠ wethAccount →
    Sevm.selector sevm ≠ selector "withdraw" [.uint256] →
    PairFrameInv vault sevm pre →
    ∀ provenance : Blanc.Prorata.ProrataAccountingProvenance,
      provenance.actor = some sevm.caller →
      ∃ steps : List (PairStepRecord vault),
        PairReplay vault (PairBoundary.ofState vault pre.state) steps
          (PairBoundary.ofState vault post.state) ∧
        ∀ r ∈ steps, r.provenance = provenance ∧
          ∀ call, r.own = some call → call.sevm = sevm ∧ call.pre = pre ∧ call.post = post

/-- The pre-call split of one committed WETH `withdraw`: the accepted payout `CALL` with its
retained callback trace, the exact storage written before it, and what the callback entry
inherits.  Nothing is said about the callback's own behaviour. -/
structure WethWithdrawSplit (sevm : Sevm) (pre post : Devm) where
  callPre : Devm
  callPost : Devm
  /-- The accepted value-bearing `CALL` to the caller, paying exactly `wad`. -/
  payout : Blanc.Prorata.AcceptedPayoutTrace sevm (Sevm.argWord sevm 0) callPre callPost
  /-- Before the `CALL`, WETH's storage moved in the caller's own row only. -/
  written : Devm.getStor callPre sevm.currentTarget =
    (Devm.getStor pre sevm.currentTarget).set sevm.caller.toB256
      (Devm.getStorVal pre sevm.currentTarget sevm.caller.toB256 - Sevm.argWord sevm 0)
  /-- Before the `CALL`, no other account's storage moved. -/
  foreignKept : ∀ account, sevm.currentTarget ≠ account →
    Devm.getStor callPre account = Devm.getStor pre account
  /-- The callback entry sees the frame-entry world's code. -/
  childCode : ∀ account,
    (initDevm (payout.childMsg.withBenv payout.entry)).getCode account = pre.getCode account
  /-- The callback inherits the block statics. -/
  childStat : (initSevm (payout.childMsg.withBenv payout.entry)).benvStat = sevm.benvStat
  /-- WETH's solvency precondition holds at the callback entry: the row was debited first. -/
  childWeth : wethSpec.Pre sevm.currentTarget
    (initSevm (payout.childMsg.withBenv payout.entry))
    (initDevm (payout.childMsg.withBenv payout.entry))
  /-- After the `CALL` returns, the suffix writes no storage. -/
  after : Devm.getStor post = Devm.getStor callPost

/-- The retained entered-call witnesses are named once so the locator can pin
the payout trace to the exact `Xlot` selected by the CALL step. -/
structure WethWithdrawCallFacts (sevm : Sevm) (callPre callPost : Devm) where
  xl : Xlot
  retained : ExecutionTrace.RetainedXlot xl
  (parent child : Devm)
  delegated : Bool
  nextAddress : Adr
  code : ByteArray
  (avail pc : Nat)
  step : Ninst.StepRun pc sevm callPre Ninst.call xl (.ok callPost)
  positive : 0 < sevm.depth
  stack : callPre.stack = 0 :: sevm.caller.toB256 :: Sevm.argWord sevm 0 ::
    0 :: 0 :: 0 :: 0 :: parent.stack
  parentState : parent.state = callPre.state
  parentMemory : parent.memory = callPre.memory.extends [(0, 0), (0, 0)]
  parentLogs : parent.logs = callPre.logs
  parentOutput : parent.output = callPre.output
  delegation :
    (getDelegatedCodeAddress (callPre.getCode sevm.caller.toB256.toAdr) = none ∧
      nextAddress = sevm.caller.toB256.toAdr ∧
      code = callPre.getCode sevm.caller.toB256.toAdr ∧ delegated = false) ∨
    (∃ d, getDelegatedCodeAddress (callPre.getCode sevm.caller.toB256.toAdr) = some d ∧
      nextAddress = d ∧ code = callPre.getCode d ∧ delegated = true)
  filled : Xlot.Filled xl
  processed : ProcessMessage
    (callMsg sevm parent
      (min (0 : Nat) (except64th avail) +
        (if (Sevm.argWord sevm 0).toNat = 0 then 0 else gCallStipend))
      (Sevm.argWord sevm 0) sevm.currentTarget sevm.caller.toB256.toAdr
      nextAddress true false ((callPre.memory.read 0 0).1) code delegated)
    xl (.ok child)
  clean : child.error.isSome = false
  resume : (Resume.call parent 0 0).run (.ok child) = .ok callPost
  postState : callPost.state = child.state
  postReturnData : callPost.returnData = child.output
  postMemory : callPost.memory = parent.memory.write 0 (child.output.take 0)
  postStack : callPost.stack = (1 : B256) :: parent.stack

/-- Build the split and also pin the constructed payout trace to the call's slot. -/
theorem WethWithdrawSplit.ofCallFacts_pinned {sevm : Sevm} {pre post : Devm}
    {callPre callPost : Devm}
    (target : sevm.currentTarget = wethAccount)
    (callerNe : sevm.caller ≠ wethAccount)
    (precondition : wethSpec.Pre wethAccount sevm pre)
    (written : Devm.getStor callPre sevm.currentTarget =
      (Devm.getStor pre sevm.currentTarget).set sevm.caller.toB256
        (Devm.getStorVal pre sevm.currentTarget sevm.caller.toB256 -
          Sevm.argWord sevm 0))
    (foreignKept : ∀ account, sevm.currentTarget ≠ account →
      Devm.getStor callPre account = Devm.getStor pre account)
    (facts : WethWithdrawCallFacts sevm callPre callPost)
    (callBal : Devm.getBal callPre = Devm.getBal pre)
    (callCode : Devm.getCode callPre = Devm.getCode pre)
    (solvent : wethSpec.Pre sevm.currentTarget sevm pre →
      Stor.Solvent (Devm.getStor callPre sevm.currentTarget) 0
        (Devm.getBal callPre sevm.currentTarget - Sevm.argWord sevm 0))
    (after : Devm.getStor post = Devm.getStor callPost)
    :
    ∃ split : WethWithdrawSplit sevm pre post,
      split.callPre = callPre ∧ split.callPost = callPost ∧
      split.payout.trace.slot = facts.xl ∧
      HEq split.payout.trace.retained facts.retained ∧
      HEq split.payout.trace.run facts.processed ∧
      HEq split.payout.trace
        (⟨facts.xl, facts.retained, facts.processed⟩ :
          ExecutionTrace.ProcessMessageTrace _ _) := by
  rcases facts with
    ⟨xl, retained, parent, child, delegated, nextAddress, code, avail, pc,
      step, positive, stack, parentState, parentMemory, parentLogs, parentOutput,
      delegation, filled, processed, clean, resume, callPostState,
      postReturnData, postMemory, postStack⟩
  let wad := Sevm.argWord sevm 0
  let childMsg :=
    callMsg sevm parent
      (min (0 : B256).toNat (except64th avail) +
        (if wad.toNat = 0 then 0 else gCallStipend))
      wad sevm.currentTarget sevm.caller.toB256.toAdr nextAddress true false
      ((callPre.memory.read (0 : B256).toNat (0 : B256).toNat).1) code delegated
  change ProcessMessage childMsg xl (.ok child) at processed
  have recipientNe : sevm.caller.toB256.toAdr ≠ sevm.currentTarget := by
    rw [toAdr_toB256, target]
    exact callerNe
  obtain ⟨settledRaw, frameBody, settled⟩ := ProcessMessage.iff_body.mp processed
  unfold FrameBody at frameBody
  rcases transfer : childMsg.benvAfterTransfer with error | entry <;>
    rw [transfer] at frameBody
  · rw [frameBody.2, processMessage.settle_error] at settled
    cases settled
  rcases of_benvAfterTransfer (rfl : childMsg.shouldTransferValue = true) transfer with
    ⟨debited, debit, entryEq⟩
  change parent.state.subBal sevm.currentTarget wad = some debited at debit
  rw [parentState] at debit
  have entryState : entry.state = debited.addBal sevm.caller.toB256.toAdr wad := by
    rw [entryEq]
    rfl
  have fields := of_state_transfer_fields (callee := sevm.caller.toB256.toAdr) debit
  let payout : Blanc.Prorata.AcceptedPayoutTrace sevm wad callPre callPost :=
    { childMsg := childMsg
      entry := entry
      child := child
      trace := ⟨xl, retained, processed⟩
      childClean := clean
      messageState := parentState
      shouldTransferValue := rfl
      caller := rfl
      value := rfl
      target := rfl
      targetNe := recipientNe
      depth := by
        change sevm.depth - 1 < sevm.depth
        omega
      entryTransfer := transfer
      entryStor := by
        rw [entryState]
        exact fields.1 sevm.currentTarget
      entryBalance := by
        rw [entryState]
        exact fields.2.2.2.2 recipientNe
      callPostState := callPostState }
  have atTarget : wethSpec.Pre sevm.currentTarget sevm pre := target ▸ precondition
  refine ⟨⟨callPre, callPost, payout, written, foreignKept, ?_, ?_, ?_, after⟩,
    rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro account
    change ((entry.state).get account).code = (pre.getAcct account).code
    rw [entryState, fields.2.1 account]
    exact congrFun callCode account
  · change entry.stat = sevm.benvStat
    rw [benvAfterTransfer_stat transfer]
    rfl
  · apply ContractSpec.Pre.child_of_outbound_transfer
      (st := callPre.state) (st_mid := debited)
      (target := sevm.caller.toB256.toAdr) (value := wad)
    · have entryCode := atTarget.code
      rw [← congrFun callCode sevm.currentTarget] at entryCode
      exact entryCode
    · have side := atTarget.side
      rw [← callBal] at side
      exact side
    · exact solvent atTarget
    · exact debit
    · exact entryState
    · rfl
    · rfl
  · change xl = xl
    rfl
  · exact HEq.rfl
  · exact HEq.rfl
  · exact HEq.rfl

/-- Build the accepted-payout split from the common facts at WETH's value-bearing
`CALL`.  Both the compiled source route and the retained execution-node route
use this constructor; their only differing work is obtaining `callFacts`. -/
theorem WethWithdrawSplit.ofCallFacts {sevm : Sevm} {pre post : Devm}
    {callPre callPost : Devm}
    (target : sevm.currentTarget = wethAccount)
    (callerNe : sevm.caller ≠ wethAccount)
    (precondition : wethSpec.Pre wethAccount sevm pre)
    (written : Devm.getStor callPre sevm.currentTarget =
      (Devm.getStor pre sevm.currentTarget).set sevm.caller.toB256
        (Devm.getStorVal pre sevm.currentTarget sevm.caller.toB256 -
          Sevm.argWord sevm 0))
    (foreignKept : ∀ account, sevm.currentTarget ≠ account →
      Devm.getStor callPre account = Devm.getStor pre account)
    (callFacts :
      ∃ (parent child : Devm) (xl : Xlot) (delegated : Bool) (nextAddress : Adr)
        (code : ByteArray) (avail pc : Nat),
        Ninst.StepRun pc sevm callPre Ninst.call xl (.ok callPost) ∧
        0 < sevm.depth ∧
        callPre.stack = 0 :: sevm.caller.toB256 :: Sevm.argWord sevm 0 ::
          0 :: 0 :: 0 :: 0 :: parent.stack ∧
        parent.state = callPre.state ∧
        parent.memory = callPre.memory.extends
          [(0, 0), (0, 0)] ∧
        parent.logs = callPre.logs ∧ parent.output = callPre.output ∧
        ((getDelegatedCodeAddress (callPre.getCode sevm.caller.toB256.toAdr) = none ∧
            nextAddress = sevm.caller.toB256.toAdr ∧ code = callPre.getCode sevm.caller.toB256.toAdr ∧
            delegated = false) ∨
          (∃ d, getDelegatedCodeAddress (callPre.getCode sevm.caller.toB256.toAdr) = some d ∧
            nextAddress = d ∧ code = callPre.getCode d ∧ delegated = true)) ∧
        Xlot.Filled xl ∧
        ProcessMessage
          (callMsg sevm parent
            (min (0 : Nat) (except64th avail) +
              (if (Sevm.argWord sevm 0).toNat = 0 then 0 else gCallStipend))
            (Sevm.argWord sevm 0) sevm.currentTarget sevm.caller.toB256.toAdr
            nextAddress true false
            ((callPre.memory.read 0 0).1) code delegated)
          xl (.ok child) ∧
        child.error.isSome = false ∧
        (Resume.call parent 0 0).run (.ok child) = .ok callPost ∧
        callPost.state = child.state ∧ callPost.returnData = child.output ∧
        callPost.memory = parent.memory.write 0 (child.output.take 0) ∧
        callPost.stack = (1 : B256) :: parent.stack)
    (callBal : Devm.getBal callPre = Devm.getBal pre)
    (callCode : Devm.getCode callPre = Devm.getCode pre)
    (solvent : wethSpec.Pre sevm.currentTarget sevm pre →
      Stor.Solvent (Devm.getStor callPre sevm.currentTarget) 0
        (Devm.getBal callPre sevm.currentTarget - Sevm.argWord sevm 0))
    (after : Devm.getStor post = Devm.getStor callPost)
    :
    Nonempty (WethWithdrawSplit sevm pre post) := by
  rcases callFacts with
    ⟨parent, child, xl, delegated, nextAddress, code, avail, pc, step,
      positive, stack, parentState, parentMemory, parentLogs, parentOutput,
      delegation, filled, processed, clean, resume, callPostState,
      postReturnData, postMemory, postStack⟩
  obtain ⟨retained⟩ := ExecutionTrace.exists_retainedXlot_of_filled filled
  let facts : WethWithdrawCallFacts sevm callPre callPost :=
    { xl := xl
      retained := retained
      parent := parent
      child := child
      delegated := delegated
      nextAddress := nextAddress
      code := code
      avail := avail
      pc := pc
      step := step
      positive := positive
      stack := stack
      parentState := parentState
      parentMemory := parentMemory
      parentLogs := parentLogs
      parentOutput := parentOutput
      delegation := delegation
      filled := filled
      processed := processed
      clean := clean
      resume := resume
      postState := callPostState
      postReturnData := postReturnData
      postMemory := postMemory
      postStack := postStack }
  obtain ⟨split, -, -, -, -, -⟩ :=
    WethWithdrawSplit.ofCallFacts_pinned target callerNe precondition written
      foreignKept facts callBal callCode solvent after
  exact ⟨split⟩

/-- **Segment hypothesis (WETH `withdraw`).**  Every committed compiled `withdraw` entered
freshly under WETH's precondition by a caller other than WETH splits at its accepted payout. -/
def WethWithdrawAcceptedPayout : Prop :=
  ∀ {sevm : Sevm} {pre post : Devm},
    Prog.RunCompiled sevm pre Blanc.weth post →
    sevm.currentTarget = wethAccount → sevm.codeAddress = some wethAccount →
    sevm.caller ≠ wethAccount →
    Sevm.selector sevm = selector "withdraw" [.uint256] →
    wethSpec.Pre wethAccount sevm pre →
    Exec.FreshEntry sevm pre →
    Nonempty (WethWithdrawSplit sevm pre post)

/-- **Segment hypothesis A8 (WETH `withdraw`, located).**  From the actual frame derivation, a
split whose retained callback is a raw subtree of that derivation. -/
def WethWithdrawAcceptedPayoutAt : Prop :=
  ∀ {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post)),
    some sevm.code.toList = Blanc.weth.compile →
    sevm.currentTarget = wethAccount → sevm.codeAddress = some wethAccount →
    sevm.caller ≠ wethAccount → Sevm.selector sevm = selector "withdraw" [.uint256] →
    wethSpec.Pre wethAccount sevm pre → Exec.FreshEntry sevm pre →
    ∃ split : WethWithdrawSplit sevm pre post,
      ∀ d ∈ split.payout.trace.rawFrames, d ∈ Exec.rawFrameRoots run

/-! ## The pair boundary as a settlement carrier -/

/-- Two storage equalities are one boundary equality. -/
theorem PairBoundary.ofState_eq {vault : Adr} {pre post : State}
    (vaultEq : post.getStor vault = pre.getStor vault)
    (wethEq : post.getStor wethAccount = pre.getStor wethAccount) :
    PairBoundary.ofState vault post = PairBoundary.ofState vault pre := by
  unfold PairBoundary.ofState
  rw [vaultEq, wethEq]

/-- Provenance admissible below a child path is admissible at the parent path. -/
theorem PairProvenanceOk.of_child {vault : Adr} {blockIndex : Nat}
    {transactionIndex : Option Nat} {framePath : List Nat} {child : Nat}
    {r : PairStepRecord vault}
    (ok : PairProvenanceOk blockIndex transactionIndex (framePath ++ [child]) r) :
    PairProvenanceOk blockIndex transactionIndex framePath r :=
  ⟨ok.block, ok.tx, (List.prefix_append framePath [child]).trans ok.path⟩

namespace PairReplayBetween

variable {vault : Adr} {blockIndex : Nat} {transactionIndex : Option Nat}
  {framePath : List Nat}

theorem nil_of_eq {pre post : PairBoundary} (eq : post = pre) :
    PairReplayBetween vault blockIndex transactionIndex framePath pre post :=
  ⟨[], PairReplay.nil_of_eq eq, by simp⟩

theorem append {pre mid post : PairBoundary}
    (first : PairReplayBetween vault blockIndex transactionIndex framePath pre mid)
    (second : PairReplayBetween vault blockIndex transactionIndex framePath mid post) :
    PairReplayBetween vault blockIndex transactionIndex framePath pre post := by
  obtain ⟨left, leftReplay, leftOk⟩ := first
  obtain ⟨right, rightReplay, rightOk⟩ := second
  refine ⟨left ++ right, leftReplay.append rightReplay, fun r member => ?_⟩
  rcases List.mem_append.mp member with inLeft | inRight
  · exact leftOk r inLeft
  · exact rightOk r inRight

theorem of_child {child : Nat} {pre post : PairBoundary}
    (replay : PairReplayBetween vault blockIndex transactionIndex (framePath ++ [child])
      pre post) :
    PairReplayBetween vault blockIndex transactionIndex framePath pre post := by
  obtain ⟨steps, stepsReplay, ok⟩ := replay
  exact ⟨steps, stepsReplay, fun r member => (ok r member).of_child⟩

theorem of_tagged {provenance : Blanc.Prorata.ProrataAccountingProvenance}
    {pre post : PairBoundary}
    (block : provenance.blockIndex = blockIndex)
    (tx : provenance.transactionIndex = transactionIndex)
    (path : provenance.framePath = framePath)
    (tagged : ∃ steps : List (PairStepRecord vault), PairReplay vault pre steps post ∧
      ∀ r ∈ steps, r.provenance = provenance) :
    PairReplayBetween vault blockIndex transactionIndex framePath pre post := by
  obtain ⟨steps, replay, tags⟩ := tagged
  refine ⟨steps, replay, fun r member => ?_⟩
  have tag := tags r member
  exact ⟨by rw [tag, block], by rw [tag, tx], by rw [tag, path]⟩

end PairReplayBetween

/-- The pair boundary presented to the contract-neutral settlement seams, at a record
admissibility `ok`.  Its boundary reads two accounts' storage and no balance, so it is a
`SettlementCarrier` and not an account-local `ReplayCarrier`: the whole-world silence law is what
it can discharge. -/
def pairCarrierWith (vault : Adr) (ok : PairStepRecord vault → Prop) :
    ExecutionAccountingReplay.SettlementCarrier wethAccount where
  Snap := PairBoundary
  Step := PairStepRecord vault
  Replay pre steps post := PairReplay vault pre steps post ∧ ∀ r ∈ steps, ok r
  ofState := PairBoundary.ofState vault
  frameEntry _ state := PairBoundary.ofState vault state
  nil boundary := ⟨.nil boundary, by simp⟩
  worldSilent := by
    intro _ _ storage_eq _
    exact PairBoundary.ofState_eq (congrFun storage_eq vault) (congrFun storage_eq wethAccount)
  entry_eq_ofState := by
    intro _ _ _ _ transfer _
    have storage := benvAfterTransfer_getStor_eq transfer
    exact PairBoundary.ofState_eq (congrFun storage vault) (congrFun storage wethAccount)

/-- The pair boundary presented to the contract-neutral settlement seams, at admissible
provenance. -/
def pairCarrier (vault : Adr) (blockIndex : Nat) (transactionIndex : Option Nat)
    (framePath : List Nat) : ExecutionAccountingReplay.SettlementCarrier wethAccount :=
  pairCarrierWith vault (PairProvenanceOk blockIndex transactionIndex framePath)

/-! ## Transport of the frame invariant across a foreign frame's steps

The vault half discharges the four foreign-frame obligations that
`vault_rely_preserves_conserved` discharges inline. -/

/-- A childless step of a frame foreign to the vault keeps the vault's frame invariant. -/
theorem VaultFrameInv.ninst_none {vault : Adr} {pc : Nat} {sevm : Sevm} {pre inter : Devm}
    {n : Ninst} (h_run : Ninst.StepRun pc sevm pre n .none (.ok inter))
    (h_ne : sevm.currentTarget ≠ vault) (inv : VaultFrameInv vault sevm pre) :
    VaultFrameInv vault sevm inter := by
  refine ⟨⟨?_, fun h => absurd h h_ne⟩,
    inv.config.of_codePreserve rfl
      (Ninst.stepRun_codePreserve (xl := .none) trivial h_run),
    inv.code⟩
  have hσ' := inv.preWf.pre
  cases n with
  | push xs le =>
    simp only [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at h_run
    rcases Except.bind_eq_ok h_run.2.symm with ⟨devm1, h_charge, h_push⟩
    exact hσ'.state_eq
      (((Devm.burn_of_chargeGas h_charge).state).trans
        ((Devm.push_of_push h_push).state)).symm
  | reg r =>
    have h_reg : Rinst.run ⟨pc, sevm, pre⟩ r = .ok inter := by
      simp only [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at h_run
      exact h_run.2.symm
    by_cases h_ss : r = Rinst.sstore
    · subst h_ss
      have h_frame := Rinst.sstore_run_stateWriteFrame pc pre sevm
      rw [h_reg] at h_frame
      refine ContractSpec.Pre.of_eqs hσ' (h_frame.getCode_eq vault).symm ?_
        (sstore_preserves_getStor_ne h_reg h_ne)
      funext b
      exact (h_frame.getBal_eq b).symm
    · exact ContractSpec.Pre.of_eqs hσ' (Rinst.preserves_getCode h_reg vault)
        (Rinst.preserves_bal h_reg).symm
        (congr_fun (Rinst.preserves_stor h_ss h_reg) vault).symm
  | exec x =>
    refine ContractSpec.Xinst.none_preserves_precond (x := x) ?_ h_ne hσ'
    simpa only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.Run]
      using h_run

/-- A spawning step of a frame foreign to the vault hands the vault's frame invariant to the
child, and gets it back once the child's outcome satisfies the vault postcondition. -/
theorem VaultFrameInv.xinst_some {vault : Adr} {pc : Nat} {sevm : Sevm} {pre inter : Devm}
    {x : Xinst} {evm' : Evm} {out' : Execution}
    (h_run : Ninst.StepRun pc sevm pre (.exec x) (.some ⟨evm', out'⟩) (.ok inter))
    (child : Exec evm'.pc evm'.sta evm'.dyna out')
    (h_ne : sevm.currentTarget ≠ vault) (inv : VaultFrameInv vault sevm pre) :
    VaultFrameInv vault evm'.sta evm'.dyna ∧
      (ifOk (Blanc.ProrataWethVault.vaultSpec.Post vault evm'.sta) out' →
        VaultFrameInv vault sevm inter) := by
  have hx : Xinst.Run sevm pre x (.some ⟨evm', out'⟩) (.ok inter) := by
    simpa only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.Run]
      using h_run
  obtain ⟨h_child, h_back⟩ :=
    ContractSpec.Xinst.some_preserves_precond (x := x) hx child h_ne inv.preWf.pre
  obtain ⟨f, rsm, hstep, henter, -⟩ := XStep.Run.some_inv hx
  have childCode : Devm.CodePreserve pre evm'.dyna := by
    intro a _
    rw [Frame.enter_run_getCode henter a]
    exact Xinst.step_spawn_getCode hstep a
  have childStat : evm'.sta.benvStat = sevm.benvStat := by
    rw [Frame.enter_run_benvStat henter]
    exact _root_.Blanc.Xinst.step_spawn_benvStat hstep
  have childOwnCode : evm'.sta.currentTarget = vault →
      some evm'.sta.code.toList = Prog.compile Blanc.ProrataWethVault.vault := by
    intro childTarget
    have targetEq := Frame.enter_run_currentTarget henter
    rw [Frame.enter_run_code henter]
    rw [childTarget] at targetEq
    rcases Xinst.step_spawn_source hstep with hempty | hsame | hsrc
    · rw [← targetEq] at hempty
      exact absurd hempty (not_empty_of_compile inv.preWf.pre.code)
    · rw [← targetEq] at hsame
      exact absurd hsame.symm h_ne
    · rw [← targetEq] at hsrc
      rw [hsrc (not_delegation_of_compile inv.preWf.pre.code)]
      exact inv.preWf.pre.code
  refine ⟨⟨⟨h_child, fun _ => Xinst.some_child_wf hx⟩,
    inv.config.of_codePreserve childStat childCode, childOwnCode⟩, ?_⟩
  intro h_if
  have wholeStep : Devm.CodePreserve pre inter :=
    Ninst.stepRun_codePreserve (xl := .some ⟨evm', out'⟩)
      (Exec.effect codePreserve_refl_trans.1 codePreserve_refl_trans.2
        Ninst.codePreserve_effectRec Jinst.codePreserve_effect
        Linst.codePreserve_effect child) h_run
  exact ⟨⟨h_back h_if, fun h => absurd h h_ne⟩,
    inv.config.of_codePreserve rfl wholeStep, inv.code⟩

/-- A jump of a frame foreign to the vault keeps the vault's frame invariant. -/
theorem VaultFrameInv.jinst {vault : Adr} {pc pc' : Nat} {sevm : Sevm} {pre inter : Devm}
    {j : Jinst} (h_run : Jinst.Run ⟨pc, sevm, pre⟩ j (.ok ⟨pc', inter⟩))
    (h_ne : sevm.currentTarget ≠ vault) (inv : VaultFrameInv vault sevm pre) :
    VaultFrameInv vault sevm inter := by
  have state := Jinst.preserves_state h_run
  refine ⟨⟨inv.preWf.pre.state_eq state, fun h => absurd h h_ne⟩,
    inv.config.of_codePreserve rfl ?_, inv.code⟩
  intro a _
  exact getCode_eq_of_state_eq state a

/-- Both installed programs at a frame that runs neither. -/
theorem PairFrameInv.programsAt {vault : Adr} {sevm : Sevm} {pre : Devm} (pc : Nat)
    (inv : PairFrameInv vault sevm pre)
    (vaultNe : sevm.currentTarget ≠ vault) (wethNe : sevm.currentTarget ≠ wethAccount) :
    Prog.At Blanc.ProrataWethVault.vault vault pc sevm pre ∧
      Prog.At Blanc.weth wethAccount pc sevm pre :=
  ⟨⟨inv.vault.preWf.pre.code, fun target => (vaultNe target).elim⟩,
    ⟨inv.weth.code, fun target => (wethNe target).elim⟩⟩

/-! ## The handlers -/

/-- A failed raw execution cannot satisfy the committed replay premise. -/
theorem Exec.CorePairReplay.error {vault : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm}
    {error : EvmError × Devm} :
    Exec.CorePairReplay vault pc sevm pre (.error error) := by
  intro _ committed
  simp [Execution.commits] at committed

/-- The continuation of a genuinely foreign frame, re-entered at the transported invariant. -/
private theorem Exec.CorePairReplay.resume {vault : Adr} {pc : Nat} {sevm : Sevm}
    {inter : Devm} {out : Execution}
    (ih : Exec.CorePairReplay vault pc sevm inter out)
    (next : Exec pc sevm inter out) (committed : Execution.commits out = true)
    (inv : PairFrameInv vault sevm inter)
    (vaultNe : sevm.currentTarget ≠ vault) (wethNe : sevm.currentTarget ≠ wethAccount)
    (blockIndex : Nat) (transactionIndex : Option Nat) (framePath : List Nat)
    (nextChild : Nat) :
    PairReplayWith vault
      (fun r => PairProvenanceOk blockIndex transactionIndex framePath r ∧
        PairStepRecord.OwnIn vault (Exec.rawFrameRoots next) r)
      (PairBoundary.ofState vault inter.state)
      (PairBoundary.ofState vault (Execution.committedPost out committed).state) :=
  ih next committed (inv.programsAt pc vaultNe wethNe).1 (inv.programsAt pc vaultNe wethNe).2
    inv (fun target => (vaultNe target).elim) (fun target => (wethNe target).elim)
    blockIndex transactionIndex framePath nextChild

/-- A childless step of a genuinely foreign frame moves neither storage. -/
theorem Exec.CorePairReplay.nextNone {vault : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm}
    {n : Ninst} {inter : Devm} {out : Execution}
    (vaultSeg : VaultFramePairSegment vault)
    (hat : Ninst.At sevm.code pc n)
    (step : Ninst.StepRun pc sevm pre n .none (.ok inter))
    (next : Exec (pc + n.size) sevm inter out)
    (wethNe : sevm.currentTarget ≠ wethAccount)
    (ih : Exec.CorePairReplay vault (pc + n.size) sevm inter out) :
    Exec.CorePairReplay vault pc sevm pre out := by
  by_cases vaultEq : sevm.currentTarget = vault
  · exact Exec.CorePairReplay.vaultFrame vaultSeg vaultEq
  intro run committed _ _ inv _ _ blockIndex transactionIndex framePath nextChild
  cases out with
  | error error => simp [Execution.commits] at committed
  | ok post =>
  have sub : ∀ d ∈ Exec.rawFrameDescendants next, d ∈ Exec.rawFrameRoots run :=
    fun d member => List.mem_cons.mpr
      (Or.inr (Exec.rawFrameDescendants_sub_of_stepNone hat step next run d member))
  refine PairReplayWith.mono
    (ok := fun r => PairProvenanceOk blockIndex transactionIndex framePath r ∧
      PairStepRecord.OwnIn vault (Exec.rawFrameRoots next) r)
    (fun r h => ⟨h.1, h.2.of_foreignRoot vaultEq wethNe sub⟩) ?_
  have interInv : PairFrameInv vault sevm inter :=
    ⟨inv.vault.ninst_none step vaultEq,
      _root_.Blanc.ContractSpec.Ninst.none_preserves_precond (c := wethSpec) step wethNe
        inv.weth,
      fun target => (wethNe target).elim⟩
  have boundary : PairBoundary.ofState vault inter.state =
      PairBoundary.ofState vault pre.state :=
    PairBoundary.ofState_eq (_root_.Blanc.Ninst.foreignNone_getStor_eq step vaultEq)
      (_root_.Blanc.Ninst.foreignNone_getStor_eq step wethNe)
  rw [← boundary]
  cases stepShape : Ninst.step ⟨pc, sevm, pre⟩ n with
  | halt execution =>
      simp only [Ninst.StepRun, stepShape, Step.Run] at step
      rcases step with ⟨_, impossible⟩
      cases impossible
      exact False.elim (Ninst.step_ne_halt_ok stepShape)
  | cont pc' actual =>
      exact ih.resume next committed interInv vaultEq wethNe
        blockIndex transactionIndex framePath nextChild
  | spawn frame resume pc' =>
      exact ih.resume next committed interInv vaultEq wethNe
        blockIndex transactionIndex framePath (nextChild + 1)

/-- A terminal instruction of a genuinely foreign frame moves no storage at all. -/
theorem Exec.CorePairReplay.last {vault : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm}
    {l : Linst} {out : Execution}
    (vaultSeg : VaultFramePairSegment vault)
    (step : Linst.Run sevm pre l out)
    (_wethNe : sevm.currentTarget ≠ wethAccount) :
    Exec.CorePairReplay vault pc sevm pre out := by
  by_cases vaultEq : sevm.currentTarget = vault
  · exact Exec.CorePairReplay.vaultFrame vaultSeg vaultEq
  intro _ committed _ _ _ _ _ blockIndex transactionIndex framePath _
  cases out with
  | error error => simp [Execution.commits] at committed
  | ok post =>
      have storage := _root_.Blanc.Linst.getStor_eq step
      exact PairReplayWith.nil_of_eq
        (PairBoundary.ofState_eq (congrFun storage vault) (congrFun storage wethAccount))

/-- A jump is world-state silent. -/
theorem Exec.CorePairReplay.jump {vault : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm}
    {j : Jinst} {pc' : Nat} {inter : Devm} {out : Execution}
    (vaultSeg : VaultFramePairSegment vault)
    (hat : Jinst.At sevm.code pc j)
    (step : Jinst.Run ⟨pc, sevm, pre⟩ j (.ok ⟨pc', inter⟩))
    (next : Exec pc' sevm inter out)
    (wethNe : sevm.currentTarget ≠ wethAccount)
    (ih : Exec.CorePairReplay vault pc' sevm inter out) :
    Exec.CorePairReplay vault pc sevm pre out := by
  by_cases vaultEq : sevm.currentTarget = vault
  · exact Exec.CorePairReplay.vaultFrame vaultSeg vaultEq
  intro run committed _ _ inv _ _ blockIndex transactionIndex framePath nextChild
  cases out with
  | error error => simp [Execution.commits] at committed
  | ok post =>
  have sub : ∀ d ∈ Exec.rawFrameDescendants next, d ∈ Exec.rawFrameRoots run :=
    fun d member => List.mem_cons.mpr
      (Or.inr (Exec.rawFrameDescendants_sub_of_jump hat step next run d member))
  refine PairReplayWith.mono
    (ok := fun r => PairProvenanceOk blockIndex transactionIndex framePath r ∧
      PairStepRecord.OwnIn vault (Exec.rawFrameRoots next) r)
    (fun r h => ⟨h.1, h.2.of_foreignRoot vaultEq wethNe sub⟩) ?_
  have stateEq : inter.state = pre.state := Jinst.preserves_state step
  have interInv : PairFrameInv vault sevm inter :=
    ⟨inv.vault.jinst step vaultEq, inv.weth.state_eq stateEq,
      fun target => (wethNe target).elim⟩
  rw [← stateEq]
  exact ih.resume next committed interInv vaultEq wethNe
    blockIndex transactionIndex framePath nextChild


/-- A filled child of a genuinely foreign frame is replayed at its own child path, transported
through complete CALL/CREATE settlement by the contract-neutral seam, and followed by the
parent's continuation at the next sibling ordinal.  Both halves of the frame invariant are handed
to the child and recovered from its outcome by the two standing preservation theorems. -/
theorem Exec.CorePairReplay.nextSome {vault : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm}
    {n : Ninst} {cevm : Evm} {raw : Execution} {inter : Devm} {out : Execution}
    (vaultSeg : VaultFramePairSegment vault)
    (hat : Ninst.At sevm.code pc n)
    (step : Ninst.StepRun pc sevm pre n (.some ⟨cevm, raw⟩) (.ok inter))
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (next : Exec (pc + n.size) sevm inter out)
    (wethNe : sevm.currentTarget ≠ wethAccount)
    (ihChild : Exec.CorePairReplay vault cevm.pc cevm.sta cevm.dyna raw)
    (ihNext : Exec.CorePairReplay vault (pc + n.size) sevm inter out) :
    Exec.CorePairReplay vault pc sevm pre out := by
  by_cases vaultEq : sevm.currentTarget = vault
  · exact Exec.CorePairReplay.vaultFrame vaultSeg vaultEq
  cases n with
  | reg r =>
      simp [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at step
  | push xs length =>
      simp [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at step
  | exec x =>
      intro run committed vaultAt wethAt inv _ _
        blockIndex transactionIndex framePath nextChild
      cases out with
      | error error => simp [Execution.commits] at committed
      | ok post =>
      obtain ⟨childSub, nextSub⟩ :=
        Exec.rawFrameDescendants_sub_of_stepSome hat step child next run
      have xrun : Xinst.Run sevm pre x (.some ⟨cevm, raw⟩) (.ok inter) := by
        simpa only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep,
          Xinst.Run] using step
      have hxrun := XStep.run_toStep.mp step
      cases spawnEq : Xinst.step sevm pre x with
      | done execution =>
          simp [spawnEq, XStep.Run] at hxrun
      | spawn frame resume =>
          simp only [spawnEq, XStep.Run] at hxrun
          obtain ⟨result, frameRun, resumeRun⟩ := hxrun
          cases result with
          | error error =>
              cases resume <;>
                simp [Resume.run, liftToExecution] at resumeRun
          | ok settled =>
              have enter := (RunFrame.some_inv frameRun).1
              have evmStep : Evm.step ⟨pc, sevm, pre⟩ =
                  .spawn frame resume (pc + 1) := by
                rw [Evm.step_next hat]
                simp only [Ninst.step_exec, spawnEq, XStep.toStep]
              obtain ⟨childPcZero, childGetCode, childCodeSource⟩ :=
                Evm.step_spawn_child evmStep enter
              -- the child runs an installed program's own code whenever it is aimed at one
              have childAtOf : ∀ {p : Prog} {ca : Adr},
                  some (pre.getCode ca).toList = Prog.compile p →
                  sevm.currentTarget ≠ ca →
                  Prog.At p ca cevm.pc cevm.sta cevm.dyna := by
                intro p ca installed targetNe
                refine ⟨?_, fun childTarget => ⟨?_, childPcZero⟩⟩
                · rw [childGetCode ca]
                  exact installed
                · have parentTargetNe :
                      sevm.currentTarget ≠ cevm.sta.currentTarget := by
                    rw [childTarget]
                    exact targetNe
                  have codeEq := childCodeSource parentTargetNe
                    (by rw [childTarget]
                        exact not_empty_of_compile installed)
                    (by rw [childTarget]
                        exact not_delegation_of_compile installed)
                  rw [codeEq, childTarget]
                  exact installed
              have childVaultAt := childAtOf vaultAt.1 vaultEq
              have childWethAt := childAtOf wethAt.1 wethNe
              rcases Frame.enter_run_inv enter with
                ⟨entry, transfer, childEvmEq⟩
              have childCallerEq : cevm.sta.caller = frame.inner.caller := by
                have eq := congrArg (fun evm : Evm => evm.sta.caller) childEvmEq
                dsimp [initEvm, initSevm, Msg.withBenv] at eq
                exact eq
              -- a child aimed at an installed account is a direct call
              have childDirectOf : ∀ {p : Prog} {ca : Adr},
                  some (pre.getCode ca).toList = Prog.compile p →
                  sevm.currentTarget ≠ ca →
                  cevm.sta.currentTarget = ca →
                  cevm.sta.codeAddress = some ca := by
                intro p ca installed targetNe childTarget
                have innerTarget : frame.inner.currentTarget = ca := by
                  rw [← Frame.enter_run_currentTarget enter]
                  exact childTarget
                have parentTargetNe :
                    sevm.currentTarget ≠ frame.inner.currentTarget := by
                  rw [innerTarget]
                  exact targetNe
                have targetCodeNonempty :
                    pre.getCode frame.inner.currentTarget ≠ .empty := by
                  rw [innerTarget]
                  exact not_empty_of_compile installed
                have codeAddress :=
                  _root_.Blanc.Xinst.step_spawn_codeAddress_eq_currentTarget
                    spawnEq parentTargetNe targetCodeNonempty
                    (by rw [innerTarget]
                        dsimp only [getDelegatedCodeAddress]
                        rw [if_neg (not_delegation_of_compile installed)])
                have childCodeAddress :=
                  congrArg (fun evm : Evm => evm.sta.codeAddress) childEvmEq
                dsimp [initEvm, initSevm, Msg.withBenv] at childCodeAddress
                rw [childCodeAddress, codeAddress, innerTarget]
              have innerTargetOf : ∀ {ca : Adr}, cevm.sta.currentTarget = ca →
                  frame.inner.currentTarget = ca := by
                intro ca childTarget
                rw [← Frame.enter_run_currentTarget enter]
                exact childTarget
              have childVaultFacts : cevm.sta.currentTarget = vault →
                  cevm.sta.codeAddress = some vault ∧ cevm.sta.caller ≠ vault := by
                intro childTarget
                refine ⟨childDirectOf vaultAt.1 vaultEq childTarget, ?_⟩
                rw [childCallerEq]
                exact _root_.Blanc.Xinst.step_spawn_caller_ne_of_target_eq
                  spawnEq vaultEq (innerTargetOf childTarget)
              have childWethFacts : cevm.sta.currentTarget = wethAccount →
                  cevm.sta.codeAddress = some wethAccount ∧
                    cevm.sta.caller ≠ vault ∧ cevm.sta.caller ≠ wethAccount := by
                intro childTarget
                refine ⟨childDirectOf wethAt.1 wethNe childTarget, ?_, ?_⟩
                · rw [childCallerEq]
                  rcases _root_.Blanc.Xinst.step_spawn_caller_eq_parent_or_target_eq_parent
                      spawnEq with callerEq | targetEq
                  · rw [callerEq]
                    exact vaultEq
                  · exact (wethNe
                      (targetEq.symm.trans (innerTargetOf childTarget))).elim
                · rw [childCallerEq]
                  exact _root_.Blanc.Xinst.step_spawn_caller_ne_of_target_eq
                    spawnEq wethNe (innerTargetOf childTarget)
              -- σ: handed to the child, recovered from its outcome
              obtain ⟨childVaultInv, vaultOfPost⟩ :=
                inv.vault.xinst_some step child vaultEq
              obtain ⟨childWethPre, wethOfPost⟩ :=
                _root_.Blanc.ContractSpec.Xinst.some_preserves_precond
                  (c := wethSpec) xrun child wethNe inv.weth
              have childInv : PairFrameInv vault cevm.sta cevm.dyna :=
                ⟨childVaultInv, childWethPre, fun _ => Frame.enter_run_fresh enter⟩
              have childVaultPost :
                  ifOk (Blanc.ProrataWethVault.vaultSpec.Post vault cevm.sta) raw := by
                cases raw with
                | error error => trivial
                | ok rawPost =>
                    exact vault_rely_preserves_conserved vault cevm.pc cevm.sta
                      cevm.dyna rawPost child childVaultAt childVaultInv
              have childWethPost : ifOk (wethSpec.Post wethAccount cevm.sta) raw := by
                cases raw with
                | error error => trivial
                | ok rawPost =>
                    have childAtZero :
                        Exec 0 cevm.sta cevm.dyna (.ok rawPost) := by
                      rw [← childPcZero]
                      exact child
                    exact wethSpec_preservesNoMem wethAccount cevm.sta cevm.dyna
                      rawPost childAtZero
                      (fun childTarget => (childWethAt.2 childTarget).1)
                      childWethPre
              have interInv : PairFrameInv vault sevm inter :=
                ⟨vaultOfPost childVaultPost, wethOfPost childWethPost,
                  fun target => (wethNe target).elim⟩
              have sumNof : sum pre.state.bal < 2 ^ 256 := inv.weth.side
              let okParent : PairStepRecord vault → Prop := fun r =>
                PairProvenanceOk blockIndex transactionIndex framePath r ∧
                  PairStepRecord.OwnIn vault (Exec.rawFrameRoots run) r
              have childBody :
                  ∀ childCommitted : Execution.commits raw = true,
                    PairReplayWith vault okParent
                      (PairBoundary.ofState vault cevm.dyna.state)
                      (PairBoundary.ofState vault
                        (Execution.committedPost raw childCommitted).state) := by
                intro childCommitted
                exact (ihChild child childCommitted childVaultAt childWethAt childInv
                  childVaultFacts childWethFacts blockIndex transactionIndex
                  (framePath ++ [nextChild]) 0).mono fun r h =>
                    ⟨h.1.of_child, h.2.mono fun d member =>
                      List.mem_cons.mpr (Or.inr (childSub d member))⟩
              have headReplay :
                  PairReplayWith vault okParent
                    (PairBoundary.ofState vault pre.state)
                    (PairBoundary.ofState vault inter.state) :=
                (pairCarrierWith vault okParent).xinstForeignSome
                  spawnEq frameRun resumeRun.symm wethNe sumNof childBody
              exact headReplay.append
                ((ihNext.resume next committed interInv vaultEq wethNe
                  blockIndex transactionIndex framePath (nextChild + 1)).mono fun r h =>
                    ⟨h.1, h.2.of_foreignRoot vaultEq wethNe fun d member =>
                      List.mem_cons.mpr (Or.inr (nextSub d member))⟩)

/-- The record a committed `withdraw` prefix emits: from frame entry to the callback's
post-transfer entry, WETH's storage moved in the caller's row alone. -/
private def withdrawPrefixRecord {vault : Adr} (before after : State) (caller : Adr)
    (provenance : Blanc.Prorata.ProrataAccountingProvenance)
    (actor : provenance.actor = some caller)
    (vaultKept : after.getStor vault = before.getStor vault)
    (rowKept : Stor.rest (after.getStor wethAccount) vault =
      Stor.rest (before.getStor wethAccount) vault)
    (quiet : ∀ key, ¬ ValidAdr key →
      (after.getStor wethAccount).get key = (before.getStor wethAccount).get key) :
    PairStepRecord vault where
  before := before
  after := after
  step := .silent caller vaultKept rowKept
  own := none
  linked := fun _ impossible => by cases impossible
  quiet := fun _ => quiet
  debitOwn := fun _ _ _ _ _ _ impossible => by cases impossible
  provenance := provenance
  actor := actor

/-- The compiled WETH frame handler.  Every class but `withdraw` closes in the WETH segment; a
`withdraw` emits its prefix record, recurses through `deeper` into the exact retained callback —
always a frame foreign to both accounts, located among the frame's own raw roots — and contributes
nothing after it. -/
theorem Exec.CorePairReplay.atTarget {vault : Adr} {sevm : Sevm} {pre post : Devm}
    (wethSeg : WethFramePairSegment vault)
    (withdrawAt : WethWithdrawAcceptedPayoutAt)
    (target : sevm.currentTarget = wethAccount)
    (deeper : ForallDeeperAt sevm.depth wethAccount Blanc.weth
      (fun pc childSevm childPre childOut _ =>
        Exec.CorePairReplay vault pc childSevm childPre childOut)) :
    Exec.CorePairReplay vault 0 sevm pre (.ok post) := by
  intro run committed _ wethAt inv _ wethFacts
    blockIndex transactionIndex framePath nextChild
  obtain ⟨direct, callerNotVault, callerNotWeth⟩ := wethFacts target
  have compiled : Prog.RunCompiled sevm pre Blanc.weth post :=
    Prog.runCompiled_of_exec sevm pre Blanc.weth post weth_pcFree run
      (wethAt.2 target).1
  let provenance : Blanc.Prorata.ProrataAccountingProvenance :=
    { blockIndex := blockIndex
      transactionIndex := transactionIndex
      framePath := framePath
      actor := some sevm.caller }
  by_cases selected : Sevm.selector sevm = selector "withdraw" [.uint256]
  · obtain ⟨split, located⟩ := withdrawAt run (wethAt.2 target).1 target direct callerNotWeth
      selected inv.weth (inv.wethFresh target)
    have distinct : wethAccount ≠ vault := inv.vault.config.distinct
    -- the callback is aimed at the caller, which is neither account
    have childTargetEq :
        (initSevm (split.payout.childMsg.withBenv split.payout.entry)).currentTarget =
          sevm.caller := by
      show split.payout.childMsg.currentTarget = sevm.caller
      rw [split.payout.target, toAdr_toB256]
    have entryStorage : split.payout.entry.state.getStor = split.callPre.state.getStor := by
      rw [benvAfterTransfer_getStor_eq split.payout.entryTransfer,
        split.payout.messageState]
    -- the prefix record
    have vaultKept : split.payout.entry.state.getStor vault = pre.state.getStor vault := by
      rw [entryStorage]
      exact split.foreignKept vault (by rw [target]; exact distinct)
    have written : split.payout.entry.state.getStor wethAccount =
        (pre.state.getStor wethAccount).set sevm.caller.toB256
          (Devm.getStorVal pre wethAccount sevm.caller.toB256 - Sevm.argWord sevm 0) := by
      rw [entryStorage]
      have := split.written
      rw [target] at this
      exact this
    have callerKeyNe : ∀ {key : B256}, key ≠ sevm.caller.toB256 →
        (split.payout.entry.state.getStor wethAccount).get key =
          (pre.state.getStor wethAccount).get key := by
      intro key different
      rw [written, Stor.get_set_ne _ different.symm]
    have rowKept : Stor.rest (split.payout.entry.state.getStor wethAccount) vault =
        Stor.rest (pre.state.getStor wethAccount) vault := by
      simp only [Stor.rest, Function.comp_apply]
      apply callerKeyNe
      intro equal
      exact callerNotVault (by rw [← toAdr_toB256 sevm.caller, ← equal, toAdr_toB256])
    have quiet : ∀ key, ¬ ValidAdr key →
        (split.payout.entry.state.getStor wethAccount).get key =
          (pre.state.getStor wethAccount).get key := by
      intro key invalid
      apply callerKeyNe
      intro equal
      exact invalid ⟨sevm.caller, equal.symm⟩
    let record : PairStepRecord vault :=
      withdrawPrefixRecord pre.state split.payout.entry.state sevm.caller provenance rfl
        vaultKept rowKept quiet
    have headReplay : PairReplayWith vault
        (fun r => PairProvenanceOk blockIndex transactionIndex framePath r ∧
          PairStepRecord.OwnIn vault (Exec.rawFrameRoots run) r)
        (PairBoundary.ofState vault pre.state)
        (PairBoundary.ofState vault split.payout.entry.state) :=
      ⟨[record], PairReplay.singleton record, by
        intro r member
        rw [List.mem_singleton.mp member]
        exact And.intro ⟨rfl, rfl, List.prefix_refl _⟩ (fun _ impossible => by cases impossible)⟩
    -- nothing after the callback
    have postBoundary : PairBoundary.ofState vault post.state =
        PairBoundary.ofState vault split.payout.child.state := by
      have storage : post.state.getStor = split.payout.child.state.getStor := by
        rw [← split.payout.callPostState]
        exact split.after
      exact PairBoundary.ofState_eq (congrFun storage vault) (congrFun storage wethAccount)
    show PairReplayWith vault
      (fun r => PairProvenanceOk blockIndex transactionIndex framePath r ∧
        PairStepRecord.OwnIn vault (Exec.rawFrameRoots run) r)
      (PairBoundary.ofState vault pre.state) (PairBoundary.ofState vault post.state)
    rw [postBoundary]
    refine headReplay.append ?_
    -- the callback subtree
    generalize split.payout.trace = trace at located
    rcases trace with ⟨slot, retained, process⟩
    cases retained with
    | none =>
        have childState :=
          _root_.Blanc.ProcessMessage.none_ok_state_eq_entry_of_clean
            process split.payout.entryTransfer split.payout.childClean
        exact PairReplayWith.nil_of_eq
          (congrArg (PairBoundary.ofState vault) childState)
    | @some childPc childSevm childPre childOut childRun =>
        have settles :=
          _root_.Blanc.ProcessMessage.settlementCommits_of_some_ok_clean
            process split.payout.childClean
        have childCommitted := Frame.raw_commits_of_settlementCommits settles
        have enter := (RunFrame.some_inv process).1
        rcases Frame.enter_run_inv enter with ⟨entry, transfer, childEvmEq⟩
        simp only [Frame.ofCall] at transfer childEvmEq
        have entryEq : entry = split.payout.entry :=
          Except.ok.inj (transfer.symm.trans split.payout.entryTransfer)
        subst entry
        have childSevmEq : childSevm =
            initSevm (split.payout.childMsg.withBenv split.payout.entry) :=
          congrArg (fun evm : Evm => evm.sta) childEvmEq
        have childPreEq : childPre =
            initDevm (split.payout.childMsg.withBenv split.payout.entry) :=
          congrArg (fun evm : Evm => evm.dyna) childEvmEq
        have childTarget : childSevm.currentTarget = sevm.caller := by
          rw [childSevmEq]
          exact childTargetEq
        have childNotVault : childSevm.currentTarget ≠ vault := by
          rw [childTarget]
          exact callerNotVault
        have childNotWeth : childSevm.currentTarget ≠ wethAccount := by
          rw [childTarget]
          exact callerNotWeth
        have childWeth : wethSpec.Pre wethAccount childSevm childPre := by
          rw [childSevmEq, childPreEq, ← target]
          exact split.childWeth
        have childVaultStorage :
            Devm.getStor childPre vault = Devm.getStor pre vault := by
          rw [childPreEq]
          exact vaultKept
        have childVaultPre :
            Blanc.ProrataWethVault.vaultSpec.Pre vault childSevm childPre := by
          refine ⟨?_, trivial, ?_⟩
          · rw [childPreEq, split.childCode vault]
            exact inv.vault.preWf.pre.code
          · exact (ContractSpec.ofStorageOnly_preInv_iff).mpr (by
              rw [childVaultStorage]
              exact (ContractSpec.ofStorageOnly_preInv_iff).mp inv.vault.preWf.pre.inv)
        have childInv : PairFrameInv vault childSevm childPre :=
          ⟨⟨⟨childVaultPre, fun atVault => (childNotVault atVault).elim⟩,
              ⟨distinct, by
                rw [childSevmEq, split.childStat]
                exact inv.vault.config.nonprecompile, by
                rw [childPreEq, split.childCode wethAccount]
                exact inv.vault.config.code⟩,
              fun atVault => (childNotVault atVault).elim⟩,
            childWeth, fun atWeth => (childNotWeth atWeth).elim⟩
        have childAts := childInv.programsAt childPc childNotVault childNotWeth
        have childDepth : childSevm.depth < sevm.depth := by
          rw [childSevmEq]
          exact split.payout.depth
        have childCore : Exec.CorePairReplay vault childPc childSevm childPre childOut :=
          deeper childPc childSevm childPre childOut childRun childDepth childAts.2
        have childReplay := (childCore childRun childCommitted childAts.1 childAts.2
          childInv (fun atVault => (childNotVault atVault).elim)
          (fun atWeth => (childNotWeth atWeth).elim)
          blockIndex transactionIndex (framePath ++ [nextChild]) 0).mono
            (ok' := fun r => PairProvenanceOk blockIndex transactionIndex framePath r ∧
              PairStepRecord.OwnIn vault (Exec.rawFrameRoots run) r)
            fun r h => ⟨h.1.of_child, h.2.mono fun d member => located d member⟩
        have startEq : childPre.state = split.payout.entry.state := by
          rw [childPreEq]
          rfl
        have childPost :=
          _root_.Blanc.ProcessMessage.ok_state_eq_committedPost process childCommitted
        rw [← startEq, childPost]
        exact childReplay
  · obtain ⟨steps, replay, tagged⟩ :=
      wethSeg compiled target direct callerNotVault callerNotWeth selected inv provenance rfl
    refine ⟨steps, replay, fun r member => ?_⟩
    obtain ⟨tag, owned⟩ := tagged r member
    refine ⟨⟨by rw [tag], by rw [tag], by rw [tag]⟩, fun call own => ?_⟩
    obtain ⟨sevmEq, preEq, -⟩ := owned call own
    exact ⟨⟨0, sevm, pre, .ok post, run⟩, Exec.mem_rawFrameRoots_self run,
      pairVisit?_wethFrame call committed rfl target direct (wethAt.2 target).1 sevmEq preEq⟩

/-- **The pair core, from its three segments.**  The complete interpreter recursion for
committed pair replay, by the single-target eliminator at `(wethAccount, Blanc.weth)`: a WETH
frame is discharged by the compiled-frame handler, a vault frame is consumed whole at `pc = 0`
inside every structural handler, and a genuinely foreign frame composes the replay. -/
theorem Exec.corePairReplay_of_segments {vault : Adr}
    (vaultSeg : VaultFramePairSegment vault)
    (wethSeg : WethFramePairSegment vault)
    (withdrawAt : WethWithdrawAcceptedPayoutAt) :
    Exec.Fa (Exec.Wkn wethAccount Blanc.weth
      (fun pc sevm pre out _ => Exec.CorePairReplay vault pc sevm pre out)) := by
  apply lift_core
    (ε := fun pc sevm pre out => Exec.CorePairReplay vault pc sevm pre out)
    (π := fun sevm pre post => Exec.CorePairReplay vault 0 sevm pre (.ok post))
    (analog := fun h => h)
    (ca := wethAccount) (p := Blanc.weth)
  · intro sevm pre post _ target deeper
    exact Exec.CorePairReplay.atTarget wethSeg withdrawAt target deeper
  · intro pc sevm pre error post target
    exact Exec.CorePairReplay.error
  · intro pc sevm pre noneAt targetNe
    exact Exec.CorePairReplay.error
  · intro pc sevm pre n error post hat step targetNe
    exact Exec.CorePairReplay.error
  · intro pc sevm pre n childEvm childOut error post hat step child targetNe ihChild
    exact Exec.CorePairReplay.error
  · intro pc sevm pre n inter out hat step next targetNe ihNext
    exact Exec.CorePairReplay.nextNone vaultSeg hat step next targetNe ihNext
  · intro pc sevm pre n childEvm childOut inter out hat step child next targetNe
      ihChild ihNext
    exact Exec.CorePairReplay.nextSome vaultSeg hat step child next targetNe
      ihChild ihNext
  · intro pc sevm pre j error post hat step targetNe
    exact Exec.CorePairReplay.error
  · intro pc sevm pre j pc' inter out hat step next targetNe ihNext
    exact Exec.CorePairReplay.jump vaultSeg hat step next targetNe ihNext
  · intro pc sevm pre l out hat step targetNe
    exact Exec.CorePairReplay.last vaultSeg step targetNe

end Blanc.Composition.ProrataWethVault
