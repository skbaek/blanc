import Blanc.Lift.WithdrawalRequest.WordFifo
import Blanc.Lift.WithdrawalRequest.HistoryFifo
import Blanc.Lift.WithdrawalRequest.WordDelivery
import Blanc.Composition.WithdrawalRequestDrainControl
import Blanc.Lift.WithdrawalRequest.SystemHistory
import Blanc.Lift.WithdrawalRequest.ExactFeeDomain
import Blanc.Composition.WithdrawalRequestFeeRefutation
import Blanc.Lift.WithdrawalRequest.NatLiveness
import Blanc.Lift.WithdrawalRequest.Creation.Deploy
import Blanc.Lift.WithdrawalRequest.HeadlineFee
import Blanc.Lift.WithdrawalRequest.HeadlineSystem
import Blanc.Lift.WithdrawalRequest.HeadlineHistory
import Blanc.Lift.WithdrawalRequest.FifoDrainControl
import Blanc.Composition.WithdrawalRequestFeeHeadline
import Blanc.Composition.ConsolidationRequestPublicHeadlines
import Blanc.Composition.ConsolidationRequestPublicHistory
import Blanc.Lift.BeaconDeposit.BeaconEnv
import Blanc.Lift.BeaconDeposit.Creation.Deploy
import Blanc.Lift.BeaconDeposit.HistDeployment
-- `open private` below; no longer reached transitively under mathlib 4.35.
import Batteries.Tactic.OpenPrivate

/-!
Statement pins for the paper-v2 contract families and shared execution machinery.
Each
wrapper has the exact intended type and uses the named declaration as its
body, so a statement change breaks this file while a proof-only refactor does
not.  `Stor.Weth10Inv` is pinned separately by definitional unfolding.
-/

namespace Blanc

open Jaune

example {sevm : Sevm} {devm : Devm} {x : Xinst}
    {f : Frame} {rsm : Resume}
    (hs : Xinst.step sevm devm x = .spawn f rsm)
    (hne : sevm.currentTarget ≠ f.inner.currentTarget)
    (hcode : devm.getCode f.inner.currentTarget ≠ .empty)
    (hnodel :
      getDelegatedCodeAddress (devm.getCode f.inner.currentTarget) = none) :
    f.inner.codeAddress = some f.inner.currentTarget :=
  Xinst.step_spawn_codeAddress_eq_currentTarget hs hne hcode hnodel

example {root target : Exec.Deriv} {program : Prog}
    {path : Prog.SourcePath} {source : Func} {instruction : Ninst}
    (cursor : Exec.Deriv.SourceCursor root program path source)
    (compiled : some root.sevm.code.toList = program.compile)
    (reached : Exec.Deriv.ParentPrefix cursor.node target)
    (nonPush : NinstNonPush instruction)
    (instructionAt : Ninst.At target.sevm.code target.pc instruction) :
    Exec.Deriv.SourceCursor.Toward cursor target instruction cursor :=
  cursor.toward compiled reached nonPush instructionAt

example {root target : Exec.Deriv} {program : Prog}
    {initialPath path : Prog.SourcePath} {initialSource source : Func}
    {initial : Exec.Deriv.SourceCursor root program initialPath initialSource}
    {cursor : Exec.Deriv.SourceCursor root program path source}
    (chronology : Exec.Deriv.SourceCursor.Chronology initial cursor target)
    (distinct : cursor.node ≠ target) :
    Exec.Deriv.lt target cursor.node :=
  chronology.strictBefore distinct

namespace Weth10






/-!
The two pins above name `ContractSpec.Sound` and `ContractSpec.Preserves`,
which are `def`s: adding a premise to either changes what the flagship claims
while leaving those two examples typechecking.  The four pins below spell the
quantifier and premise list out instead, so the premise list itself is what is
pinned and a premise added anywhere in it breaks this file.

The flagship obligations are the `NoMem` ones: no WETH10 selector reads the
machine's memory, so neither the obligation nor the frame theorem is entitled
to a `Mem.Wf` premise.  The memory-carrying pair is pinned too, because the
message-, transaction- and block-level rungs consume it.

Since the 2026-09-23 coverage restriction each obligation, and the
deeper-frame hypothesis inside it, is stated only for frames whose fork is
`CoveredFork` (Prague, Osaka, BPO1, BPO2); Amsterdam frames are not covered.
-/























/-! Constructor pins make the frozen record obligations fail closed.  Merely
checking each record's outer function type would not detect a field-level
weakening or a hidden success premise. -/
















/-! Deployment constructor pins make the pre-execution/result boundary fail
closed on record-field additions, removals, or type changes. -/














/-! The holder-flow history pins are intentionally proof-carrying and retain
the complete applied-block sequence.  These examples make weakening the
history to an endpoint-only summary, or dropping ordinary-reach coverage,
fail closed in the claims gate. -/



open Blanc.ExecutionTrace (AppliedBodyTrace SystemMessageTrace)

example {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {ommers : List Header} {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs ommers wds state bout) :
    SystemMessageTrace benv beaconRootsAddress
      benv.stat.parentBeaconBlockRoot.toBytes
      trace.beaconState trace.beaconOut :=
  trace.beacon

example {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {ommers : List Header} {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs ommers wds state bout) :
    SystemMessageTrace (benv.withState trace.beaconState)
      historyStorageAddress trace.lastHash.toBytes
      trace.historyState trace.historyOut :=
  trace.history

example {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {ommers : List Header} {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs ommers wds state bout) :
    SystemMessageTrace
      (trace.transactionBenv.withState
        (processWithdrawalsState trace.transactionBenv.state wds))
      withdrawalRequestPredeployAddress []
      trace.requests.withdrawalState trace.requests.withdrawalOut :=
  trace.requests.withdrawal

example {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {ommers : List Header} {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs ommers wds state bout) :
    SystemMessageTrace
      ((trace.transactionBenv.withState
        (processWithdrawalsState trace.transactionBenv.state wds)).withState
          trace.requests.withdrawalState)
      consolidationRequestPredeployAddress []
      trace.requests.consolidationState trace.requests.consolidationOut :=
  trace.requests.consolidation










/-! C1's taxonomy and provenance remain data, while executable authenticity
is supplied separately by the accepted-debit and emitter witnesses. -/























/-! CREATE children are retained only through complete code-deposit
settlement, not merely because their raw interpreter result committed. -/

example : Jaune.Frame → Execution → Bool :=
  Blanc.Frame.settlementCommits


/-! C2's local reverse theorem and classification record pin the same action
across the executed write, rich storage effect, WETH emitter, and accepted
debit evidence. -/




/-! C3-C6 public theorem pins.  The committed interpreter cores are concrete;
the frozen equations carry only the stable checkpoint and authentic retained
history premises. -/











/-! Goal-specific boundary falsifiers and arithmetic deductions. -/
















/-! The executable numeric fixtures pin the category fold independently of
the proof-carrying history constructors. -/






/-! ## `weth10-redeem-future-v2`

The attribution definitions below are pinned twice over. A type pin alone
would not notice a *strengthening* of `NoAllowanceKeyCollision` or
`AllowanceQuiescent` — replacing either with `False` or `True` respectively
leaves its type untouched while making `hardenedDescription`,
`deploymentRoot_allowanceQuiescent` and the full-window corollary vacuous —
so each carries a definitional `Iff.rfl` pin as well. Decidability of the two
history-local predicates is frozen surface (they are properties of an explicit
history's finitely many entries, never global assumptions) and is pinned by
`inferInstance`.

The mirror image of that risk is a *weakening of a conclusion term*, and it
hollows out the identical set of claims. `hardenedOutflow` redefined as the
plain ledger outflow leaves every pinned type intact while
`hardenedOutflow_le_permanentOutflow` degenerates into `n ≤ n`,
`permanentOutflow_eq_hardenedOutflow_of_noCollision` and the flagship's
`hardenedDescription` field become content-free with `hnc` unused, and
`holderFlow_hardened_floor` restates the residual floor it was meant to
strengthen. No axiom moves under that rewrite, because the vacuous route
carries the same axioms. The computation is therefore pinned as well as the
type: the chronological fold, the per-frame contribution it sums, and the
per-debit witness that contribution tests. `touchedAllowancePairs` is pinned
the same way for the same reason in the opposite direction — it is the last
unpinned term inside `NoAllowanceKeyCollision`, and *adding* pairs to it
strengthens the hypothesis until every claim carrying it is vacuous.

`projectedAllowanceKey` is the term both pinned hypothesis predicates are
stated through, so its derivation and the two identities that make it the key
the compiled runtime computes are pinned first. Were those to drift together
the predicates would go on type-checking while describing a slot the runtime
never visits. -/










/-! The hardened outflow's computation, not merely its type: the chronological
fold over the attribution ledger, the per-frame contribution the fold sums, and
the per-debit witness that contribution tests. The fold itself is private to
its own module, so it is named here through `open private`; a pin that stops
resolving because the fold was renamed or exposed fails closed, exactly as a
rewritten body does. -/










/-! The allowance-dispatch transport endpoints the attribution layer runs on:
the compiled program's committed allowance obligation, and the history-level
statement that every tagged allowance key holds exactly the ledger's last
committed write. -/



/-! ## The read-sound strengthening

The two pins above are deliberately left exactly as they were. The transport
they state was *not* strengthened in place; instead a `Sound` sibling was
proved beside each, adding entry-read soundness of the same ledger against the
same entry storage. The carriers are pinned by definitional unfolding, so the
added conjunct cannot quietly become vacuous, and the downgrade witnesses at
the end of this section recover both original endpoints from their siblings —
the strengthening therefore cannot have been bought by weakening the published
statements. -/







/-! The flash-loan record carries no exemption from the entry-read clause. It
is the one record whose read is reconstructed from the committed post state
rather than observed at frame entry, and the pin below is what makes that
honest: the record is measured at the **post-callback settlement entry**,
which is where the runtime performed the read, and `Exec.frameContribution`
places the record after its subtree precisely so that the prefix the clause
measures it against replays to that state. Weakening this back to an
exemption is a semantic change, so it is pinned in full. -/


/-! The read-sound endpoints themselves: the compiled program's read-sound
committed obligation, and the history-level read-sound transport that the
dormant-holder theorem consumes. -/



/-! The downgrade witnesses. Each pinned original is recovered from its `Sound`
sibling by the generic downgrade, so the sibling asserts everything the pinned
statement asserts. -/



/-! The hardened outflow is a sub-sum of the permanent outflow unconditionally,
and equals it under trace-local collision-freedom. The collision hypothesis
appears on the equality and nowhere else. -/




/-! The dormant-holder theorem, the family's most human-legible claim: a holder
who performed no authorizing act and held no allowance at the checkpoint cannot
have lost a wei. Its five hypotheses are the whole content of "did nothing" —
`hquiet` is the checkpoint-side allowance quiescence and `hdormant` the
ledger-side absence of any authorizing act by `u`, and the conclusion is a bare
inequality on booked balances with no outflow term at all. Adding a hypothesis,
or weakening the conclusion to mention an outflow, breaks this pin. -/


/-! The two enabledness capstones state their residual bound at the checkpoint
and discharge redemption at the future snapshot. Neither takes a collision
hypothesis; a holder's ability to redeem never rests on an assumption about
hash keys. -/





/-! The rebased pair states its bound against the *full booked balance at the
future snapshot itself*: rebasing the window at the future collapses the
outflow terms, so no residual subtraction appears in either statement. -/





/-! The flagship record, pinned field by field. This is the pin that protects
the goal's central invariant: `hardenedDescription` carries
`NoAllowanceKeyCollision` as its OWN hypothesis, while `messageEnabled` and
`transactionEnabled` carry no collision hypothesis at all. Field assignment is
checked up to definitional equality, so moving the collision hypothesis onto
an enabledness field — or off `hardenedDescription` — breaks this example. -/














/-! The any-order records are constructor-pinned for the same reason. A
`budget` field weakened from the per-owner **aggregate** to a per-claim bound
would silently permit overbooking by splitting one owner's claim in two, and a
`remaining` field weakened to anything less than "every extension admissible
before is admissible after" would gut the any-order induction. -/










/-! ## Current-mainnet and Prague specialization pins -/



























end Weth10

namespace LidoCircuitBreaker






































/-! S3 Registry enumeration/observability public-role pins.  The dedicated
gate additionally hashes each normalized declaration header fail-closed. -/
-- getPausables_runCompiled

-- getPausables_noSstore_occurrence

-- registryViews_coherent

-- pauserSet_local_transition

-- pauserSet_target_zero_no_success

-- pauserSet_target_zero_error_logs_unchanged

-- pauserSet_register_success

-- pauserSet_register_success_committed

-- pauserSet_settled_error_not_observable

-- registryObservation_sound

/-! S9 carrier-field pins. The dedicated deployment gate hashes the complete
record bodies; these Lean wrappers independently pin each public field's type. -/






example {chainId : UInt64} {base : BlockChain} {sender ca : Adr}
    (h : CanonicalDeploymentBase .prague chainId base sender ca) :
    base.ValidContext ∧
      chainId = base.chainId ∧
      SumNof base.state.bal ∧
      ca = computeContractAddress sender (base.state.getNonce sender) ∧
      ca ≠ 0 ∧
      (¬ pragueRules.isPrecomp ca) ∧
      sender ≠ ca ∧
      withdrawalRequestPredeployAddress ≠ ca ∧
      consolidationRequestPredeployAddress ≠ ca ∧
      accountHasCodeOrNonce base.state ca = false ∧
      accountHasStorage base.state ca = false ∧
      (∃ lastHash,
        List.getLast? (getLast256BlockHashes base) = some lastHash) ∧
      some (base.state.getCode beaconRootsAddress).toList =
        Prog.compile deploymentSystemProgram ∧
      some (base.state.getCode historyStorageAddress).toList =
        Prog.compile deploymentSystemProgram ∧
      some (base.state.getCode withdrawalRequestPredeployAddress).toList =
        Prog.compile deploymentSystemProgram ∧
      some (base.state.getCode consolidationRequestPredeployAddress).toList =
        Prog.compile deploymentSystemProgram :=
  ⟨h.validContext, h.chainId_eq, h.sumNof, h.target_eq, h.target_ne_zero,
    h.target_not_precompile, h.sender_ne_target,
    h.withdrawalRequest_ne_target, h.consolidationRequest_ne_target,
    h.target_noCodeOrNonce, h.target_noStorage, h.lastBlockHash, h.beaconCode,
    h.historyCode, h.withdrawalRequestCode, h.consolidationRequestCode⟩







/-! S9 constructor-to-block theorem pins. These wrappers freeze every public
premise, including the distinction between raw CREATE success, collision-
checked message settlement, receipt success, and the complete request suffix. -/






/-! S9 direct-deployment root pins. The constructor pin freezes every public
field of the root package; the theorem and seven method pins freeze the exact
premise and consequence surfaces rather than merely checking that the names
still resolve. -/










/-! Selected-fork direct-deployment root pins. The constructor pin freezes
every field of the selected-fork root package, including the selected rules'
target non-precompile fact at the deployed tip; the producer pin freezes its
exact premises (the schedule lookup at the block's own number and timestamp,
coverage, and the configured transition as the only chain premise); the method
pins freeze the floor-relative reachable consequences. -/










/-! Mainnet specialization pins. The three registered coordinates are pinned
by unfolding (the deployment gate binds the same literals to the reference
manifest); the BPO2 selection is pinned against the full historical mainnet
schedule; the root package, producer and consequences are pinned exactly, the
consequences taking reachability under that schedule and no coverage
premise. -/














end LidoCircuitBreaker



/-! ## Reverting-walk vocabulary (vault-max-design-v1).

The visiting relation carries the meaning of every PRORATA WETH vault
nonrevert headline below, so its definition and every constructor type are
pinned, together with its anti-vacuity projection. -/













end Blanc

/-!
Deployed-bytecode claim map headlines: one exact statement pin per required headline of
`scripts/check-deployed-claim-map.py`, each written in the namespace and with the `open`s of the
module that states it, so every name resolves as it does there.  A change to any headline statement
breaks this file; a proof-only change does not.
-/






namespace Blanc.Lift.WithdrawalRequest
open Jaune ExecutionTrace ExecutionAccountingReplay Blanc.WithdrawalRequest

-- EIP-7002: block_word_fifo
example
    {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (deployment : DeploymentHistory cfg checkpoint)
    (admission : deployment.Admission)
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post)
    (otherInstalled : OtherSystemCodeInstalled checkpoint.state)
    (senders : (ConfiguredHistoryTrace.step history block).NoSenderAt systemAddress)
    (authorities : (ConfiguredHistoryTrace.step history block).NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ (ConfiguredHistoryTrace.step history block).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (occurrences : ((ConfiguredHistoryTrace.step history block).settledFrames.flatMap
      submissionFramePayments).length ≤ wordOccurrenceCap) :
    BlockWordFifo deployment history block :=
  block_word_fifo deployment admission history block otherInstalled senders authorities avoid occurrences

-- EIP-7002: block_word_fifo_or_overflow
example
    {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (deployment : DeploymentHistory cfg checkpoint)
    (admission : deployment.Admission)
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post)
    (otherInstalled : OtherSystemCodeInstalled checkpoint.state)
    (senders : (ConfiguredHistoryTrace.step history block).NoSenderAt systemAddress)
    (authorities : (ConfiguredHistoryTrace.step history block).NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ (ConfiguredHistoryTrace.step history block).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress) :
    BlockWordFifo deployment history block ∨
      wordOccurrenceCap < ((ConfiguredHistoryTrace.step history block).settledFrames.flatMap
        submissionFramePayments).length :=
  block_word_fifo_or_overflow deployment admission history block otherInstalled senders authorities avoid

-- EIP-7002: block_word_fifo_of_blockCount
example
    {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (deployment : DeploymentHistory cfg checkpoint)
    (admission : deployment.Admission)
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post)
    (otherInstalled : OtherSystemCodeInstalled checkpoint.state)
    (senders : (ConfiguredHistoryTrace.step history block).NoSenderAt systemAddress)
    (authorities : (ConfiguredHistoryTrace.step history block).NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ (ConfiguredHistoryTrace.step history block).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (blocks : (ConfiguredHistoryTrace.step history block).blockCount ≤ 2 ^ 190) :
    BlockWordFifo deployment history block :=
  block_word_fifo_of_blockCount deployment admission history block otherInstalled senders authorities avoid blocks

-- EIP-7002: block_word_fifo_of_checkpoint
example
    {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post)
    (installed : SystemCodeInstalled checkpoint.state)
    (senders : (ConfiguredHistoryTrace.step history block).NoSenderAt systemAddress)
    (authorities : (ConfiguredHistoryTrace.step history block).NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ (ConfiguredHistoryTrace.step history block).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (systemEmpty : checkpoint.state.getCode systemAddress = ByteArray.empty)
    (init : RepresentsStorage (checkpoint.state.getStor withdrawalRequestPredeployAddress).get initial)
    (occurrences : ((ConfiguredHistoryTrace.step history block).settledFrames.flatMap
      submissionFramePayments).length ≤ wordOccurrenceCap) :
    CheckpointBlockWordFifo history block :=
  block_word_fifo_of_checkpoint history block installed senders authorities avoid systemEmpty init occurrences

-- EIP-7002: blockWordFifo_iff_checkpoint
example {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (deployment : DeploymentHistory cfg checkpoint)
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post)
    (initialized : deployment.Initialized) :
    BlockWordFifo deployment history block ↔ CheckpointBlockWordFifo history block :=
  blockWordFifo_iff_checkpoint deployment history block initialized

end Blanc.Lift.WithdrawalRequest

namespace Blanc.Lift.WithdrawalRequest
open Jaune

-- EIP-7002: word_fee_eq_iff_natFeeDomain
example {excess : B256} {iterations : Nat}
    {output : B256}
    (run : WordFakeExponential.Run excess 17 1 17 0 iterations output)
    (model : Blanc.WithdrawalRequest.State) (excessEq : model.excess = excess.toNat) :
    (output / (17 : B256)).toNat = Blanc.WithdrawalRequest.fee model ↔
      NatFeeDomain excess iterations :=
  word_fee_eq_iff_natFeeDomain run model excessEq

end Blanc.Lift.WithdrawalRequest

namespace Blanc.Lift.WithdrawalRequest.FeeCounterexample
open Jaune Blanc.Lift Blanc.ExecutionTrace Blanc.BlockForward FloodTx FloodWalk

-- EIP-7002: nat_fee_guarantee_refuted
example : NatFeeGuaranteeRefuted :=
  nat_fee_guarantee_refuted

end Blanc.Lift.WithdrawalRequest.FeeCounterexample

namespace Blanc.Lift.WithdrawalRequest
open Jaune Blanc.ExecutionTrace

-- EIP-7002: history_submission_nat_live
example {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint future)
    (code : checkpoint.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode)
    (sevm : Sevm) (b : Devm) (data : Bytes) (fork : CoveredFork sevm.benvStat.fork)
    (user : sevm.caller ≠ systemAddress) (length : data.length = 56) :
    let fresh := historySubmissionSevm future.state sevm data
    let base := b.withState future.state
    (base.getStorVal withdrawalRequestPredeployAddress 0 = B256.max →
      ∀ gas post, ¬ Nonempty (Exec 0 fresh (St base [] Mem.empty gas) (.ok post))) ∧
    (base.getStorVal withdrawalRequestPredeployAddress 0 ≠ B256.max →
      fakeExp 1 (base.getStorVal withdrawalRequestPredeployAddress 0).toNat 17 ≤
        sevm.value.toNat →
      ∃! result : Nat × B256,
        WordFakeExponential.Run (base.getStorVal withdrawalRequestPredeployAddress 0)
          17 1 17 0 result.1 result.2 ∧
        ∀ G, gCallStipend < G →
          Nonempty (Exec 0 fresh (St base [] Mem.empty
            (G + (1258 + 87 * result.1 + sloadScheduleCost fresh (userSubmissionReads fresh base) +
              submissionStoreGas fresh (afterSload fresh base 0) Mem.empty)))
            (.ok (submissionPost fresh (afterSload fresh base 0) Mem.empty G)))) :=
  history_submission_nat_live history code sevm b data fork user length

end Blanc.Lift.WithdrawalRequest


/-! The project definitions those headline statements are stated through, where the definition
body is itself the claim, are pinned by unfolding (`Iff.rfl`), and record types by an exact
field-wise equivalence, so a weakened body or an added/removed field fails here. -/

namespace Blanc
open Jaune

-- WETH9 definition: SumNof
example (f : Adr → B256) :
    SumNof f ↔
      (sum f < 2 ^ 256) :=
  Iff.rfl

end Blanc




namespace Blanc.Lift.WithdrawalRequest
open Jaune ExecutionTrace ExecutionAccountingReplay Blanc.WithdrawalRequest

-- EIP-7002 constructor: BlockWordReplay.mk
example : ∀ {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    {history : ConfiguredHistoryTrace cfg checkpoint pre}
    {block : ConfiguredBlockTrace cfg pre post}
    (past transactions : List WordReplayEvent) (reset : WordReplayEvent),
    WordStorageReplay (checkpoint.state.getStor withdrawalRequestPredeployAddress)
      ((past ++ transactions) ++ [reset]) (post.state.getStor withdrawalRequestPredeployAddress) →
    past.map WordReplayEvent.frame = history.settledFrames.flatMap balanceFrameObservation →
    transactions.map WordReplayEvent.frame =
      block.bodyTrace.transactions.settledFrames.flatMap balanceFrameObservation →
    reset.kind = .system →
    reset.frame.pre.state = block.bodyTrace.requestBenv.state →
    BlockWordReplay history block :=
  @BlockWordReplay.mk

-- EIP-7002 definition: BlockWordReplay.model
example {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    {history : ConfiguredHistoryTrace cfg checkpoint pre}
    {block : ConfiguredBlockTrace cfg pre post} (r : BlockWordReplay history block) :
    r.model = (r.past ++ r.transactions).foldl wordModelUpdate initial :=
  rfl

-- EIP-7002 definition: BlockWordReplay.submissions
example {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    {history : ConfiguredHistoryTrace cfg checkpoint pre}
    {block : ConfiguredBlockTrace cfg pre post} (r : BlockWordReplay history block) :
    r.submissions = wordModelSubmissions (r.past ++ r.transactions) :=
  rfl

-- EIP-7002 definition: BlockWordReplay.pastOutputs
example {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    {history : ConfiguredHistoryTrace cfg checkpoint pre}
    {block : ConfiguredBlockTrace cfg pre post} (r : BlockWordReplay history block) :
    r.pastOutputs = wordModelOutputs initial r.past :=
  rfl

-- EIP-7002 definition: BlockWordReplay.outputs
example {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    {history : ConfiguredHistoryTrace cfg checkpoint pre}
    {block : ConfiguredBlockTrace cfg pre post} (r : BlockWordReplay history block) :
    r.outputs = r.pastOutputs ++ emitted r.model :=
  rfl

-- EIP-7002 definition: BlockWordReplay.frames
example {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    {history : ConfiguredHistoryTrace cfg checkpoint pre}
    {block : ConfiguredBlockTrace cfg pre post} (r : BlockWordReplay history block) :
    r.frames = wordSubmissionFrames (r.past ++ r.transactions) :=
  rfl

-- EIP-7002 definition: BlockWordReplay.BoundaryModel
example {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    {history : ConfiguredHistoryTrace cfg checkpoint pre}
    {block : ConfiguredBlockTrace cfg pre post} (r : BlockWordReplay history block) :
    r.BoundaryModel ↔
      (RepresentsStorage (checkpoint.state.getStor withdrawalRequestPredeployAddress).get initial) ∧
      (WordHistory initial r.model r.submissions r.pastOutputs) ∧
      (RepresentsStorage (block.bodyTrace.requestBenv.state.getStor
        withdrawalRequestPredeployAddress).get r.model) :=
  ⟨fun h => ⟨h.origin, h.wordHistory, h.represents⟩,
    fun ⟨h0, h1, h2⟩ => ⟨h0, h1, h2⟩⟩

-- EIP-7002 definition: BlockWordReplay.Emission
example {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    {history : ConfiguredHistoryTrace cfg checkpoint pre}
    {block : ConfiguredBlockTrace cfg pre post} (r : BlockWordReplay history block) :
    r.Emission ↔
      (block.bodyTrace.requests.withdrawalOut.returnData = systemOutput r.model) ∧
      (block.blockOutput.requests =
        optionalRequestEntry 0 block.bodyTrace.requests.depositRequests ++
        optionalRequestEntry 1 (systemOutput r.model) ++
        optionalRequestEntry 2 block.bodyTrace.requests.consolidationOut.returnData) ∧
      (optionalRequestEntry 1 block.bodyTrace.requests.withdrawalOut.returnData = [] ↔
        emitted r.model = []) :=
  ⟨fun h => ⟨h.withdrawal, h.requests, h.omittedIff⟩, fun ⟨h0, h1, h2⟩ => ⟨h0, h1, h2⟩⟩

-- EIP-7002 definition: BlockWordReplay.AfterReset
example {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    {history : ConfiguredHistoryTrace cfg checkpoint pre}
    {block : ConfiguredBlockTrace cfg pre post} (r : BlockWordReplay history block) :
    r.AfterReset ↔
      (RepresentsStorage (checkpoint.state.getStor withdrawalRequestPredeployAddress).get initial) ∧
      (WordHistory initial (Blanc.WithdrawalRequest.system r.model) r.submissions r.outputs) ∧
      (RepresentsStorage (post.state.getStor withdrawalRequestPredeployAddress).get
        (Blanc.WithdrawalRequest.system r.model)) :=
  ⟨fun h => ⟨h.origin, h.wordHistory, h.represents⟩,
    fun ⟨h0, h1, h2⟩ => ⟨h0, h1, h2⟩⟩

-- EIP-7002 definition: BlockWordReplay.Fifo
example {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    {history : ConfiguredHistoryTrace cfg checkpoint pre}
    {block : ConfiguredBlockTrace cfg pre post} (r : BlockWordReplay history block) :
    r.Fifo ↔
      r.submissions.map Submission.entry =
        r.outputs ++ (Blanc.WithdrawalRequest.system r.model).queue :=
  Iff.rfl

-- EIP-7002 definition: BlockWordReplay.Provenance
example {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    {history : ConfiguredHistoryTrace cfg checkpoint pre}
    {block : ConfiguredBlockTrace cfg pre post} (r : BlockWordReplay history block) :
    r.Provenance ↔
      (r.frames.map Prod.fst =
        ((ConfiguredHistoryTrace.step history block).settledFrames.flatMap
          submissionFramePayments).map Prod.fst) ∧
      (∀ pair ∈ r.frames,
        pair.1.sevm.caller = pair.2.caller ∧ pair.1.sevm.data = submissionPayload pair.2) ∧
      (r.frames.map Prod.snd = r.outputs ++ (Blanc.WithdrawalRequest.system r.model).queue) :=
  ⟨fun h => ⟨h.stepFrames, h.payloads, h.entries⟩,
    fun ⟨h0, h1, h2⟩ => ⟨h0, h1, h2⟩⟩

-- EIP-7002 definition: WordBookkeepingSafe
example (state : Blanc.WithdrawalRequest.State) :
    WordBookkeepingSafe state ↔
      (effectiveExcess state ≤ wordOccurrenceCap) ∧
      (state.count ≤ wordOccurrenceCap) ∧
      (state.head ≤ state.tail) ∧
      (state.tail ≤ wordOccurrenceCap) ∧
      (state.queue.length = state.tail - state.head) ∧
      (effectiveExcess state + state.count < 2 ^ 256) ∧
      (queueBase state.tail + 2 < 2 ^ 256) ∧
      (QueueSlotsSafe state) :=
  ⟨fun h => ⟨h.excessLe, h.countLe, h.headLe, h.tailLe, h.length, h.sumLt, h.slotLt, h.slots⟩,
    fun ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ => ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩⟩

-- EIP-7002 definition: CheckpointBlockWordFifo
example {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post) :
    CheckpointBlockWordFifo history block ↔
      ∃ r : BlockWordReplay history block,
        r.BoundaryModel ∧ r.Emission ∧ r.AfterReset ∧ r.Fifo ∧ r.Provenance ∧
        WordBookkeepingSafe r.model ∧
        WordBookkeepingSafe (Blanc.WithdrawalRequest.system r.model) :=
  Iff.rfl


-- EIP-7002 definition: Creation.CanonicalDeploymentInput
example (msg : Msg) :
    Creation.CanonicalDeploymentInput msg ↔
      (msg.target = none) ∧
      (msg.currentTarget = withdrawalRequestPredeployAddress) ∧
      (msg.code = Creation.creationCode) ∧
      (msg.value = 0) ∧
      (123017 ≤ msg.gas) ∧
      (messageCreateCollision msg = false) :=
  ⟨fun h => ⟨h.target, h.address, h.code, h.value, h.gas, h.collision⟩,
    fun ⟨h0, h1, h2, h3, h4, h5⟩ => ⟨h0, h1, h2, h3, h4, h5⟩⟩

-- EIP-7002 constructor: Creation.DeploymentCut.mk
example {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) (position : Nat)
    (cut : block.bodyTrace.transactions.TxSplit position)
    (input : Creation.CanonicalDeploymentInput cut.head.msg) (fork : block.fork = .cancun) :
    Creation.DeploymentCut block :=
  ⟨position, cut, input, fork⟩

-- EIP-7002 constructor: DeploymentHistory.mk
example (cfg : ChainConfig) (checkpoint before after : BlockChain)
    (block : ConfiguredBlockTraceIn HistFork cfg before after)
    (deployment : Creation.DeploymentCut block)
    (following : ConfiguredHistoryTraceIn HistFork cfg after checkpoint) :
    DeploymentHistory cfg checkpoint :=
  ⟨before, after, block, deployment, following⟩

-- EIP-7002 definition: DeploymentHistory.prefix
example {cfg : ChainConfig} {checkpoint : BlockChain}
    (deployment : DeploymentHistory cfg checkpoint) :
    deployment.prefix =
      (MidHistoryTraceIn.tail deployment.block deployment.deployment.cut).append
        deployment.following :=
  rfl

-- EIP-7002 definition: DeploymentHistory.Admission
example {cfg : ChainConfig} {checkpoint : BlockChain}
    (deployment : DeploymentHistory cfg checkpoint) :
    deployment.Admission ↔
      deployment.prefix.AllCancun ∧
      deployment.prefix.NoSenderAt systemAddress ∧
      deployment.prefix.BeaconCodeInstalled ∧
      (∀ root ∈ deployment.prefix.rawFrames, root.sevm.codeAddress = none →
        root.sevm.currentTarget ≠ systemAddress) ∧
      (deployment.deployment.cut.afterBenv.state.getCode systemAddress = ByteArray.empty) :=
  ⟨fun h => ⟨h.forks, h.senders, h.beacon, h.avoid, h.systemEmpty⟩,
    fun ⟨h0, h1, h2, h3, h4⟩ => ⟨h0, h1, h2, h3, h4⟩⟩

-- EIP-7002 definition: MidHistoryTraceIn.AllCancun (tail)
example {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i) :
    (MidHistoryTraceIn.tail block cut).AllCancun ↔ block.fork = .cancun :=
  Iff.rfl

-- EIP-7002 definition: MidHistoryTraceIn.AllCancun (step)
example {F : Fork → Prop} {cfg : ChainConfig} {start : Benv} {current future : BlockChain}
    (prior : MidHistoryTraceIn F cfg start current)
    (block : ConfiguredBlockTraceIn F cfg current future) :
    (prior.step block).AllCancun ↔ prior.AllCancun ∧ block.fork = .cancun :=
  Iff.rfl

-- EIP-7002 definition: MidHistoryTraceIn.NoSenderAt (tail)
example {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i) (a : Adr) :
    (MidHistoryTraceIn.tail block cut).NoSenderAt a ↔ cut.after.NoSenderAt a :=
  Iff.rfl

-- EIP-7002 definition: MidHistoryTraceIn.NoSenderAt (step)
example {F : Fork → Prop} {cfg : ChainConfig} {start : Benv} {current future : BlockChain}
    (prior : MidHistoryTraceIn F cfg start current)
    (block : ConfiguredBlockTraceIn F cfg current future) (a : Adr) :
    (prior.step block).NoSenderAt a ↔
      prior.NoSenderAt a ∧ block.bodyTrace.transactions.NoSenderAt a :=
  Iff.rfl

-- EIP-7002 definition: MidHistoryTraceIn.BeaconCodeInstalled (tail)
example {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i) :
    (MidHistoryTraceIn.tail block cut).BeaconCodeInstalled ↔ True :=
  Iff.rfl

-- EIP-7002 definition: MidHistoryTraceIn.BeaconCodeInstalled (step)
example {F : Fork → Prop} {cfg : ChainConfig} {start : Benv} {current future : BlockChain}
    (prior : MidHistoryTraceIn F cfg start current)
    (block : ConfiguredBlockTraceIn F cfg current future) :
    (prior.step block).BeaconCodeInstalled ↔
      prior.BeaconCodeInstalled ∧
      current.state.getCode beaconRootsAddress = beaconRootsCode :=
  Iff.rfl

-- EIP-7002 definition: DeploymentHistory.Initialized
example {cfg : ChainConfig} {checkpoint : BlockChain}
    (deployment : DeploymentHistory cfg checkpoint) :
    deployment.Initialized ↔
      deployment.prefix.AllCancun ∧
      (deployment.deployment.cut.index = deployment.deployment.position ∧
        deployment.block.bodyTrace.decodedTxs[deployment.deployment.position]? =
          some deployment.deployment.cut.tx) ∧
      (deployment.deployment.cut.afterBenv.state.getCode withdrawalRequestPredeployAddress =
        Blanc.withdrawalRequestCode) ∧
      (RepresentsStorage
        (deployment.deployment.cut.afterBenv.state.getStor withdrawalRequestPredeployAddress).get
        initial) ∧
      (checkpoint.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode) ∧
      (RepresentsStorage (checkpoint.state.getStor withdrawalRequestPredeployAddress).get initial) ∧
      (deployment.prefix.settledFrames.flatMap balanceFrameObservation = []) ∧
      (checkpoint.state.getCode systemAddress = ByteArray.empty) :=
  ⟨fun h => ⟨h.prefixCancun, h.transactionIdentity, h.deployedCode, h.deployedStorage, h.checkpointCode,
      h.checkpointStorage, h.noDynamicTargets, h.systemEmpty⟩,
    fun ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ => ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩⟩

-- EIP-7002: DeploymentHistory.initialized
example {cfg : ChainConfig} {checkpoint : BlockChain}
    (deployment : DeploymentHistory cfg checkpoint) (admission : deployment.Admission) :
    deployment.Initialized :=
  deployment.initialized admission

-- EIP-7002 definition: OtherSystemCodeInstalled
example (state : Jaune.State) :
    OtherSystemCodeInstalled state ↔
      (state.getCode beaconRootsAddress = beaconRootsCode) ∧
      (state.getCode historyStorageAddress = historyStorageCode) ∧
      (state.getCode consolidationRequestPredeployAddress = consolidationRequestCode) :=
  ⟨fun h => ⟨h.beaconRoots, h.historyStorage, h.consolidation⟩,
    fun ⟨h0, h1, h2⟩ => ⟨h0, h1, h2⟩⟩

-- EIP-7002 definition: BlockWordFifo
example {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (deployment : DeploymentHistory cfg checkpoint)
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post) :
    BlockWordFifo deployment history block ↔
      deployment.Initialized ∧
      deployment.prefix.settledFrames.flatMap submissionFramePayments = [] ∧
      CheckpointBlockWordFifo history block :=
  Iff.rfl

end Blanc.Lift.WithdrawalRequest

namespace Blanc.Lift.WithdrawalRequest
open Jaune

-- EIP-7002 definition: NatFeeDomain
example (excess : B256) (iterations : Nat) :
    NatFeeDomain excess iterations ↔
      (∃ output, ∃ run : FakeExponential.Run excess.toNat
      Blanc.WithdrawalRequest.feeUpdateFraction 1 Blanc.WithdrawalRequest.feeUpdateFraction
      iterations output, FakeExponentialWordCorrespondence.NoWrap run 0) :=
  Iff.rfl

end Blanc.Lift.WithdrawalRequest

namespace Blanc.Lift.WithdrawalRequest.FeeCounterexample
open Jaune Blanc.Lift Blanc.ExecutionTrace Blanc.BlockForward FloodTx

-- EIP-7002 definition: NatFeeGuaranteeRefuted
example :
    NatFeeGuaranteeRefuted ↔
      (∃ (cfg : ChainConfig) (checkpoint future : BlockChain)
    (trace : ConfiguredHistoryTrace cfg checkpoint future),
    SystemCodeInstalled checkpoint.state ∧
    trace.NoSenderAt systemAddress ∧ trace.NoAuthorityAt systemAddress ∧
    (∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ systemAddress) ∧
    checkpoint.state.getCode systemAddress = ByteArray.empty ∧
    Blanc.WithdrawalRequest.RepresentsStorage
      (checkpoint.state.getStor withdrawalRequestPredeployAddress).get
      Blanc.WithdrawalRequest.initial ∧
    ∃ frame ∈ trace.settledFrames.flatMap balanceFrameObservation,
      ∃ (model : Blanc.WithdrawalRequest.State) (iterations : Nat) (output : B256),
        submissionPaymentFrame frame ∧
        model.excess = ((frame.pre.getStor withdrawalRequestPredeployAddress).get 0).toNat ∧
        WordFakeExponential.Run ((frame.pre.getStor withdrawalRequestPredeployAddress).get 0)
          17 1 17 0 iterations output ∧
        (output / 17).toNat ≤ frame.sevm.value.toNat ∧
        frame.sevm.value.toNat < Blanc.WithdrawalRequest.fee model) :=
  Iff.rfl

end Blanc.Lift.WithdrawalRequest.FeeCounterexample

namespace Blanc.WithdrawalRequest
open Jaune

-- EIP-7002 definition: RepresentsStorage
example (storage : B256 → B256) (state : State) :
    RepresentsStorage storage state ↔
      (Coherent state) ∧
      (StorageBounds state) ∧
      (storage 0 = state.excess.toB256) ∧
      (storage 1 = state.count.toB256) ∧
      (storage 2 = state.head.toB256) ∧
      (storage 3 = state.tail.toB256) ∧
      (∀ i (hi : i < state.queue.length),
    storage (queueSlot (state.head + i) 0) = callerWord state.queue[i] ∧
    storage (queueSlot (state.head + i) 1) = pubkeyWord state.queue[i] ∧
    storage (queueSlot (state.head + i) 2) = pubkeyAmountWord state.queue[i]) :=
  ⟨fun h => ⟨h.coherent, h.bounds, h.excess, h.count, h.head, h.tail, h.live⟩, fun ⟨h0, h1, h2, h3, h4, h5, h6⟩ => ⟨h0, h1, h2, h3, h4, h5, h6⟩⟩

end Blanc.WithdrawalRequest

namespace Blanc.Lift.WithdrawalRequest
open Jaune ExecutionTrace ExecutionAccountingReplay Blanc.WithdrawalRequest

-- EIP-7002: block_word_delivery
example
    {cfg : ChainConfig} {checkpoint preB postB preD postD : BlockChain}
    (historyB : ConfiguredHistoryTrace cfg checkpoint preB)
    (blockB : ConfiguredBlockTrace cfg preB postB)
    (historyD : ConfiguredHistoryTrace cfg checkpoint preD)
    (blockD : ConfiguredBlockTrace cfg preD postD) {depth : Nat}
    (extension : (ConfiguredHistoryTrace.step historyB blockB).ExtendsBy
      (ConfiguredHistoryTrace.step historyD blockD) depth)
    (installed : SystemCodeInstalled checkpoint.state)
    (senders : (ConfiguredHistoryTrace.step historyD blockD).NoSenderAt systemAddress)
    (authorities : (ConfiguredHistoryTrace.step historyD blockD).NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ (ConfiguredHistoryTrace.step historyD blockD).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (systemEmpty : checkpoint.state.getCode systemAddress = ByteArray.empty)
    (init : RepresentsStorage (checkpoint.state.getStor withdrawalRequestPredeployAddress).get initial)
    (occurrences : ((ConfiguredHistoryTrace.step historyD blockD).settledFrames.flatMap
      submissionFramePayments).length ≤ wordOccurrenceCap)
    (modelB : Blanc.WithdrawalRequest.State)
    (repB : RepresentsStorage (blockB.bodyTrace.requestBenv.state.getStor
      withdrawalRequestPredeployAddress).get modelB)
    {q : Nat} {entry : Blanc.WithdrawalRequest.Entry} (queued : modelB.queue[q]? = some entry)
    (exactDepth : depth = q / 16) :
    ∃ modelD : Blanc.WithdrawalRequest.State,
      RepresentsStorage (blockD.bodyTrace.requestBenv.state.getStor
        withdrawalRequestPredeployAddress).get modelD ∧
      blockD.bodyTrace.requests.withdrawalOut.returnData = systemOutput modelD ∧
      (emitted modelD)[q % 16]? = some entry ∧
      (emitted modelD).take (q % 16 + 1) =
        (modelB.queue.drop (16 * depth)).take (q % 16 + 1) :=
  block_word_delivery historyB blockB historyD blockD extension installed senders authorities avoid systemEmpty init occurrences modelB repB queued exactDepth

-- EIP-7002: block_word_queue_after_from_deployment
example
    {cfg : ChainConfig} {checkpoint preB postB preD postD : BlockChain}
    (deployment : DeploymentHistory cfg checkpoint) (admission : deployment.Admission)
    (historyB : ConfiguredHistoryTrace cfg checkpoint preB)
    (blockB : ConfiguredBlockTrace cfg preB postB)
    (historyD : ConfiguredHistoryTrace cfg checkpoint preD)
    (blockD : ConfiguredBlockTrace cfg preD postD) {depth : Nat}
    (extension : (ConfiguredHistoryTrace.step historyB blockB).ExtendsBy
      (ConfiguredHistoryTrace.step historyD blockD) depth)
    (otherInstalled : OtherSystemCodeInstalled checkpoint.state)
    (senders : (ConfiguredHistoryTrace.step historyD blockD).NoSenderAt systemAddress)
    (authorities : (ConfiguredHistoryTrace.step historyD blockD).NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ (ConfiguredHistoryTrace.step historyD blockD).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (occurrences : ((ConfiguredHistoryTrace.step historyD blockD).settledFrames.flatMap
      submissionFramePayments).length ≤ wordOccurrenceCap)
    (modelB : Blanc.WithdrawalRequest.State)
    (repB : RepresentsStorage (blockB.bodyTrace.requestBenv.state.getStor
      withdrawalRequestPredeployAddress).get modelB) :
    ∃ modelD : Blanc.WithdrawalRequest.State,
      RepresentsStorage (blockD.bodyTrace.requestBenv.state.getStor
        withdrawalRequestPredeployAddress).get modelD ∧
      blockD.bodyTrace.requests.withdrawalOut.returnData = systemOutput modelD ∧
      (16 * depth ≤ modelB.queue.length →
        ∃ later, modelD.queue = modelB.queue.drop (16 * depth) ++ later) :=
  block_word_queue_after_from_deployment deployment admission historyB blockB historyD blockD extension otherInstalled senders authorities avoid occurrences modelB repB

-- EIP-7002: block_word_delivery_from_deployment
example
    {cfg : ChainConfig} {checkpoint preB postB preD postD : BlockChain}
    (deployment : DeploymentHistory cfg checkpoint) (admission : deployment.Admission)
    (historyB : ConfiguredHistoryTrace cfg checkpoint preB)
    (blockB : ConfiguredBlockTrace cfg preB postB)
    (historyD : ConfiguredHistoryTrace cfg checkpoint preD)
    (blockD : ConfiguredBlockTrace cfg preD postD) {depth : Nat}
    (extension : (ConfiguredHistoryTrace.step historyB blockB).ExtendsBy
      (ConfiguredHistoryTrace.step historyD blockD) depth)
    (otherInstalled : OtherSystemCodeInstalled checkpoint.state)
    (senders : (ConfiguredHistoryTrace.step historyD blockD).NoSenderAt systemAddress)
    (authorities : (ConfiguredHistoryTrace.step historyD blockD).NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ (ConfiguredHistoryTrace.step historyD blockD).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (occurrences : ((ConfiguredHistoryTrace.step historyD blockD).settledFrames.flatMap
      submissionFramePayments).length ≤ wordOccurrenceCap)
    (modelB : Blanc.WithdrawalRequest.State)
    (repB : RepresentsStorage (blockB.bodyTrace.requestBenv.state.getStor
      withdrawalRequestPredeployAddress).get modelB)
    {q : Nat} {entry : Blanc.WithdrawalRequest.Entry} (queued : modelB.queue[q]? = some entry)
    (exactDepth : depth = q / 16) :
    ∃ modelD : Blanc.WithdrawalRequest.State,
      RepresentsStorage (blockD.bodyTrace.requestBenv.state.getStor
        withdrawalRequestPredeployAddress).get modelD ∧
      blockD.bodyTrace.requests.withdrawalOut.returnData = systemOutput modelD ∧
      (emitted modelD)[q % 16]? = some entry ∧
      (emitted modelD).take (q % 16 + 1) =
        (modelB.queue.drop (16 * depth)).take (q % 16 + 1) :=
  block_word_delivery_from_deployment deployment admission historyB blockB historyD blockD extension otherInstalled senders authorities avoid occurrences modelB repB queued exactDepth

end Blanc.Lift.WithdrawalRequest

namespace Blanc.Lift.WithdrawalRequest
open Jaune ExecutionAccountingReplay

-- EIP-7002: wordSystem_excess_wraps
example :
    let storage := (Stor.empty.set 0 (2 ^ 256 - 2 : Nat).toB256).set 1 10
    (∃ state, Blanc.WithdrawalRequest.RepresentsStorage storage.get state) ∧
    ((wordSystemStorage storage).get 0).toNat = 6 ∧
    ∀ state, Blanc.WithdrawalRequest.RepresentsStorage storage.get state →
      (Blanc.WithdrawalRequest.system state).excess = 2 ^ 256 + 6 ∧
      ¬ Blanc.WithdrawalRequest.RepresentsStorage (wordSystemStorage storage).get
        (Blanc.WithdrawalRequest.system state) :=
  wordSystem_excess_wraps

end Blanc.Lift.WithdrawalRequest

namespace Blanc.ExecutionTrace
open Jaune

-- EIP-7002 definition: the history-extension relation `block_word_delivery` is stated over
example {cfg : ChainConfig} {checkpoint current : BlockChain}
    (base : ConfiguredHistoryTrace cfg checkpoint current) :
    ConfiguredHistoryTrace.ExtendsBy base base 0 :=
  .refl

example {cfg : ChainConfig} {checkpoint current middle future : BlockChain}
    {base : ConfiguredHistoryTrace cfg checkpoint current}
    {trace : ConfiguredHistoryTrace cfg checkpoint middle} {n : Nat}
    (prior : ConfiguredHistoryTrace.ExtendsBy base trace n)
    (block : ConfiguredBlockTrace cfg middle future) :
    ConfiguredHistoryTrace.ExtendsBy base (.step trace block) (n + 1) :=
  .step prior block

end Blanc.ExecutionTrace

/-!
Uniswap V2 Pair claim-map headlines (section 5.8): one exact statement pin per required headline of
`scripts/check-deployed-claim-map.py`, each written in the namespace and with the `open`s of the
module that states it, so every name resolves as it does there.  A change to any headline statement
breaks this file; a proof-only change does not.
-/


















/-! The Uniswap V2 Pair definitions those headline statements are stated through and the claim map
cites (the authentication and replay vocabulary, the answer premises, the oracle and ledger laws, the
storage representation, the gas expressions and the premise records), where the definition body is
itself the claim.  They are pinned by unfolding (`Iff.rfl`, `rfl`), recursive ones case by case, and
records by their exact constructor, so a weakened body or an added, removed or retyped field fails
here.  A premise record's own sub-records (for example the per-call environments a forward
environment is built from) are not unfolded here. -/





namespace Blanc
open Jaune

-- Common CALL/STATICCALL statement: successful flag commits the entered child
example {sevm : Sevm} {pre post : Devm} {x : Xinst}
    {child : Evm} {raw : Execution}
    (fork : CoveredFork sevm.benvStat.fork) (callFamily : x = .call ∨ x = .staticcall)
    (run : Xinst.Run sevm pre x (.some ⟨child, raw⟩) (.ok post))
    (flag : ∃ f rest, post.stack = f :: rest ∧ f ≠ 0) : Execution.commits raw = true :=
  Xinst.call_run_flag_commits fork callFamily run flag

end Blanc









/-! Paper review 2 (proposal): the claim-carrying definitions the repaired Uniswap headlines are
newly stated through — the positional entry authentication, the admitted positional consumption and
its recursive admission, the observed replay and step outcome they instantiate, and the two
canonical result records.  Definitions are pinned by unfolding, inductive families by the exact type
of every constructor, records by their exact constructor.  As above, a record's own sub-records
(`CallOccurrenceStep`, `SourceReplyAt`, `SourceSlotQueue`/`SourceSlotEvents`, `ExactTurns`, the
Burn/Swap physical-position and source-step records) are not unfolded here. -/



















































































/-! ## Paper review 2 approved statement coverage -/

-- Paper review 2 statement: weth9_history_tx_withdraw

-- Paper review 2 statement (M1): weth9_prefix_footprint_universe

-- Paper review 2 statement (M1): weth9_prefix_tx_withdraw

-- Paper review 2 statement (D2, conditional): weth9_closed_exit_instance

-- Paper review 2 constructor (D2, conditional): ClosedExitWitness.mk

-- Paper review 2 statement: vplus_reachable_capstone
-- Paper review 2 statement: vminus_reachable_capstone
-- Paper review 2 statement: vminus_reach_violation
-- Paper review 2 statement: registerPauser_nonzero_finite

-- Paper review 2 statement: lido_create_finite_init

-- Paper review 2 statement: exampleApplicable

-- Paper review 2 statement: checkRegistryOn_eq_true

-- Paper review 2 statement: checkLiveCovered_eq_true

-- Paper review 2 statement: runTyped_mint_initial

-- Paper review 2 statement: runTyped_mint_later

-- Paper review 2 statement: runTyped_burn_payout

-- Paper review 2 statement: runTyped_swap_canonical_success

-- Paper review 2 statement: swap_uint112_control

-- Paper review 2 statement: sqrt_of_run

-- Paper review 2 statement: sqrt_exact

-- Paper review 2 statement: swap_bytecode_exact_consumes

-- Paper review 2 statement: pairAddress_eq

-- Paper review 2 statement: pairAddress_wrong_salt

-- Paper review 2 statement: pairAddress_wrong_initHash

-- Paper review 2 statement: noShrink_required

-- Paper review 2 statement: mintRoundUp_breaks_feeOff_product

-- Paper review 2 statement: feeMutant_disagrees

-- Paper review 2 statement: burnRoundUp_disagrees

-- Paper review 2 statement: oracle_law_requires_timestamp_wrap

-- Paper review 2 statement: swap_bytecode_uint112_control

-- Paper review 2 statement: approve_storage_alias_breaks_ledger

-- Paper review 2 statement: sync_no_success_of_reverting_token0

-- Paper review 2 statement: sync_no_success_of_reverting_token1

-- Paper review 2 statement: skim_no_success_of_reverting_token0

-- Paper review 2 statement: mint_no_success_of_reverting_token0

-- Paper review 2 statement: mint_no_success_of_reverting_token1

-- Paper review 2 statement: swap_no_success_of_reverting_token0

-- Paper review 2 statement: swap_no_success_of_reverting_token1

-- Paper review 2 statement: swap_no_success_of_reverting_callback

-- Paper review 2 statement: sync_liveness_refuted

-- Paper review 2 definition: ViolationAt
-- Paper review 2 definition: ViolationStmt
-- Paper review 2 definition: CapstoneStmt
-- Paper review 2 definition: registryQueries

-- Paper review 2 definition: checkRegistryOn

-- Paper review 2 definition: checkLiveCovered

-- Paper review 2 definition: State.MinimumLocked

-- Paper review 2 definition: State.ZeroAllowances

-- Paper review 2 definition: State.SupplyFloor

-- Paper review 2 definition: SourceInvocation.CallersNonzero

-- Paper review 2 definition: sqrtCharge

-- Paper review 2 definition: factory

-- Paper review 2 definition: token0

-- Paper review 2 definition: token1

-- Paper review 2 definition: pairAddress

-- Paper review 2 definition: salt

-- Paper review 2 definition: saltWord

-- Paper review 2 definition: initHash

-- Paper review 2 definition: initializedStor

-- Paper review 2 definition: ConfiguredWorld

-- Paper review 2 definition: SyncLive

-- Paper review 2 definition: rawBalance

-- Paper review 2 definition: RawLedgerOn

-- Paper review 2 definition: _root_.Blanc.Lift.UniswapV2Pair.OracleUpdate.LawfulNoWrap

-- Paper review 2 definition: answer

-- Paper review 2 definition: initialized

-- Paper review 2 definition: wrapContext

-- Paper review 2 definition: syncTranscript

-- Paper review 2 definition: wrapRun

-- Paper review 2 definition: production

-- Paper review 2 definition: ceilDiv

-- Paper review 2 definition: mintLiquidityUp

-- Paper review 2 definition: mintAmountUp

-- Paper review 2 definition: burnAmountsUp

-- Paper review 2 definition: swapCheckFee

-- Paper review 2 definition: mintRoundUp

-- Paper review 2 definition: burnRoundUp

-- Paper review 2 definition: feeMutant

-- Paper review 2 definition: context

-- Paper review 2 definition: answer

-- Paper review 2 definition: initialized

-- Paper review 2 definition: mintTranscript

-- Paper review 2 definition: mintRun

-- Paper review 2 definition: minted

-- Paper review 2 definition: donationTranscript

-- Paper review 2 definition: donationRun

-- Paper review 2 definition: checkpoint

-- Paper review 2 definition: mintExpected

-- Paper review 2 definition: checkpointExpected

-- Paper review 2 definition: shrinkingTranscript

-- Paper review 2 definition: shrinkingRun

-- Paper review 2 definition: shrunk

-- Paper review 2 definition: laterTranscript

-- Paper review 2 definition: upMintRun

-- Paper review 2 definition: upDonationRun

-- Paper review 2 definition: upLaterRun

-- Paper review 2 definition: transferOk

-- Paper review 2 definition: feeSwapTranscript

-- Paper review 2 definition: feeMutantRun

-- Paper review 2 definition: burnReady

-- Paper review 2 definition: burnTranscript

-- Paper review 2 constructor: RegistryOn.mk

-- Paper review 2 definition: Transcript.CallersNonzero (every constructor)

-- Paper review 2 definition: InitialMintResult

-- Paper review 2 definition: mintObservation

-- Paper review 2 definition: LaterMintResult

-- Paper review 2 definition: burnObservation

-- Paper review 2 definition: BurnPayoutResult

-- Paper review 2 definition: SwapCanonicalBody

-- Paper review 2 definition: swapTraceKeys

-- Paper review 2 definition: swapCanonicalTranscript

-- Paper review 2 definition: swapControlState

-- Paper review 2 definition: swapControlContext

-- Paper review 2 definition: swapOk

-- Paper review 2 definition: swapAnswer

-- Paper review 2 definition: swapCanonicalPostTransfers

-- Paper review 2 definition: swapCanonicalTail

-- Paper review 2 definition: mintLiquidity

-- Paper review 2 definition: burnPayment

-- Paper review 2 definition: exampleEntries

-- Paper review 2 definition: exampleProbes

-- Paper review 2 definition: exampleInitialWrites

-- Paper review 2 definition: exampleStorage

-- Paper review 2 definition: swapOwnedRaw













-- usdc-weth9-pair-composition-v1: the never-signer predicate (derived for the Pair by usdc_neverSigner_pair)
set_option linter.unusedVariables false


namespace Blanc.Lift.WithdrawalRequest
open Jaune ExecutionTrace ExecutionAccountingReplay Blanc.WithdrawalRequest

-- The public FIFO statement and every concrete observer it uses.
example {cfg : ChainConfig} {checkpoint final : BlockChain}
    (deployment : DeploymentHistory cfg checkpoint)
    (admission : deployment.Admission)
    (history : ConfiguredHistoryTrace cfg checkpoint final)
    (otherInstalled : OtherSystemCodeInstalled checkpoint.state)
    (senders : history.NoSenderAt systemAddress)
    (authorities : history.NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ history.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (occurrences : (submissions history).length ≤ wordOccurrenceCap) :
    HistoryFifo history :=
  history_fifo deployment admission history otherInstalled senders authorities avoid occurrences

example {cfg : ChainConfig} {checkpoint final : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint final) :
    HistoryFifo history ↔ submissions history = emissions history ++ remainingQueue history := Iff.rfl

example (frame : Exec.Frame) : submissionRecord frame =
    frame.sevm.caller.toBytes ++ frame.sevm.data.take 48 ++ (frame.sevm.data.drop 48).reverse := rfl

example {cfg : ChainConfig} {checkpoint final : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint final) :
    submissions history = (history.settledFrames.flatMap submissionFramePayments).map
      (fun pair => submissionRecord pair.1) := rfl

example (bytes : Bytes) : withdrawalRecords bytes =
    (List.range ((bytes.length + 75) / 76)).map
      (fun i => (bytes.drop (76 * i)).take 76) := rfl

example (requests : List Bytes) : withdrawalRequestRecords requests =
    requests.flatMap (fun request => match request with
      | tag :: payload => if tag = 1 then withdrawalRecords payload else []
      | [] => []) := rfl

example {cfg : ChainConfig} {checkpoint : BlockChain}
    (hcfg : cfg.Valid) (hctx : checkpoint.ValidContext)
    (hid : cfg.chainId = checkpoint.chainId) :
    emissions (ConfiguredHistoryTrace.refl hcfg hctx hid) = [] := rfl

example {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post) :
    emissions (ConfiguredHistoryTrace.step history block) =
      emissions history ++ withdrawalRequestRecords block.blockOutput.requests := rfl

example (storage : B256 → B256) (index : Nat) : storedQueueRecord storage index =
    (storage (queueSlot index 0)).toAdr.toBytes ++
      (storage (queueSlot index 1)).toBytes ++
      (storage (queueSlot index 2)).toBytes.take 16 ++
      ((storage (queueSlot index 2)).toBytes.drop 16 |>.take 8).reverse := rfl

example (storage : B256 → B256) : storedQueue storage =
    (List.range ((storage 3).toNat - (storage 2).toNat)).map
      (fun i => storedQueueRecord storage ((storage 2).toNat + i)) := rfl

example {cfg : ChainConfig} {checkpoint final : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint final) :
    remainingQueue history =
      storedQueue (final.state.getStor withdrawalRequestPredeployAddress).get := rfl

end Blanc.Lift.WithdrawalRequest

/-! Public headlines in their trimmed form (headline facelift): each headline concludes one named
Prop over observers that read the history directly, and each observer is pinned by unfolding. -/

namespace Blanc.Lift.WithdrawalRequest
open Jaune ExecutionTrace

-- EIP-7002: fee_le_spec
example {excess : B256} {iterations : Nat} {output : B256}
    (run : WordFakeExponential.Run excess 17 1 17 0 iterations output) :
    WordFee output ≤ SpecFee excess :=
  fee_le_spec run

-- EIP-7002: fee_eq_spec_iff
example {excess : B256} {iterations : Nat} {output : B256}
    (run : WordFakeExponential.Run excess 17 1 17 0 iterations output) :
    WordFee output = SpecFee excess ↔ NatFeeDomain excess iterations :=
  fee_eq_spec_iff run

-- EIP-7002 definition: SpecFee
example (excess : B256) : SpecFee excess = fakeExp 1 excess.toNat 17 :=
  rfl

-- EIP-7002 definition: WordFee
example (output : B256) : WordFee output = (output / (17 : B256)).toNat :=
  rfl

-- EIP-7002 definition: storedExcess
example (world : Jaune.State) :
    storedExcess world = (world.getStor withdrawalRequestPredeployAddress).get 0 :=
  rfl

-- EIP-7002 definition: paid
example (frame : Exec.Frame) : paid frame = frame.sevm.value.toNat :=
  rfl

-- EIP-7002 definition: submissionFrames
example {cfg : ChainConfig} {checkpoint final : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint final) :
    submissionFrames history =
      (history.settledFrames.flatMap submissionFramePayments).map Prod.fst :=
  rfl

-- EIP-7002 definition: InitialStorage
example (storage : B256 → B256) :
    InitialStorage storage ↔
      (storage 0 = B256.max ∧ storage 1 = 0 ∧ storage 2 = 0 ∧ storage 3 = 0) :=
  Iff.rfl

-- EIP-7002 definition: SystemCallOk
example (benv : Benv) :
    SystemCallOk benv ↔
      (∃ post out, processCheckedSystemTransaction benv withdrawalRequestPredeployAddress [] =
          .ok (post, out) ∧
        systemTransactionGas - out.gasLeft ≤ 210000) :=
  Iff.rfl

-- EIP-7002: system_call_succeeds
example {benv : Benv} (fork : CoveredFork benv.stat.fork)
    (installed : benv.state.getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode) :
    SystemCallOk benv :=
  system_call_succeeds fork installed

-- EIP-7002: history_system_call_succeeds
example {cfg : ChainConfig} {checkpoint future : BlockChain}
    (deployment : DeploymentHistory cfg checkpoint) (admission : deployment.Admission)
    (history : ConfiguredHistoryTrace cfg checkpoint future)
    {benv : Benv} (state : benv.state = future.state) (fork : CoveredFork benv.stat.fork) :
    SystemCallOk benv :=
  history_system_call_succeeds deployment admission history state fork

-- EIP-7002 definition: submissionCost
example (fresh : Sevm) (base : Devm) (iterations : Nat) :
    submissionCost fresh base iterations =
      1258 + 87 * iterations + sloadScheduleCost fresh (userSubmissionReads fresh base) +
        submissionStoreGas fresh (afterSload fresh base 0) Mem.empty :=
  rfl

-- EIP-7002 definition: SubmissionLive
example (world : Jaune.State) (sevm : Sevm) (b : Devm) (data : Bytes) :
    SubmissionLive world sevm b data ↔
      let fresh := historySubmissionSevm world sevm data
      let base := b.withState world
      (storedExcess world = B256.max →
        ∀ gas post, ¬ Nonempty (Exec 0 fresh (St base [] Mem.empty gas) (.ok post))) ∧
      (storedExcess world ≠ B256.max → SpecFee (storedExcess world) ≤ sevm.value.toNat →
        ∃! result : Nat × B256,
          WordFakeExponential.Run (storedExcess world) 17 1 17 0 result.1 result.2 ∧
          ∀ G, gCallStipend < G →
            Nonempty (Exec 0 fresh (St base [] Mem.empty (G + submissionCost fresh base result.1))
              (.ok (submissionPost fresh (afterSload fresh base 0) Mem.empty G)))) :=
  Iff.rfl

-- EIP-7002: history_submission_live
example {cfg : ChainConfig} {checkpoint future : BlockChain}
    (deployment : DeploymentHistory cfg checkpoint) (admission : deployment.Admission)
    (history : ConfiguredHistoryTrace cfg checkpoint future)
    (sevm : Sevm) (b : Devm) (data : Bytes) (fork : CoveredFork sevm.benvStat.fork)
    (user : sevm.caller ≠ systemAddress) (length : data.length = 56) :
    SubmissionLive future.state sevm b data :=
  history_submission_live deployment admission history sevm b data fork user length

end Blanc.Lift.WithdrawalRequest

namespace Blanc.Lift.WithdrawalRequest
open Jaune Blanc.ExecutionTrace Blanc.WithdrawalRequest ExecutionAccountingReplay

-- EIP-7002 definition: InitialWords
example (storage : B256 → B256) :
    InitialWords storage ↔
      ((storage 0).toNat = 2 ^ 256 - 1 ∧ (storage 1).toNat = 0 ∧ (storage 2).toNat = 0 ∧
        (storage 3).toNat = 0) :=
  Iff.rfl

-- EIP-7002: deploy
example {cfg : ChainConfig} {checkpoint : BlockChain}
    (deployment : DeploymentHistory cfg checkpoint) (admission : deployment.Admission) :
    deployment.deployment.cut.afterBenv.state.getCode withdrawalRequestPredeployAddress =
        Blanc.withdrawalRequestCode ∧
      InitialWords
        (deployment.deployment.cut.afterBenv.state.getStor withdrawalRequestPredeployAddress).get ∧
      checkpoint.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode ∧
      InitialWords (checkpoint.state.getStor withdrawalRequestPredeployAddress).get :=
  deploy deployment admission

-- EIP-7002: deploy_mainnet
example {before after checkpoint : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig before after)
    (cut : block.bodyTrace.transactions.TxSplit 0)
    (following : ConfiguredHistoryTraceIn HistFork mainnetChainConfig after checkpoint)
    (obs : WithdrawalDeploymentObservation block checkpoint)
    (prefixSystemAvoid : ∀ root ∈ block.rawFrames ++ following.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress) :
    cut.afterBenv.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode ∧
      InitialWords (cut.afterBenv.state.getStor withdrawalRequestPredeployAddress).get ∧
      checkpoint.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode ∧
      InitialWords (checkpoint.state.getStor withdrawalRequestPredeployAddress).get :=
  deploy_mainnet block cut following obs prefixSystemAvoid

-- EIP-7002 definition: submissionPaid
example {cfg : ChainConfig} {checkpoint final : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint final) :
    submissionPaid history =
      ((history.settledFrames.flatMap submissionFramePayments).map Prod.snd).sum :=
  rfl

-- EIP-7002: history_payments
example {cfg : ChainConfig} {checkpoint final : BlockChain}
    (deployment : DeploymentHistory cfg checkpoint) (admission : deployment.Admission)
    (history : ConfiguredHistoryTrace cfg checkpoint final) :
    (checkpoint.state.bal withdrawalRequestPredeployAddress).toNat + submissionPaid history ≤
      (final.state.bal withdrawalRequestPredeployAddress).toNat :=
  history_payments deployment admission history

-- EIP-7002: history_payments_mainnet
example {before after checkpoint final : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig before after)
    (cut : block.bodyTrace.transactions.TxSplit 0)
    (following : ConfiguredHistoryTraceIn HistFork mainnetChainConfig after checkpoint)
    (obs : WithdrawalDeploymentObservation block checkpoint)
    (prefixSystemAvoid : ∀ root ∈ block.rawFrames ++ following.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (history : ConfiguredHistoryTrace mainnetChainConfig checkpoint final) :
    (checkpoint.state.bal withdrawalRequestPredeployAddress).toNat + submissionPaid history ≤
      (final.state.bal withdrawalRequestPredeployAddress).toNat :=
  history_payments_mainnet block cut following obs prefixSystemAvoid history

-- EIP-7002 definition: queueAtRequests
example {cfg : ChainConfig} {pre post : BlockChain} (block : ConfiguredBlockTrace cfg pre post) :
    queueAtRequests block =
      storedQueue (block.bodyTrace.requestBenv.state.getStor withdrawalRequestPredeployAddress).get :=
  rfl

-- EIP-7002 definition: blockWithdrawals
example {cfg : ChainConfig} {pre post : BlockChain} (block : ConfiguredBlockTrace cfg pre post) :
    blockWithdrawals block = withdrawalRequestRecords block.blockOutput.requests :=
  rfl

-- EIP-7002 definition: Delivered
example {cfg : ChainConfig} {preB postB preD postD : BlockChain}
    (blockB : ConfiguredBlockTrace cfg preB postB) (blockD : ConfiguredBlockTrace cfg preD postD)
    (q : Nat) :
    Delivered blockB blockD q ↔
      (∀ record, (queueAtRequests blockB)[q]? = some record →
        (blockWithdrawals blockD)[q % 16]? = some record ∧
        (blockWithdrawals blockD).take (q % 16 + 1) =
          ((queueAtRequests blockB).drop (16 * (q / 16))).take (q % 16 + 1)) :=
  Iff.rfl

-- EIP-7002: history_delivery
example {cfg : ChainConfig} {checkpoint preB postB preD postD : BlockChain}
    (deployment : DeploymentHistory cfg checkpoint) (admission : deployment.Admission)
    (historyB : ConfiguredHistoryTrace cfg checkpoint preB)
    (blockB : ConfiguredBlockTrace cfg preB postB)
    (historyD : ConfiguredHistoryTrace cfg checkpoint preD)
    (blockD : ConfiguredBlockTrace cfg preD postD) {depth : Nat}
    (extension : (ConfiguredHistoryTrace.step historyB blockB).ExtendsBy
      (ConfiguredHistoryTrace.step historyD blockD) depth)
    (otherInstalled : OtherSystemCodeInstalled checkpoint.state)
    (senders : (ConfiguredHistoryTrace.step historyD blockD).NoSenderAt systemAddress)
    (authorities : (ConfiguredHistoryTrace.step historyD blockD).NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ (ConfiguredHistoryTrace.step historyD blockD).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (occurrences : (submissions (ConfiguredHistoryTrace.step historyD blockD)).length ≤
      wordOccurrenceCap)
    {q : Nat} (exactDepth : depth = q / 16) :
    Delivered blockB blockD q :=
  history_delivery deployment admission historyB blockB historyD blockD extension otherInstalled
    senders authorities avoid occurrences exactDepth

-- EIP-7002: history_delivery_mainnet
example {before after checkpoint preB postB preD postD : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig before after)
    (cut : block.bodyTrace.transactions.TxSplit 0)
    (following : ConfiguredHistoryTraceIn HistFork mainnetChainConfig after checkpoint)
    (obs : WithdrawalDeploymentObservation block checkpoint)
    (prefixSystemAvoid : ∀ root ∈ block.rawFrames ++ following.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (historyB : ConfiguredHistoryTrace mainnetChainConfig checkpoint preB)
    (blockB : ConfiguredBlockTrace mainnetChainConfig preB postB)
    (historyD : ConfiguredHistoryTrace mainnetChainConfig checkpoint preD)
    (blockD : ConfiguredBlockTrace mainnetChainConfig preD postD) {depth : Nat}
    (extension : (ConfiguredHistoryTrace.step historyB blockB).ExtendsBy
      (ConfiguredHistoryTrace.step historyD blockD) depth)
    (senders : (ConfiguredHistoryTrace.step historyD blockD).NoSenderAt systemAddress)
    (authorities : (ConfiguredHistoryTrace.step historyD blockD).NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ (ConfiguredHistoryTrace.step historyD blockD).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (occurrences : (submissions (ConfiguredHistoryTrace.step historyD blockD)).length ≤
      wordOccurrenceCap)
    {q : Nat} (exactDepth : depth = q / 16) :
    Delivered blockB blockD q :=
  history_delivery_mainnet block cut following obs prefixSystemAvoid historyB blockB historyD
    blockD extension senders authorities avoid occurrences exactDepth

-- EIP-7002: history_fifo_mainnet
example {before after checkpoint final : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig before after)
    (cut : block.bodyTrace.transactions.TxSplit 0)
    (following : ConfiguredHistoryTraceIn HistFork mainnetChainConfig after checkpoint)
    (obs : WithdrawalDeploymentObservation block checkpoint)
    (history : ConfiguredHistoryTrace mainnetChainConfig checkpoint final)
    (prefixSystemAvoid : ∀ root ∈ block.rawFrames ++ following.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (senders : history.NoSenderAt systemAddress)
    (authorities : history.NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ history.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (occurrences : (submissions history).length ≤ wordOccurrenceCap) :
    HistoryFifo history :=
  history_fifo_mainnet block cut following obs history prefixSystemAvoid senders authorities
    avoid occurrences

-- EIP-7002 definition: wordOccurrenceCap
example : wordOccurrenceCap = 2 ^ 254 :=
  rfl

-- EIP-7002 constructor: WithdrawalDeploymentObservation.mk
example {before after checkpoint : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig before after)
    (number : block.block.header.number = 21881389)
    (timestamp : block.block.header.timestamp = 1739979863)
    (hash : block.block.header.hash =
      0xbffb31041b1839dbdd4cd4531b55f979f1b4f58665ee8de987329b30038ed283)
    (stateRoot : block.block.header.stateRoot =
      0x0c5d1c80666c4f618c2d07b4d87c45e5a8e9e601b6745373e223ea8ba3b8843a)
    (slotZero : block.block.txs[0]? = some (.inr Creation.HistoricalTx.tx))
    (receipt : ∃ r : Fin 5 × Receipt,
      block.blockOutput.receiptsTrie[BLT.toBytes (.bytes (0 : Nat).toBytes)]? = some r ∧
        r.2.succeeded = true)
    (parentSystemEmpty : before.state.getCode systemAddress = ByteArray.empty)
    (parentBeacon : before.state.getCode beaconRootsAddress = beaconRootsCode)
    (checkpointTip : ∃ tip, checkpoint.blocks.getLast? = some tip ∧
      tip.header.number = 22431083 ∧ tip.header.timestamp = 1746612299 ∧
      tip.header.hash = 0x28fb2c1d988435955e569451c6ad772f7fb5e61cddd7463c7b60e933ed5ff237 ∧
      tip.header.stateRoot = 0xab350e0fe349aef68947ede26295f8946c34ce3af5e3ec76f4b26ddeef29c0e3)
    (beaconAtP : checkpoint.state.getCode beaconRootsAddress = beaconRootsCode)
    (historyAtP : checkpoint.state.getCode historyStorageAddress = historyStorageCode)
    (consolidationAtP :
      checkpoint.state.getCode consolidationRequestPredeployAddress = consolidationRequestCode)
    (systemNonceAtP : checkpoint.state.getNonce systemAddress = 0) :
    WithdrawalDeploymentObservation block checkpoint :=
  ⟨number, timestamp, hash, stateRoot, slotZero, receipt, parentSystemEmpty, parentBeacon,
    checkpointTip, beaconAtP, historyAtP, consolidationAtP, systemNonceAtP⟩

end Blanc.Lift.WithdrawalRequest

namespace Blanc.Lift.WithdrawalRequest
open Jaune ExecutionTrace ExecutionAccountingReplay Blanc.WithdrawalRequest

-- EIP-7002 definition: HistoryFifoCheckpointLoadBearing
example :
    HistoryFifoCheckpointLoadBearing ↔
      (∃ (cfg : ChainConfig) (checkpoint final : BlockChain)
        (history : ConfiguredHistoryTrace cfg checkpoint final),
        SystemCodeInstalled checkpoint.state ∧
        history.NoSenderAt systemAddress ∧
        history.NoAuthorityAt systemAddress ∧
        (∀ root ∈ history.rawFrames,
          root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress) ∧
        checkpoint.state.getCode systemAddress ≠ ByteArray.empty ∧
        RepresentsStorage (checkpoint.state.getStor withdrawalRequestPredeployAddress).get initial ∧
        (submissions history).length ≤ wordOccurrenceCap ∧
        ¬ HistoryFifo history) :=
  Iff.rfl

end Blanc.Lift.WithdrawalRequest

namespace Blanc.Lift.WithdrawalRequest.DrainControl
open Jaune Blanc.Lift Blanc.ExecutionTrace Blanc.BlockForward FloodTx FeeCounterexample

-- EIP-7002: historyFifo_of_checkpoint_needs_systemEmpty
example : HistoryFifoCheckpointLoadBearing :=
  historyFifo_of_checkpoint_needs_systemEmpty

end Blanc.Lift.WithdrawalRequest.DrainControl

namespace Blanc.Lift.WithdrawalRequest.FeeCounterexample
open Jaune Blanc.Lift Blanc.ExecutionTrace

-- EIP-7002 definition: FeeGuaranteeRefuted
example :
    FeeGuaranteeRefuted ↔
      (∃ (cfg : ChainConfig) (checkpoint future : BlockChain)
        (trace : ConfiguredHistoryTrace cfg checkpoint future),
        SystemCodeInstalled checkpoint.state ∧
        trace.NoSenderAt systemAddress ∧ trace.NoAuthorityAt systemAddress ∧
        (∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
          root.sevm.currentTarget ≠ systemAddress) ∧
        checkpoint.state.getCode systemAddress = ByteArray.empty ∧
        InitialStorage (checkpoint.state.getStor withdrawalRequestPredeployAddress).get ∧
        ∃ frame ∈ submissionFrames trace,
          (∃ iterations output,
            WordFakeExponential.Run (storedExcess frame.pre.state) 17 1 17 0 iterations output ∧
            WordFee output ≤ paid frame) ∧
          paid frame < SpecFee (storedExcess frame.pre.state)) :=
  Iff.rfl

-- EIP-7002: feeGuaranteeRefuted_iff
example : FeeGuaranteeRefuted ↔ NatFeeGuaranteeRefuted :=
  feeGuaranteeRefuted_iff

-- EIP-7002: fee_guarantee_refuted
example : FeeGuaranteeRefuted :=
  fee_guarantee_refuted

end Blanc.Lift.WithdrawalRequest.FeeCounterexample

namespace Blanc.Lift.WithdrawalRequest
open Jaune ExecutionTrace

-- EIP-7002 definition: SubmissionQueued
example (world : Jaune.State) (sevm : Sevm) (b : Devm) (data : Bytes) :
    SubmissionQueued world sevm b data ↔
      let fresh := historySubmissionSevm world sevm data
      ∀ gas post, Nonempty (Exec 0 fresh (St (b.withState world) [] Mem.empty gas) (.ok post)) →
        storedQueue (post.getStor withdrawalRequestPredeployAddress).get =
          storedQueue (world.getStor withdrawalRequestPredeployAddress).get ++
            [sevm.caller.toBytes ++ data.take 48 ++ (data.drop 48).reverse] :=
  Iff.rfl

-- EIP-7002: history_submission_queued
example {cfg : ChainConfig} {checkpoint future : BlockChain}
    (deployment : DeploymentHistory cfg checkpoint) (admission : deployment.Admission)
    (history : ConfiguredHistoryTrace cfg checkpoint future)
    (occurrences : (submissions history).length ≤ wordOccurrenceCap)
    (sevm : Sevm) (b : Devm) (data : Bytes) (fork : CoveredFork sevm.benvStat.fork)
    (user : sevm.caller ≠ systemAddress) (length : data.length = 56) :
    SubmissionQueued future.state sevm b data :=
  history_submission_queued deployment admission history occurrences sevm b data fork user length

-- EIP-7002: history_system_call_succeeds_mainnet
example {before after checkpoint future : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig before after)
    (cut : block.bodyTrace.transactions.TxSplit 0)
    (following : ConfiguredHistoryTraceIn HistFork mainnetChainConfig after checkpoint)
    (obs : WithdrawalDeploymentObservation block checkpoint)
    (prefixSystemAvoid : ∀ root ∈ block.rawFrames ++ following.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (history : ConfiguredHistoryTrace mainnetChainConfig checkpoint future)
    {benv : Benv} (state : benv.state = future.state) (fork : CoveredFork benv.stat.fork) :
    SystemCallOk benv :=
  history_system_call_succeeds_mainnet block cut following obs prefixSystemAvoid history state fork

-- EIP-7002: history_submission_live_mainnet
example {before after checkpoint future : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig before after)
    (cut : block.bodyTrace.transactions.TxSplit 0)
    (following : ConfiguredHistoryTraceIn HistFork mainnetChainConfig after checkpoint)
    (obs : WithdrawalDeploymentObservation block checkpoint)
    (prefixSystemAvoid : ∀ root ∈ block.rawFrames ++ following.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (history : ConfiguredHistoryTrace mainnetChainConfig checkpoint future)
    (sevm : Sevm) (b : Devm) (data : Bytes) (fork : CoveredFork sevm.benvStat.fork)
    (user : sevm.caller ≠ systemAddress) (length : data.length = 56) :
    SubmissionLive future.state sevm b data :=
  history_submission_live_mainnet block cut following obs prefixSystemAvoid history sevm b data
    fork user length

-- EIP-7002: history_submission_queued_mainnet
example {before after checkpoint future : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig before after)
    (cut : block.bodyTrace.transactions.TxSplit 0)
    (following : ConfiguredHistoryTraceIn HistFork mainnetChainConfig after checkpoint)
    (obs : WithdrawalDeploymentObservation block checkpoint)
    (prefixSystemAvoid : ∀ root ∈ block.rawFrames ++ following.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (history : ConfiguredHistoryTrace mainnetChainConfig checkpoint future)
    (occurrences : (submissions history).length ≤ wordOccurrenceCap)
    (sevm : Sevm) (b : Devm) (data : Bytes) (fork : CoveredFork sevm.benvStat.fork)
    (user : sevm.caller ≠ systemAddress) (length : data.length = 56) :
    SubmissionQueued future.state sevm b data :=
  history_submission_queued_mainnet block cut following obs prefixSystemAvoid history occurrences
    sevm b data fork user length

end Blanc.Lift.WithdrawalRequest

/-! ## EIP-7251 consolidation requests (proposed pins, for the user's review)

The featured C1-C5 headlines and the unfeatured C1b, each by its exact statement; the observers they
are stated through, by unfolding; and their records and the `Succeeded` classification, by their
exact constructors. -/

namespace Blanc.Composition.ConsolidationRequestPublic
open Jaune Blanc

-- EIP-7251 definition: addr
example : addr = consolidationRequestPredeployAddress :=
  rfl

-- EIP-7251 definition: code
example : code = Blanc.consolidationRequestCode :=
  rfl

-- EIP-7251 definition: installed
example (w : State) : installed w ↔ w.getCode addr = code :=
  Iff.rfl

-- EIP-7251 definition: word
example (w : State) (k : B256) : word w k = (w.getStor addr).get k :=
  rfl

-- EIP-7251 definition: SpecFee
example (excess : B256) : SpecFee excess = fakeExp 1 excess.toNat 17 :=
  rfl

-- EIP-7251 definition: quotedFee
example (excess : B256) :
    quotedFee excess =
      ((Classical.choose (Blanc.WordFakeExponential.run_exists_unique excess 17 1 17 0).exists).2 /
        (17 : B256)).toNat :=
  rfl

-- EIP-7251 definition: quotedIterations
example (excess : B256) :
    quotedIterations excess =
      (Classical.choose (Blanc.WordFakeExponential.run_exists_unique excess 17 1 17 0).exists).1 :=
  rfl

-- EIP-7251 definition: queueRecord
example (s : B256 → B256) (i : Nat) :
    queueRecord s i =
      (s (4 + 4 * i).toB256).toAdr.toBytes ++ (s (4 + 4 * i + 1).toB256).toBytes ++
        (s (4 + 4 * i + 2).toB256).toBytes ++ (s (4 + 4 * i + 3).toB256).toBytes :=
  rfl

-- EIP-7251 definition: storedQueue
example (s : B256 → B256) :
    storedQueue s = (List.range ((s 3).toNat - (s 2).toNat)).map fun i => queueRecord s ((s 2).toNat + i) :=
  rfl

-- EIP-7251 definition: remainingQueue
example (w : State) : remainingQueue w = storedQueue (w.getStor addr).get :=
  rfl

-- EIP-7251 definition: submissionRecord
example (f : Exec.Frame) : submissionRecord f = f.sevm.caller.toBytes ++ f.sevm.data :=
  rfl

-- EIP-7251 definition: submissions
example (blocks : List KeptBlock) :
    submissions blocks =
      ((blocks.flatMap (KeptBlock.keptAt addr)).filter
        fun f => decide (f.sevm.caller ≠ systemAddress ∧ f.sevm.data.length = 96)).map submissionRecord :=
  rfl

-- EIP-7251 definition: records116
example (bytes : Bytes) :
    records116 bytes = (List.range ((bytes.length + 115) / 116)).map fun i => (bytes.drop (116 * i)).take 116 :=
  rfl

-- EIP-7251 definition: blockConsolidations
example (b : KeptBlock) :
    blockConsolidations b =
      (b.output.requests.filterMap fun r => match r with | 2 :: tail => some tail | _ => none).flatten :=
  rfl

-- EIP-7251 definition: emissions
example (blocks : List KeptBlock) :
    emissions blocks = blocks.flatMap fun b => records116 (blockConsolidations b) :=
  rfl

-- EIP-7251 definition: Fifo
example (blocks : List KeptBlock) (final : State) :
    Fifo blocks final ↔ submissions blocks = emissions blocks ++ remainingQueue final :=
  Iff.rfl

-- EIP-7251 constructor: CheckpointStart.mk
example (w : State) (code : installed w) (excess : word w 0 = B256.max) (count : word w 1 = 0)
    (head : word w 2 = 0) (tail : word w 3 = 0)
    (systemEmpty : w.getCode systemAddress = ByteArray.empty) :
    CheckpointStart w :=
  ⟨code, excess, count, head, tail, systemEmpty⟩

-- EIP-7251 constructor: ConsolidationCheckpointObservation.mk
example (checkpoint : BlockChain)
    (tip : ∃ t, checkpoint.blocks.getLast? = some t ∧ t.header.number = 22431083 ∧
      t.header.hash = 0x28fb2c1d988435955e569451c6ad772f7fb5e61cddd7463c7b60e933ed5ff237 ∧
      t.header.stateRoot = 0xab350e0fe349aef68947ede26295f8946c34ce3af5e3ec76f4b26ddeef29c0e3)
    (code : installed checkpoint.state) (excess : word checkpoint.state 0 = B256.max)
    (count : word checkpoint.state 1 = 0) (head : word checkpoint.state 2 = 0)
    (tail : word checkpoint.state 3 = 0)
    (systemEmpty : checkpoint.state.getCode systemAddress = ByteArray.empty) :
    ConsolidationCheckpointObservation checkpoint :=
  ⟨tip, code, excess, count, head, tail, systemEmpty⟩

-- EIP-7251 definition: SystemCallOk
example (benv : Benv) :
    SystemCallOk benv ↔
      (∃ post out, processCheckedSystemTransaction benv consolidationRequestPredeployAddress [] =
          .ok (post, out) ∧
        systemTransactionGas - out.gasLeft ≤ 114177) :=
  Iff.rfl

-- EIP-7251: system_call_succeeds
example {benv : Benv} (fork : CoveredFork benv.stat.fork)
    (installed : benv.state.getCode consolidationRequestPredeployAddress =
      Blanc.consolidationRequestCode) :
    SystemCallOk benv :=
  system_call_succeeds fork installed

-- EIP-7251 definition: excessAfter
example (e n : Nat) : excessAfter e n = (if e = 2 ^ 256 - 1 then 0 else e) + n - 1 :=
  rfl

-- EIP-7251 constructor: Bookkept.mk
example (pre post : State) (out : Bytes)
    (excess : (word post 0).toNat = excessAfter (word pre 0).toNat (word pre 1).toNat)
    (count : word post 1 = 0)
    (queue : remainingQueue post = (remainingQueue pre).drop 2)
    (reset : (word pre 3).toNat - (word pre 2).toNat ≤ 2 → word post 2 = 0 ∧ word post 3 = 0)
    (others : ∀ k : B256, 3 < k.toNat → word post k = word pre k)
    (output : out = ((remainingQueue pre).take 2).flatten) :
    Bookkept pre post out :=
  ⟨excess, count, queue, reset, others, output⟩

-- EIP-7251: system_call_bookkept
example {benv : Benv} (fork : CoveredFork benv.stat.fork) (installed : installed benv.state)
    (ordered : (word benv.state 2).toNat ≤ (word benv.state 3).toNat)
    (room : (word benv.state 3).toNat < 2 ^ 253)
    (noWrap : (if word benv.state 0 = B256.max then 0 else (word benv.state 0).toNat) +
      (word benv.state 1).toNat < 2 ^ 256) :
    ∃ post out, processCheckedSystemTransaction benv consolidationRequestPredeployAddress [] =
        .ok (post, out) ∧
      Bookkept benv.state post out.returnData :=
  system_call_bookkept fork installed ordered room noWrap

-- EIP-7251: fee_le_spec
example (excess : B256) : quotedFee excess ≤ SpecFee excess :=
  fee_le_spec excess

-- EIP-7251: fee_eq_spec_of_le
example {excess : B256} (le : excess.toNat ≤ 2892) : quotedFee excess = SpecFee excess :=
  fee_eq_spec_of_le le

-- EIP-7251: fee_lt_spec_2893
example {excess : B256} (at2893 : excess.toNat = 2893) : quotedFee excess < SpecFee excess :=
  fee_lt_spec_2893 at2893

-- EIP-7251 constructor: FreshEntry.mk
example (sevm : Sevm) (pre : Devm) (stack : pre.stack = []) (aligned : pre.memory.size % 32 = 0)
    (wf : Mem.Wf pre.memory) (lengthBound : sevm.data.length < 2 ^ 256) :
    FreshEntry sevm pre :=
  ⟨stack, aligned, wf, lengthBound⟩

-- EIP-7251 definition: submissionLog
example (sevm : Sevm) : submissionLog sevm = ⟨addr, [], sevm.caller.toBytes ++ sevm.data⟩ :=
  rfl

-- EIP-7251 constructor: Succeeded.dequeue
example : ∀ {sevm : Sevm} {pre post : Devm}, sevm.caller = systemAddress →
    post.state = Lift.RequestSystem.sysState
      Lift.SystemExecution.ConsolidationRequest.Amsterdam.sysShape pre.state addr →
    ((pre.getStorVal addr 2).toNat ≤ (pre.getStorVal addr 3).toNat →
      post.output = ((storedQueue (pre.getStor addr).get).take 2).flatten) →
    Succeeded sevm pre post :=
  @Succeeded.dequeue

-- EIP-7251 constructor: Succeeded.submission
example : ∀ {sevm : Sevm} {pre post : Devm}, sevm.caller ≠ systemAddress → sevm.data.length = 96 →
    sevm.isStatic = false → pre.getStorVal addr 0 ≠ B256.max →
    quotedFee (pre.getStorVal addr 0) ≤ sevm.value.toNat →
    post.getStor addr = Lift.ConsolidationRequest.submittedStorage sevm (pre.getStor addr) →
    (∀ a, a ≠ addr → post.getStor a = pre.getStor a) →
    post.logs = pre.logs ++ [submissionLog sevm] → post.output = pre.output →
    Succeeded sevm pre post :=
  @Succeeded.submission

-- EIP-7251 constructor: Succeeded.feeRead
example : ∀ {sevm : Sevm} {pre post : Devm}, sevm.caller ≠ systemAddress → sevm.data = [] →
    sevm.value = 0 → pre.getStorVal addr 0 ≠ B256.max →
    post.output = (quotedFee (pre.getStorVal addr 0)).toB256.toBytes →
    (∀ a, post.getStor a = pre.getStor a) → post.logs = pre.logs →
    Succeeded sevm pre post :=
  @Succeeded.feeRead

-- EIP-7251: exec_succeeded
example {sevm : Sevm} {pre post : Devm} (target : sevm.currentTarget = consolidationRequestPredeployAddress)
    (hcode : sevm.code = Blanc.consolidationRequestCode) (fork : CoveredFork sevm.benvStat.fork)
    (fresh : FreshEntry sevm pre) (exec : Exec 0 sevm pre (.ok post)) :
    Succeeded sevm pre post :=
  exec_succeeded target hcode fork fresh exec

-- EIP-7251 definition: SubmissionQueued
example (sevm : Sevm) (pre post : Devm) :
    SubmissionQueued sevm pre post ↔
      storedQueue (post.getStor addr).get =
        storedQueue (pre.getStor addr).get ++ [sevm.caller.toBytes ++ sevm.data] :=
  Iff.rfl

-- EIP-7251: submission_queued
example {sevm : Sevm} {pre post : Devm} (target : sevm.currentTarget = consolidationRequestPredeployAddress)
    (hcode : sevm.code = Blanc.consolidationRequestCode) (fork : CoveredFork sevm.benvStat.fork)
    (fresh : FreshEntry sevm pre) (user : sevm.caller ≠ systemAddress)
    (length : sevm.data.length = 96)
    (ordered : (pre.getStorVal addr 2).toNat ≤ (pre.getStorVal addr 3).toNat)
    (room : (pre.getStorVal addr 3).toNat < 2 ^ 253)
    (exec : Exec 0 sevm pre (.ok post)) :
    SubmissionQueued sevm pre post :=
  submission_queued target hcode fork fresh user length ordered room exec

-- EIP-7251 definition: submissionReads
example (sevm : Sevm) (b : Devm) :
    submissionReads sevm b =
      sloadCost sevm b 0 + sloadCost sevm (afterSload sevm b 0) 1 +
        sloadCost sevm (Lift.ConsolidationRequest.countStore sevm (afterSload sevm b 0)) 3 :=
  rfl

-- EIP-7251 definition: submissionStores
example (sevm : Sevm) (b : Devm) :
    submissionStores sevm b =
      sstoreCost sevm (afterSload sevm (afterSload sevm b 0) 1) 1
          (1 + Lift.ConsolidationRequest.countWord sevm (afterSload sevm b 0)) +
        Lift.ConsolidationRequest.recordWritesGas sevm (Lift.ConsolidationRequest.tailRead sevm
          (afterSload sevm b 0)) (Lift.ConsolidationRequest.submissionKey
          (Lift.ConsolidationRequest.tailWord sevm (afterSload sevm b 0))) +
        Lift.ConsolidationRequest.sourceGas Mem.empty + Lift.ConsolidationRequest.copyGas
          (Mem.empty.write 0 (Lift.ConsolidationRequest.sourceWord sevm).toBytes) +
        Lift.ConsolidationRequest.log0Gas (Lift.ConsolidationRequest.copyMemory sevm Mem.empty) 116 +
        sstoreCost sevm (Lift.ConsolidationRequest.logged sevm (afterSload sevm b 0) Mem.empty) 3
          (1 + Lift.ConsolidationRequest.tailWord sevm (afterSload sevm b 0)) :=
  rfl

-- EIP-7251 definition: submissionCharge
example (sevm : Sevm) (b : Devm) (iterations : Nat) :
    submissionCharge sevm b iterations =
      269 + 87 * iterations + submissionReads sevm b + submissionStores sevm b :=
  rfl

-- EIP-7251 definition: SubmissionLive
example (sevm : Sevm) (b : Devm) :
    SubmissionLive sevm b ↔
      ∀ G, gCallStipend < G → ∃ post, Nonempty (Exec 0 sevm (Lift.St b [] Mem.empty
        (G + submissionCharge sevm b (quotedIterations (b.getStorVal addr 0)))) (.ok post)) ∧
          post.gasLeft = G :=
  Iff.rfl

-- EIP-7251: submission_live
example {sevm : Sevm} {b : Devm} (target : sevm.currentTarget = consolidationRequestPredeployAddress)
    (hcode : sevm.code = Blanc.consolidationRequestCode) (fork : CoveredFork sevm.benvStat.fork)
    (user : sevm.caller ≠ systemAddress) (length : sevm.data.length = 96)
    (dynamic : sevm.isStatic = false) (active : b.getStorVal addr 0 ≠ B256.max)
    (paid : quotedFee (b.getStorVal addr 0) ≤ sevm.value.toNat) :
    SubmissionLive sevm b :=
  submission_live target hcode fork user length dynamic active paid

-- EIP-7251: history_fifo
example {cfg : ChainConfig} {checkpoint final : BlockChain} {blocks : List KeptBlock}
    (history : KeptHistory cfg checkpoint blocks final) (covered : ∀ b ∈ blocks, CoveredFork b.fork)
    (start : CheckpointStart checkpoint.state) (clean : HistoryClean blocks)
    (cap : (submissions blocks).length ≤ 2 ^ 253) :
    Fifo blocks final.state :=
  history_fifo history covered start clean cap

-- EIP-7251: history_fifo_mainnet
example {checkpoint final : BlockChain} {blocks : List KeptBlock}
    (history : KeptHistory mainnetChainConfig checkpoint blocks final)
    (obs : ConsolidationCheckpointObservation checkpoint)
    (clean : HistoryClean blocks) (cap : (submissions blocks).length ≤ 2 ^ 253) :
    Fifo blocks final.state :=
  history_fifo_mainnet history obs clean cap

end Blanc.Composition.ConsolidationRequestPublic

namespace Blanc.Lift.BeaconDeposit
open Jaune Blanc Blanc.ExecutionTrace

-- Beacon deposit: configuredHistory_solInv_sys
example {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {initialHistory : List B256}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (systemInstalled : SystemCodeInstalled checkpoint.state)
    (systemNoAuthority : ∀ p ∈ systemContracts, trace.NoAuthorityAt p.1)
    (systemNoFrame : ∀ p ∈ systemContracts, ∀ root ∈ trace.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ p.1)
    (checkpointEmpty : checkpoint.state.getCode 2 = ByteArray.empty)
    (noAuthority : trace.NoAuthorityAt 2)
    (noFrame : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ 2)
    (installed : checkpoint.state.getCode ca = code)
    (invariant : SolInv (checkpoint.state.getStor ca) initialHistory) :
    SolInv (future.state.getStor ca) (initialHistory ++ committedNodes ca trace) :=
  configuredHistory_solInv_sys trace systemInstalled systemNoAuthority systemNoFrame checkpointEmpty noAuthority noFrame installed invariant

end Blanc.Lift.BeaconDeposit

namespace Blanc.Lift.BeaconDeposit.Creation
open Jaune Blanc.BeaconDeposit Blanc.Lift.BeaconDeposit Blanc.ForkUniform

-- Beacon deposit: beacon_deploy_covered
example (f : Fork) (hf : CoveredFork f) :
    depositAddress = computeContractAddress deployer 0 ∧
    ∃ post, processCreateMessage (deployMsg.withFork f) = .ok post ∧
      (post.getCode depositAddress).toList = Blanc.Lift.BeaconDeposit.code.toList ∧
      SolInv (Devm.getStor post depositAddress) [] :=
  beacon_deploy_covered f hf

end Blanc.Lift.BeaconDeposit.Creation

namespace Blanc.Lift.BeaconDeposit
open Jaune
open Blanc.BeaconDeposit

-- Beacon deposit definition: SolInv
example (stor : Stor) (history : List B256) :
    SolInv stor history ↔
      (SolZeroHashesCorrect stor ∧ Inv Bytes.sha256 (solAcc stor) history) :=
  Iff.rfl

end Blanc.Lift.BeaconDeposit

namespace Blanc.Lift.BeaconDeposit
open Jaune Blanc.ExecutionTrace

-- Beacon deposit definition: depositCount
example {cfg : ChainConfig} {D B : BlockChain} (history : ConfiguredHistoryTraceIn HistFork cfg D B) :
    depositCount history = ((B.state.getStor Creation.depositAddress).get solCountSlot).toNat :=
  rfl

-- Beacon deposit definition: storedRoot
example {cfg : ChainConfig} {D B : BlockChain} (history : ConfiguredHistoryTraceIn HistFork cfg D B) :
    storedRoot history =
      BeaconDeposit.Acc.root Bytes.sha256 (solAcc (B.state.getStor Creation.depositAddress)) :=
  rfl

-- Beacon deposit definition: committedDeposits
example {cfg : ChainConfig} {D B : BlockChain} (history : ConfiguredHistoryTraceIn HistFork cfg D B) :
    committedDeposits history = committedNodesIn Creation.depositAddress history :=
  rfl

-- Beacon deposit definition: DepositHistory
example {cfg : ChainConfig} {D B : BlockChain} (history : ConfiguredHistoryTraceIn HistFork cfg D B) :
    DepositHistory history ↔
      (depositCount history = (committedDeposits history).length ∧
        storedRoot history =
          BeaconDeposit.mixedRootOf Bytes.sha256 (committedDeposits history)) :=
  Iff.rfl

-- Beacon deposit: beacon_deposits
example {B : BlockChain} (d : BeaconDeploymentTo B) :
    DepositHistory d.trace :=
  beacon_deposits d

-- Beacon deposit constructor: BeaconDeploymentTo.mk
example {B : BlockChain} (pre D C C1 P : BlockChain)
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre D)
    (atTwo : block.bodyTrace.decodedTxs[2]? = some Creation.HistoricalTx.tx)
    (receipt : Fin 5 × Receipt)
    (lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes (2 : Nat).toBytes)]? =
      some receipt)
    (succeeded : receipt.2.succeeded = true)
    (emptyLogs : block.blockOutput.blockLogs.filter
      (fun log => log.address == Creation.depositAddress) = [])
    (dc : ConfiguredHistoryTraceIn HistFork mainnetChainConfig D C)
    (first : ConfiguredBlockTraceIn HistFork mainnetChainConfig C C1)
    (tail : ConfiguredHistoryTraceIn HistFork mainnetChainConfig C1 P)
    (modern : ConfiguredHistoryTrace mainnetChainConfig P B)
    (anchors : HistoricalSeamAnchors D C P first.block)
    (checkpointEmpty : D.state.getCode 2 = ByteArray.empty)
    (historicalNoFrame : ∀ root ∈ ((dc.step first).append tail).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ (2 : Adr))
    (modernSystemNoAuthority : ∀ p ∈ systemContracts, modern.NoAuthorityAt p.1)
    (modernNoAuthority : modern.NoAuthorityAt 2)
    (modernNoFrame : ∀ root ∈ modern.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ (2 : Adr)) :
    BeaconDeploymentTo B :=
  ⟨pre, D, C, C1, P, block, atTwo, receipt, lookup, succeeded, emptyLogs, dc, first, tail, modern,
    anchors, checkpointEmpty, historicalNoFrame, modernSystemNoAuthority, modernNoAuthority,
    modernNoFrame⟩

end Blanc.Lift.BeaconDeposit
