import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit.Capstone
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolFinal
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolBoundary
import Blanc.Lift.Curve3Crv.CommittedHistory
import Blanc.Lift.Curve3Crv.Safe
import Blanc.Lift.Curve3Crv.Creation.Deploy
import Blanc.Lift.Curve3Crv.HistDeployment
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exclusion
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness.Top
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2.Top
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.ForkTop
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Envelope
import Blanc.Lift.WithdrawalRequest.WordFifo
import Blanc.Lift.WithdrawalRequest.HistoryFifo
import Blanc.Lift.WithdrawalRequest.WordDelivery
import Blanc.Composition.WithdrawalRequestDrainControl
import Blanc.Lift.WithdrawalRequest.SystemHistory
import Blanc.Lift.WithdrawalRequest.ExactFeeDomain
import Blanc.Composition.WithdrawalRequestFeeRefutation
import Blanc.Lift.WithdrawalRequest.NatLiveness
import Blanc.Lift.WithdrawalRequest.Creation.Deploy
import Blanc.Composition.UsdcToken
import Blanc.Lift.Usdc.ProxyOk
import Blanc.Lift.Usdc.Book
import Blanc.Lift.Usdc.HistFCore
import Blanc.Lift.Usdc.HistoryEndFoot
import Blanc.Lift.Usdc.Governance
import Blanc.Lift.Usdc.HistoryReplay
import Blanc.Lift.Token.Signed
import Blanc.Lift.Curve3Pool.Safe
import Blanc.Lift.Curve3Pool.Refine
import Blanc.Lift.Curve3Pool.Walk.Fallback
import Blanc.Lift.Curve3Pool.History
import Blanc.Lift.Curve3Pool.Ladder
import Blanc.Lift.Curve3Pool.ExchangeLive
import Blanc.Lift.Curve3Pool.AddLiquidityLive
import Blanc.Lift.Curve3Pool.RemoveLiquidityLiveness
import Blanc.Lift.Curve3Pool.RemoveImbalanceLive
import Blanc.Lift.Curve3Pool.OneCoinLive
import Blanc.Lift.Curve3Pool.HistoryLive
import Blanc.Composition.Curve3Pool3CrvHeadlines
import Blanc.Composition.Curve3Pool3CrvLiveWitness
import Blanc.Composition.Curve3Pool3CrvCapstoneFrame
import Blanc.Composition.Curve3Pool3CrvLiveEndKeep
import Blanc.Composition.Curve3Pool3CrvLiveEndKeepAL
import Blanc.Composition.Curve3Pool3CrvLiveEndKeepRLI
import Blanc.Composition.Curve3Pool3CrvCheckpoint
import Blanc.Composition.Curve3Pool3CrvWorld
import Blanc.Composition.Curve3Pool3CrvCapstone
import Blanc.Composition.Curve3Pool3CrvCapstoneTx
import Blanc.Composition.Curve3Pool3CrvSigningRecover
import Blanc.Composition.Curve3Pool3CrvCoinAnswers
import Blanc.Lift.StableSwapNewton.D
import Blanc.Lift.StableSwapNewton.Y
import Blanc.Lift.Curve3Pool.U4Frames
import Blanc.Lift.Curve3Pool.U4ExactnessRefute
import Blanc.Lift.Curve3Pool.U4GetYRefute
import Blanc.Lift.Curve3Pool.U3Refute
import Blanc.Lift.Curve3Pool.U3History
import Blanc.Lift.Curve3Pool.U3Ledger
import Blanc.Lift.Curve3Pool.U3Bounds
import Blanc.Composition.Curve3Pool3CrvU3
import Blanc.Lift.Curve3Pool.AmpHistory
import Blanc.Lift.Curve3Pool.U5
import Blanc.Composition.Curve3PoolSupply
import Blanc.Lift.Token.Supply
import Blanc.Composition.Curve3CrvTokenCore
import Blanc.Composition.Curve3CrvPositional
import Blanc.Lift.Curve3Pool.Creation.Deploy
import Blanc.Lift.StaticGasMessage
import Blanc.Lift.Curve3Pool.RemoveLiquidityExactFrame
import Blanc.Lift.Curve3Pool.ExchangeExactLive
import Blanc.Lift.Curve3Pool.AddLiquidityExactFrame
import Blanc.Lift.Curve3Pool.RemoveLiquidityImbalanceExactFrame
import Blanc.Lift.Curve3Pool.OneCoinExactFrame
import Blanc.Lift.Curve3Pool.ExactMessage
import Blanc.Lift.Curve3Pool.HistoryLiveExact
import Blanc.Composition.Curve3Pool3CrvHeadlinesExact
import Blanc.Composition.Curve3Pool3CrvExactWitness
import Blanc.Composition.Curve3Pool3CrvExactLiteralHeadlines
import Blanc.Lift.WithdrawalRequest.HeadlineFee
import Blanc.Lift.WithdrawalRequest.HeadlineSystem
import Blanc.Lift.WithdrawalRequest.HeadlineHistory
import Blanc.Lift.WithdrawalRequest.FifoDrainControl
import Blanc.Composition.WithdrawalRequestFeeHeadline
import Blanc.Lift.Curve3Crv.Headline
import Blanc.Lift.RootMessages
-- `open private` below; no longer reached transitively under mathlib 4.35.
import Batteries.Tactic.OpenPrivate
import Blanc.Lift.Usdc.AllowanceQuiet

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

































open scoped BigOperators





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






namespace Blanc.Lift.Curve3Crv
open Jaune Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

-- Curve 3Crv: c3crv_history_committed_derived
example {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {initial : Blanc.Curve3Crv.State}
    {initialKeys : Key → Prop}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode ca).toList = c3crvSem.image)
    (invariant : VyInv (checkpoint.state.getStor ca) initial initialKeys)
    (fresh : FreshKeys initialKeys (historyTouchedKeys ca trace)) :
    some (future.state.getCode ca).toList = c3crvSem.image ∧
      ∃ s, InvRun initial (committedInvocations ca trace) s ∧
        runInvocations initial (committedInvocations ca trace) = some s ∧
        VyInv (future.state.getStor ca) s
          (Key.extend initialKeys (invocationKeys (committedInvocations ca trace))) ∧
        Blanc.Curve3Crv.Conserved s :=
  c3crv_history_committed_derived trace installed invariant fresh

end Blanc.Lift.Curve3Crv

namespace Blanc.Lift.Curve3Crv
open Jaune
open Blanc.Curve3Crv (Call)

-- Curve 3Crv: c3crv_frame_refines
example {sevm : Sevm} {pre post : Devm} {s : Curve3Crv.State}
    {K : Key → Prop}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hcd : sevm.data.length < 2 ^ 256) (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty)
    (houtput : pre.output = [])
    (hinv : VyInv (Devm.getStor pre sevm.currentTarget) s K)
    (hfresh : FreshKeys K (callKeys sevm.caller (decodeCall sevm)))
    (exc : Exec 0 sevm pre (.ok post)) :
    (IsWriter (decodeCall sevm) →
      ∃ ow : Option B256, (∀ w, ow = some w → OwnerAnswer sevm pre s.minter w) ∧
        ∃ o, Curve3Crv.step (c3ctx sevm ow) (decodeCall sevm) s = .ok o ∧
          VyInv (Devm.getStor post sevm.currentTarget) o.1
            (Key.extend K (callKeys sevm.caller (decodeCall sevm))) ∧
          (∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor pre a) ∧
          post.logs = pre.logs ++ o.2.1.map (eventLog sevm.currentTarget) ∧
          RetOut post.output o.2.2) ∧
    (¬ IsWriter (decodeCall sevm) →
      (∀ a, Devm.getStor post a = Devm.getStor pre a) ∧ post.logs = pre.logs ∧
        ∃ o, Curve3Crv.step (c3ctx sevm none) (decodeCall sevm) s = .ok o ∧
          RetOut post.output o.2.2) :=
  c3crv_frame_refines hcode hfork hcd hstack hmem houtput hinv hfresh exc

end Blanc.Lift.Curve3Crv

namespace Blanc.Lift.Curve3Crv.Creation
open Jaune Blanc.Lift Blanc.Lift.Curve3Crv Blanc.ForkUniform

-- Curve 3Crv: curve_deploy_covered
example (f : Fork) (hf : CoveredFork f) :
    tokenAddress = computeContractAddress deployer 42 ∧
    ∃ post, processCreateMessage (deployMsg.withFork f) = .ok post ∧
      (post.getCode tokenAddress).toList = Blanc.Lift.Curve3Crv.code.toList ∧
      Devm.getStor post tokenAddress = deployedStor deployer.toB256 ∧
      VyInv (Devm.getStor post tokenAddress) (curveDeployedState deployer) (fun _ => False) :=
  curve_deploy_covered f hf

end Blanc.Lift.Curve3Crv.Creation

namespace Blanc.Lift.Curve3Crv
open Jaune Blanc.ExecutionTrace Blanc.Lift.Curve3Crv.Creation

-- Curve 3Crv constructor: C3crvDeploymentTo.mk
example {checkpoint : BlockChain} (pre completed : BlockChain)
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed)
    (number : block.block.header.number = 10809467)
    (time : block.block.header.timestamp = 1599414946)
    (entry : Bytes ⊕ Tx) (slot : block.block.txs[76]? = some entry)
    (decoded : decodeTx block.fork.ruleSet entry = .ok HistoricalTx.tx)
    (receipt : Fin 5 × Receipt)
    (lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes (76 : Nat).toBytes)]? =
      some receipt)
    (succeeded : receipt.2.succeeded = true)
    (history : ConfiguredHistoryTraceIn HistFork mainnetChainConfig completed checkpoint)
    (fresh : FreshKeys (fun _ => False)
      (midTouchedKeysIn tokenAddress
        ((MidHistoryTraceIn.tail block (block.bodyTrace.txSplitOfSlot slot decoded)).append
          history))) :
    C3crvDeploymentTo checkpoint :=
  ⟨pre, completed, block, number, time, entry, slot, decoded, receipt, lookup, succeeded,
    history, fresh⟩

end Blanc.Lift.Curve3Crv

namespace Blanc.Lift.Curve3Crv.Creation.HistoricalTx
open Jaune Blanc Blanc.ExecutionTrace

-- Curve 3Crv: HistoricalTx.actual_block_cut
example {pre D : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre D)
    (number : block.block.header.number = 10809467)
    (timestamp : block.block.header.timestamp = 1599414946) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i) (sameTx : cut.tx = tx)
    {receipt : Fin 5 × Receipt}
    (lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes cut.index.toBytes)]? =
      some receipt) (succeeded : receipt.2.succeeded = true) :
    (cut.txState.getCode tokenAddress).toList = Blanc.Lift.Curve3Crv.code.toList ∧
      cut.txState.getStor tokenAddress = deployedStor deployer.toB256 ∧
      cut.txBout.blockLogs = cut.bout.blockLogs ++ [creationLog] ∧
      cut.txBout.blockGasUsed = cut.bout.blockGasUsed + 678343 :=
  actual_block_cut block number timestamp cut sameTx lookup succeeded

end Blanc.Lift.Curve3Crv.Creation.HistoricalTx



namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed
open Jaune Blanc.LockExclusion
open Jaune.Exec.Deriv (ParentPrefix)

-- Vyper V+: vplus_exclusion
example {sevm : Sevm} {pre : Devm} {out : Execution}
    (R : Exec 0 sevm pre out) (hfork : CoveredFork sevm.benvStat.fork) {P : Adr}
    (hP : pre.getCode P = forwarderCode curvePlainImpl847e ∨ pre.getCode P = code)
    (hI : pre.getCode curvePlainImpl847e = code)
    (hroot : sevm.currentTarget = P → sevm.code = pre.getCode P)
    (hash : lockL.HashAvoidIn P R)
    {F h c : Exec.Deriv} (hF : F ∈ Exec.rawFrameRoots R)
    (active : ActiveRel P F h) (spawn : Spawns h c)
    {G : Exec.Deriv} (hG : G ∈ Exec.rawFrameRoots c.exc) :
    ¬ lockL.Enters P G :=
  vplus_exclusion R hfork hP hI hroot hash hF active spawn hG

end Blanc.Lift.VyperNonreentrantDeployed.Fixed

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness
open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.LockExclusion Blanc.ForkUniform
open Jaune.Exec.Deriv (ParentPrefix ParentStep)

-- Vyper V+: vplus_witness_covered
example (g : Fork) (hg : CoveredFork g) :
    (msg0.withFork g).benv.stat.fork = g ∧ (f0.withFork g).enter = .run (e0.withFork g) ∧
    (e0.withFork g).pc = 0 ∧
    (∀ out, Exec 0 (e0.withFork g).sta (e0.withFork g).dyna out → out = .error (.revert, dF)) ∧
    ∃ (out : Execution) (R : Exec 0 (e0.withFork g).sta (e0.withFork g).dyna out)
      (h c G : Exec.Deriv),
      -- the antecedent of `vplus_exclusion`, for `F` the root of `R`
      (⟨0, (e0.withFork g).sta, (e0.withFork g).dyna, out, R⟩ : Exec.Deriv) ∈
        Exec.rawFrameRoots R ∧
      ActiveRel curvePlainImpl847e ⟨0, (e0.withFork g).sta, (e0.withFork g).dyna, out, R⟩ h ∧
      Spawns h c ∧
      -- the premises of `vplus_exclusion_impl`, for this `R`
      CoveredFork (e0.withFork g).sta.benvStat.fork ∧
      (e0.withFork g).dyna.getCode curvePlainImpl847e = code ∧
      ((e0.withFork g).sta.currentTarget = curvePlainImpl847e →
        (e0.withFork g).sta.code = (e0.withFork g).dyna.getCode curvePlainImpl847e) ∧
      lockL.HashAvoidIn curvePlainImpl847e R ∧
      -- the spawn: `remove_liquidity`'s `STATICCALL` of the coin `R`
      h.pc = 0x337a ∧ Ninst.At h.sevm.code h.pc (.exec .staticcall) ∧
      c.sevm.currentTarget = readerAddress ∧ c.sevm.code = Reader.code ∧
      -- the reentry into `get_virtual_price()`, refused
      G ∈ Exec.rawFrameRoots c.exc ∧ CPFrame curvePlainImpl847e code G ∧
      G.sevm.data = [0xbb, 0x7b, 0x8b, 0x80] ∧ G.exn = .error (.revert, dG) ∧
      (∀ x, ParentPrefix G x → x.pc ∉ lockBodies) ∧
      ¬ lockL.Enters curvePlainImpl847e G :=
  vplus_witness_covered g hg

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2
open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.LockExclusion Blanc.ForkUniform
open Jaune.Exec.Deriv (ParentPrefix ParentStep)

-- Vyper V+: vplus_witness2_covered
example (g : Fork) (hg : CoveredFork g) :
    (msgTop.withFork g).benv.stat.fork = g ∧
    (frameTop.withFork g).enter = .run (eTop.withFork g) ∧ (eTop.withFork g).pc = 0 ∧
    (∀ out, Exec 0 (eTop.withFork g).sta (eTop.withFork g).dyna out → out = .ok dTop) ∧
    ∃ (out : Execution) (R : Exec 0 (eTop.withFork g).sta (eTop.withFork g).dyna out)
      (F h c q G : Exec.Deriv),
      -- the premises of `vplus_exclusion_stethPool`, for this `R`
      CoveredFork (eTop.withFork g).sta.benvStat.fork ∧
      (eTop.withFork g).dyna.getCode curveStethPool847e = forwarderCode curvePlainImpl847e ∧
      (eTop.withFork g).dyna.getCode curvePlainImpl847e = code ∧
      ((eTop.withFork g).sta.currentTarget = curveStethPool847e →
        (eTop.withFork g).sta.code = (eTop.withFork g).dyna.getCode curveStethPool847e) ∧
      lockL.HashAvoidIn curveStethPool847e R ∧
      -- its antecedent: the pool body, active, spawns the receiver with the ETH payment
      F ∈ Exec.rawFrameRoots R ∧ ActiveRel curveStethPool847e F h ∧ Spawns h c ∧
      h.pc = 7427 ∧ Ninst.At h.sevm.code h.pc (.exec .call) ∧
      c.sevm.currentTarget = receiverAddress ∧ c.sevm.code = Receiver.code ∧
      c.sevm.value.toNat = 100 ∧
      -- the reentry through the forwarder, refused at the lock check
      q ∈ Exec.rawFrameRoots c.exc ∧ q.sevm.currentTarget = curveStethPool847e ∧
      q.sevm.code = forwarderCode curvePlainImpl847e ∧ G ∈ Exec.rawFrameRoots q.exc ∧
      G ∈ Exec.rawFrameRoots c.exc ∧ CPFrame curveStethPool847e code G ∧
      G.sevm.data = reentryCall ∧ G.exn = .error (.revert, dRe) ∧
      (∀ x, ParentPrefix G x → x.pc ∉ lockBodies) ∧
      (∃ y y', ParentPrefix G y ∧ y.pc = 0x53 ∧ ParentPrefix y y' ∧ y'.pc = 0x477e) ∧
      ¬ lockL.Enters curveStethPool847e G ∧
      -- the transaction commits
      out = .ok dTop ∧
      ((eTop.withFork g).dyna.getBal curveStethPool847e).toNat = 1000 ∧
      (dTop.getBal curveStethPool847e).toNat = 900 ∧
      ((eTop.withFork g).dyna.getBal receiverAddress).toNat = 0 ∧
      (dTop.getBal receiverAddress).toNat = 100 ∧
      lockAt curveStethPool847e 0 (eTop.withFork g).dyna = (3 : Nat).toB256 ∧
      lockAt curveStethPool847e 0 dTop = (3 : Nat).toB256 :=
  vplus_witness2_covered g hg

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Top
open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.Witness.Boundary Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree
variable {g : Fork}

-- Vyper V−: vminus_witness_covered
example (g : Fork) (hg : CoveredFork g) :
    ∃ post0 post1 : Devm,
      -- the top-level message call, under `g`
      (msg0.withFork g).benv.stat.fork = g ∧ CoveredFork (msg0.withFork g).benv.stat.fork ∧
      (f0.withFork g).enter = .run (e0.withFork g) ∧
      Nonempty (Exec (e0.withFork g).pc (e0.withFork g).sta (e0.withFork g).dyna (.ok post0)) ∧
      processMessage (msg0.withFork g) = .ok post0 ∧ post0.error = none ∧
      post0.output = word 100 ++ word 100 ∧
      -- (a) frame 1: `P` running the implementation's `remove_liquidity`, spawned by the proxy
      stepN 11 (e0.withFork g) = some (e0_31.withFork g) ∧
      SpawnedBy (e0_31.withFork g).sta (e0_31.withFork g).dyna .delegatecall
        ⟨0, sevm1.withFork g, pre1⟩ ∧
      (sevm1.withFork g).currentTarget = proxyAddress ∧ (sevm1.withFork g).code = code ∧
      (sevm1.withFork g).data = removeCalldata ∧
      Nonempty (Exec 0 (sevm1.withFork g) pre1 (.ok post1)) ∧ post1.error = none ∧
      -- frame 1 takes slot 2 and calls `A` holding it
      storOf pre1.state proxyAddress (2 : Nat).toB256 = 0 ∧
      wrun fs1 (sevm1.withFork g) 339 c0 = .cont cfg339 ∧ Agree cfg339 ∧
      storOf cfg339.devm.state proxyAddress (2 : Nat).toB256 = (1 : Nat).toB256 ∧
      SpawnedBy (sevm1.withFork g) cfg339.devm .call (e2.withFork g) ∧
      (e2.withFork g).sta.currentTarget = attackerAddress ∧
      (e2.withFork g).sta.code = attackerCode ∧
      -- `A` calls `P`; the proxy delegates to the implementation: frame 4
      wrun fs2 (e2.withFork g).sta 24 cc2 = .cont aCall ∧
      SpawnedBy (e2.withFork g).sta aCall.devm .call (e3.withFork g) ∧
      (e3.withFork g).sta.currentTarget = proxyAddress ∧
      (e3.withFork g).sta.code = proxyCode ∧
      stepN 11 (e3.withFork g) = some (e31.withFork g) ∧
      SpawnedBy (e31.withFork g).sta (e31.withFork g).dyna .delegatecall (e4.withFork g) ∧
      (e4.withFork g).sta.currentTarget = proxyAddress ∧ (e4.withFork g).sta.code = code ∧
      (e4.withFork g).sta.data = addCalldata ∧
      -- frame 4 is entered while slot 2 = 1, its own lock (slot 0) free
      storOf e4.dyna.state proxyAddress (2 : Nat).toB256 = (1 : Nat).toB256 ∧
      storOf e4.dyna.state proxyAddress (0 : Nat).toB256 = 0 ∧
      Nonempty (Exec (e4.withFork g).pc (e4.withFork g).sta (e4.withFork g).dyna (.ok post4)) ∧
      -- frame 4 reaches `add_liquidity`'s body with slot 0 taken and slot 2 still held
      (∃ cB : Cfg, wrun fs1 (e4.withFork g).sta 2625 c4 = .cont cB ∧ Agree cB ∧
        cB.f = t_0370_c63 ∧
        storOf cB.devm.state proxyAddress (0 : Nat).toB256 = (1 : Nat).toB256 ∧
        storOf cB.devm.state proxyAddress (2 : Nat).toB256 = (1 : Nat).toB256) ∧
      (storOf post4.state proxyAddress balanceOfASlot.toB256).toNat = 2106 ∧
      storOf post4.state proxyAddress (0 : Nat).toB256 = 0 ∧
      -- (b) the two guards in the deployed bytes: slot 2 and slot 0
      (code.getInst 6900 = some (.next (.push [0x02] (by decide))) ∧
        code.getInst 6902 = some (.next (.reg .sload)) ∧
        code.getInst 6911 = some (.next (.reg .sstore))) ∧
      (code.getInst 88 = some (.next (.push [0x00] (by decide))) ∧
        code.getInst 90 = some (.next (.reg .sload)) ∧
        code.getInst 99 = some (.next (.reg .sstore))) ∧
      (storOf post1.state proxyAddress (2 : Nat).toB256).toNat = 0 ∧
      -- (c) the harm
      (storOf post0.state proxyAddress (26 : Nat).toB256).toNat = 1800 ∧
      (storOf post0.state proxyAddress balanceOfASlot.toB256).toNat = 1906 ∧
      (storOf post0.state proxyAddress (26 : Nat).toB256).toNat <
        (storOf post0.state proxyAddress balanceOfASlot.toB256).toNat :=
  vminus_witness_covered g hg

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Top

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC
open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Witness Blanc.ForkUniform
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop
variable {g : Fork}

-- Vyper V−: vminus_txC_process
example (g : Fork) (hg : CoveredFork g) (bout : BlockOutput)
    (hroom : bout.blockGasUsed + txC.gas ≤ 60000000) :
    txC.gas < 2 ^ 24 ∧
    ∃ (st : State) (bout' : BlockOutput),
      processTransaction (benvPre.withFork g) bout txC 0 = .ok (st, bout') ∧
      (storOf st proxyAddress (26 : Nat).toB256).toNat = 1800 ∧
      (storOf st proxyAddress balanceOfA2Slot.toB256).toNat = 1906 ∧
      (storOf st proxyAddress (26 : Nat).toB256).toNat <
        (storOf st proxyAddress balanceOfA2Slot.toB256).toNat :=
  vminus_txC_process g hg bout hroom

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC

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




namespace Blanc.Lift.Curve3Crv
open Jaune
open Blanc.Curve3Crv (Conserved)

-- Curve 3Crv definition: VyInv
example (stor : Stor) (s : Curve3Crv.State) (K : Key → Prop) :
    VyInv stor s K ↔
      (stor.get vyDecimalsSlot = s.decimals) ∧
      (stor.get vySupplySlot = s.totalSupply) ∧
      (stor.get vyMinterSlot = s.minter.toB256) ∧
      (VyStr stor vyNameBase 2 s.name) ∧
      (VyStr stor vySymbolBase 1 s.symbol) ∧
      (∀ k, K k → stor.get k.slot = k.val s) ∧
      (∀ k, ¬ K k → k.val s = 0) ∧
      (∀ x, stor.get x ≠ 0 → x ∈ vyFixedSlots ∨ ∃ k, K k ∧ k.slot = x) ∧
      (∀ k k', K k → K k' → k.slot = k'.slot → k = k') ∧
      (∀ k, K k → k.slot ∉ vyFixedSlots) ∧
      (Conserved s) :=
  ⟨fun h => ⟨h.decimals, h.supply, h.minter, h.name, h.symbol, h.known, h.unknown, h.support, h.inj, h.apart, h.conserved⟩, fun ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ => ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩⟩

end Blanc.Lift.Curve3Crv

namespace Blanc.Curve3Crv
open Jaune

-- Curve 3Crv definition: Conserved
example (s : State) :
    Conserved s ↔
      (s.totalSupply.toNat = sum s.balanceOf) :=
  Iff.rfl

end Blanc.Curve3Crv

namespace Blanc.Lift.Curve3Crv
open Jaune
open Blanc.Curve3Crv (Call Ctx Event Ret)

-- Curve 3Crv definition: OwnerAnswer
example (sevm : Sevm) (b : Devm) (m : Adr) (w : B256) :
    OwnerAnswer sevm b m w ↔
      (∃ out, StaticAnswered sevm b m ownerCalldata out ∧ 32 ≤ out.length ∧
    Bytes.toB256 (out.take 32) = w) :=
  Iff.rfl

-- Curve 3Crv definition: OwnerAnswerH
example (sevm : Sevm) (b : Devm) (m : Adr) (w : B256) :
    OwnerAnswerH sevm b m w ↔
      (∃ out, StaticAnsweredH sevm b m ownerCalldata out ∧ 32 ≤ out.length ∧
    Bytes.toB256 (out.take 32) = w) :=
  Iff.rfl

end Blanc.Lift.Curve3Crv



namespace Blanc.LockExclusion
open Jaune
open Jaune.Exec.Deriv

-- Vyper V± definition: CPFrame
example (P : Adr) (code : ByteArray) (F : Exec.Deriv) :
    CPFrame P code F ↔
      (F.pc = 0 ∧ F.sevm.currentTarget = P ∧ F.sevm.code = code) :=
  Iff.rfl

end Blanc.LockExclusion

namespace Blanc.LockExclusion.LockSpec
open Jaune
open Jaune.Exec.Deriv

-- Vyper V± definition: Enters
example (L : LockSpec) (P : Adr) (G : Exec.Deriv) :
    Enters L P G ↔
      (CPFrame P L.code G ∧ ∃ x, ParentPrefix G x ∧ x.pc ∈ L.bodies) :=
  Iff.rfl

end Blanc.LockExclusion.LockSpec

namespace Blanc.LockExclusion.LockSpec
open Jaune
open Jaune.Exec.Deriv

-- Vyper V± definition: HashAvoidIn
example (L : LockSpec) (P : Adr)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) :
    HashAvoidIn L P run ↔
      (∀ G ∈ Exec.rawFrameRoots run, CPFrame P L.code G → HashAvoid L.slot G) :=
  Iff.rfl

end Blanc.LockExclusion.LockSpec

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed
open Jaune Blanc.LockExclusion
open Jaune.Exec.Deriv (ParentPrefix)

-- Vyper V+ definition: ActiveRel
example (P : Adr) (F h : Exec.Deriv) :
    ActiveRel P F h ↔
      (CPFrame P code F ∧ ParentPrefix F h ∧
    ∃ b, ParentPrefix F b ∧ ParentPrefix b h ∧ b.pc ∈ lockMutBodies ∧
      ∀ x, ParentPrefix b x → ParentPrefix x h → x ≠ h → x.pc ∉ lockReleasePcs) :=
  Iff.rfl

end Blanc.Lift.VyperNonreentrantDeployed.Fixed

namespace Blanc.Lift.Witness
open Jaune Blanc.Lift

-- Vyper V− definition: SpawnedBy
example (sevm : Sevm) (devm : Devm) (x : Xinst) (child : Evm) :
    SpawnedBy sevm devm x child ↔
      (∃ f rsm, Xinst.step sevm devm x = .spawn f rsm ∧ f.enter = .run child) :=
  Iff.rfl

end Blanc.Lift.Witness

namespace Blanc.Lift.Witness
open Jaune Blanc.Lift

-- Vyper V− definition: Agree
example (c : Cfg) :
    Agree c ↔
      ((∀ x, x ∈ c.devm.accessedStorageKeys ↔ x ∈ c.keys) ∧
    (∀ a, a ∈ c.devm.accessedAddresses ↔ a ∈ c.adrs) ∧
    (∀ a k, storOf c.devm.state a k = lookupS c.stor a k) ∧
    AcctAgree c.devm.state c.acs) :=
  Iff.rfl

end Blanc.Lift.Witness

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

namespace Blanc.Lift.UniswapV2Pair
open Jaune Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

-- Uniswap V2 Pair definition: Blanc.Exec.Frame.obsAt
example (pair : Adr) (frame : Exec.Frame)  :
    Blanc.Exec.Frame.obsAt pair frame =
      (if frame.sevm.currentTarget = pair ∧ frame.sevm.isStatic = false then [frame] else []) :=
  rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

-- Uniswap V2 Pair definition: Blanc.Exec.Frame.subtreeAt
example (pair : Adr) (f : Exec.Frame)  :
    Blanc.Exec.Frame.subtreeAt pair f =
      ((Exec.committedFrames f.run).flatMap (Blanc.Exec.Frame.obsAt pair)) :=
  rfl

end Blanc.Lift.UniswapV2Pair





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
namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit
open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.LockExclusion
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Fund
open Jaune.Exec.Deriv (ParentPrefix)
open Blanc.Lift.VyperNonreentrantDeployed.Fixed (ActiveRel lockBodies lockL)

example : ∀ (fork : Fork) (hfork : CoveredFork fork),
    ∃ postI postP postInit postOracle postT postR postA postD postX : Devm,

      processCreateMessage (implCreateMsg fork initialWorld) = .ok postI ∧ postI.error = none ∧
      processCreateMessage (cloneCreateMsg fork postI.state) = .ok postP ∧ postP.error = none ∧
      processMessage (initMsg fork postP.state) = .ok postInit ∧ postInit.error = none ∧
      processMessage (oracleMsg fork postInit.state) = .ok postOracle ∧
      postOracle.error = none ∧ CleanPool postOracle.state ∧
      processCreateMessage (tokenCreateMsg fork postOracle.state) = .ok postT ∧
      postT.error = none ∧
      processCreateMessage (receiverCreateMsg fork postT.state) = .ok postR ∧
      postR.error = none ∧
      processMessage (approveMsg fork postR.state) = .ok postA ∧ postA.error = none ∧
      processMessage (addMsg fork postA.state) = .ok postD ∧ postD.error = none ∧

      Checkpoint postD.state ∧
      (storOf postD.state proxyAddr 0x16).toNat =
        Blanc.ledgerSumOn {creator} (fun holder => storOf postD.state proxyAddr (lpSlot holder)) ∧
      storOf postD.state proxyAddr 0x16 = 2000 ∧

      processMessage (removeMsg fork postD.state) = .ok postX ∧ postX.error = none ∧
      postX.gasLeft = 920078 ∧
      (Frame.ofCall (removeMsg fork postD.state)).enter = .run (eTop.re fork world8) ∧
      postD.state = world8 ∧ postX = dTop ∧
      ∃ (out : Execution) (R : Exec 0 (reS eTop.sta fork) eTop.dyna out)
        (F h c q G : Exec.Deriv),

        F ∈ Exec.rawFrameRoots R ∧ ActiveRel proxyAddr F h ∧ Spawns h c ∧ h.pc = 7427 ∧
        c.sevm.currentTarget = receiverAddr ∧ c.sevm.value.toNat = 100 ∧

        q ∈ Exec.rawFrameRoots c.exc ∧ q.sevm.currentTarget = proxyAddr ∧
        G ∈ Exec.rawFrameRoots q.exc ∧ CPFrame proxyAddr code G ∧ G.sevm.data = reentryData ∧
        G.exn = .error (.revert, dRe) ∧ (∀ x, ParentPrefix G x → x.pc ∉ lockBodies) ∧
        (∃ y y', ParentPrefix G y ∧ y.pc = 0x53 ∧ ParentPrefix y y' ∧ y'.pc = 0x477e) ∧

        lockL.HashAvoidIn proxyAddr R ∧
        (∀ G' ∈ Exec.rawFrameRoots c.exc, ¬ lockL.Enters proxyAddr G') ∧
        ¬ lockL.Enters proxyAddr G ∧

        out = .ok postX ∧
        (storOf postX.state proxyAddr 0x16).toNat =
          Blanc.ledgerSumOn {creator} (fun holder => storOf postX.state proxyAddr (lpSlot holder)) ∧
        storOf postX.state proxyAddr 0x16 = 1800 ∧
        (postX.state.get receiverAddr).bal = 100 ∧
        storOf postX.state tokenAddr receiverAddr.toB256 = 100 ∧
        (postX.state.get proxyAddr).bal = 900 ∧ storOf postX.state proxyAddr 0 = 3 :=
  @vplus_reachable_capstone

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit

-- Paper review 2 statement: vminus_reachable_capstone
namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol


example : CapstoneStmt :=
  @vminus_reachable_capstone

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

-- Paper review 2 statement: vminus_reach_violation
namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol


example : ViolationStmt :=
  @vminus_reach_violation

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

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
namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach (creator creatorFunds initialWorld rootBenv rootTenv)
open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed

example (g : Fork) (W : State) (post : Devm) :
    ViolationAt g W post = (
      processMessage (violMsg g W) = .ok post ∧ post.error = none ∧ post.gasLeft = gasV ∧
      storOf post.state proxyAddr 26 = 1800 ∧ storOf post.state proxyAddr lpSlotA = 1906 ∧
      (storOf post.state proxyAddr 26).toNat < (storOf post.state proxyAddr lpSlotA).toNat ∧
      storOf post.state proxyAddr 2 = 0 ∧
      ∃ (e0 e1 e1' e2 e3 e4 e4' e5 : Evm) (c0 cR c2 c339 c3 cA c5 cB : Cfg) (post2 post5 : Devm),

        (Frame.ofCall (violMsg g W)).enter = .run e0 ∧ Nonempty (Exec e0.pc e0.sta e0.dyna (.ok post)) ∧
        e0.sta.caller = creator ∧ e0.sta.currentTarget = attackerAddr ∧ e0.sta.code = AttackerR.code ∧
        c0.devm = e0.dyna ∧ c0.f = AttackerR.t_0000_c0 ∧ c0.K = [] ∧ Agree c0 ∧
        wrun fsA e0.sta 33 c0 = .cont cR ∧ Agree cR ∧ SpawnedBy e0.sta cR.devm .call e1 ∧
        e1.sta.currentTarget = proxyAddr ∧ e1.sta.code = fwdCode ∧
        stepN 11 e1 = some e1' ∧ SpawnedBy e1'.sta e1'.dyna .delegatecall e2 ∧

        e2.sta.currentTarget = proxyAddr ∧ e2.sta.code = Vulnerable.code ∧ e2.sta.data = removeCallR ∧
        Nonempty (Exec e2.pc e2.sta e2.dyna (.ok post2)) ∧ post2.error = none ∧
        storOf e2.dyna.state proxyAddr 2 = 0 ∧
        c2.devm = e2.dyna ∧ c2.f = Vulnerable.t_0000_c0 ∧ c2.K = [] ∧ Agree c2 ∧
        wrun fsI e2.sta 339 c2 = .cont c339 ∧ Agree c339 ∧
        storOf c339.devm.state proxyAddr 2 = 1 ∧ storOf c339.devm.state proxyAddr 26 = 2000 ∧
        SpawnedBy e2.sta c339.devm .call e3 ∧
        e3.sta.currentTarget = attackerAddr ∧ e3.sta.code = AttackerR.code ∧ e3.sta.value = 100 ∧

        c3.devm = e3.dyna ∧ c3.f = AttackerR.t_0000_c0 ∧ c3.K = [] ∧ Agree c3 ∧
        wrun fsA e3.sta 32 c3 = .cont cA ∧ Agree cA ∧ SpawnedBy e3.sta cA.devm .call e4 ∧
        e4.sta.currentTarget = proxyAddr ∧ e4.sta.code = fwdCode ∧ e4.sta.value = 100 ∧
        stepN 11 e4 = some e4' ∧ SpawnedBy e4'.sta e4'.dyna .delegatecall e5 ∧
        e5.sta.currentTarget = proxyAddr ∧ e5.sta.code = Vulnerable.code ∧ e5.sta.data = reAddCall ∧
        storOf e5.dyna.state proxyAddr 2 = 1 ∧ storOf e5.dyna.state proxyAddr 0 = 0 ∧
        Nonempty (Exec e5.pc e5.sta e5.dyna (.ok post5)) ∧ post5.error = none ∧
        c5.devm = e5.dyna ∧ c5.f = Vulnerable.t_0000_c0 ∧ c5.K = [] ∧ Agree c5 ∧
        wrun fsI e5.sta 2625 c5 = .cont cB ∧ Agree cB ∧ cB.f = Vulnerable.t_0370_c63 ∧
        storOf cB.devm.state proxyAddr 0 = 1 ∧ storOf cB.devm.state proxyAddr 2 = 1 ∧
        storOf post5.state proxyAddr 26 = 2106 ∧ storOf post5.state proxyAddr lpSlotA = 2106 ∧
        storOf post5.state proxyAddr 0 = 0 ∧ storOf post5.state proxyAddr 2 = 1 ∧

        (Vulnerable.code.getInst 6900 = some (.next (.push [0x02] (by decide))) ∧
          Vulnerable.code.getInst 6902 = some (.next (.reg .sload)) ∧
          Vulnerable.code.getInst 6911 = some (.next (.reg .sstore))) ∧
        (Vulnerable.code.getInst 88 = some (.next (.push [0x00] (by decide))) ∧
          Vulnerable.code.getInst 90 = some (.next (.reg .sload)) ∧
          Vulnerable.code.getInst 99 = some (.next (.reg .sstore))) ∧

        storOf post2.state proxyAddr 26 = 1800 ∧ storOf post2.state proxyAddr lpSlotA = 1906 ∧
        storOf post2.state proxyAddr 2 = 0
    ) := by
  unfold ViolationAt
  rfl

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

-- Paper review 2 definition: ViolationStmt
namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach (creator creatorFunds initialWorld rootBenv rootTenv)
open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed

example :
    ViolationStmt = (
      ∀ g : Fork, CoveredFork g → ∀ W : State, Checkpoint W → ∃ post : Devm, ViolationAt g W post
    ) := by
  unfold ViolationStmt
  rfl

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

-- Paper review 2 definition: CapstoneStmt
namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach (creator creatorFunds initialWorld rootBenv rootTenv)
open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed

example :
    CapstoneStmt = (
      ∀ fork : Fork, CoveredFork fork →
        ∃ postI postP postC tokenPost attackerPost approvePost addPost post : Devm,
          processCreateMessage (implCreateMsg fork initialWorld) = .ok postI ∧ postI.error = none ∧
          processCreateMessage (cloneCreateMsg fork postI.state) = .ok postP ∧ postP.error = none ∧
          processMessage (initMsg fork postP.state) = .ok postC ∧ postC.error = none ∧
          processCreateMessage (tokenCreateMsg fork postC.state) = .ok tokenPost ∧
          tokenPost.error = none ∧
          processCreateMessage (attackerCreateMsg fork tokenPost.state) = .ok attackerPost ∧
          attackerPost.error = none ∧
          processMessage (approveMsg fork attackerPost.state) = .ok approvePost ∧
          approvePost.error = none ∧
          processMessage (addMsg fork approvePost.state) = .ok addPost ∧ addPost.error = none ∧
          SoundCheckpoint addPost.state ∧ Checkpoint addPost.state ∧
          ViolationAt fork addPost.state post
    ) := by
  unfold CapstoneStmt
  rfl

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

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


namespace Blanc.Lift.Token
open Jaune Blanc Blanc.ExecutionTrace

example : ∀ {B : Book},
    (∀ {l l' : B.Ledger} {a : Sevm} {h : Adr}, B.Good l → B.step l a = some l' →
      B.bal l' h < B.bal l h → a.caller = h ∨ 0 < B.allow l h a.caller) →
    (∀ {l l' : B.Ledger} {a : Sevm} {h g : Adr}, B.Good l → B.step l a = some l' →
      B.allow l h g < B.allow l' h g → a.caller = h) →
    (∀ {l l' : B.Ledger} {a : Sevm} {h : Adr}, B.Good l → B.step l a = some l' →
      a.caller = h → (B.op a).HolderSafe → B.bal l h ≤ B.bal l' h + (B.op a).debit h) →
    (∀ {l l' : B.Ledger} {a : Sevm} {dst : Adr} {v : Nat}, B.Good l →
      B.step l a = some l' → B.op a = .transfer dst v → dst ≠ a.caller →
      B.bal l' a.caller + v = B.bal l a.caller) →
    (∀ {l l' : B.Ledger} {a : Sevm} {h g : Adr}, B.Good l → B.step l a = some l' →
      a.caller = h → (B.op a).HolderSafe → B.allow l' h g ≤ B.allow l h g) →
    (∀ {l : B.Ledger} {h : Adr}, B.Good l → B.bal l h < 2 ^ 256) →
    BookLaws B :=
  @BookLaws.mk

example : ∀ {T : Adr} {B : Book} {C : Core T B},
    (∀ {cfg : ChainConfig} {checkpoint future : BlockChain}
      (tr : ConfiguredHistoryTrace cfg checkpoint future), C.Hist tr →
        ∀ G ∈ tr.settledFrames, G.sevm.currentTarget = T → G.sevm.isStatic = false →
          ∀ c ∈ Exec.childFrames G.run, IsEntry T c → c.sevm.caller = T) →
    SelfCaller C :=
  @SelfCaller.mk

example {B : Book} (laws : BookLaws B) {h : Adr} :
    ∀ {as : List Sevm} {l l' : B.Ledger},
      B.run l as = some l' →
      (∀ n pre, n < as.length → B.run l (as.take n) = some pre → B.Good pre) →
      (∀ g, B.allow l h g = 0) →
      (∀ a ∈ as, a.caller = h → (B.op a).HolderSafe) →
      B.bal l h ≤ B.bal l' h + ((as.filter fun a => decide (a.caller = h)).map
        fun a => (B.op a).debit h).sum ∧
      ∀ g, B.allow l' h g = 0 :=
  laws.run_holder

example {T : Adr} {B : Book} (C : Core T B) {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : C.Hist tr) {pre mid post : List Exec.Frame} {f g : Exec.Frame}
    (split : tr.settledFrames = pre ++ f :: mid ++ g :: post) :
    B.run (C.ledgerOf tr f.pre.state) (entryAsks T (f :: mid)) =
      some (C.ledgerOf tr g.pre.state) :=
  C.segment tr hist split

end Blanc.Lift.Token










-- usdc-weth9-pair-composition-v1: the USDC x WETH9 Pair joint invariant, share rows, liveness rows and checkpoint

-- usdc-weth9-pair-composition-v1: the two-token joint checkpoint by deployment and its checker

-- usdc-finite-checkpoint-v1: the support-free checkpoint, quiet premise and `_finite` headlines
namespace Blanc.Composition.UniswapV2PairUsdcWeth9
open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Composition.UsdcToken Blanc.Lift.FiniteCheckpoint


example (pair usdc : Adr) {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) :
    PairUsdcAllowQuiet pair usdc trace =
      (∀ g, (.allow pair g) ∈ Usdc.historyTouchedKeys usdc trace →
        (checkpoint.state.getStor usdc).get (Usdc.allowSlot pair g) = 0) :=
  rfl











end Blanc.Composition.UniswapV2PairUsdcWeth9

-- usdc-weth9-pair-composition-v1: USDC is an instance of the writer-shadowed token core
namespace Blanc.Composition.UsdcToken
open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.Usdc

example (P : Adr) (K₀ : Key → Prop) : Nonempty (CoreW P (usdcBookS P).toBook) :=
  ⟨usdcCore P K₀⟩

end Blanc.Composition.UsdcToken

-- usdc-weth9-pair-composition-v1: the USDC proxy frame, signature-book laws, history end and the definitions the headlines are stated through
namespace Blanc.Lift.Usdc
open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Blanc.Lift.Token

example {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec 0 sevm pre out)
    (codeEq : sevm.code = Proxy.code) (fork : CoveredFork sevm.benvStat.fork)
    {I : Adr} (slot : (pre.state.getStor sevm.currentTarget).get implSlot = I.toB256)
    (notAdmin : sevm.caller ≠ adminOf pre.state sevm.currentTarget)
    (undelegated : getDelegatedCodeAddress (pre.state.getCode I) = none)
    (notPrecompile : ¬ sevm.benvStat.rules.isPrecomp I)
    (dataBound : sevm.data.length < 2 ^ 256) :
    (∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, out, run⟩ N →
      ∀ x, Ninst.At N.sevm.code N.pc (.exec x) → x = .delegatecall) ∧
    (∀ c ∈ Exec.childFrames run, c.sevm.currentTarget = sevm.currentTarget ∧
      c.sevm.codeAddress = some I ∧ c.sevm.caller = sevm.caller ∧ c.sevm.value = sevm.value ∧
      c.sevm.data = sevm.data ∧ c.sevm.isStatic = sevm.isStatic ∧
      c.sevm.code = pre.state.getCode I) ∧
    (∀ post, out = .ok post → ∃ c ∈ Exec.childFrames run,
      post.output = c.post.output ∧ post.state = c.post.state) :=
  proxy_forwards run codeEq fork slot notAdmin undelegated notPrecompile dataBound

example (P : Adr) : BookLawsS (usdcBookS P) :=
  usdcBook_lawsS P

example {P : Adr} {K₀ : Usdc.Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : Usdc.UsdcHist P K₀ tr) :
    Usdc.UsdcInstalled P future.state ∧
      Usdc.FootInv (Usdc.historyKeyUniverse P tr K₀) (future.state.getStor P) ∧
      Usdc.adminOf future.state P = Usdc.adminOf checkpoint.state P :=
  usdc_history_end tr hist

example {cfg : ChainConfig} {checkpoint future : BlockChain} (P : Adr)
    (tr : ConfiguredHistoryTrace cfg checkpoint future) :
    UsdcGovernance P tr = (
      ∀ G ∈ tr.settledFrames, IsEntry P G → G.sevm.caller = adminOf checkpoint.state P →
        Blanc.Sevm.selector G.sevm ∉ [0x3659cfe6, 0x4f1ef286, 0x8f283970]
    ) := by
  unfold UsdcGovernance
  rfl

example (P : Adr) {cfg : ChainConfig} {checkpoint future : BlockChain}
    (tr : ConfiguredHistoryTrace cfg checkpoint future) (before : List Exec.Frame)
    (f : Exec.Frame) :
    UsdcShadowed P tr before f = (
      (f.sevm.currentTarget = P ∧ ¬ IsEntry P f) ∨
        ∃ (b : List Exec.Frame) (A : Exec.Frame) (m n : List Exec.Frame), before = b ++ A :: m ∧
          A.sevm.currentTarget = P ∧ A.sevm.codeAddress = some usdcLib ∧
          Exec.descendantFrames A.run = m ++ f :: n
    ) := by
  unfold UsdcShadowed
  rfl

end Blanc.Lift.Usdc

-- usdc-weth9-pair-composition-v1: the never-signer predicate (derived for the Pair by usdc_neverSigner_pair)
namespace Blanc.Lift.Token
open Jaune Blanc Blanc.ExecutionTrace

example : ∀ {T : Adr} {S : BookS} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {tr : ConfiguredHistoryTrace cfg checkpoint future} {p : Adr},
    (∀ g ∈ tr.settledFrames, IsEntry T g → g.sevm.isStatic = false → S.signer g.sevm ≠ some p) →
    NeverSigner T S tr p :=
  @NeverSigner.mk

end Blanc.Lift.Token

-- curve-3pool-stableswap-v1: Curve 3pool frame, history, liveness (with the end-to-end
-- concrete instances), Newton-loop, U3, amplification, composition and deployment headlines.
-- Each binder is named as in its source; the names need not be referenced.
set_option linter.unusedVariables false

namespace Blanc.Lift.Curve3Pool
open Jaune Blanc Blanc.Lift

example : ∀ {sevm : Sevm} {pre post : Devm} {s : State} (exc : Exec 0 sevm pre (.ok post)) (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) (hcd : sevm.data.length < 2 ^ 256) (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256) (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hck : Checkpoint (pre.getStor sevm.currentTarget) s) (henv : PoolFrameEnv ⟨0, sevm, pre, .ok post, exc⟩),
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o :=
  @Blanc.Lift.Curve3Pool.pool_frame_refines_env

example : PoolFrameRefines poolEntry :=
  @Blanc.Lift.Curve3Pool.pool_frame_refines

end Blanc.Lift.Curve3Pool

namespace Blanc.Lift.Curve3Pool
open Jaune

example : ∀ {D : Exec.Deriv} {post : Devm} {s : State} {e : Env} {o : Out} (hc : Checkpoint (entryStor D) s) (hstep : step s e (decodeCall D.sevm) = some o) (hraw : RawEffect D post e o),
    Checkpoint (post.getStor D.sevm.currentTarget) o.state ∧
      post.logs = D.devm.logs ++ (children D).flatMap (fun c => c.post.logs) ++
        o.events.map (eventLog D.sevm.currentTarget) ∧
      post.output = retOut D.devm.output o.ret ∧
      (D.sevm.isStatic = false → CallsOf D =
        (o.calls.map (encodeCall D.sevm.currentTarget (fun k => adrOf (s.coins.get k))
          (adrOf s.token))).filter fun r => framed D r.target) ∧
      o.state.coins = s.coins ∧ o.state.token = s.token :=
  @Blanc.Lift.Curve3Pool.rawEffect_refines

end Blanc.Lift.Curve3Pool

namespace Blanc.Lift.Curve3Pool
open Jaune Blanc.Lift

example : ∀ {sevm : Sevm} {pre post : Devm} (exc : Exec 0 sevm pre (.ok post)) (hcode : sevm.code = code) (hcd : sevm.data.length < 2 ^ 256) (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256),
    decodeCall sevm ≠ .other :=
  @Blanc.Lift.Curve3Pool.pool_other_fails

example : ∀ {sevm : Sevm} {pre post : Devm} (exc : Exec 0 sevm pre (.ok post)) (hs : sevm.isStatic = true) (hfork : CoveredFork sevm.benvStat.fork) (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hcommit : post.error = none),
    post.logs = pre.logs ∧ ∀ a, post.getStor a = pre.getStor a :=
  @Blanc.Lift.Curve3Pool.pool_static_noEffect

end Blanc.Lift.Curve3Pool

namespace Blanc.Lift.Curve3Pool
open Jaune Blanc Blanc.ExecutionTrace

example : ∀ {pool : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {s₀ : State} (trace : ConfiguredHistoryTrace cfg checkpoint future) (installed : some (checkpoint.state.getCode pool).toList = poolSem.image) (initial : Checkpoint (checkpoint.state.getStor pool) s₀) (callbacks : trace.FrameAdmitted pool
      (Exec.derivEntry fun D => PoolCallsKeep D ∧ PoolCoinCallsKeepToken D)) (parties : ∀ root ∈ trace.rawFrames, root.sevm.currentTarget = pool →
      (∀ k : Fin 3, ¬ root.sevm.benvStat.rules.isPrecomp (adrOf (s₀.coins.get k))) ∧
        ¬ root.sevm.benvStat.rules.isPrecomp (adrOf s₀.token)) (idEmpty : checkpoint.state.getCode 4 = ByteArray.empty) (idNoAuthority : trace.NoAuthorityAt 4) (idNoFrame : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ 4) (sysNe : ∀ root ∈ trace.systemRawFrames, root.sevm.currentTarget ≠ pool),
    some (future.state.getCode pool).toList = poolSem.image ∧
    ∃ invs : List PoolInvocation,
      invs.flatMap (fun i => poolSubtreeFrames pool i.frame) = committedPoolFrames pool trace ∧
      (∀ i ∈ invs, i.Authentic pool) ∧
      ∃ s, PoolRun s₀ invs s ∧ runPool s₀ invs = some s ∧
        Checkpoint (future.state.getStor pool) s ∧ s.coins = s₀.coins ∧ s.token = s₀.token :=
  @Blanc.Lift.Curve3Pool.pool_history_committed_derived

example : ∀ {pool : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {s₀ : State} (trace : ConfiguredHistoryTrace cfg checkpoint future) (installed : some (checkpoint.state.getCode pool).toList = poolSem.image) (initial : Checkpoint (checkpoint.state.getStor pool) s₀) (env : PoolTraceEnv trace pool s₀.coins s₀.token),
    some (future.state.getCode pool).toList = poolSem.image ∧
    ∃ invs : List PoolInvocation,
      invs.flatMap (fun i => poolSubtreeFrames pool i.frame) = committedPoolFrames pool trace ∧
      (∀ i ∈ invs, i.Authentic pool) ∧
      ∃ s, PoolRun s₀ invs s ∧ runPool s₀ invs = some s ∧
        Checkpoint (future.state.getStor pool) s ∧ s.coins = s₀.coins ∧ s.token = s₀.token :=
  @Blanc.Lift.Curve3Pool.pool_history_committed_env

end Blanc.Lift.Curve3Pool

namespace Blanc.Lift.Curve3Pool
open Jaune Blanc Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

example : ∀ {E : Sevm → Devm → Prop} (refines : PoolFrameRefines E) {pool : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {s₀ : State} (trace : ConfiguredHistoryTrace cfg checkpoint future) (installed : some (checkpoint.state.getCode pool).toList = poolSem.image) (initial : Checkpoint (checkpoint.state.getStor pool) s₀) (admitted : trace.FrameAdmitted pool E),
    some (future.state.getCode pool).toList = poolSem.image ∧
    ∃ invs : List PoolInvocation,
      invs.flatMap (fun i => poolSubtreeFrames pool i.frame) = committedPoolFrames pool trace ∧
      (∀ i ∈ invs, i.Authentic pool) ∧
      ∃ s, PoolRun s₀ invs s ∧ runPool s₀ invs = some s ∧
        Checkpoint (future.state.getStor pool) s ∧ s.coins = s₀.coins ∧ s.token = s₀.token :=
  @Blanc.Lift.Curve3Pool.pool_history_committed_with

end Blanc.Lift.Curve3Pool

namespace Blanc.Lift.Curve3Pool
open Jaune Blanc Blanc.ExecutionTrace

example : ∀ {pool : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} (trace : ConfiguredHistoryTrace cfg checkpoint future) (deployedCode : (checkpoint.state.getCode pool).toList = code.toList) (deployedStorage : checkpoint.state.getStor pool = Creation.deployedStor Creation.deployTime) (callbacks : trace.FrameAdmitted pool
      (Exec.derivEntry fun D => PoolCallsKeep D ∧ PoolCoinCallsKeepToken D)) (parties : ∀ root ∈ trace.rawFrames, root.sevm.currentTarget = pool →
      (∀ k : Fin 3, ¬ root.sevm.benvStat.rules.isPrecomp
        (adrOf ((Creation.poolInitState Creation.deployTime.toNat).coins.get k))) ∧
        ¬ root.sevm.benvStat.rules.isPrecomp
          (adrOf (Creation.poolInitState Creation.deployTime.toNat).token)) (idEmpty : checkpoint.state.getCode 4 = ByteArray.empty) (idNoAuthority : trace.NoAuthorityAt 4) (idNoFrame : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ 4) (sysNe : ∀ root ∈ trace.systemRawFrames, root.sevm.currentTarget ≠ pool),
    some (future.state.getCode pool).toList = poolSem.image ∧
    ∃ invs : List PoolInvocation,
      invs.flatMap (fun i => poolSubtreeFrames pool i.frame) = committedPoolFrames pool trace ∧
      (∀ i ∈ invs, i.Authentic pool) ∧
      ∃ s, PoolRun (Creation.poolInitState Creation.deployTime.toNat) invs s ∧
        runPool (Creation.poolInitState Creation.deployTime.toNat) invs = some s ∧
        Checkpoint (future.state.getStor pool) s ∧
        s.coins = (Creation.poolInitState Creation.deployTime.toNat).coins ∧
        s.token = (Creation.poolInitState Creation.deployTime.toNat).token :=
  @Blanc.Lift.Curve3Pool.pool_history_initialized

end Blanc.Lift.Curve3Pool

namespace Blanc.Lift.Curve3Pool
open Jaune Blanc.Lift Blanc.StableSwapNewton

example : ∀ {sevm : Sevm} {pre : Devm} {s : State} {o : Out} {i j : Fin 3} {B1 B2 : B256} {W W' W'' : Devm → Prop} {U G : Nat} (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0) (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256) (hsel : Sevm.selector sevm = selExchange) (hi : i.val = (exI sevm).toNat) (hj : j.val = (exJ sevm).toNat) (hck : Checkpoint (pre.getStor sevm.currentTarget) s) (hstep : step s (exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)) (decodeCall sevm) = some o) (hcoin : ∀ k : Fin 3,
      ¬ sevm.benvStat.rules.isPrecomp ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr) (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm pre) (hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
      PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
        ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) (hWc : WClosed sevm W) (hW'c : WClosed sevm W') (hWb : W pre) (hbal : i = feeIndex →
      CoinBalOkAt sevm W W ((pre.getStor sevm.currentTarget).get (coinSlot i)) B1 U 0x3dc 0x440 ∧
      CoinBalOkAt sevm W' W' ((pre.getStor sevm.currentTarget).get (coinSlot i)) B2 U 0x71c 0x780) (hpull : CoinPullOkAt sevm W W' ((pre.getStor sevm.currentTarget).get (coinSlot i))
      (exDx sevm) U 0x600 0x6c0) (hW''c : WClosed sevm W'') (hpush : CoinPushOkAt sevm W' W'' ((pre.getStor sevm.currentTarget).get (coinSlot j))
      (Nat.toB256 (exPushAmt o)) U 0xb60 0xc00) (hG : costExchange sevm pre s (exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)) i j
      (exDx sevm).toNat + 4 * U ≤ G) (hGm : (St pre [] Mem.empty G).gasMeasure < 2 ^ 256),
    ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post), ∃ bp bq,
      pullIn (exEnv sevm i j bp bq) i (exDx sevm).toNat =
        pullIn (exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)) i (exDx sevm).toNat ∧
      RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (exEnv sevm i j bp bq) o ∧
        Checkpoint (post.getStor sevm.currentTarget) o.state ∧ W'' post :=
  @Blanc.Lift.Curve3Pool.exchange_live

end Blanc.Lift.Curve3Pool

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton in
example : ∀ {sevm : Sevm} {pre : Devm} {s : State} {o : Out} {T B1 B2 : B256} {W : Nat → Devm → Prop} {U G : Nat} (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0) (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256) (hsel : Sevm.selector sevm = selAddLiquidity) (hck : Checkpoint (pre.getStor sevm.currentTarget) s) (hstep : step s (alEnvW sevm T.toNat B1.toNat B2.toNat) (decodeCall sevm) = some o) (htok : ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr) (hcoin : ∀ k : Fin 3,
      ¬ sevm.benvStat.rules.isPrecomp ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr) (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm pre) (hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
      PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
        ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) (hWc : ∀ j, j ≤ 4 → WClosed sevm (W j)) (hWb : W 0 pre) (hsup : SupplyOkAt sevm (W 0) (W 0) ((pre.getStor sevm.currentTarget).get tokenSlot) T U
      0x27c 0x2c0) (hpull : ∀ k : Fin 3, k ≠ feeIndex → alAmt sevm k.val ≠ 0 →
      CoinPullOkAt sevm (W k) (W (k + 1)) ((pre.getStor sevm.currentTarget).get (coinSlot k))
        (alAmt sevm k.val) U 0x760 0x820) (hskip : ∀ k : Fin 3, alAmt sevm k.val = 0 → ∀ b, W k b → W (k + 1) b) (hfee : alAmt sevm 2 ≠ 0 →
      CoinBalOkAt sevm (W 2) (W 2) ((pre.getStor sevm.currentTarget).get (coinSlot 2)) B1 U
        0x53c 0x5a0 ∧
      CoinPullOkAt sevm (W 2) (W 3) ((pre.getStor sevm.currentTarget).get (coinSlot 2))
        (alAmt sevm 2) U 0x760 0x820 ∧
      CoinBalOkAt sevm (W 3) (W 3) ((pre.getStor sevm.currentTarget).get (coinSlot 2)) B2 U
        0x87c 0x8e0) (hmint : MintOkAt sevm (W 3) (W 4) ((pre.getStor sevm.currentTarget).get tokenSlot)
      (Nat.toB256 (alMintAmt o)) U 0xc7c 0xd00) (hG : costAddLiquidity s (alEnvW sevm T.toNat B1.toNat B2.toNat) (argV3 sevm 0) + 7 * U ≤ G) (hGm : (St pre [] Mem.empty G).gasMeasure + 3000 < 2 ^ 256),
    ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post), ∃ e : Env,
      e.supply = some T.toNat ∧ step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post e o ∧
      Checkpoint (post.getStor sevm.currentTarget) o.state :=
  @Blanc.Lift.Curve3Pool.addLiquidity_live

end Blanc.Lift.Curve3Pool

namespace Blanc.Lift.Curve3Pool
open Jaune Blanc.Lift Blanc.StableSwapNewton

example : ∀ {sevm : Sevm} {pre : Devm} {s : State} {o : Out} {T : B256} {W : Nat → Devm → Prop} {U G : Nat} (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0) (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256) (hsel : Sevm.selector sevm = selRemoveLiquidity) (hck : Checkpoint (pre.getStor sevm.currentTarget) s) (hstep : step s (rlEnv sevm T) (decodeCall sevm) = some o) (htok : ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr) (hcoin : ∀ k : Fin 3,
      ¬ sevm.benvStat.rules.isPrecomp ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr) (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm pre) (hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
      PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
        ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) (hWc : ∀ k, k ≤ 3 → WClosed sevm (W k)) (hWb : W 0 pre) (hsup : SupplyOk sevm (W 0) ((pre.getStor sevm.currentTarget).get tokenSlot) T U) (hpush : ∀ k : Fin 3, CoinPushOkAt sevm (W k) (W (k + 1))
      ((pre.getStor sevm.currentTarget).get (coinSlot k))
      (balAt (pre.getStor sevm.currentTarget) k * rlAmt sevm / T) U 0x520 0x5c0) (hburn : BurnOkTo sevm (W 3) (W 4) ((pre.getStor sevm.currentTarget).get tokenSlot)
      (rlAmt sevm) U) (hG : 167000 + 5 * U ≤ G) (hGm : (St pre [] Mem.empty G).gasMeasure < 2 ^ 256),
    ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post),
      RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (rlEnv sevm T) o ∧
        Checkpoint (post.getStor sevm.currentTarget) o.state :=
  @Blanc.Lift.Curve3Pool.removeLiquidity_live

example : ∀ {sevm : Sevm} {pre : Devm} {s : State} {o : Out} {T : B256} {W : Nat → Devm → Prop} {U G : Nat} (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0) (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256) (hsel : Sevm.selector sevm = selRemoveLiquidityImbalance) (hck : Checkpoint (pre.getStor sevm.currentTarget) s) (hstep : step s (rliEnvW sevm T.toNat) (decodeCall sevm) = some o) (htok : ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr) (hcoin : ∀ k : Fin 3,
      ¬ sevm.benvStat.rules.isPrecomp ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr) (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm pre) (hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
      PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
        ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) (hWc : ∀ j, j ≤ 4 → WClosed sevm (W j)) (hWb : W 0 pre) (hsup : SupplyOkAt sevm (W 0) (W 0) ((pre.getStor sevm.currentTarget).get tokenSlot) T U
      0x17c 0x1c0) (hburn : BurnOkAt sevm (W 0) (W 1) ((pre.getStor sevm.currentTarget).get tokenSlot)
      (Nat.toB256 (rliBurnAmt o)) U 0x85c 0x8e0) (hpush : ∀ k : Fin 3, rliAmt sevm k.val ≠ 0 → CoinPushOkAt sevm (W (k + 1)) (W (k + 2))
      ((pre.getStor sevm.currentTarget).get (coinSlot k)) (rliAmt sevm k.val) U 0xaa0 0xb40) (hskip : ∀ k : Fin 3, rliAmt sevm k.val = 0 → ∀ b, W (k + 1) b → W (k + 2) b) (hG : costImbalance s (rliEnvW sevm T.toNat) (argV3 sevm 0) + 5 * U ≤ G) (hGm : (St pre [] Mem.empty G).gasMeasure + 3000 < 2 ^ 256),
    ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post),
      RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (rliEnvW sevm T.toNat) o ∧
      Checkpoint (post.getStor sevm.currentTarget) o.state ∧ W 4 post :=
  @Blanc.Lift.Curve3Pool.removeLiquidityImbalance_live

example : ∀ {sevm : Sevm} {pre : Devm} {s : State} {o : Out} {i : Fin 3} {T : B256} {W W' W'' : Devm → Prop} {U G : Nat} (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0) (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256) (hsel : Sevm.selector sevm = selRemoveLiquidityOneCoin) (hi : i.val = (ocI sevm).toNat) (hck : Checkpoint (pre.getStor sevm.currentTarget) s) (hstep : step s (ocEnv sevm i T.toNat) (decodeCall sevm) = some o) (htok : ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr) (hcoin : ∀ k : Fin 3,
      ¬ sevm.benvStat.rules.isPrecomp ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr) (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm pre) (hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
      PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
        ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) (hWc : WClosed sevm W) (hW'c : WClosed sevm W') (hWb : W pre) (hsup : SupplyOkAt sevm W W ((pre.getStor sevm.currentTarget).get tokenSlot) T U 0x2bc 0x300) (hburn : BurnOkAt sevm W W' ((pre.getStor sevm.currentTarget).get tokenSlot) (ocAmt sevm) U
      0x31c 0x3a0) (hW''c : WClosed sevm W'') (hpush : CoinPushOkAt sevm W' W'' ((pre.getStor sevm.currentTarget).get (coinSlot i))
      (Nat.toB256 (ocPushAmt o)) U 0x540 0x5e0) (hG : costOneCoin s (ocEnv sevm i T.toNat) (ocAmt sevm).toNat i + 3 * U ≤ G) (hGm : (St pre [] Mem.empty G).gasMeasure + 2000 < 2 ^ 256),
    ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post), ∃ T' : Nat,
      RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (ocEnv sevm i T') o ∧
        Checkpoint (post.getStor sevm.currentTarget) o.state ∧ W'' post :=
  @Blanc.Lift.Curve3Pool.removeLiquidityOneCoin_live

end Blanc.Lift.Curve3Pool

namespace Blanc.Lift.Curve3Pool
open Jaune Blanc.Lift Blanc.ExecutionTrace

example : ∀ {pool : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {s₀ : State} (trace : ConfiguredHistoryTrace cfg checkpoint future) (installed : some (checkpoint.state.getCode pool).toList = poolSem.image) (initial : Checkpoint (checkpoint.state.getStor pool) s₀) (env : PoolTraceEnv trace pool s₀.coins s₀.token) {sevm : Sevm} {pre : Devm} (target : sevm.currentTarget = pool) (state : pre.state = future.state),
    ∃ s, PoolHistoryAt trace pool s₀ s ∧
      ∀ {o : Out} {i j : Fin 3} {B1 B2 : B256} {W W' W'' : Devm → Prop} {U G : Nat}
        (_hcode : sevm.code = code) (_hfork : CoveredFork sevm.benvStat.fork)
        (_hstatic : sevm.isStatic = false) (_hdepth : sevm.depth ≠ 0)
        (_hlen : 4 ≤ sevm.data.length) (_hcd : sevm.data.length < 2 ^ 256)
        (_hsel : Sevm.selector sevm = selExchange)
        (_hi : i.val = (exI sevm).toNat) (_hj : j.val = (exJ sevm).toNat)
        (_hstep : step s (exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)) (decodeCall sevm) =
          some o)
        (_hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
          ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : pre.getCode sevm.currentTarget ≠ .empty) (_hid : IdReady sevm pre)
        (_hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
          PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
            ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4)
        (_hWc : WClosed sevm W) (_hW'c : WClosed sevm W') (_hWb : W pre)
        (_hbal : i = feeIndex →
          CoinBalOkAt sevm W W ((pre.getStor sevm.currentTarget).get (coinSlot i)) B1 U
            0x3dc 0x440 ∧
          CoinBalOkAt sevm W' W' ((pre.getStor sevm.currentTarget).get (coinSlot i)) B2 U
            0x71c 0x780)
        (_hpull : CoinPullOkAt sevm W W' ((pre.getStor sevm.currentTarget).get (coinSlot i))
          (exDx sevm) U 0x600 0x6c0)
        (_hW''c : WClosed sevm W'')
        (_hpush : CoinPushOkAt sevm W' W'' ((pre.getStor sevm.currentTarget).get (coinSlot j))
          (Nat.toB256 (exPushAmt o)) U 0xb60 0xc00)
        (_hG : costExchange sevm pre s (exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)) i j
          (exDx sevm).toNat + 4 * U ≤ G)
        (_hGm : (St pre [] Mem.empty G).gasMeasure < 2 ^ 256),
        ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post), ∃ bp bq,
          pullIn (exEnv sevm i j bp bq) i (exDx sevm).toNat =
            pullIn (exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)) i (exDx sevm).toNat ∧
          RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (exEnv sevm i j bp bq)
            o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state ∧ W'' post :=
  @Blanc.Lift.Curve3Pool.pool_history_exchange_live

example : ∀ {pool : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {s₀ : State} (trace : ConfiguredHistoryTrace cfg checkpoint future) (installed : some (checkpoint.state.getCode pool).toList = poolSem.image) (initial : Checkpoint (checkpoint.state.getStor pool) s₀) (env : PoolTraceEnv trace pool s₀.coins s₀.token) {sevm : Sevm} {pre : Devm} (target : sevm.currentTarget = pool) (state : pre.state = future.state),
    ∃ s, PoolHistoryAt trace pool s₀ s ∧
      ∀ {o : Out} {T B1 B2 : B256} {W : Nat → Devm → Prop} {U G : Nat}
        (_hcode : sevm.code = code) (_hfork : CoveredFork sevm.benvStat.fork)
        (_hstatic : sevm.isStatic = false) (_hdepth : sevm.depth ≠ 0)
        (_hlen : 4 ≤ sevm.data.length) (_hcd : sevm.data.length < 2 ^ 256)
        (_hsel : Sevm.selector sevm = selAddLiquidity)
        (_hstep : step s (alEnvW sevm T.toNat B1.toNat B2.toNat) (decodeCall sevm) = some o)
        (_htok : ¬ sevm.benvStat.rules.isPrecomp
          ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr)
        (_hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
          ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : pre.getCode sevm.currentTarget ≠ .empty) (_hid : IdReady sevm pre)
        (_hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
          PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
            ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4)
        (_hWc : ∀ j, j ≤ 4 → WClosed sevm (W j)) (_hWb : W 0 pre)
        (_hsup : SupplyOkAt sevm (W 0) (W 0) ((pre.getStor sevm.currentTarget).get tokenSlot) T U
          0x27c 0x2c0)
        (_hpull : ∀ k : Fin 3, k ≠ feeIndex → alAmt sevm k.val ≠ 0 →
          CoinPullOkAt sevm (W k) (W (k + 1)) ((pre.getStor sevm.currentTarget).get (coinSlot k))
            (alAmt sevm k.val) U 0x760 0x820)
        (_hskip : ∀ k : Fin 3, alAmt sevm k.val = 0 → ∀ b, W k b → W (k + 1) b)
        (_hfee : alAmt sevm 2 ≠ 0 →
          CoinBalOkAt sevm (W 2) (W 2) ((pre.getStor sevm.currentTarget).get (coinSlot 2)) B1 U
            0x53c 0x5a0 ∧
          CoinPullOkAt sevm (W 2) (W 3) ((pre.getStor sevm.currentTarget).get (coinSlot 2))
            (alAmt sevm 2) U 0x760 0x820 ∧
          CoinBalOkAt sevm (W 3) (W 3) ((pre.getStor sevm.currentTarget).get (coinSlot 2)) B2 U
            0x87c 0x8e0)
        (_hmint : MintOkAt sevm (W 3) (W 4) ((pre.getStor sevm.currentTarget).get tokenSlot)
          (Nat.toB256 (alMintAmt o)) U 0xc7c 0xd00)
        (_hG : costAddLiquidity s (alEnvW sevm T.toNat B1.toNat B2.toNat) (argV3 sevm 0) + 7 * U ≤
          G)
        (_hGm : (St pre [] Mem.empty G).gasMeasure + 3000 < 2 ^ 256),
        ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post), ∃ e : Env,
          e.supply = some T.toNat ∧ step s e (decodeCall sevm) = some o ∧
          RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post e o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state :=
  @Blanc.Lift.Curve3Pool.pool_history_addLiquidity_live

example : ∀ {pool : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {s₀ : State} (trace : ConfiguredHistoryTrace cfg checkpoint future) (installed : some (checkpoint.state.getCode pool).toList = poolSem.image) (initial : Checkpoint (checkpoint.state.getStor pool) s₀) (env : PoolTraceEnv trace pool s₀.coins s₀.token) {sevm : Sevm} {pre : Devm} (target : sevm.currentTarget = pool) (state : pre.state = future.state),
    ∃ s, PoolHistoryAt trace pool s₀ s ∧
      ∀ {o : Out} {T : B256} {W : Nat → Devm → Prop} {U G : Nat}
        (_hcode : sevm.code = code) (_hfork : CoveredFork sevm.benvStat.fork)
        (_hstatic : sevm.isStatic = false) (_hdepth : sevm.depth ≠ 0)
        (_hlen : 4 ≤ sevm.data.length) (_hcd : sevm.data.length < 2 ^ 256)
        (_hsel : Sevm.selector sevm = selRemoveLiquidity)
        (_hstep : step s (rlEnv sevm T) (decodeCall sevm) = some o)
        (_htok : ¬ sevm.benvStat.rules.isPrecomp
          ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr)
        (_hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
          ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : pre.getCode sevm.currentTarget ≠ .empty) (_hid : IdReady sevm pre)
        (_hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
          PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
            ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4)
        (_hWc : ∀ k, k ≤ 3 → WClosed sevm (W k)) (_hWb : W 0 pre)
        (_hsup : SupplyOk sevm (W 0) ((pre.getStor sevm.currentTarget).get tokenSlot) T U)
        (_hpush : ∀ k : Fin 3, CoinPushOkAt sevm (W k) (W (k + 1))
          ((pre.getStor sevm.currentTarget).get (coinSlot k))
          (balAt (pre.getStor sevm.currentTarget) k * rlAmt sevm / T) U 0x520 0x5c0)
        (_hburn : BurnOkTo sevm (W 3) (W 4) ((pre.getStor sevm.currentTarget).get tokenSlot)
          (rlAmt sevm) U)
        (_hG : 167000 + 5 * U ≤ G) (_hGm : (St pre [] Mem.empty G).gasMeasure < 2 ^ 256),
        ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post),
          RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (rlEnv sevm T) o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state :=
  @Blanc.Lift.Curve3Pool.pool_history_removeLiquidity_live

example : ∀ {pool : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {s₀ : State} (trace : ConfiguredHistoryTrace cfg checkpoint future) (installed : some (checkpoint.state.getCode pool).toList = poolSem.image) (initial : Checkpoint (checkpoint.state.getStor pool) s₀) (env : PoolTraceEnv trace pool s₀.coins s₀.token) {sevm : Sevm} {pre : Devm} (target : sevm.currentTarget = pool) (state : pre.state = future.state),
    ∃ s, PoolHistoryAt trace pool s₀ s ∧
      ∀ {o : Out} {T : B256} {W : Nat → Devm → Prop} {U G : Nat}
        (_hcode : sevm.code = code) (_hfork : CoveredFork sevm.benvStat.fork)
        (_hstatic : sevm.isStatic = false) (_hdepth : sevm.depth ≠ 0)
        (_hlen : 4 ≤ sevm.data.length) (_hcd : sevm.data.length < 2 ^ 256)
        (_hsel : Sevm.selector sevm = selRemoveLiquidityImbalance)
        (_hstep : step s (rliEnvW sevm T.toNat) (decodeCall sevm) = some o)
        (_htok : ¬ sevm.benvStat.rules.isPrecomp
          ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr)
        (_hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
          ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : pre.getCode sevm.currentTarget ≠ .empty) (_hid : IdReady sevm pre)
        (_hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
          PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
            ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4)
        (_hWc : ∀ j, j ≤ 4 → WClosed sevm (W j)) (_hWb : W 0 pre)
        (_hsup : SupplyOkAt sevm (W 0) (W 0) ((pre.getStor sevm.currentTarget).get tokenSlot) T U
          0x17c 0x1c0)
        (_hburn : BurnOkAt sevm (W 0) (W 1) ((pre.getStor sevm.currentTarget).get tokenSlot)
          (Nat.toB256 (rliBurnAmt o)) U 0x85c 0x8e0)
        (_hpush : ∀ k : Fin 3, rliAmt sevm k.val ≠ 0 → CoinPushOkAt sevm (W (k + 1)) (W (k + 2))
          ((pre.getStor sevm.currentTarget).get (coinSlot k)) (rliAmt sevm k.val) U 0xaa0 0xb40)
        (_hskip : ∀ k : Fin 3, rliAmt sevm k.val = 0 → ∀ b, W (k + 1) b → W (k + 2) b)
        (_hG : costImbalance s (rliEnvW sevm T.toNat) (argV3 sevm 0) + 5 * U ≤ G)
        (_hGm : (St pre [] Mem.empty G).gasMeasure + 3000 < 2 ^ 256),
        ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post),
          RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (rliEnvW sevm T.toNat)
            o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state ∧ W 4 post :=
  @Blanc.Lift.Curve3Pool.pool_history_removeLiquidityImbalance_live

example : ∀ {pool : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {s₀ : State} (trace : ConfiguredHistoryTrace cfg checkpoint future) (installed : some (checkpoint.state.getCode pool).toList = poolSem.image) (initial : Checkpoint (checkpoint.state.getStor pool) s₀) (env : PoolTraceEnv trace pool s₀.coins s₀.token) {sevm : Sevm} {pre : Devm} (target : sevm.currentTarget = pool) (state : pre.state = future.state),
    ∃ s, PoolHistoryAt trace pool s₀ s ∧
      ∀ {o : Out} {i : Fin 3} {T : B256} {W W' W'' : Devm → Prop} {U G : Nat}
        (_hcode : sevm.code = code) (_hfork : CoveredFork sevm.benvStat.fork)
        (_hstatic : sevm.isStatic = false) (_hdepth : sevm.depth ≠ 0)
        (_hlen : 4 ≤ sevm.data.length) (_hcd : sevm.data.length < 2 ^ 256)
        (_hsel : Sevm.selector sevm = selRemoveLiquidityOneCoin)
        (_hi : i.val = (ocI sevm).toNat)
        (_hstep : step s (ocEnv sevm i T.toNat) (decodeCall sevm) = some o)
        (_htok : ¬ sevm.benvStat.rules.isPrecomp
          ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr)
        (_hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
          ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : pre.getCode sevm.currentTarget ≠ .empty) (_hid : IdReady sevm pre)
        (_hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
          PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
            ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4)
        (_hWc : WClosed sevm W) (_hW'c : WClosed sevm W') (_hWb : W pre)
        (_hsup : SupplyOkAt sevm W W ((pre.getStor sevm.currentTarget).get tokenSlot) T U
          0x2bc 0x300)
        (_hburn : BurnOkAt sevm W W' ((pre.getStor sevm.currentTarget).get tokenSlot)
          (ocAmt sevm) U 0x31c 0x3a0)
        (_hW''c : WClosed sevm W'')
        (_hpush : CoinPushOkAt sevm W' W'' ((pre.getStor sevm.currentTarget).get (coinSlot i))
          (Nat.toB256 (ocPushAmt o)) U 0x540 0x5e0)
        (_hG : costOneCoin s (ocEnv sevm i T.toNat) (ocAmt sevm).toNat i + 3 * U ≤ G)
        (_hGm : (St pre [] Mem.empty G).gasMeasure + 2000 < 2 ^ 256),
        ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post), ∃ T' : Nat,
          RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (ocEnv sevm i T') o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state ∧ W'' post :=
  @Blanc.Lift.Curve3Pool.pool_history_removeLiquidityOneCoin_live

end Blanc.Lift.Curve3Pool

namespace Blanc.Composition.Curve3Pool3CrvHeadlines
open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.ExecutionTrace
open Blanc.Composition.Curve3Pool3CrvJoint (JointCheckpoint)
open Blanc.Composition.Curve3PoolCalleeLive

example : ∀ {pool c3 : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {ps₀ : Curve3Pool.State} {cs₀ : Blanc.Curve3Crv.State} {K₀ : Curve3Crv.Key → Prop} (trace : ConfiguredHistoryTrace cfg checkpoint future) (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image) (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image) (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state) (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace)) (env : PoolTraceEnv trace pool ps₀.coins ps₀.token) (notSystem : pool ≠ systemAddress) {sevm : Sevm} {pre : Devm} (target : sevm.currentTarget = pool) (state : pre.state = future.state),
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 pre ∧
      ∀ {o : Out} {T : B256} {V : Nat → Devm → Prop} {U G : Nat}
        (_hcode : sevm.code = code) (_hfork : CoveredFork sevm.benvStat.fork)
        (_hstatic : sevm.isStatic = false) (_hdepth : sevm.depth ≠ 0)
        (_hlen : 4 ≤ sevm.data.length) (_hcd : sevm.data.length < 2 ^ 256)
        (_hsel : Sevm.selector sevm = selRemoveLiquidity)
        (_hstep : step s (rlEnv sevm T) (decodeCall sevm) = some o)
        (_htok : ¬ sevm.benvStat.rules.isPrecomp c3)
        (_hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
          ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : pre.getCode sevm.currentTarget ≠ .empty) (_hid : IdReady sevm pre)
        (_hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
          PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
            ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4)
        (_hU : 70000 ≤ U)
        (_hT : (Devm.getStor pre c3).get Curve3Crv.vySupplySlot = T)
        (_hburn : BurnFits (Devm.getStor pre c3) pool sevm.caller.toB256 (rlAmt sevm))
        (_hVc : ∀ k, k ≤ 3 → WClosed sevm (V k)) (_hVb : V 0 pre) (_hVs : ∀ k, C3Blind c3 (V k))
        (_hpush : ∀ k : Fin 3, CoinPushOkAt sevm (C3With c3 (Devm.getStor pre c3) (V k))
          (C3With c3 (Devm.getStor pre c3) (V (k + 1)))
          ((pre.getStor sevm.currentTarget).get (coinSlot k))
          (balAt (pre.getStor sevm.currentTarget) k * rlAmt sevm / T) U 0x520 0x5c0)
        (_hG : 167000 + 5 * U ≤ G) (_hGm : (St pre [] Mem.empty G).gasMeasure < 2 ^ 256),
        ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post),
          RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (rlEnv sevm T) o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state :=
  @Blanc.Composition.Curve3Pool3CrvHeadlines.pool_3crv_removeLiquidity_live_entry

example : ∀ {pool c3 : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {ps₀ : Curve3Pool.State} {cs₀ : Blanc.Curve3Crv.State} {K₀ : Curve3Crv.Key → Prop} (trace : ConfiguredHistoryTrace cfg checkpoint future) (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image) (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image) (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state) (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace)) (env : PoolTraceEnv trace pool ps₀.coins ps₀.token) (notSystem : pool ≠ systemAddress) {sevm : Sevm} {pre : Devm} (target : sevm.currentTarget = pool) (state : pre.state = future.state),
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 pre ∧
      ∀ {o : Out} {T B1 B2 : B256} {V : Nat → Devm → Prop} {U G : Nat}
        (_hcode : sevm.code = code) (_hfork : CoveredFork sevm.benvStat.fork)
        (_hstatic : sevm.isStatic = false) (_hdepth : sevm.depth ≠ 0)
        (_hlen : 4 ≤ sevm.data.length) (_hcd : sevm.data.length < 2 ^ 256)
        (_hsel : Sevm.selector sevm = selAddLiquidity)
        (_hstep : step s (alEnvW sevm T.toNat B1.toNat B2.toNat) (decodeCall sevm) = some o)
        (_htok : ¬ sevm.benvStat.rules.isPrecomp c3)
        (_hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
          ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : pre.getCode sevm.currentTarget ≠ .empty) (_hid : IdReady sevm pre)
        (_hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
          PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
            ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4)
        (_hU : 70000 ≤ U)
        (_hT : (Devm.getStor pre c3).get Curve3Crv.vySupplySlot = T)
        (_hmint : MintFits (Devm.getStor pre c3) pool sevm.caller.toB256
          (Nat.toB256 (alMintAmt o)))
        (_hVc : ∀ k, k ≤ 3 → WClosed sevm (V k)) (_hVb : V 0 pre) (_hVs : ∀ k, C3Blind c3 (V k))
        (_hpull : ∀ k : Fin 3, k ≠ feeIndex → alAmt sevm k.val ≠ 0 →
          CoinPullOkAt sevm (C3With c3 (Devm.getStor pre c3) (V k))
            (C3With c3 (Devm.getStor pre c3) (V (k + 1)))
            ((pre.getStor sevm.currentTarget).get (coinSlot k)) (alAmt sevm k.val) U 0x760 0x820)
        (_hskip : ∀ k : Fin 3, alAmt sevm k.val = 0 → ∀ b, V k b → V (k + 1) b)
        (_hfee : alAmt sevm 2 ≠ 0 →
          CoinBalOkAt sevm (C3With c3 (Devm.getStor pre c3) (V 2))
            (C3With c3 (Devm.getStor pre c3) (V 2))
            ((pre.getStor sevm.currentTarget).get (coinSlot 2)) B1 U 0x53c 0x5a0 ∧
          CoinPullOkAt sevm (C3With c3 (Devm.getStor pre c3) (V 2))
            (C3With c3 (Devm.getStor pre c3) (V 3))
            ((pre.getStor sevm.currentTarget).get (coinSlot 2)) (alAmt sevm 2) U 0x760 0x820 ∧
          CoinBalOkAt sevm (C3With c3 (Devm.getStor pre c3) (V 3))
            (C3With c3 (Devm.getStor pre c3) (V 3))
            ((pre.getStor sevm.currentTarget).get (coinSlot 2)) B2 U 0x87c 0x8e0)
        (_hG : costAddLiquidity s (alEnvW sevm T.toNat B1.toNat B2.toNat) (argV3 sevm 0) + 7 * U ≤
          G)
        (_hGm : (St pre [] Mem.empty G).gasMeasure + 3000 < 2 ^ 256),
        ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post), ∃ e : Env,
          e.supply = some T.toNat ∧ step s e (decodeCall sevm) = some o ∧
          RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post e o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state :=
  @Blanc.Composition.Curve3Pool3CrvHeadlines.pool_3crv_addLiquidity_live_entry

example : ∀ {pool c3 : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {ps₀ : Curve3Pool.State} {cs₀ : Blanc.Curve3Crv.State} {K₀ : Curve3Crv.Key → Prop} (trace : ConfiguredHistoryTrace cfg checkpoint future) (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image) (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image) (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state) (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace)) (env : PoolTraceEnv trace pool ps₀.coins ps₀.token) (notSystem : pool ≠ systemAddress) {sevm : Sevm} {pre : Devm} (target : sevm.currentTarget = pool) (state : pre.state = future.state),
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 pre ∧
      ∀ {o : Out} {T : B256} {V : Nat → Devm → Prop} {U G : Nat}
        (_hcode : sevm.code = code) (_hfork : CoveredFork sevm.benvStat.fork)
        (_hstatic : sevm.isStatic = false) (_hdepth : sevm.depth ≠ 0)
        (_hlen : 4 ≤ sevm.data.length) (_hcd : sevm.data.length < 2 ^ 256)
        (_hsel : Sevm.selector sevm = selRemoveLiquidityImbalance)
        (_hstep : step s (rliEnvW sevm T.toNat) (decodeCall sevm) = some o)
        (_htok : ¬ sevm.benvStat.rules.isPrecomp c3)
        (_hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
          ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : pre.getCode sevm.currentTarget ≠ .empty) (_hid : IdReady sevm pre)
        (_hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
          PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
            ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4)
        (_hU : 70000 ≤ U)
        (_hT : (Devm.getStor pre c3).get Curve3Crv.vySupplySlot = T)
        (_hburn : BurnFits (Devm.getStor pre c3) pool sevm.caller.toB256
          (Nat.toB256 (rliBurnAmt o)))
        (_hVc : ∀ k, k ≤ 3 → WClosed sevm (V k)) (_hVb : V 0 pre) (_hVs : ∀ k, C3Blind c3 (V k))
        (_hpush : ∀ k : Fin 3, rliAmt sevm k.val ≠ 0 →
          CoinPushOkAt sevm
            (C3With c3 (burnStor (Devm.getStor pre c3) sevm.caller.toB256
              (Nat.toB256 (rliBurnAmt o))) (V k))
            (C3With c3 (burnStor (Devm.getStor pre c3) sevm.caller.toB256
              (Nat.toB256 (rliBurnAmt o))) (V (k + 1)))
            ((pre.getStor sevm.currentTarget).get (coinSlot k)) (rliAmt sevm k.val) U 0xaa0 0xb40)
        (_hskip : ∀ k : Fin 3, rliAmt sevm k.val = 0 → ∀ b, V k b → V (k + 1) b)
        (_hG : costImbalance s (rliEnvW sevm T.toNat) (argV3 sevm 0) + 5 * U ≤ G)
        (_hGm : (St pre [] Mem.empty G).gasMeasure + 3000 < 2 ^ 256),
        ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post),
          RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (rliEnvW sevm T.toNat)
            o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state ∧
          C3With c3 (burnStor (Devm.getStor pre c3) sevm.caller.toB256
            (Nat.toB256 (rliBurnAmt o))) (V 3) post :=
  @Blanc.Composition.Curve3Pool3CrvHeadlines.pool_3crv_removeLiquidityImbalance_live_entry

example : ∀ {pool c3 : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {ps₀ : Curve3Pool.State} {cs₀ : Blanc.Curve3Crv.State} {K₀ : Curve3Crv.Key → Prop} (trace : ConfiguredHistoryTrace cfg checkpoint future) (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image) (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image) (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state) (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace)) (env : PoolTraceEnv trace pool ps₀.coins ps₀.token) (notSystem : pool ≠ systemAddress) {sevm : Sevm} {pre : Devm} (target : sevm.currentTarget = pool) (state : pre.state = future.state),
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 pre ∧
      ∀ {o : Out} {i : Fin 3} {T : B256} {V : Nat → Devm → Prop} {U G : Nat}
        (_hcode : sevm.code = code) (_hfork : CoveredFork sevm.benvStat.fork)
        (_hstatic : sevm.isStatic = false) (_hdepth : sevm.depth ≠ 0)
        (_hlen : 4 ≤ sevm.data.length) (_hcd : sevm.data.length < 2 ^ 256)
        (_hsel : Sevm.selector sevm = selRemoveLiquidityOneCoin)
        (_hi : i.val = (ocI sevm).toNat)
        (_hstep : step s (ocEnv sevm i T.toNat) (decodeCall sevm) = some o)
        (_htok : ¬ sevm.benvStat.rules.isPrecomp c3)
        (_hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
          ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : pre.getCode sevm.currentTarget ≠ .empty) (_hid : IdReady sevm pre)
        (_hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
          PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
            ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4)
        (_hU : 70000 ≤ U)
        (_hT : (Devm.getStor pre c3).get Curve3Crv.vySupplySlot = T)
        (_hburn : BurnFits (Devm.getStor pre c3) pool sevm.caller.toB256 (ocAmt sevm))
        (_hVc : ∀ k, k ≤ 1 → WClosed sevm (V k)) (_hVb : V 0 pre) (_hVs : C3Blind c3 (V 0))
        (_hpush : CoinPushOkAt sevm
          (C3With c3 (burnStor (Devm.getStor pre c3) sevm.caller.toB256 (ocAmt sevm)) (V 0))
          (C3With c3 (burnStor (Devm.getStor pre c3) sevm.caller.toB256 (ocAmt sevm)) (V 1))
          ((pre.getStor sevm.currentTarget).get (coinSlot i)) (Nat.toB256 (ocPushAmt o)) U
          0x540 0x5e0)
        (_hG : costOneCoin s (ocEnv sevm i T.toNat) (ocAmt sevm).toNat i + 3 * U ≤ G)
        (_hGm : (St pre [] Mem.empty G).gasMeasure + 2000 < 2 ^ 256),
        ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post), ∃ T' : Nat,
          RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (ocEnv sevm i T') o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state ∧
          C3With c3 (burnStor (Devm.getStor pre c3) sevm.caller.toB256 (ocAmt sevm)) (V 1)
            post :=
  @Blanc.Composition.Curve3Pool3CrvHeadlines.pool_3crv_removeLiquidityOneCoin_live_entry

end Blanc.Composition.Curve3Pool3CrvHeadlines

namespace Blanc.Composition.Curve3Pool3CrvInstance
open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool
open Blanc.Composition.Curve3PoolCalleeLive
open Blanc.Composition.Curve3Pool3CrvHeadlines (C3At c3At_burn c3At_mint precomp_false)
open Blanc.Lift.Token20 (balSlot allowSlot balanceOfGas balanceOfPost boHolder balanceOf_runExact cert_check cert_jumpsOk)

example : ∀ {sevm : Sevm} {pre : Devm} {T : B256} (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0) (hc3 : C3Entry sevm pre T) (hcoins : T20Coins sevm pre) (hburn : BurnFits (Devm.getStor pre (tokOf sevm pre)) sevm.currentTarget sevm.caller.toB256
      (rlAmt sevm)) (hfits : ∀ k : Fin 3, T20MoveFits (pre.getStor (coinOf sevm pre k)) sevm.currentTarget
      sevm.caller (balAt (pre.getStor sevm.currentTarget) k * rlAmt sevm / T)),
    (∀ k, k ≤ 3 → WClosed sevm (rlWorld sevm pre k)) ∧ rlWorld sevm pre 0 pre ∧
      SupplyOk sevm (rlWorld sevm pre 0) ((pre.getStor sevm.currentTarget).get tokenSlot) T
        80000 ∧
      (∀ k : Fin 3, CoinPushOkAt sevm (rlWorld sevm pre k) (rlWorld sevm pre (k + 1))
        ((pre.getStor sevm.currentTarget).get (coinSlot k))
        (balAt (pre.getStor sevm.currentTarget) k * rlAmt sevm / T) 80000 0x520 0x5c0) ∧
      BurnOkTo sevm (rlWorld sevm pre 3) (rlWorld sevm pre 4)
        ((pre.getStor sevm.currentTarget).get tokenSlot) (rlAmt sevm) 80000 :=
  @Blanc.Composition.Curve3Pool3CrvInstance.removeLiquidity_premises_satisfiable

example : ∀ {sevm : Sevm} {pre : Devm} {T m : B256} (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0) (hc3 : C3Entry sevm pre T) (hcoins : T20Coins sevm pre) (hmint : MintFits (Devm.getStor pre (tokOf sevm pre)) sevm.currentTarget sevm.caller.toB256 m) (hfits : ∀ k : Fin 3, alAmt sevm k.val ≠ 0 → T20PullFits (pre.getStor (coinOf sevm pre k))
      sevm.caller sevm.currentTarget sevm.currentTarget (alAmt sevm k.val)),
    (∀ k, k ≤ 4 → WClosed sevm (alWorld sevm pre m k)) ∧ alWorld sevm pre m 0 pre ∧
      SupplyOkAt sevm (alWorld sevm pre m 0) (alWorld sevm pre m 0)
        ((pre.getStor sevm.currentTarget).get tokenSlot) T 80000 0x27c 0x2c0 ∧
      (∀ k : Fin 3, k ≠ feeIndex → alAmt sevm k.val ≠ 0 →
        CoinPullOkAt sevm (alWorld sevm pre m k) (alWorld sevm pre m (k + 1))
          ((pre.getStor sevm.currentTarget).get (coinSlot k)) (alAmt sevm k.val) 80000 0x760
          0x820) ∧
      (∀ k : Fin 3, alAmt sevm k.val = 0 → ∀ b, alWorld sevm pre m k b →
        alWorld sevm pre m (k + 1) b) ∧
      (alAmt sevm 2 ≠ 0 →
        CoinBalOkAt sevm (alWorld sevm pre m 2) (alWorld sevm pre m 2)
          ((pre.getStor sevm.currentTarget).get (coinSlot 2))
          ((pre.getStor (coinOf sevm pre 2)).get
            (Blanc.Lift.Token20.balSlot sevm.currentTarget)) 80000 0x53c 0x5a0 ∧
        CoinPullOkAt sevm (alWorld sevm pre m 2) (alWorld sevm pre m 3)
          ((pre.getStor sevm.currentTarget).get (coinSlot 2)) (alAmt sevm 2) 80000 0x760 0x820 ∧
        CoinBalOkAt sevm (alWorld sevm pre m 3) (alWorld sevm pre m 3)
          ((pre.getStor sevm.currentTarget).get (coinSlot 2))
          ((alFeeStor sevm pre).get (Blanc.Lift.Token20.balSlot sevm.currentTarget))
          80000 0x87c 0x8e0) ∧
      MintOkAt sevm (alWorld sevm pre m 3) (alWorld sevm pre m 4)
        ((pre.getStor sevm.currentTarget).get tokenSlot) m 80000 0xc7c 0xd00 :=
  @Blanc.Composition.Curve3Pool3CrvInstance.addLiquidity_premises_satisfiable

example : ∀ {sevm : Sevm} {pre : Devm} {T m : B256} (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0) (hc3 : C3Entry sevm pre T) (hcoins : T20Coins sevm pre) (hburn : BurnFits (Devm.getStor pre (tokOf sevm pre)) sevm.currentTarget sevm.caller.toB256 m) (hfits : ∀ k : Fin 3, rliAmt sevm k.val ≠ 0 → T20MoveFits (pre.getStor (coinOf sevm pre k))
      sevm.currentTarget sevm.caller (rliAmt sevm k.val)),
    (∀ j, j ≤ 4 → WClosed sevm (rliWorld sevm pre m j)) ∧ rliWorld sevm pre m 0 pre ∧
      SupplyOkAt sevm (rliWorld sevm pre m 0) (rliWorld sevm pre m 0)
        ((pre.getStor sevm.currentTarget).get tokenSlot) T 80000 0x17c 0x1c0 ∧
      BurnOkAt sevm (rliWorld sevm pre m 0) (rliWorld sevm pre m 1)
        ((pre.getStor sevm.currentTarget).get tokenSlot) m 80000 0x85c 0x8e0 ∧
      (∀ k : Fin 3, rliAmt sevm k.val ≠ 0 →
        CoinPushOkAt sevm (rliWorld sevm pre m (k + 1)) (rliWorld sevm pre m (k + 2))
          ((pre.getStor sevm.currentTarget).get (coinSlot k)) (rliAmt sevm k.val) 80000 0xaa0
          0xb40) ∧
      (∀ k : Fin 3, rliAmt sevm k.val = 0 → ∀ b, rliWorld sevm pre m (k + 1) b →
        rliWorld sevm pre m (k + 2) b) :=
  @Blanc.Composition.Curve3Pool3CrvInstance.removeLiquidityImbalance_premises_satisfiable

example : ∀ {sevm : Sevm} {pre : Devm} {T v : B256} {i : Fin 3} (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0) (hc3 : C3Entry sevm pre T) (hcode : pre.getCode (coinOf sevm pre i) = Blanc.Lift.Token20.code) (hprec : ¬ sevm.benvStat.rules.isPrecomp (coinOf sevm pre i)) (hpool : coinOf sevm pre i ≠ sevm.currentTarget) (htok : coinOf sevm pre i ≠ tokOf sevm pre) (hburn : BurnFits (Devm.getStor pre (tokOf sevm pre)) sevm.currentTarget sevm.caller.toB256
      (ocAmt sevm)) (hfits : T20MoveFits (pre.getStor (coinOf sevm pre i)) sevm.currentTarget sevm.caller v),
    WClosed sevm (ocWorld sevm pre (Devm.getStor pre (tokOf sevm pre)) i) ∧
      WClosed sevm (ocWorld sevm pre (burnStor (Devm.getStor pre (tokOf sevm pre))
        sevm.caller.toB256 (ocAmt sevm)) i) ∧
      ocWorld sevm pre (Devm.getStor pre (tokOf sevm pre)) i pre ∧
      SupplyOkAt sevm (ocWorld sevm pre (Devm.getStor pre (tokOf sevm pre)) i)
        (ocWorld sevm pre (Devm.getStor pre (tokOf sevm pre)) i)
        ((pre.getStor sevm.currentTarget).get tokenSlot) T 80000 0x2bc 0x300 ∧
      BurnOkAt sevm (ocWorld sevm pre (Devm.getStor pre (tokOf sevm pre)) i)
        (ocWorld sevm pre (burnStor (Devm.getStor pre (tokOf sevm pre)) sevm.caller.toB256
          (ocAmt sevm)) i)
        ((pre.getStor sevm.currentTarget).get tokenSlot) (ocAmt sevm) 80000 0x31c 0x3a0 ∧
      WClosed sevm (fun _ => True) ∧
      CoinPushOkAt sevm (ocWorld sevm pre (burnStor (Devm.getStor pre (tokOf sevm pre))
          sevm.caller.toB256 (ocAmt sevm)) i) (fun _ => True)
        ((pre.getStor sevm.currentTarget).get (coinSlot i)) v 80000 0x540 0x5e0 :=
  @Blanc.Composition.Curve3Pool3CrvInstance.removeLiquidityOneCoin_premises_satisfiable

end Blanc.Composition.Curve3Pool3CrvInstance

namespace Blanc.Composition.Curve3Pool3CrvInstance
open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.StableSwapNewton
open Blanc.Composition.Curve3Pool3CrvJoint

example : ∀ {sevm : Sevm} {b : Devm} (hf : Curve3Pool3CrvInstance.ExFrame sevm b),
    ∃ post, ∃ exc : Exec 0 sevm b (.ok post), ∃ bp bq,
      pullIn (exEnv sevm 0 1 bp bq) 0 100 =
        pullIn (exEnv sevm 0 1 (exBalOpt 0 0) (exBalOpt 0 0)) 0 100 ∧
      RawEffect ⟨0, sevm, b, .ok post, exc⟩ post (exEnv sevm 0 1 bp bq) exOut ∧
        Checkpoint (post.getStor sevm.currentTarget) exOut.state ∧
        post.error = none ∧ 0 ≤ post.refundCounter :=
  @Blanc.Composition.Curve3Pool3CrvInstance.ex_frame_live

end Blanc.Composition.Curve3Pool3CrvInstance

namespace Blanc.Composition.Curve3Pool3CrvInstance
open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool
open Blanc.Composition.Curve3Pool3CrvJoint

example : ∃ post, ∃ exc : Exec 0 (cSevm rlwData) (St (wPre rlwData) [] Mem.empty 878400) (.ok post),
      RawEffect ⟨0, cSevm rlwData, St (wPre rlwData) [] Mem.empty 878400, .ok post, exc⟩ post
          (rlEnv (cSevm rlwData) 6000) rlOut ∧
        Checkpoint (post.getStor poolAddr) rlOut.state :=
  @Blanc.Composition.Curve3Pool3CrvInstance.rl_frame_live

example : ∃ post, ∃ exc : Exec 0 (cSevm ocwData) (St (wPre ocwData) [] Mem.empty 878400) (.ok post),
      ∃ T' : Nat,
      RawEffect ⟨0, cSevm ocwData, St (wPre ocwData) [] Mem.empty 878400, .ok post, exc⟩ post
          (ocEnv (cSevm ocwData) 1 T') ocOut ∧
        Checkpoint (post.getStor poolAddr) ocOut.state :=
  @Blanc.Composition.Curve3Pool3CrvInstance.oc_frame_live

example : ∃ post, ∃ exc : Exec 0 (cSevm alDataW) (St (wPre alDataW) [] Mem.empty 1110000) (.ok post),
      ∃ e : Env,
      e.supply = some (6000 : B256).toNat ∧
        step poolState e (decodeCall (cSevm alDataW)) = some alOutW ∧
        RawEffect ⟨0, cSevm alDataW, St (wPre alDataW) [] Mem.empty 1110000, .ok post, exc⟩ post
          e alOutW ∧
        Checkpoint (post.getStor poolAddr) alOutW.state :=
  @Blanc.Composition.Curve3Pool3CrvInstance.al_frame_live

example : ∃ post, ∃ exc : Exec 0 (cSevm rliDataW) (St (wPre rliDataW) [] Mem.empty 878400) (.ok post),
      RawEffect ⟨0, cSevm rliDataW, St (wPre rliDataW) [] Mem.empty 878400, .ok post, exc⟩ post
          (rliEnvW (cSevm rliDataW) (6000 : B256).toNat) rliOutW ∧
        Checkpoint (post.getStor poolAddr) rliOutW.state ∧
        rliWorld (cSevm rliDataW) (wPre rliDataW) (Nat.toB256 (rliBurnAmt rliOutW)) 4 post :=
  @Blanc.Composition.Curve3Pool3CrvInstance.rli_frame_live

end Blanc.Composition.Curve3Pool3CrvInstance

namespace Blanc.Composition.Curve3Pool3CrvJoint
open Jaune Blanc Blanc.Lift.FiniteCheckpoint

example : ∀ {pool c3crv : Adr} {ps : Lift.Curve3Pool.State} {rows : List C3Row} {base : C3Base} {w : Jaune.State} (h : checkJoint pool c3crv ps rows base w = true),
    JointCheckpoint pool c3crv ps (rowsState base rows) (c3Keys rows) w :=
  @Blanc.Composition.Curve3Pool3CrvJoint.checkJoint_sound

example : JointCheckpoint poolAddr c3crvAddr poolState (rowsState c3Base c3Rows)
      (c3Keys c3Rows) world :=
  @Blanc.Composition.Curve3Pool3CrvJoint.world_joint

end Blanc.Composition.Curve3Pool3CrvJoint

namespace Blanc.Composition.Curve3Pool3CrvInstance
open Jaune Blanc Blanc.Lift
open Blanc.Composition.Curve3Pool3CrvJoint

example : JointCheckpoint poolAddr c3crvAddr poolState (rowsState c3Base c3Rows) (c3Keys c3Rows) P0 :=
  @Blanc.Composition.Curve3Pool3CrvInstance.p0_joint

end Blanc.Composition.Curve3Pool3CrvInstance

namespace Blanc.Composition.Curve3Pool3CrvInstance
open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Blanc.BlockForward
open Blanc.Composition.Curve3Pool3CrvJoint
open Blanc.Composition.Curve3PoolSupply (supplyAt pool_3crv_u3)
open Blanc.Lift.Curve3Pool (PoolInvocation PoolRun poolSubtreeFrames)
open Blanc.SyntheticBpo2Envelope (config checkpoint input)
open Blanc.SyntheticSystemWorld (systemAddresses SystemCodes systemCode)

example : ∀ {st : Jaune.State} (canonical : st.Canonical) (bound : SumNof st.bal) (ag : AgreesP0 st),
    ClosedExchangeOutcome st :=
  @Blanc.Composition.Curve3Pool3CrvInstance.curve3pool_closed_agreeing

example : ClosedExchangeOutcome P0 :=
  @Blanc.Composition.Curve3Pool3CrvInstance.curve3pool_closed_instance

end Blanc.Composition.Curve3Pool3CrvInstance

namespace Blanc.Composition.Curve3Pool3CrvInstance
open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Composition.Curve3Pool3CrvJoint

example : ∀ {benv : Benv} (ctx : ExTxContext benv),
    ∃ (s1 : Jaune.State) (bout : BlockOutput),
      processTransaction benv BlockOutput.init signedExchangeTx 0 = .ok (s1, bout) ∧
      parseDepositRequests bout = .ok [] ∧ bout.blockGasUsed ≤ 1000000 :=
  @Blanc.Composition.Curve3Pool3CrvInstance.ex_transaction

end Blanc.Composition.Curve3Pool3CrvInstance

namespace Blanc.Composition.Curve3Pool3CrvInstance
open Jaune Blanc Blanc.Lift

example : recoverSender 1 signedExchangeTx = .ok trader :=
  @Blanc.Composition.Curve3Pool3CrvInstance.exchange_recoveredSender

end Blanc.Composition.Curve3Pool3CrvInstance

namespace Blanc.Composition.Curve3Pool3CrvInstance
open Jaune Blanc Blanc.Lift Blanc.Composition.Curve3Pool3CrvJoint
open Blanc.Lift (vcsm_benvStat vcsm_caller vcsm_currentTarget vcsm_value vcsm_isStatic vcsm_code vcsm_state vcsm_gasLeft vcsm_stack vcsm_memory vcsm_error mem_read_fst callSpawnParent_memory_data addAccessedAddress_setMach_memory)
open Blanc.Lift.Token20 (balSlot allowSlot)

example : ∀ {sevm : Sevm} {t amt : B256} {W W' : Devm → Prop} {c : Adr} {U : Nat} {ii oi : B256} (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0) (hprec : ¬ sevm.benvStat.rules.isPrecomp c) (ht : t.toAdr = c) (hne : c ≠ sevm.currentTarget) (hU : 80000 ≤ U) (hii : ii.toNat + 0x64 ≤ 3104) (hoi : oi.toNat + 32 ≤ 3104) (hW : ∀ b, W b → b.getCode c = Blanc.Lift.Token20.code ∧
      T20PullFits (b.getStor c) sevm.caller sevm.currentTarget sevm.currentTarget amt) (hW' : ∀ b d, W b → CoinLeaves c (t20Move (t20Allow (b.getStor c) sevm.caller
        sevm.currentTarget amt) sevm.caller sevm.currentTarget amt)
      ((getOrigAcct sevm c).stor = b.getStor c ∧ c ∉ b.createdAccounts ∧
        allowSlot sevm.caller sevm.currentTarget ≠ balSlot sevm.caller ∧
        allowSlot sevm.caller sevm.currentTarget ≠ balSlot sevm.currentTarget ∧
        balSlot sevm.caller ≠ balSlot sevm.currentTarget) b d → W' d),
    Curve3Pool.CoinPullOkAt sevm W W' t amt U ii oi :=
  @Blanc.Composition.Curve3Pool3CrvInstance.token20_coinPullOkAt

example : ∀ {sevm : Sevm} {t amt : B256} {W W' : Devm → Prop} {c : Adr} {U : Nat} {ii oi : B256} (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0) (hprec : ¬ sevm.benvStat.rules.isPrecomp c) (ht : t.toAdr = c) (hne : c ≠ sevm.currentTarget) (hU : 80000 ≤ U) (hii : ii.toNat + 0x44 ≤ 3104) (hoi : oi.toNat + 32 ≤ 3104) (hW : ∀ b, W b → b.getCode c = Blanc.Lift.Token20.code ∧
      T20MoveFits (b.getStor c) sevm.currentTarget sevm.caller amt) (hW' : ∀ b d, W b → CoinLeaves c (t20Move (b.getStor c) sevm.currentTarget sevm.caller amt)
      ((getOrigAcct sevm c).stor = b.getStor c ∧ c ∉ b.createdAccounts ∧
        balSlot sevm.currentTarget ≠ balSlot sevm.caller) b d → W' d),
    Curve3Pool.CoinPushOkAt sevm W W' t amt U ii oi :=
  @Blanc.Composition.Curve3Pool3CrvInstance.token20_coinPushOkAt

end Blanc.Composition.Curve3Pool3CrvInstance

namespace Blanc.StableSwapNewton

example : ∀ {x : Fin 3 → Nat} {amp tol v : Nat} (h : getDChk x amp tol = some v) (hx : ∀ i, 0 < x i) (hamp : 1 ≤ amp),
    aboveRoot x (amp * 3) (v + 1) :=
  @Blanc.StableSwapNewton.getDChk_lower

example : ¬ aboveRoot ceilW 600 (getDCeil ceilW 200 1 + 1) ∧
    getDCeil ceilW 200 1 = 14615550493253435060542 ∧
    floorRoot ceilW 600 = 14615550493253435060544 ∧
    getD ceilW 200 1 = 14615550493253435060546 :=
  @Blanc.StableSwapNewton.getDCeil_breaks_lower

example : (∀ i, monoPre i ≤ monoPost i) ∧
    getD monoPost 1 1 < getD monoPre 1 1 ∧ getD monoPost 1 2 < getD monoPre 1 2 :=
  @Blanc.StableSwapNewton.getD_not_mono

example : runsOut capW 6000 1 255 (sum3 capW) = true ∧
    getD capW 2000 1 = (bodyD capW 6000)^[255] (sum3 capW) ∧
    getD capW 2000 1 = 680031527231617479170632831 ∧
    bodyD capW 6000 680031527231617479170632831 = 680031527231617479170632834 ∧
    bodyD capW 6000 680031527231617479170632834 = 680031527231617479170632831 ∧
    floorRoot capW 6000 + 2 = 680031527231617479170632831 :=
  @Blanc.StableSwapNewton.getD_cap_cycle

example : ∀ {amp : Nat} {i : Fin 3} {xp : Fin 3 → Nat} {D v : Nat} (h : getYDChk amp i xp D = some v),
    rootOrSucc (cOf (xp (others i).1) (xp (others i).2) D (amp * 3))
      (bOf (xp (others i).1) (xp (others i).2) D (amp * 3)) D v :=
  @Blanc.StableSwapNewton.getYDChk_rootOrSucc

example : ∀ {amp : Nat} {i j : Fin 3} {x : Nat} {xp : Fin 3 → Nat} {v : Nat} (h : getYChk amp i j x xp = some v),
    rootOrSucc (cOf (withAt xp i x (others j).1) (withAt xp i x (others j).2)
      (getD xp amp 1) (amp * 3)) (bOf (withAt xp i x (others j).1)
      (withAt xp i x (others j).2) (getD xp amp 1) (amp * 3)) (getD xp amp 1) v :=
  @Blanc.StableSwapNewton.getYChk_rootOrSucc

example : ∀ {c b D v : Nat} (h : loopYChk c b D 1 255 D = some v) (hc : c ≤ D ^ 4),
    rootOrSucc c b D v :=
  @Blanc.StableSwapNewton.loopYChk_rootOrSucc

end Blanc.StableSwapNewton

namespace Blanc.Lift.Curve3Pool
open Jaune Blanc Blanc.Lift Blanc.StableSwapNewton

example : ∀ {sevm : Sevm} {pre post : Devm} {s : State} (exc : Exec 0 sevm pre (.ok post)) (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256) (hsel : Sevm.selector sevm = selCalcWithdrawOneCoin) (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256) (hck : Checkpoint (pre.getStor sevm.currentTarget) s) (htok : ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr),
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o ∧
      ∃ (hi : arg sevm 1 < 3) (T : Nat), e.supply = some T ∧
        CwFirstGetYDLaw s e.time (arg sevm 0) ⟨arg sevm 1, hi⟩ T :=
  @Blanc.Lift.Curve3Pool.pool_getYD_rootOrSucc_cwo

example : ∀ {sevm : Sevm} {pre post : Devm} {s : State} (exc : Exec 0 sevm pre (.ok post)) (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256) (hsel : Sevm.selector sevm = selRemoveLiquidityOneCoin) (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256) (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hck : Checkpoint (pre.getStor sevm.currentTarget) s) (henv : PoolFrameEnv ⟨0, sevm, pre, .ok post, exc⟩),
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o ∧
      ∃ (hi : arg sevm 1 < 3) (T : Nat), e.supply = some T ∧
        CwFirstGetYDLaw s e.time (arg sevm 0) ⟨arg sevm 1, hi⟩ T :=
  @Blanc.Lift.Curve3Pool.pool_getYD_rootOrSucc_oneCoin

example : ∀ {sevm : Sevm} {pre post : Devm} {s : State} (exc : Exec 0 sevm pre (.ok post)) (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256) (hsel : Sevm.selector sevm = selCalcWithdrawOneCoin) (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256) (hck : Checkpoint (pre.getStor sevm.currentTarget) s) (htok : ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr),
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o ∧
      ∃ (hi : arg sevm 1 < 3) (T : Nat), e.supply = some T ∧
        CwSecondGetYDLaw s e.time (arg sevm 0) ⟨arg sevm 1, hi⟩ T :=
  @Blanc.Lift.Curve3Pool.pool_getYD2_rootOrSucc_cwo

example : ∀ {sevm : Sevm} {pre post : Devm} {s : State} (exc : Exec 0 sevm pre (.ok post)) (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256) (hsel : Sevm.selector sevm = selRemoveLiquidityOneCoin) (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256) (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hck : Checkpoint (pre.getStor sevm.currentTarget) s) (henv : PoolFrameEnv ⟨0, sevm, pre, .ok post, exc⟩),
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o ∧
      ∃ (hi : arg sevm 1 < 3) (T : Nat), e.supply = some T ∧
        CwSecondGetYDLaw s e.time (arg sevm 0) ⟨arg sevm 1, hi⟩ T :=
  @Blanc.Lift.Curve3Pool.pool_getYD2_rootOrSucc_oneCoin

example : ∀ {sevm : Sevm} {pre post : Devm} {s : State} (exc : Exec 0 sevm pre (.ok post)) (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256) (hsel : Sevm.selector sevm = selExchange) (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256) (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hck : Checkpoint (pre.getStor sevm.currentTarget) s) (henv : PoolFrameEnv ⟨0, sevm, pre, .ok post, exc⟩),
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o ∧
      ∃ (i j : Fin 3) (dx md : Nat), decodeCall sevm = .exchange i.val j.val dx md ∧
      ∃ (amp : Nat) (x0 x1 x2 x y : B256), aChk s e.time = some amp ∧
        xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
        getYChk amp i j x.toNat (V3.mk x0.toNat x1.toNat x2.toNat).get = some y.toNat ∧
        rootOrSucc
          (cOf (withAt (V3.mk x0.toNat x1.toNat x2.toNat).get i x.toNat (others j).1)
            (withAt (V3.mk x0.toNat x1.toNat x2.toNat).get i x.toNat (others j).2)
            (getD (V3.mk x0.toNat x1.toNat x2.toNat).get amp 1) (amp * 3))
          (bOf (withAt (V3.mk x0.toNat x1.toNat x2.toNat).get i x.toNat (others j).1)
            (withAt (V3.mk x0.toNat x1.toNat x2.toNat).get i x.toNat (others j).2)
            (getD (V3.mk x0.toNat x1.toNat x2.toNat).get amp 1) (amp * 3))
          (getD (V3.mk x0.toNat x1.toNat x2.toNat).get amp 1) y.toNat :=
  @Blanc.Lift.Curve3Pool.pool_getY_rootOrSucc_exchange

example : ∀ {sevm : Sevm} {pre post : Devm} {s : State} (exc : Exec 0 sevm pre (.ok post)) (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256) (hsel : Sevm.selector sevm = selGetDy) (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256) (hck : Checkpoint (pre.getStor sevm.currentTarget) s),
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o ∧
      ∃ (hi : (dyI sevm).toNat < 3) (hj : (dyJ sevm).toNat < 3) (amp : Nat)
        (x0 x1 x2 y : B256),
        aChk s e.time = some amp ∧ xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
        getYChk amp ⟨(dyI sevm).toNat, hi⟩ ⟨(dyJ sevm).toNat, hj⟩ (dyX sevm x0 x1 x2).toNat
          (V3.mk x0.toNat x1.toNat x2.toNat).get = some y.toNat ∧
        rootOrSucc
          (cOf (withAt (V3.mk x0.toNat x1.toNat x2.toNat).get ⟨(dyI sevm).toNat, hi⟩
              (dyX sevm x0 x1 x2).toNat (others ⟨(dyJ sevm).toNat, hj⟩).1)
            (withAt (V3.mk x0.toNat x1.toNat x2.toNat).get ⟨(dyI sevm).toNat, hi⟩
              (dyX sevm x0 x1 x2).toNat (others ⟨(dyJ sevm).toNat, hj⟩).2)
            (getD (V3.mk x0.toNat x1.toNat x2.toNat).get amp 1) (amp * 3))
          (bOf (withAt (V3.mk x0.toNat x1.toNat x2.toNat).get ⟨(dyI sevm).toNat, hi⟩
              (dyX sevm x0 x1 x2).toNat (others ⟨(dyJ sevm).toNat, hj⟩).1)
            (withAt (V3.mk x0.toNat x1.toNat x2.toNat).get ⟨(dyI sevm).toNat, hi⟩
              (dyX sevm x0 x1 x2).toNat (others ⟨(dyJ sevm).toNat, hj⟩).2)
            (getD (V3.mk x0.toNat x1.toNat x2.toNat).get amp 1) (amp * 3))
          (getD (V3.mk x0.toNat x1.toNat x2.toNat).get amp 1) y.toNat :=
  @Blanc.Lift.Curve3Pool.pool_getY_rootOrSucc_dy

example : ∀ {sevm : Sevm} {pre post : Devm} {s : State} (exc : Exec 0 sevm pre (.ok post)) (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256) (hsel : Sevm.selector sevm = selGetDyUnderlying) (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256) (hck : Checkpoint (pre.getStor sevm.currentTarget) s),
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o ∧
      ∃ (hi : (dyI sevm).toNat < 3) (hj : (dyJ sevm).toNat < 3) (amp : Nat)
        (x0 x1 x2 y : B256),
        aChk s e.time = some amp ∧ xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
        getYChk amp ⟨(dyI sevm).toNat, hi⟩ ⟨(dyJ sevm).toNat, hj⟩ (dyuX sevm x0 x1 x2).toNat
          (V3.mk x0.toNat x1.toNat x2.toNat).get = some y.toNat ∧
        rootOrSucc
          (cOf (withAt (V3.mk x0.toNat x1.toNat x2.toNat).get ⟨(dyI sevm).toNat, hi⟩
              (dyuX sevm x0 x1 x2).toNat (others ⟨(dyJ sevm).toNat, hj⟩).1)
            (withAt (V3.mk x0.toNat x1.toNat x2.toNat).get ⟨(dyI sevm).toNat, hi⟩
              (dyuX sevm x0 x1 x2).toNat (others ⟨(dyJ sevm).toNat, hj⟩).2)
            (getD (V3.mk x0.toNat x1.toNat x2.toNat).get amp 1) (amp * 3))
          (bOf (withAt (V3.mk x0.toNat x1.toNat x2.toNat).get ⟨(dyI sevm).toNat, hi⟩
              (dyuX sevm x0 x1 x2).toNat (others ⟨(dyJ sevm).toNat, hj⟩).1)
            (withAt (V3.mk x0.toNat x1.toNat x2.toNat).get ⟨(dyI sevm).toNat, hi⟩
              (dyuX sevm x0 x1 x2).toNat (others ⟨(dyJ sevm).toNat, hj⟩).2)
            (getD (V3.mk x0.toNat x1.toNat x2.toNat).get amp 1) (amp * 3))
          (getD (V3.mk x0.toNat x1.toNat x2.toNat).get amp 1) y.toNat :=
  @Blanc.Lift.Curve3Pool.pool_getY_rootOrSucc_dyu

end Blanc.Lift.Curve3Pool

namespace Blanc.Lift.Curve3Pool.U4Exactness
open Blanc.StableSwapNewton

example : getYDChk 873512 0 scaled.get 2682365305673 = some 1 ∧
    1 ≠ rootQ
      (cOf (scaled.get (others 0).1) (scaled.get (others 0).2) 2682365305673 (873512 * 3))
      (bOf (scaled.get (others 0).1) (scaled.get (others 0).2) 2682365305673 (873512 * 3))
      2682365305673 :=
  @Blanc.Lift.Curve3Pool.U4Exactness.callee_not_floor

end Blanc.Lift.Curve3Pool.U4Exactness

namespace Blanc.Lift.Curve3Pool.U4GetY
open Blanc.StableSwapNewton

example : getYChk 100 0 1 6108135850388754573 scaled.get = some 1 ∧
    1 ≠ rootQ
      (cOf (withAt scaled.get 0 6108135850388754573 (others 1).1)
        (withAt scaled.get 0 6108135850388754573 (others 1).2) 129202949715990 (100 * 3))
      (bOf (withAt scaled.get 0 6108135850388754573 (others 1).1)
        (withAt scaled.get 0 6108135850388754573 (others 1).2) 129202949715990 (100 * 3))
      129202949715990 :=
  @Blanc.Lift.Curve3Pool.U4GetY.callee_not_floor

end Blanc.Lift.Curve3Pool.U4GetY

namespace Blanc.Lift.Curve3Pool.U4GetY.Primary
open Blanc.StableSwapNewton

example : getYChk 1000 0 2 58490115785954294677660391985888334 scaled.get = some 27029 ∧
    27029 ≠ rootQ
      (cOf (withAt scaled.get 0 58490115785954294677660391985888334 (others 2).1)
        (withAt scaled.get 0 58490115785954294677660391985888334 (others 2).2)
        135660340458536610005534075 (1000 * 3))
      (bOf (withAt scaled.get 0 58490115785954294677660391985888334 (others 2).1)
        (withAt scaled.get 0 58490115785954294677660391985888334 (others 2).2)
        135660340458536610005534075 (1000 * 3))
      135660340458536610005534075 :=
  @Blanc.Lift.Curve3Pool.U4GetY.Primary.callee_not_floor

end Blanc.Lift.Curve3Pool.U4GetY.Primary

namespace Blanc.Lift.Curve3Pool
open Blanc.StableSwapNewton

example : ∃ w w' r, reach 1 1000000 10000000000 exchangePre = some w ∧
      worldRun w t0 1 (.exchange 1 0 1512569520375 0) = some (w', r) ∧
      VpFalls w w' t0 :=
  @Blanc.Lift.Curve3Pool.u3_refuted_exchange

example : ∃ w w' r, reach 1 544575293 0 addLiquidityPre = some w ∧
      worldRun w t0 1 (.addLiquidity ⟨3, 0, 0⟩ 0) = some (w', r) ∧
      VpFalls w w' t0 :=
  @Blanc.Lift.Curve3Pool.u3_refuted_add_liquidity

example : ∃ w w' r, reach 10 0 10000000000 removeLiquidityPre = some w ∧
      worldRun w t0 1 (.removeLiquidity 2 ⟨0, 0, 0⟩) = some (w', r) ∧
      VpFalls w w' t0 :=
  @Blanc.Lift.Curve3Pool.u3_refuted_remove_liquidity

example : ∃ w w' r, reach 1 402788378 0 removeLiquidityImbalancePre = some w ∧
      worldRun w t0 1 (.removeLiquidityImbalance ⟨100000, 0, 0⟩ (2 ^ 256 - 1)) = some (w', r) ∧
      VpFalls w w' t0 :=
  @Blanc.Lift.Curve3Pool.u3_refuted_remove_liquidity_imbalance

example : ∃ w w' r, reach 200 1000000 5000000000 removeLiquidityOneCoinDeployedPre = some w ∧
      worldRun w t0 1 (.removeLiquidityOneCoin 1000 0 0) = some (w', r) ∧
      VpFalls w w' t0 :=
  @Blanc.Lift.Curve3Pool.u3_refuted_remove_liquidity_one_coin_deployed

example : ∃ w w' r, reach 1 5000000000 10000000000 donateAdminFeesPre = some w ∧
      worldRun w t0 1 (.donateAdminFees) = some (w', r) ∧
      VpFalls w w' t0 :=
  @Blanc.Lift.Curve3Pool.u3_refuted_donate_admin_fees

example : ∃ w w' r, reach 100 1000000 5000000000 exchangeDeployedPre = some w ∧
      worldRun w t0 1 (.exchange 1 0 0 0) = some (w', r) ∧
      VpFalls w w' t0 :=
  @Blanc.Lift.Curve3Pool.u3_refuted_exchange_deployed

example : ∃ w w' r, reach 2000 1000000 5000000000 removeLiquidityDeployedPre = some w ∧
      worldRun w t0 1 (.removeLiquidity 1 ⟨0, 0, 0⟩) = some (w', r) ∧
      VpFalls w w' t0 :=
  @Blanc.Lift.Curve3Pool.u3_refuted_remove_liquidity_deployed

end Blanc.Lift.Curve3Pool

namespace Blanc.Lift.Curve3Pool
open Jaune Blanc Blanc.ExecutionTrace Blanc.StableSwapNewton

example : ∀ {s : State} {e : Env} {c : Call} {o : Out} (h : step s e c = some o),
    U3Step s e c o :=
  @Blanc.Lift.Curve3Pool.u3Step_of_step

end Blanc.Lift.Curve3Pool

namespace Blanc.Lift.Curve3Pool
open Blanc.StableSwapNewton

example : ∀ {s : State} {e : Env} {c : Call} {o : Out} {T T' : Nat} (h : step s e c = some o) (hT : ∀ T₀, e.supply = some T₀ → T₀ = T) (hT' : supplyAfter T o.calls = T'),
    U3Ledger s e c o T T' :=
  @Blanc.Lift.Curve3Pool.u3Ledger_of_step

example : ∀ {s : State} {e : Env} {i j : Fin 3} {dx md : Nat} {o : Out} {T amp D D' : Nat} (h : exchange s e i j dx md = some o) (hA : aChk s e.time = some amp) (hadm : s.adminFee ≤ feeDen) (hD : getDMem s.balances amp = some D) (hD' : getDMem o.state.balances amp = some D'),
    (∀ t, aChk o.state t = aChk s t) ∧ supplyAfter T o.calls = T ∧
      D ≤ D' + yGap (xpOf s.balances) i j (xpOf o.state.balances i) D (amp * 3) :=
  @Blanc.Lift.Curve3Pool.u3_bound_exchange

example : ∀ {s : State} {e : Env} {a : Nat} {mins : V3} {o : Out} {T amp D D' : Nat} (h : removeLiquidity s e a mins = some o) (hT : e.supply = some T) (hT0 : 0 < T) (hD : getDMem s.balances amp = some D) (hD' : getDMem o.state.balances amp = some D'),
    (∀ t, aChk o.state t = aChk s t) ∧
    D * supplyAfter T o.calls ≤
      (D' + 1) * T + (D - floorRoot (xpOf s.balances) (amp * 3)) * supplyAfter T o.calls :=
  @Blanc.Lift.Curve3Pool.u3_bound_remove_liquidity

example : ∀ {s : State} {e : Env} {a : Nat} {i : Fin 3} {mn : Nat} {o : Out} {T amp D D' : Nat} (h : removeLiquidityOneCoin s e a i mn = some o) (hA : aChk s e.time = some amp) (hT : e.supply = some T) (hadm : s.adminFee ≤ feeDen) (hD : getDMem s.balances amp = some D) (hD' : getDMem o.state.balances amp = some D'),
    (∀ t, aChk o.state t = aChk s t) ∧
    D * supplyAfter T o.calls ≤
      (D' + oneGap (xpOf s.balances) i (D - a * D / T) (amp * 3)) * T :=
  @Blanc.Lift.Curve3Pool.u3_bound_remove_liquidity_one_coin

example : ∀ {s : State} {e : Env} {am : V3} {mb : Nat} {o : Out} {T amp D D' : Nat} (h : removeLiquidityImbalance s e am mb = some o) (hA : aChk s e.time = some amp) (hT : e.supply = some T) (hadm : s.adminFee ≤ feeDen) (hD : getDMem s.balances amp = some D) (hD' : getDMem o.state.balances amp = some D'),
    (∀ t, aChk o.state t = aChk s t) ∧ ∃ mid D2, getDMem mid amp = some D2 ∧
      (∀ k, mid.get k ≤ o.state.balances.get k) ∧
      D * supplyAfter T o.calls ≤ (D' + (D2 - floorRoot (xpOf mid) (amp * 3))) * T :=
  @Blanc.Lift.Curve3Pool.u3_bound_remove_liquidity_imbalance

example : ∀ {s : State} {e : Env} {am : V3} {mm : Nat} {o : Out} {T amp D D' : Nat} (h : addLiquidity s e am mm = some o) (hA : aChk s e.time = some amp) (hT : e.supply = some T) (hT0 : 0 < T) (hadm : s.adminFee ≤ feeDen) (hD : getDMem s.balances amp = some D) (hD' : getDMem o.state.balances amp = some D'),
    (∀ t, aChk o.state t = aChk s t) ∧ ∃ mid D2, getDMem mid amp = some D2 ∧
      (∀ k, mid.get k ≤ o.state.balances.get k) ∧
      D * supplyAfter T o.calls ≤ (D' + (D2 - floorRoot (xpOf mid) (amp * 3))) * T :=
  @Blanc.Lift.Curve3Pool.u3_bound_add_liquidity

example : ∀ {s : State} {e : Env} {o : Out} {T amp D D' : Nat} (h : donateAdminFees s e = some o) (hcoin : ∀ k v, (e.coin k).balPre = some v → s.balances.get k ≤ v) (hD' : getDMem o.state.balances amp = some D'),
    (∀ t, aChk o.state t = aChk s t) ∧ supplyAfter T o.calls = T ∧ floorRoot (xpOf s.balances) (amp * 3) ≤ D' ∧
      D ≤ D' + (D - floorRoot (xpOf s.balances) (amp * 3)) :=
  @Blanc.Lift.Curve3Pool.u3_bound_donate_admin_fees

end Blanc.Lift.Curve3Pool

namespace Blanc.Lift.Curve3Pool
open Jaune Blanc Blanc.ExecutionTrace Blanc.StableSwapNewton

example : ∀ {pool : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {s₀ : State} (trace : ConfiguredHistoryTrace cfg checkpoint future) (installed : some (checkpoint.state.getCode pool).toList = poolSem.image) (initial : Checkpoint (checkpoint.state.getStor pool) s₀) (env : PoolTraceEnv trace pool s₀.coins s₀.token),
    ∃ invs : List PoolInvocation,
      invs.flatMap (fun i => poolSubtreeFrames pool i.frame) = committedPoolFrames pool trace ∧
      (∀ i ∈ invs, i.Authentic pool) ∧
      (∃ s, PoolRun s₀ invs s ∧ Checkpoint (future.state.getStor pool) s) ∧
      ∀ (pre : List PoolInvocation) (i : PoolInvocation) (post : List PoolInvocation)
        (sᵢ : State), invs = pre ++ i :: post → PoolRun s₀ pre sᵢ →
        (∃ blk : Block, (blk, i.frame) ∈ trace.blockFrames ∧
          i.env.time = blk.header.timestamp.toB256.toNat) ∧
        ∃ o, step sᵢ i.env (decodeCall i.frame.sevm) = some o ∧
          RawEffect (Exec.Frame.rootDeriv i.frame) i.frame.post i.env o ∧
          U3Step sᵢ i.env (decodeCall i.frame.sevm) o :=
  @Blanc.Lift.Curve3Pool.pool_history_u3

end Blanc.Lift.Curve3Pool

namespace Blanc.Composition.Curve3PoolSupply
open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Crv Blanc.ExecutionTrace
open Blanc.Lift.Curve3Pool (PoolInvocation PoolRun poolSubtreeFrames)

open Blanc.Composition.Curve3Pool3CrvJoint in
example : ∀ {pool c3 : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {ps₀ : Curve3Pool.State} {cs₀ : Blanc.Curve3Crv.State} {K₀ : Key → Prop} (trace : ConfiguredHistoryTrace cfg checkpoint future) (poolInstalled : some (checkpoint.state.getCode pool).toList = Curve3Pool.poolSem.image) (c3Installed : some (checkpoint.state.getCode c3).toList = c3crvSem.image) (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state) (fresh : FreshKeys K₀ (historyTouchedKeys c3 trace)) (env : Curve3Pool.PoolTraceEnv trace pool ps₀.coins ps₀.token) (notSystem : pool ≠ systemAddress),
    ∃ invs : List PoolInvocation,
      invs.flatMap (fun i => poolSubtreeFrames pool i.frame) =
        Curve3Pool.committedPoolFrames pool trace ∧
      (∀ i ∈ invs, i.Authentic pool) ∧
      (∃ s, PoolRun ps₀ invs s ∧ Curve3Pool.Checkpoint (future.state.getStor pool) s) ∧
      ∀ (pre : List PoolInvocation) (i : PoolInvocation) (post : List PoolInvocation)
        (sᵢ : Curve3Pool.State), invs = pre ++ i :: post → PoolRun ps₀ pre sᵢ →
        (∃ blk : Block, (blk, i.frame) ∈ trace.blockFrames ∧
          i.env.time = blk.header.timestamp.toB256.toNat) ∧
        (Curve3Pool.FeeBounded ps₀ → Curve3Pool.FeeBounded sᵢ) ∧
        ∃ o, Curve3Pool.step sᵢ i.env (Curve3Pool.decodeCall i.frame.sevm) = some o ∧
          Curve3Pool.RawEffect (Blanc.Exec.Frame.rootDeriv i.frame) i.frame.post i.env o ∧
          SupplyObserved c3 i ∧
          Curve3Pool.supplyAfter (supplyAt c3 i.frame.pre.state) o.calls =
            supplyAt c3 i.frame.post.state ∧
          Curve3Pool.U3Ledger sᵢ i.env (Curve3Pool.decodeCall i.frame.sevm) o
            (supplyAt c3 i.frame.pre.state) (supplyAt c3 i.frame.post.state) :=
  @Blanc.Composition.Curve3PoolSupply.pool_3crv_u3

end Blanc.Composition.Curve3PoolSupply

namespace Blanc.Composition.Curve3Pool3CrvHeadlines
open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.ExecutionTrace
open Blanc.Composition.Curve3Pool3CrvJoint (JointCheckpoint)
open Blanc.Composition.Curve3PoolCalleeLive

example : ∀ {pool c3 : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {cs₀ : Blanc.Curve3Crv.State} {K₀ : Curve3Crv.Key → Prop} {t₀ : Nat} (trace : ConfiguredHistoryTrace cfg checkpoint future) (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image) (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image) (joint : JointCheckpoint pool c3 (Creation.poolInitState t₀) cs₀ K₀ checkpoint.state) (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace)) (env : PoolTraceEnv trace pool (Creation.poolInitState t₀).coins
      (Creation.poolInitState t₀).token) (notSystem : pool ≠ systemAddress),
    ∃ invs : List PoolInvocation,
      invs.flatMap (fun i => poolSubtreeFrames pool i.frame) = committedPoolFrames pool trace ∧
      (∀ i ∈ invs, i.Authentic pool) ∧
      (∃ s, PoolRun (Creation.poolInitState t₀) invs s ∧
        Checkpoint (future.state.getStor pool) s) ∧
      ∀ (pre : List PoolInvocation) (i : PoolInvocation) (post : List PoolInvocation)
        (sᵢ : Curve3Pool.State), invs = pre ++ i :: post →
        PoolRun (Creation.poolInitState t₀) pre sᵢ →
        (∃ blk : Block, (blk, i.frame) ∈ trace.blockFrames ∧
          i.env.time = blk.header.timestamp.toB256.toNat) ∧
        sᵢ.adminFee ≤ feeDen ∧
        ∃ o, step sᵢ i.env (decodeCall i.frame.sevm) = some o ∧
          RawEffect (Blanc.Exec.Frame.rootDeriv i.frame) i.frame.post i.env o ∧
          Curve3PoolSupply.SupplyObserved c3 i ∧
          supplyAfter (Curve3PoolSupply.supplyAt c3 i.frame.pre.state) o.calls =
            Curve3PoolSupply.supplyAt c3 i.frame.post.state ∧
          U3Ledger sᵢ i.env (decodeCall i.frame.sevm) o
            (Curve3PoolSupply.supplyAt c3 i.frame.pre.state)
            (Curve3PoolSupply.supplyAt c3 i.frame.post.state) :=
  @Blanc.Composition.Curve3Pool3CrvHeadlines.pool_3crv_u3_deployed

end Blanc.Composition.Curve3Pool3CrvHeadlines

namespace Blanc.Lift.Curve3Pool
open Blanc.StableSwapNewton

example : ∀ {t : Nat} {invs : List PoolInvocation} {s : State} (h : PoolRun (Creation.poolInitState t) invs s),
    FeeBounded s :=
  @Blanc.Lift.Curve3Pool.feeBounded_of_poolRun_init

end Blanc.Lift.Curve3Pool

namespace Blanc.Lift.Curve3Pool
open Jaune Blanc Blanc.ExecutionTrace

example : ∀ {pool : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {s₀ : State} (trace : ConfiguredHistoryTrace cfg checkpoint future) (installed : some (checkpoint.state.getCode pool).toList = poolSem.image) (initial : Checkpoint (checkpoint.state.getStor pool) s₀) (env : PoolTraceEnv trace pool s₀.coins s₀.token),
    ∃ invs : List PoolInvocation,
      invs.flatMap (fun i => poolSubtreeFrames pool i.frame) = committedPoolFrames pool trace ∧
      (∀ i ∈ invs, i.Authentic pool) ∧
      (∃ s, PoolRun s₀ invs s ∧ Checkpoint (future.state.getStor pool) s) ∧
      ∀ (pre : List PoolInvocation) (i : PoolInvocation) (post : List PoolInvocation)
        (sᵢ : State), invs = pre ++ i :: post → PoolRun s₀ pre sᵢ →
        ∃ blk : Block, (blk, i.frame) ∈ trace.blockFrames ∧
          i.env.time = blk.header.timestamp.toB256.toNat ∧
          (sᵢ.initialATime ≤ i.env.time → sᵢ.futureA < StableSwapNewton.wordSize →
            (max sᵢ.futureA sᵢ.initialA - min sᵢ.futureA sᵢ.initialA) *
              (i.env.time - sᵢ.initialATime) < StableSwapNewton.wordSize →
            aChk sᵢ i.env.time = some (aInterp sᵢ i.env.time)) ∧
          (sᵢ.futureATime ≤ i.env.time → aChk sᵢ i.env.time = some sᵢ.futureA) ∧
          ∀ fA fT, decodeCall i.frame.sevm = .rampA fA fT → ∃ o,
            step sᵢ i.env (decodeCall i.frame.sevm) = some o ∧
            o.state.initialATime + minRampTime ≤ o.state.futureATime ∧ 0 < o.state.futureA ∧
            o.state.futureA < maxA ∧ aChk sᵢ i.env.time = some o.state.initialA ∧
            o.state.futureA ≤ o.state.initialA * maxAChange ∧
            o.state.initialA ≤ o.state.futureA * maxAChange :=
  @Blanc.Lift.Curve3Pool.pool_history_amp

end Blanc.Lift.Curve3Pool

namespace Blanc.Lift.Curve3Pool
open Blanc.StableSwapNewton

example : ∀ {s : State} {t : Nat} (ht : s.initialATime ≤ t) (hA1 : s.futureA < wordSize) (hmul : (max s.futureA s.initialA - min s.futureA s.initialA) * (t - s.initialATime) <
      wordSize),
    aChk s t = some (aInterp s t) :=
  @Blanc.Lift.Curve3Pool.aChk_eq_aInterp

example : ∀ {s : State} {t : Nat} (h : s.futureATime ≤ t),
    aChk s t = some s.futureA :=
  @Blanc.Lift.Curve3Pool.aChk_of_le

example : ∀ {s : State} {e : Env} {fA fT : Nat} {o : Out} (h : rampA s e fA fT = some o),
    o.state.initialATime + minRampTime ≤ o.state.futureATime ∧ 0 < o.state.futureA ∧
      o.state.futureA < maxA ∧ aChk s e.time = some o.state.initialA ∧
      o.state.futureA ≤ o.state.initialA * maxAChange ∧
      o.state.initialA ≤ o.state.futureA * maxAChange :=
  @Blanc.Lift.Curve3Pool.rampA_guards

example : ∀ {s : State} {e : Env} {o : Out} (h : stopRampA s e = some o) {t : Nat} (ht : e.time ≤ t),
    aChk o.state t = aChk s e.time :=
  @Blanc.Lift.Curve3Pool.stopRampA_const

end Blanc.Lift.Curve3Pool

namespace Blanc.Lift.Curve3Pool
open Jaune Blanc Blanc.ExecutionTrace

example : ∀ {cfg : ChainConfig} {pre post : BlockChain} (block : ConfiguredBlockTrace cfg pre post) {parent : Block} (head : pre.blocks.getLast? = some parent) (bound : block.block.header.timestamp < 2 ^ 256) {frame : Exec.Frame} (member : frame ∈ block.settledFrames) {e : Env} (henv : EnvOf (Exec.Frame.rootDeriv frame) e),
    e.time ≠ parent.header.timestamp.toB256.toNat :=
  @Blanc.Lift.Curve3Pool.pool_invocation_time_ne_parent

end Blanc.Lift.Curve3Pool

namespace Blanc.Lift.Curve3Pool
open Blanc.StableSwapNewton

example : u5ControlState.initialA = 100 ∧ u5ControlState.futureA = 1000 ∧
    u5ControlState.initialATime + minRampTime ≤ u5ControlState.futureATime ∧
    0 < u5ControlState.futureA ∧ u5ControlState.futureA < maxA ∧
    u5ControlState.futureA ≤ u5ControlState.initialA * maxAChange ∧
    u5ControlState.initialA ≤ u5ControlState.futureA * maxAChange ∧
    aInterp u5ControlState 1043200 = 550 ∧ aInterp u5ControlState 1043199 = 549 ∧
    ¬ aChk u5ControlState 1043200 = some (aInterp u5ControlState 1043199) :=
  @Blanc.Lift.Curve3Pool.u5_parent_time_control

example : DMonoInA :=
  @Blanc.Lift.Curve3Pool.dMonoInA

example : (rampWorld.bind fun w => do some (← aDT w (rampT0 + 86400), ← aDT w (rampT0 + 2 * 86400))) =
      some ((2000, 200044801219456106169, 200044801219456106169),
            (200, 192793226260180884069, 200044801219456106169)) :=
  @Blanc.Lift.Curve3Pool.u5_ramp_control

example : 192793226260180884069 * 200044801219456106169 <
      200044801219456106169 * 200044801219456106169 :=
  @Blanc.Lift.Curve3Pool.u5_ramp_control_falls

end Blanc.Lift.Curve3Pool

namespace Blanc.Composition.Curve3PoolSupply
open Jaune Blanc Blanc.Lift Blanc.Lift.Token Blanc.Lift.Curve3Crv Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay Blanc.Composition.Curve3CrvToken
open Blanc.Curve3Crv (Call)
open Blanc.Lift.Curve3Pool (PoolInvocation PoolRun PoolEntries poolFrameObs poolSubtreeFrames)

open Blanc.Composition.Curve3Pool3CrvJoint in
example : ∀ {pool c3 : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {ps₀ : Curve3Pool.State} {cs₀ : Blanc.Curve3Crv.State} {K₀ : Key → Prop} (trace : ConfiguredHistoryTrace cfg checkpoint future) (poolInstalled : some (checkpoint.state.getCode pool).toList = Curve3Pool.poolSem.image) (c3Installed : some (checkpoint.state.getCode c3).toList = c3crvSem.image) (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state) (fresh : FreshKeys K₀ (historyTouchedKeys c3 trace)) (env : Curve3Pool.PoolTraceEnv trace pool ps₀.coins ps₀.token) (notSystem : pool ≠ systemAddress),
    some (future.state.getCode pool).toList = Curve3Pool.poolSem.image ∧
    ∃ invs : List PoolInvocation,
      invs.flatMap (fun i => poolSubtreeFrames pool i.frame) =
        Curve3Pool.committedPoolFrames pool trace ∧
      (∀ i ∈ invs, i.Authentic pool) ∧
      ∃ s, PoolRun ps₀ invs s ∧ Curve3Pool.runPool ps₀ invs = some s ∧
        Curve3Pool.Checkpoint (future.state.getStor pool) s ∧ s.coins = ps₀.coins ∧
        s.token = ps₀.token ∧
      ∃ cs, runInvocations cs₀ (committedInvocations c3 trace) = some cs ∧
        VyInv (future.state.getStor c3) cs
          (Key.extend K₀ (invocationKeys (committedInvocations c3 trace))) ∧
        cs.minter = pool ∧
        cs.totalSupply.toNat + poolBurned ps₀ invs = cs₀.totalSupply.toNat + poolMinted ps₀ invs ∧
        ∀ (pre : List PoolInvocation) (i : PoolInvocation) (post : List PoolInvocation)
          (sᵢ : Curve3Pool.State), invs = pre ++ i :: post → PoolRun ps₀ pre sᵢ →
          ∃ o, Curve3Pool.step sᵢ i.env (Curve3Pool.decodeCall i.frame.sevm) = some o ∧
            Curve3Pool.RawEffect (Blanc.Exec.Frame.rootDeriv i.frame) i.frame.post i.env o ∧
            supplyAt c3 i.frame.post.state + callsBurned o.calls =
              supplyAt c3 i.frame.pre.state + callsMinted o.calls ∧
            SupplyObserved c3 i :=
  @Blanc.Composition.Curve3PoolSupply.pool_3crv_history

end Blanc.Composition.Curve3PoolSupply

namespace Blanc.Lift.Token.SupplyFacet
open Jaune Blanc

example : ∀ {B : Book} (F : SupplyFacet B),
    ∀ {as : List Sevm} {l l' : B.Ledger}, B.run l as = some l' →
      (∀ a ∈ as, a.caller = F.minter l → F.KeepsMinter a) →
      F.minter l' = F.minter l ∧ F.supply l' + F.burned as = F.supply l + F.minted as :=
  @Blanc.Lift.Token.SupplyFacet.run_supply

end Blanc.Lift.Token.SupplyFacet

namespace Blanc.Composition.Curve3CrvToken
open Jaune Blanc Blanc.Lift Blanc.Lift.Token Blanc.Lift.Curve3Crv
open Blanc.Curve3Crv (Call)

example : ∀ {ca : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {initial : Blanc.Curve3Crv.State} {initialKeys : Key → Prop} (trace : ExecutionTrace.ConfiguredHistoryTrace cfg checkpoint future) (installed : some (checkpoint.state.getCode ca).toList = c3crvSem.image) (invariant : VyInv (checkpoint.state.getStor ca) initial initialKeys) (fresh : FreshKeys initialKeys (historyTouchedKeys ca trace)) (keeps : ∀ inv ∈ committedInvocations ca trace, inv.sevm.caller = initial.minter →
      c3crvSupply.KeepsMinter inv.sevm),
    ∃ s, runInvocations initial (committedInvocations ca trace) = some s ∧
      VyInv (future.state.getStor ca) s
        (Key.extend initialKeys (invocationKeys (committedInvocations ca trace))) ∧
      s.minter = initial.minter ∧
      s.totalSupply.toNat + c3crvSupply.burned (invMessages (committedInvocations ca trace)) =
        initial.totalSupply.toNat + c3crvSupply.minted (invMessages (committedInvocations ca trace)) :=
  @Blanc.Composition.Curve3CrvToken.c3crv_history_supply

end Blanc.Composition.Curve3CrvToken

namespace Blanc.Composition.Curve3CrvToken
open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Crv Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

example : ∀ {ca : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {initial : Blanc.Curve3Crv.State} {initialKeys : Key → Prop} (trace : ConfiguredHistoryTrace cfg checkpoint future) (installed : some (checkpoint.state.getCode ca).toList = c3crvSem.image) (invariant : VyInv (checkpoint.state.getStor ca) initial initialKeys) (fresh : FreshKeys initialKeys (historyTouchedKeys ca trace)),
    ∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      trace.settledFrames = before ++ f :: after →
      (∀ A ∈ before, A.Encloses f → ¬ (A.sevm.currentTarget = ca ∧ A.sevm.isStatic = false)) →
      ∃ s, InvRun initial (before.flatMap (viewFrameObs ca)) s ∧
        VyInv (f.pre.state.getStor ca) s
          (Key.extend initialKeys (invocationKeys (before.flatMap (viewFrameObs ca)))) :=
  @Blanc.Composition.Curve3CrvToken.c3crv_history_at

end Blanc.Composition.Curve3CrvToken

namespace Blanc.Composition.Curve3CrvToken
open Jaune Blanc Blanc.Lift Blanc.Lift.Token Blanc.Lift.Curve3Crv
open Blanc.Curve3Crv (Call)

example : ¬ ∃ F : SupplyFacet mutantBook, F.minter = (·.minter) ∧ F.mintOf = c3crvMintOf :=
  @Blanc.Composition.Curve3CrvToken.control_mutant_no_supplyFacet

end Blanc.Composition.Curve3CrvToken

namespace Blanc.Composition.Curve3Pool3CrvHeadlines
open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.ExecutionTrace
open Blanc.Composition.Curve3Pool3CrvJoint (JointCheckpoint)
open Blanc.Composition.Curve3PoolCalleeLive

example : ¬ ∃ F : Token.SupplyFacet Curve3CrvToken.mutantBook,
      F.minter = (·.minter) ∧ F.mintOf = Curve3CrvToken.c3crvMintOf :=
  @Blanc.Composition.Curve3Pool3CrvHeadlines.u8_control

end Blanc.Composition.Curve3Pool3CrvHeadlines

namespace Blanc.Lift.Curve3Pool.Creation
open Jaune Blanc.Lift Blanc.Lift.Curve3Pool Blanc.ForkUniform Blanc.StableSwapNewton

example : ∀ (f : Fork) (hf : CoveredFork f),
    poolAddress = computeContractAddress deployer 43 ∧
    init ownerN coinsN tokenN 100 4000000 0 deployTime.toNat 0 =
      some (poolInitState deployTime.toNat) ∧
    ∃ post, processCreateMessage (deployMsg.withFork f) = .ok post ∧
      (post.getCode poolAddress).toList = Blanc.Lift.Curve3Pool.code.toList ∧
      Devm.getStor post poolAddress = deployedStor deployTime ∧
      Checkpoint (Devm.getStor post poolAddress) (poolInitState deployTime.toNat) ∧
      (∀ x, x ∉ poolSlots → (Devm.getStor post poolAddress).get x = 0) :=
  @Blanc.Lift.Curve3Pool.Creation.pool_deploy_covered

example : ∀ (msg : Msg) (hvalue : msg.value = 0) (hcodeAddress : msg.codeAddress = .none) (hcode : msg.code = code) (hgas : 4500000 ≤ msg.gas) (hfork : CoveredFork msg.benv.stat.fork) (hstatic : msg.isStatic = false) (hmax : 0x52cf ≤ msg.benv.stat.rules.code.maxCodeSize) (ht : msg.benv.stat.time.toNat + killDeadlineDt < 2 ^ 256),
    ∃ post, processCreateMessage msg = .ok post ∧
      (post.getCode msg.currentTarget).toList = Blanc.Lift.Curve3Pool.code.toList ∧
      Devm.getStor post msg.currentTarget = deployedStor msg.benv.stat.time ∧
      post.error = .none :=
  @Blanc.Lift.Curve3Pool.Creation.pool_create

example : ∀ {t fee' : Nat} {s : State} (hfee : fee' ≠ 4000000) (u : B256) (hs : init ownerN coinsN tokenN 100 fee' 0 t 0 = some s),
    ¬ Abstracts (deployedStor u) s :=
  @Blanc.Lift.Curve3Pool.Creation.deployedStor_wrong_fee

end Blanc.Lift.Curve3Pool.Creation

-- curve-3pool-stableswap-v1: the exact-gas liveness headlines (frame, message entry, history,
-- composed with 3Crv) and their premise-bundle witnesses, with the message grant `Msg.withGas`
-- and the word pin `RliWordsPin` they are stated through, pinned by unfolding.

namespace Blanc.Lift.Curve3Pool
open Jaune Blanc.Lift Blanc.StableSwapNewton

example : ∀ {sevm : Sevm} {pre : Devm} {s : State} {o : Out} {T : B256} {W : Nat → Devm → Prop} {U : Nat} (P : RLExactCalls) (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0) (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256) (hsel : Sevm.selector sevm = selRemoveLiquidity) (hck : Checkpoint (pre.getStor sevm.currentTarget) s) (hstep : step s (rlEnv sevm T) (decodeCall sevm) = some o) (htok : ¬ sevm.benvStat.rules.isPrecomp ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr) (hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr) (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm pre) (hWc : ∀ k, k ≤ 3 → WClosed sevm (W k)) (hWb : W 0 pre) (hP : RLExactPremises sevm pre T W U P),
        ∀ R, 167000 + 5 * U ≤ R →
      (St pre [] Mem.empty (R + rlExactCost sevm pre T P)).gasMeasure < 2 ^ 256 →
      (∀ post (exc : Exec 0 sevm (St pre [] Mem.empty (R + rlExactCost sevm pre T P)) (.ok post)),
        PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty (R + rlExactCost sevm pre T P), .ok post, exc⟩ ∧
          ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
      ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty (R + rlExactCost sevm pre T P)) (.ok post),
        post.gasLeft = R ∧
        RawEffect ⟨0, sevm, St pre [] Mem.empty (R + rlExactCost sevm pre T P), .ok post, exc⟩
          post (rlEnv sevm T) o ∧
        Checkpoint (post.getStor sevm.currentTarget) o.state :=
  @Blanc.Lift.Curve3Pool.removeLiquidity_live_exact

example : ∀ {sevm : Sevm} {pre : Devm} {s : State} {o : Out} {i j : Fin 3} {B1 B2 : B256} {W W' W'' : Devm → Prop} {U : Nat} (P : ExchangeExactCalls) (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0) (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256) (hsel : Sevm.selector sevm = selExchange) (hi : i.val = (exI sevm).toNat) (hj : j.val = (exJ sevm).toNat) (hck : Checkpoint (pre.getStor sevm.currentTarget) s) (hstep : step s (exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)) (decodeCall sevm) = some o) (hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr) (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm pre) (hWc : WClosed sevm W) (hW'c : WClosed sevm W') (hWb : W pre) (hbal : i = feeIndex → StaticWordCallProfile sevm W W ((pre.getStor sevm.currentTarget).get (coinSlot i)) (balanceOfData sevm.currentTarget) B1 U 0x3dc 0x24 0x440 P.balD1 P.balN1 ∧ StaticWordCallProfile sevm W' W' ((pre.getStor sevm.currentTarget).get (coinSlot i)) (balanceOfData sevm.currentTarget) B2 U 0x71c 0x24 0x780 P.balD2 P.balN2) (hpull : MutableCallProfile sevm W W' ((pre.getStor sevm.currentTarget).get (coinSlot i)) (transferFromSel ++ sevm.caller.toB256.toBytes ++ sevm.currentTarget.toB256.toBytes ++ (exDx sevm).toBytes) RawCallOk U 0x600 0x64 0x6c0 P.pullD P.pullN) (hW''c : WClosed sevm W'') (hpush : MutableCallProfile sevm W' W'' ((pre.getStor sevm.currentTarget).get (coinSlot j)) (transferSel ++ sevm.caller.toB256.toBytes ++ (Nat.toB256 (exPushAmt o)).toBytes) RawCallOk U 0xb60 0x44 0xc00 P.pushD P.pushN),
        ∃ (x0 x1 x2 : B256) (amp v : Nat),
      xpChk ⟨(balAt (pre.getStor sevm.currentTarget) 0).toNat,
        (balAt (pre.getStor sevm.currentTarget) 1).toNat,
        (balAt (pre.getStor sevm.currentTarget) 2).toNat⟩ = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
      aChk s sevm.benvStat.time.toNat = some amp ∧
      (∃ (hi3 : (exI sevm).toNat < 3) (hj3 : (exJ sevm).toNat < 3),
        getYChk amp ⟨(exI sevm).toNat, hi3⟩ ⟨(exJ sevm).toNat, hj3⟩
          (exW3 x0 x1 x2 (exI sevm).toNat + exCred sevm B1 B2 * exRate (exI sevm).toNat /
            exR0).toNat (V3.mk x0.toNat x1.toNat x2.toNat).get = some v) ∧
      ∀ R, 60000 + U ≤ R →
        costExchange sevm pre s (exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)) i j
          (exDx sevm).toNat + 4 * U ≤ R + exExactCost sevm pre P x0 x1 x2 B1 B2 amp v →
        (St pre [] Mem.empty (R + exExactCost sevm pre P x0 x1 x2 B1 B2 amp v)).gasMeasure <
          2 ^ 256 →
        (∀ post (exc : Exec 0 sevm
            (St pre [] Mem.empty (R + exExactCost sevm pre P x0 x1 x2 B1 B2 amp v)) (.ok post)),
          PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty
            (R + exExactCost sevm pre P x0 x1 x2 B1 B2 amp v), .ok post, exc⟩ ∧
            ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
        ∃ post, ∃ exc : Exec 0 sevm
            (St pre [] Mem.empty (R + exExactCost sevm pre P x0 x1 x2 B1 B2 amp v)) (.ok post),
          ∃ bp bq,
          pullIn (exEnv sevm i j bp bq) i (exDx sevm).toNat =
            pullIn (exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)) i (exDx sevm).toNat ∧
          RawEffect ⟨0, sevm, St pre [] Mem.empty
            (R + exExactCost sevm pre P x0 x1 x2 B1 B2 amp v), .ok post, exc⟩ post
            (exEnv sevm i j bp bq) o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state ∧ W'' post ∧ post.gasLeft = R :=
  @Blanc.Lift.Curve3Pool.exchange_live_exact

example : ∀ {sevm : Sevm} {pre : Devm} {s : State} {o : Out} {T B1 B2 : B256} {W : Nat → Devm → Prop} {U : Nat} (P : ALExactCalls) (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0) (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256) (hsel : Sevm.selector sevm = selAddLiquidity) (hck : Checkpoint (pre.getStor sevm.currentTarget) s) (hstep : step s (alEnvW sevm T.toNat B1.toNat B2.toNat) (decodeCall sevm) = some o) (htok : ¬ sevm.benvStat.rules.isPrecomp ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr) (hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr) (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm pre) (hWc : ∀ j, j ≤ 4 → WClosed sevm (W j)) (hWb : W 0 pre) (hskip : ∀ k : Fin 3, alAmt sevm k.val = 0 → ∀ b, W k b → W (k + 1) b) (hP : ALExactPremises sevm (pre.getStor sevm.currentTarget) T B1 B2 (Nat.toB256 (alMintAmt o)) W U P),
        ∃ (amp v0 v1 v2 : Nat) (xa xb xc : V3) (f0 f1 f2 s0 s1 s2 x0 x1 x2 : B256),
      aChk s sevm.benvStat.time.toNat = some amp ∧
      xpChk ⟨(alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2 0).toNat,
        (alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2 1).toNat,
        (alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2 2).toNat⟩ = some xb ∧
      getDChk xb.get amp 1 = some v1 ∧
      (T ≠ 0 →
        xpChk ⟨(balAt (pre.getStor sevm.currentTarget) 0).toNat,
          (balAt (pre.getStor sevm.currentTarget) 1).toNat,
          (balAt (pre.getStor sevm.currentTarget) 2).toNat⟩ = some xa ∧
        getDChk xa.get amp 1 = some v0 ∧
        RliFeeIter (cwFee ((pre.getStor sevm.currentTarget).get feeSlot))
          ((pre.getStor sevm.currentTarget).get adminFeeSlot) (Nat.toB256 v0) (Nat.toB256 v1)
          (balAt (pre.getStor sevm.currentTarget) 0)
          (alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2 0) f0 s0 x0 ∧
        RliFeeIter (cwFee ((pre.getStor sevm.currentTarget).get feeSlot))
          ((pre.getStor sevm.currentTarget).get adminFeeSlot) (Nat.toB256 v0) (Nat.toB256 v1)
          (balAt (pre.getStor sevm.currentTarget) 1)
          (alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2 1) f1 s1 x1 ∧
        RliFeeIter (cwFee ((pre.getStor sevm.currentTarget).get feeSlot))
          ((pre.getStor sevm.currentTarget).get adminFeeSlot) (Nat.toB256 v0) (Nat.toB256 v1)
          (balAt (pre.getStor sevm.currentTarget) 2)
          (alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2 2) f2 s2 x2 ∧
        xpChk ⟨x0.toNat, x1.toNat, x2.toNat⟩ = some xc ∧ getDChk xc.get amp 1 = some v2) ∧
      ∀ R, 100000 + 5 * U ≤ R →
      costAddLiquidity s (alEnvW sevm T.toNat B1.toNat B2.toNat) (argV3 sevm 0) + 7 * U ≤
        R + alExactCost sevm pre P amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2 →
      (St pre [] Mem.empty (R + alExactCost sevm pre P amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2)).gasMeasure + 6000 < 2 ^ 256 →
      (∀ post (exc : Exec 0 sevm (St pre [] Mem.empty (R + alExactCost sevm pre P amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2)) (.ok post)),
        PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty (R + alExactCost sevm pre P amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2), .ok post, exc⟩ ∧
          ∀ c' ∈ Exec.childFrames exc, c'.post.getCode 4 = c'.pre.getCode 4) →
      ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty (R + alExactCost sevm pre P amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2)) (.ok post),
        post.gasLeft = R ∧
        ∃ e : Env, e.supply = some T.toNat ∧ step s e (decodeCall sevm) = some o ∧
          RawEffect ⟨0, sevm, St pre [] Mem.empty (R + alExactCost sevm pre P amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2), .ok post, exc⟩ post e o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state :=
  @Blanc.Lift.Curve3Pool.addLiquidity_live_exact

example : ∀ {sevm : Sevm} {pre : Devm} {s : State} {o : Out} {T : B256} {W : Nat → Devm → Prop} {U : Nat} (P : RLIExactCalls) (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0) (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256) (hsel : Sevm.selector sevm = selRemoveLiquidityImbalance) (hck : Checkpoint (pre.getStor sevm.currentTarget) s) (hstep : step s (rliEnvW sevm T.toNat) (decodeCall sevm) = some o) (htok : ¬ sevm.benvStat.rules.isPrecomp ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr) (hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr) (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm pre) (hWc : ∀ j, j ≤ 4 → WClosed sevm (W j)) (hWb : W 0 pre) (hP : RLIExactPremises sevm (pre.getStor sevm.currentTarget) T (Nat.toB256 (rliBurnAmt o)) W U P) (hskip : ∀ k : Fin 3, rliAmt sevm k.val = 0 → ∀ b, W (k + 1) b → W (k + 2) b),
        ∃ w : RliWords, RliWordsPin sevm pre s w ∧
      ∀ R, 66000 + 3 * U ≤ R →
        costImbalance s (rliEnvW sevm T.toNat) (argV3 sevm 0) + 5 * U ≤
          R + rliExactCost sevm pre P T w →
        (St pre [] Mem.empty (R + rliExactCost sevm pre P T w)).gasMeasure + 3000 < 2 ^ 256 →
        (∀ post (exc : Exec 0 sevm
            (St pre [] Mem.empty (R + rliExactCost sevm pre P T w)) (.ok post)),
          PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty (R + rliExactCost sevm pre P T w), .ok post,
            exc⟩ ∧ ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
        ∃ post, ∃ exc : Exec 0 sevm
            (St pre [] Mem.empty (R + rliExactCost sevm pre P T w)) (.ok post),
          post.gasLeft = R ∧
          RawEffect ⟨0, sevm, St pre [] Mem.empty (R + rliExactCost sevm pre P T w), .ok post, exc⟩
            post (rliEnvW sevm T.toNat) o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state ∧ W 4 post :=
  @Blanc.Lift.Curve3Pool.removeLiquidityImbalance_live_exact

example : ∀ {sevm : Sevm} {pre : Devm} {s : State} {o : Out} {i : Fin 3} {T : B256} {W W' W'' : Devm → Prop} {U : Nat} (P : OCExactCalls) (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0) (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256) (hsel : Sevm.selector sevm = selRemoveLiquidityOneCoin) (hi : i.val = (ocI sevm).toNat) (hck : Checkpoint (pre.getStor sevm.currentTarget) s) (hstep : step s (ocEnv sevm i T.toNat) (decodeCall sevm) = some o) (htok : ¬ sevm.benvStat.rules.isPrecomp ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr) (hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr) (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm pre) (hWc : WClosed sevm W) (hW'c : WClosed sevm W') (hWb : W pre) (hW''c : WClosed sevm W'') (hP : OCExactPremises sevm pre T (Nat.toB256 (ocPushAmt o)) W W' W'' U P),
        ∃ (amp : Nat) (x0 x1 x2 D0 y r0 r1 r2 y2 : B256) (hi3 : (ocI sevm).toNat < 3),
      aChk s sevm.benvStat.time.toNat = some amp ∧
      xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
      getDChk (V3.mk x0.toNat x1.toNat x2.toNat).get amp 1 = some D0.toNat ∧
      getYDChk amp ⟨(ocI sevm).toNat, hi3⟩ (V3.mk x0.toNat x1.toNat x2.toNat).get
        (D0 - ocAmt sevm * D0 / T).toNat = some y.toNat ∧
      CwStep (Bytes.toB256 [0] = ocI sevm) x0 (D0 - ocAmt sevm * D0 / T) D0 y
        (cwFee ((pre.getStor sevm.currentTarget).get feeSlot)) x0 r0 ∧
      CwStep (Bytes.toB256 [1] = ocI sevm) x1 (D0 - ocAmt sevm * D0 / T) D0 y
        (cwFee ((pre.getStor sevm.currentTarget).get feeSlot)) x1 r1 ∧
      CwStep (Bytes.toB256 [2] = ocI sevm) x2 (D0 - ocAmt sevm * D0 / T) D0 y
        (cwFee ((pre.getStor sevm.currentTarget).get feeSlot)) x2 r2 ∧
      getYDChk amp ⟨(ocI sevm).toNat, hi3⟩ (V3.mk r0.toNat r1.toNat r2.toNat).get
        (D0 - ocAmt sevm * D0 / T).toNat = some y2.toNat ∧
      ∀ R, 131000 + 3 * U ≤ R →
      (St pre [] Mem.empty (R + ocExactCost sevm pre T P amp x0 x1 x2 D0 y r0 r1 r2 y2)).gasMeasure +
        2000 < 2 ^ 256 →
      (∀ post (exc : Exec 0 sevm
          (St pre [] Mem.empty (R + ocExactCost sevm pre T P amp x0 x1 x2 D0 y r0 r1 r2 y2))
          (.ok post)),
        PoolCallsKeep ⟨0, sevm,
          St pre [] Mem.empty (R + ocExactCost sevm pre T P amp x0 x1 x2 D0 y r0 r1 r2 y2), .ok post,
          exc⟩ ∧
          ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
      ∃ post, ∃ exc : Exec 0 sevm
          (St pre [] Mem.empty (R + ocExactCost sevm pre T P amp x0 x1 x2 D0 y r0 r1 r2 y2))
          (.ok post), ∃ T' : Nat,
        post.gasLeft = R ∧
        RawEffect ⟨0, sevm,
          St pre [] Mem.empty (R + ocExactCost sevm pre T P amp x0 x1 x2 D0 y r0 r1 r2 y2), .ok post,
          exc⟩ post (ocEnv sevm i T') o ∧
        Checkpoint (post.getStor sevm.currentTarget) o.state ∧ W'' post :=
  @Blanc.Lift.Curve3Pool.removeLiquidityOneCoin_live_exact

example : ∀ {msg : Msg} {s : State} {o : Out} {T : B256} {W : Nat → Devm → Prop} {U : Nat} (P : RLExactCalls) (hcode : (initSevm msg).code = code) (hfork : CoveredFork (initSevm msg).benvStat.fork) (hstatic : (initSevm msg).isStatic = false) (hdepth : (initSevm msg).depth ≠ 0) (hlen : 4 ≤ (initSevm msg).data.length) (hcd : (initSevm msg).data.length < 2 ^ 256) (hsel : Sevm.selector (initSevm msg) = selRemoveLiquidity) (hck : Checkpoint ((initDevm msg).getStor msg.currentTarget) s) (hstep : step s (rlEnv (initSevm msg) T) (decodeCall (initSevm msg)) = some o) (htok : ¬ (initSevm msg).benvStat.rules.isPrecomp (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr) (hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr) (hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty) (hid : IdReady (initSevm msg) (initDevm msg)) (hWc : ∀ k, k ≤ 3 → WClosed (initSevm msg) (W k)) (hWb : W 0 (initDevm msg)) (hP : RLExactPremises (initSevm msg) (initDevm msg) T W U P),
        ∀ R, 167000 + 5 * U ≤ R →
      R + rlExactCost (initSevm msg) (initDevm msg) T P < 2 ^ 256 →
      (∀ post (exc : Exec 0 (initSevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T P)))
          (initDevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T P))) (.ok post)),
        PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
          ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
      ∃ post, ∃ exc : Exec 0 (initSevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T P)))
          (initDevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T P))) (.ok post),
        exec (initEvm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T P))) =
          .ok post ∧
        post.gasLeft = R ∧
        RawEffect ⟨0, _, _, .ok post, exc⟩ post (rlEnv (initSevm msg) T) o ∧
        Checkpoint (post.getStor msg.currentTarget) o.state :=
  @Blanc.Lift.Curve3Pool.removeLiquidity_msg_exact

example : ∀ {msg : Msg} {s : State} {o : Out} {i j : Fin 3} {B1 B2 : B256} {W W' W'' : Devm → Prop} {U : Nat} (P : ExchangeExactCalls) (hcode : (initSevm msg).code = code) (hfork : CoveredFork (initSevm msg).benvStat.fork) (hstatic : (initSevm msg).isStatic = false) (hdepth : (initSevm msg).depth ≠ 0) (hlen : 4 ≤ (initSevm msg).data.length) (hcd : (initSevm msg).data.length < 2 ^ 256) (hsel : Sevm.selector (initSevm msg) = selExchange) (hi : i.val = (exI (initSevm msg)).toNat) (hj : j.val = (exJ (initSevm msg)).toNat) (hck : Checkpoint ((initDevm msg).getStor msg.currentTarget) s) (hstep : step s (exEnv (initSevm msg) i j (exBalOpt i B1) (exBalOpt i B2)) (decodeCall (initSevm msg)) = some o) (hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr) (hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty) (hid : IdReady (initSevm msg) (initDevm msg)) (hWc : WClosed (initSevm msg) W) (hW'c : WClosed (initSevm msg) W') (hWb : W (initDevm msg)) (hbal : i = feeIndex → StaticWordCallProfile (initSevm msg) W W (((initDevm msg).getStor msg.currentTarget).get (coinSlot i)) (balanceOfData msg.currentTarget) B1 U 0x3dc 0x24 0x440 P.balD1 P.balN1 ∧ StaticWordCallProfile (initSevm msg) W' W' (((initDevm msg).getStor msg.currentTarget).get (coinSlot i)) (balanceOfData msg.currentTarget) B2 U 0x71c 0x24 0x780 P.balD2 P.balN2) (hpull : MutableCallProfile (initSevm msg) W W' (((initDevm msg).getStor msg.currentTarget).get (coinSlot i)) (transferFromSel ++ msg.caller.toB256.toBytes ++ msg.currentTarget.toB256.toBytes ++ (exDx (initSevm msg)).toBytes) RawCallOk U 0x600 0x64 0x6c0 P.pullD P.pullN) (hW''c : WClosed (initSevm msg) W'') (hpush : MutableCallProfile (initSevm msg) W' W'' (((initDevm msg).getStor msg.currentTarget).get (coinSlot j)) (transferSel ++ msg.caller.toB256.toBytes ++ (Nat.toB256 (exPushAmt o)).toBytes) RawCallOk U 0xb60 0x44 0xc00 P.pushD P.pushN),
        ∃ (x0 x1 x2 : B256) (amp v : Nat),
      xpChk ⟨(balAt ((initDevm msg).getStor msg.currentTarget) 0).toNat,
        (balAt ((initDevm msg).getStor msg.currentTarget) 1).toNat,
        (balAt ((initDevm msg).getStor msg.currentTarget) 2).toNat⟩ =
          some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
      aChk s (initSevm msg).benvStat.time.toNat = some amp ∧
      (∃ (hi3 : (exI (initSevm msg)).toNat < 3) (hj3 : (exJ (initSevm msg)).toNat < 3),
        getYChk amp ⟨(exI (initSevm msg)).toNat, hi3⟩ ⟨(exJ (initSevm msg)).toNat, hj3⟩
          (exW3 x0 x1 x2 (exI (initSevm msg)).toNat + exCred (initSevm msg) B1 B2 *
            exRate (exI (initSevm msg)).toNat / exR0).toNat (V3.mk x0.toNat x1.toNat x2.toNat).get =
          some v) ∧
      ∀ R, 60000 + U ≤ R →
        costExchange (initSevm msg) (initDevm msg) s
          (exEnv (initSevm msg) i j (exBalOpt i B1) (exBalOpt i B2)) i j
          (exDx (initSevm msg)).toNat + 4 * U ≤
            R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v →
        R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v < 2 ^ 256 →
        (∀ post (exc : Exec 0 (initSevm (msg.withGas
              (R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v)))
            (initDevm (msg.withGas
              (R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v))) (.ok post)),
          PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
            ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
        ∃ post, ∃ exc : Exec 0 (initSevm (msg.withGas
              (R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v)))
            (initDevm (msg.withGas
              (R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v))) (.ok post),
          exec (initEvm (msg.withGas
            (R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v))) = .ok post ∧
          post.gasLeft = R ∧ ∃ bp bq,
          pullIn (exEnv (initSevm msg) i j bp bq) i (exDx (initSevm msg)).toNat =
            pullIn (exEnv (initSevm msg) i j (exBalOpt i B1) (exBalOpt i B2)) i
              (exDx (initSevm msg)).toNat ∧
          RawEffect ⟨0, _, _, .ok post, exc⟩ post (exEnv (initSevm msg) i j bp bq) o ∧
          Checkpoint (post.getStor msg.currentTarget) o.state ∧ W'' post :=
  @Blanc.Lift.Curve3Pool.exchange_msg_exact

example : ∀ {msg : Msg} {s : State} {o : Out} {T B1 B2 : B256} {W : Nat → Devm → Prop} {U : Nat} (P : ALExactCalls) (hcode : (initSevm msg).code = code) (hfork : CoveredFork (initSevm msg).benvStat.fork) (hstatic : (initSevm msg).isStatic = false) (hdepth : (initSevm msg).depth ≠ 0) (hlen : 4 ≤ (initSevm msg).data.length) (hcd : (initSevm msg).data.length < 2 ^ 256) (hsel : Sevm.selector (initSevm msg) = selAddLiquidity) (hck : Checkpoint ((initDevm msg).getStor msg.currentTarget) s) (hstep : step s (alEnvW (initSevm msg) T.toNat B1.toNat B2.toNat) (decodeCall (initSevm msg)) = some o) (htok : ¬ (initSevm msg).benvStat.rules.isPrecomp (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr) (hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr) (hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty) (hid : IdReady (initSevm msg) (initDevm msg)) (hWc : ∀ j, j ≤ 4 → WClosed (initSevm msg) (W j)) (hWb : W 0 (initDevm msg)) (hskip : ∀ k : Fin 3, alAmt (initSevm msg) k.val = 0 → ∀ b, W k b → W (k + 1) b) (hP : ALExactPremises (initSevm msg) ((initDevm msg).getStor msg.currentTarget) T B1 B2 (Nat.toB256 (alMintAmt o)) W U P),
        ∃ (amp v0 v1 v2 : Nat) (xa xb xc : V3) (f0 f1 f2 s0 s1 s2 x0 x1 x2 : B256),
      aChk s (initSevm msg).benvStat.time.toNat = some amp ∧
      xpChk ⟨(alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2
          0).toNat,
        (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2 1).toNat,
        (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2
          2).toNat⟩ = some xb ∧
      getDChk xb.get amp 1 = some v1 ∧
      (T ≠ 0 →
        xpChk ⟨(balAt ((initDevm msg).getStor msg.currentTarget) 0).toNat,
          (balAt ((initDevm msg).getStor msg.currentTarget) 1).toNat,
          (balAt ((initDevm msg).getStor msg.currentTarget) 2).toNat⟩ = some xa ∧
        getDChk xa.get amp 1 = some v0 ∧
        RliFeeIter (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot))
          (((initDevm msg).getStor msg.currentTarget).get adminFeeSlot) (Nat.toB256 v0)
          (Nat.toB256 v1) (balAt ((initDevm msg).getStor msg.currentTarget) 0)
          (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2 0)
          f0 s0 x0 ∧
        RliFeeIter (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot))
          (((initDevm msg).getStor msg.currentTarget).get adminFeeSlot) (Nat.toB256 v0)
          (Nat.toB256 v1) (balAt ((initDevm msg).getStor msg.currentTarget) 1)
          (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2 1)
          f1 s1 x1 ∧
        RliFeeIter (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot))
          (((initDevm msg).getStor msg.currentTarget).get adminFeeSlot) (Nat.toB256 v0)
          (Nat.toB256 v1) (balAt ((initDevm msg).getStor msg.currentTarget) 2)
          (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2 2)
          f2 s2 x2 ∧
        xpChk ⟨x0.toNat, x1.toNat, x2.toNat⟩ = some xc ∧ getDChk xc.get amp 1 = some v2) ∧
      ∀ R, 100000 + 5 * U ≤ R →
      costAddLiquidity s (alEnvW (initSevm msg) T.toNat B1.toNat B2.toNat) (argV3 (initSevm msg) 0) +
          7 * U ≤
        R + alExactCost (initSevm msg) (initDevm msg) P amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0
          s1 s2 x0 x1 x2 →
      R + alExactCost (initSevm msg) (initDevm msg) P amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1
          s2 x0 x1 x2 + 6000 < 2 ^ 256 →
      (∀ post (exc : Exec 0 (initSevm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) P
            amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2)))
          (initDevm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) P amp T B1 B2 xa xb
            xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2))) (.ok post)),
        PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
          ∀ c' ∈ Exec.childFrames exc, c'.post.getCode 4 = c'.pre.getCode 4) →
      ∃ post, ∃ exc : Exec 0 (initSevm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) P
            amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2)))
          (initDevm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) P amp T B1 B2 xa xb
            xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2))) (.ok post),
        exec (initEvm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) P amp T B1 B2 xa
          xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2))) = .ok post ∧
        post.gasLeft = R ∧
        ∃ e : Env, e.supply = some T.toNat ∧ step s e (decodeCall (initSevm msg)) = some o ∧
          RawEffect ⟨0, _, _, .ok post, exc⟩ post e o ∧
          Checkpoint (post.getStor msg.currentTarget) o.state :=
  @Blanc.Lift.Curve3Pool.addLiquidity_msg_exact

example : ∀ {msg : Msg} {s : State} {o : Out} {T : B256} {W : Nat → Devm → Prop} {U : Nat} (P : RLIExactCalls) (hcode : (initSevm msg).code = code) (hfork : CoveredFork (initSevm msg).benvStat.fork) (hstatic : (initSevm msg).isStatic = false) (hdepth : (initSevm msg).depth ≠ 0) (hlen : 4 ≤ (initSevm msg).data.length) (hcd : (initSevm msg).data.length < 2 ^ 256) (hsel : Sevm.selector (initSevm msg) = selRemoveLiquidityImbalance) (hck : Checkpoint ((initDevm msg).getStor msg.currentTarget) s) (hstep : step s (rliEnvW (initSevm msg) T.toNat) (decodeCall (initSevm msg)) = some o) (htok : ¬ (initSevm msg).benvStat.rules.isPrecomp (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr) (hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr) (hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty) (hid : IdReady (initSevm msg) (initDevm msg)) (hWc : ∀ j, j ≤ 4 → WClosed (initSevm msg) (W j)) (hWb : W 0 (initDevm msg)) (hP : RLIExactPremises (initSevm msg) ((initDevm msg).getStor msg.currentTarget) T (Nat.toB256 (rliBurnAmt o)) W U P) (hskip : ∀ k : Fin 3, rliAmt (initSevm msg) k.val = 0 → ∀ b, W (k + 1) b → W (k + 2) b),
        ∃ w : RliWords, RliWordsPin (initSevm msg) (initDevm msg) s w ∧
      ∀ R, 66000 + 3 * U ≤ R →
        costImbalance s (rliEnvW (initSevm msg) T.toNat) (argV3 (initSevm msg) 0) + 5 * U ≤
          R + rliExactCost (initSevm msg) (initDevm msg) P T w →
        R + rliExactCost (initSevm msg) (initDevm msg) P T w + 3000 < 2 ^ 256 →
        (∀ post (exc : Exec 0
            (initSevm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) P T w)))
            (initDevm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) P T w)))
            (.ok post)),
          PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
            ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
        ∃ post, ∃ exc : Exec 0
            (initSevm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) P T w)))
            (initDevm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) P T w)))
            (.ok post),
          exec (initEvm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) P T w))) =
            .ok post ∧
          post.gasLeft = R ∧
          RawEffect ⟨0, _, _, .ok post, exc⟩ post (rliEnvW (initSevm msg) T.toNat) o ∧
          Checkpoint (post.getStor msg.currentTarget) o.state ∧ W 4 post :=
  @Blanc.Lift.Curve3Pool.removeLiquidityImbalance_msg_exact

example : ∀ {msg : Msg} {s : State} {o : Out} {i : Fin 3} {T : B256} {W W' W'' : Devm → Prop} {U : Nat} (P : OCExactCalls) (hcode : (initSevm msg).code = code) (hfork : CoveredFork (initSevm msg).benvStat.fork) (hstatic : (initSevm msg).isStatic = false) (hdepth : (initSevm msg).depth ≠ 0) (hlen : 4 ≤ (initSevm msg).data.length) (hcd : (initSevm msg).data.length < 2 ^ 256) (hsel : Sevm.selector (initSevm msg) = selRemoveLiquidityOneCoin) (hi : i.val = (ocI (initSevm msg)).toNat) (hck : Checkpoint ((initDevm msg).getStor msg.currentTarget) s) (hstep : step s (ocEnv (initSevm msg) i T.toNat) (decodeCall (initSevm msg)) = some o) (htok : ¬ (initSevm msg).benvStat.rules.isPrecomp (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr) (hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr) (hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty) (hid : IdReady (initSevm msg) (initDevm msg)) (hWc : WClosed (initSevm msg) W) (hW'c : WClosed (initSevm msg) W') (hWb : W (initDevm msg)) (hW''c : WClosed (initSevm msg) W'') (hP : OCExactPremises (initSevm msg) (initDevm msg) T (Nat.toB256 (ocPushAmt o)) W W' W'' U P),
        ∃ (amp : Nat) (x0 x1 x2 D0 y r0 r1 r2 y2 : B256) (hi3 : (ocI (initSevm msg)).toNat < 3),
      aChk s (initSevm msg).benvStat.time.toNat = some amp ∧
      xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
      getDChk (V3.mk x0.toNat x1.toNat x2.toNat).get amp 1 = some D0.toNat ∧
      getYDChk amp ⟨(ocI (initSevm msg)).toNat, hi3⟩ (V3.mk x0.toNat x1.toNat x2.toNat).get
        (D0 - ocAmt (initSevm msg) * D0 / T).toNat = some y.toNat ∧
      CwStep (Bytes.toB256 [0] = ocI (initSevm msg)) x0 (D0 - ocAmt (initSevm msg) * D0 / T) D0 y
        (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot)) x0 r0 ∧
      CwStep (Bytes.toB256 [1] = ocI (initSevm msg)) x1 (D0 - ocAmt (initSevm msg) * D0 / T) D0 y
        (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot)) x1 r1 ∧
      CwStep (Bytes.toB256 [2] = ocI (initSevm msg)) x2 (D0 - ocAmt (initSevm msg) * D0 / T) D0 y
        (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot)) x2 r2 ∧
      getYDChk amp ⟨(ocI (initSevm msg)).toNat, hi3⟩ (V3.mk r0.toNat r1.toNat r2.toNat).get
        (D0 - ocAmt (initSevm msg) * D0 / T).toNat = some y2.toNat ∧
      ∀ R, 131000 + 3 * U ≤ R →
      R + ocExactCost (initSevm msg) (initDevm msg) T P amp x0 x1 x2 D0 y r0 r1 r2 y2 + 2000 <
        2 ^ 256 →
      (∀ post (exc : Exec 0 (initSevm (msg.withGas
            (R + ocExactCost (initSevm msg) (initDevm msg) T P amp x0 x1 x2 D0 y r0 r1 r2 y2)))
          (initDevm (msg.withGas
            (R + ocExactCost (initSevm msg) (initDevm msg) T P amp x0 x1 x2 D0 y r0 r1 r2 y2)))
          (.ok post)),
        PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
          ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
      ∃ post, ∃ exc : Exec 0 (initSevm (msg.withGas
            (R + ocExactCost (initSevm msg) (initDevm msg) T P amp x0 x1 x2 D0 y r0 r1 r2 y2)))
          (initDevm (msg.withGas
            (R + ocExactCost (initSevm msg) (initDevm msg) T P amp x0 x1 x2 D0 y r0 r1 r2 y2)))
          (.ok post),
        exec (initEvm (msg.withGas
          (R + ocExactCost (initSevm msg) (initDevm msg) T P amp x0 x1 x2 D0 y r0 r1 r2 y2))) =
          .ok post ∧
        post.gasLeft = R ∧ ∃ T' : Nat,
        RawEffect ⟨0, _, _, .ok post, exc⟩ post (ocEnv (initSevm msg) i T') o ∧
        Checkpoint (post.getStor msg.currentTarget) o.state ∧ W'' post :=
  @Blanc.Lift.Curve3Pool.removeLiquidityOneCoin_msg_exact

end Blanc.Lift.Curve3Pool

namespace Blanc.Lift.Curve3Pool
open Jaune Blanc.Lift Blanc.ExecutionTrace Blanc.StableSwapNewton

example : ∀ {pool : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {s₀ : State} (trace : ConfiguredHistoryTrace cfg checkpoint future) (installed : some (checkpoint.state.getCode pool).toList = poolSem.image) (initial : Checkpoint (checkpoint.state.getStor pool) s₀) (env : PoolTraceEnv trace pool s₀.coins s₀.token) {msg : Msg} (target : msg.currentTarget = pool) (state : msg.benv.state = future.state),
        ∃ s, PoolHistoryAt trace pool s₀ s ∧
      ∀ {o : Out} {T : B256} {W : Nat → Devm → Prop} {U : Nat} (P : RLExactCalls)
        (_hcode : (initSevm msg).code = code)
        (_hfork : CoveredFork (initSevm msg).benvStat.fork)
        (_hstatic : (initSevm msg).isStatic = false)
        (_hdepth : (initSevm msg).depth ≠ 0)
        (_hlen : 4 ≤ (initSevm msg).data.length)
        (_hcd : (initSevm msg).data.length < 2 ^ 256)
        (_hsel : Sevm.selector (initSevm msg) = selRemoveLiquidity)
        (_hstep : step s (rlEnv (initSevm msg) T) (decodeCall (initSevm msg)) = some o)
        (_htok : ¬ (initSevm msg).benvStat.rules.isPrecomp
          (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr)
        (_hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
          (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty)
        (_hid : IdReady (initSevm msg) (initDevm msg))
        (_hWc : ∀ k, k ≤ 3 → WClosed (initSevm msg) (W k))
        (_hWb : W 0 (initDevm msg))
        (_hP : RLExactPremises (initSevm msg) (initDevm msg) T W U P),
        ∀ R, 167000 + 5 * U ≤ R →
          R + rlExactCost (initSevm msg) (initDevm msg) T P < 2 ^ 256 →
          (∀ post (exc : Exec 0 (initSevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T P)))
              (initDevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T P))) (.ok post)),
            PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
              ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
          ∃ post, ∃ exc : Exec 0 (initSevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T P)))
              (initDevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T P))) (.ok post),
            exec (initEvm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T P))) =
              .ok post ∧
            post.gasLeft = R ∧
            RawEffect ⟨0, _, _, .ok post, exc⟩ post (rlEnv (initSevm msg) T) o ∧
            Checkpoint (post.getStor msg.currentTarget) o.state :=
  @Blanc.Lift.Curve3Pool.pool_history_removeLiquidity_live_exact

example : ∀ {pool : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {s₀ : State} (trace : ConfiguredHistoryTrace cfg checkpoint future) (installed : some (checkpoint.state.getCode pool).toList = poolSem.image) (initial : Checkpoint (checkpoint.state.getStor pool) s₀) (env : PoolTraceEnv trace pool s₀.coins s₀.token) {msg : Msg} (target : msg.currentTarget = pool) (state : msg.benv.state = future.state),
        ∃ s, PoolHistoryAt trace pool s₀ s ∧
      ∀ {o : Out} {i j : Fin 3} {B1 B2 : B256} {W W' W'' : Devm → Prop} {U : Nat} (P : ExchangeExactCalls)
        (_hcode : (initSevm msg).code = code)
        (_hfork : CoveredFork (initSevm msg).benvStat.fork)
        (_hstatic : (initSevm msg).isStatic = false)
        (_hdepth : (initSevm msg).depth ≠ 0)
        (_hlen : 4 ≤ (initSevm msg).data.length)
        (_hcd : (initSevm msg).data.length < 2 ^ 256)
        (_hsel : Sevm.selector (initSevm msg) = selExchange)
        (_hi : i.val = (exI (initSevm msg)).toNat)
        (_hj : j.val = (exJ (initSevm msg)).toNat)
        (_hstep : step s (exEnv (initSevm msg) i j (exBalOpt i B1) (exBalOpt i B2))
          (decodeCall (initSevm msg)) = some o)
        (_hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
          (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty)
        (_hid : IdReady (initSevm msg) (initDevm msg))
        (_hWc : WClosed (initSevm msg) W)
        (_hW'c : WClosed (initSevm msg) W')
        (_hWb : W (initDevm msg))
        (_hbal : i = feeIndex →
          StaticWordCallProfile (initSevm msg) W W
            (((initDevm msg).getStor msg.currentTarget).get (coinSlot i))
            (balanceOfData msg.currentTarget) B1 U 0x3dc 0x24 0x440 P.balD1 P.balN1 ∧
          StaticWordCallProfile (initSevm msg) W' W'
            (((initDevm msg).getStor msg.currentTarget).get (coinSlot i))
            (balanceOfData msg.currentTarget) B2 U 0x71c 0x24 0x780 P.balD2 P.balN2)
        (_hpull : MutableCallProfile (initSevm msg) W W'
          (((initDevm msg).getStor msg.currentTarget).get (coinSlot i))
          (transferFromSel ++ msg.caller.toB256.toBytes ++ msg.currentTarget.toB256.toBytes ++
            (exDx (initSevm msg)).toBytes) RawCallOk U 0x600 0x64 0x6c0 P.pullD P.pullN)
        (_hW''c : WClosed (initSevm msg) W'')
        (_hpush : MutableCallProfile (initSevm msg) W' W''
          (((initDevm msg).getStor msg.currentTarget).get (coinSlot j))
          (transferSel ++ msg.caller.toB256.toBytes ++ (Nat.toB256 (exPushAmt o)).toBytes) RawCallOk U
          0xb60 0x44 0xc00 P.pushD P.pushN),
        ∃ (x0 x1 x2 : B256) (amp v : Nat),
          xpChk ⟨(balAt ((initDevm msg).getStor msg.currentTarget) 0).toNat,
            (balAt ((initDevm msg).getStor msg.currentTarget) 1).toNat,
            (balAt ((initDevm msg).getStor msg.currentTarget) 2).toNat⟩ =
              some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
          aChk s (initSevm msg).benvStat.time.toNat = some amp ∧
          (∃ (hi3 : (exI (initSevm msg)).toNat < 3) (hj3 : (exJ (initSevm msg)).toNat < 3),
            getYChk amp ⟨(exI (initSevm msg)).toNat, hi3⟩ ⟨(exJ (initSevm msg)).toNat, hj3⟩
              (exW3 x0 x1 x2 (exI (initSevm msg)).toNat + exCred (initSevm msg) B1 B2 *
                exRate (exI (initSevm msg)).toNat / exR0).toNat (V3.mk x0.toNat x1.toNat x2.toNat).get =
              some v) ∧
          ∀ R, 60000 + U ≤ R →
            costExchange (initSevm msg) (initDevm msg) s
              (exEnv (initSevm msg) i j (exBalOpt i B1) (exBalOpt i B2)) i j
              (exDx (initSevm msg)).toNat + 4 * U ≤
                R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v →
            R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v < 2 ^ 256 →
            (∀ post (exc : Exec 0 (initSevm (msg.withGas
                  (R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v)))
                (initDevm (msg.withGas
                  (R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v))) (.ok post)),
              PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
                ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
            ∃ post, ∃ exc : Exec 0 (initSevm (msg.withGas
                  (R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v)))
                (initDevm (msg.withGas
                  (R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v))) (.ok post),
              exec (initEvm (msg.withGas
                (R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v))) = .ok post ∧
              post.gasLeft = R ∧ ∃ bp bq,
              pullIn (exEnv (initSevm msg) i j bp bq) i (exDx (initSevm msg)).toNat =
                pullIn (exEnv (initSevm msg) i j (exBalOpt i B1) (exBalOpt i B2)) i
                  (exDx (initSevm msg)).toNat ∧
              RawEffect ⟨0, _, _, .ok post, exc⟩ post (exEnv (initSevm msg) i j bp bq) o ∧
              Checkpoint (post.getStor msg.currentTarget) o.state ∧ W'' post :=
  @Blanc.Lift.Curve3Pool.pool_history_exchange_live_exact

example : ∀ {pool : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {s₀ : State} (trace : ConfiguredHistoryTrace cfg checkpoint future) (installed : some (checkpoint.state.getCode pool).toList = poolSem.image) (initial : Checkpoint (checkpoint.state.getStor pool) s₀) (env : PoolTraceEnv trace pool s₀.coins s₀.token) {msg : Msg} (target : msg.currentTarget = pool) (state : msg.benv.state = future.state),
        ∃ s, PoolHistoryAt trace pool s₀ s ∧
      ∀ {o : Out} {T B1 B2 : B256} {W : Nat → Devm → Prop} {U : Nat} (P : ALExactCalls)
        (_hcode : (initSevm msg).code = code)
        (_hfork : CoveredFork (initSevm msg).benvStat.fork)
        (_hstatic : (initSevm msg).isStatic = false)
        (_hdepth : (initSevm msg).depth ≠ 0)
        (_hlen : 4 ≤ (initSevm msg).data.length)
        (_hcd : (initSevm msg).data.length < 2 ^ 256)
        (_hsel : Sevm.selector (initSevm msg) = selAddLiquidity)
        (_hstep : step s (alEnvW (initSevm msg) T.toNat B1.toNat B2.toNat) (decodeCall (initSevm msg)) =
          some o)
        (_htok : ¬ (initSevm msg).benvStat.rules.isPrecomp
          (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr)
        (_hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
          (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty)
        (_hid : IdReady (initSevm msg) (initDevm msg))
        (_hWc : ∀ j, j ≤ 4 → WClosed (initSevm msg) (W j))
        (_hWb : W 0 (initDevm msg))
        (_hskip : ∀ k : Fin 3, alAmt (initSevm msg) k.val = 0 → ∀ b, W k b → W (k + 1) b)
        (_hP : ALExactPremises (initSevm msg) ((initDevm msg).getStor msg.currentTarget) T B1 B2
          (Nat.toB256 (alMintAmt o)) W U P),
        ∃ (amp v0 v1 v2 : Nat) (xa xb xc : V3) (f0 f1 f2 s0 s1 s2 x0 x1 x2 : B256),
          aChk s (initSevm msg).benvStat.time.toNat = some amp ∧
          xpChk ⟨(alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2
              0).toNat,
            (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2 1).toNat,
            (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2
              2).toNat⟩ = some xb ∧
          getDChk xb.get amp 1 = some v1 ∧
          (T ≠ 0 →
            xpChk ⟨(balAt ((initDevm msg).getStor msg.currentTarget) 0).toNat,
              (balAt ((initDevm msg).getStor msg.currentTarget) 1).toNat,
              (balAt ((initDevm msg).getStor msg.currentTarget) 2).toNat⟩ = some xa ∧
            getDChk xa.get amp 1 = some v0 ∧
            RliFeeIter (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot))
              (((initDevm msg).getStor msg.currentTarget).get adminFeeSlot) (Nat.toB256 v0)
              (Nat.toB256 v1) (balAt ((initDevm msg).getStor msg.currentTarget) 0)
              (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2 0)
              f0 s0 x0 ∧
            RliFeeIter (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot))
              (((initDevm msg).getStor msg.currentTarget).get adminFeeSlot) (Nat.toB256 v0)
              (Nat.toB256 v1) (balAt ((initDevm msg).getStor msg.currentTarget) 1)
              (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2 1)
              f1 s1 x1 ∧
            RliFeeIter (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot))
              (((initDevm msg).getStor msg.currentTarget).get adminFeeSlot) (Nat.toB256 v0)
              (Nat.toB256 v1) (balAt ((initDevm msg).getStor msg.currentTarget) 2)
              (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2 2)
              f2 s2 x2 ∧
            xpChk ⟨x0.toNat, x1.toNat, x2.toNat⟩ = some xc ∧ getDChk xc.get amp 1 = some v2) ∧
          ∀ R, 100000 + 5 * U ≤ R →
          costAddLiquidity s (alEnvW (initSevm msg) T.toNat B1.toNat B2.toNat) (argV3 (initSevm msg) 0) +
              7 * U ≤
            R + alExactCost (initSevm msg) (initDevm msg) P amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0
              s1 s2 x0 x1 x2 →
          R + alExactCost (initSevm msg) (initDevm msg) P amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1
              s2 x0 x1 x2 + 6000 < 2 ^ 256 →
          (∀ post (exc : Exec 0 (initSevm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) P
                amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2)))
              (initDevm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) P amp T B1 B2 xa xb
                xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2))) (.ok post)),
            PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
              ∀ c' ∈ Exec.childFrames exc, c'.post.getCode 4 = c'.pre.getCode 4) →
          ∃ post, ∃ exc : Exec 0 (initSevm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) P
                amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2)))
              (initDevm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) P amp T B1 B2 xa xb
                xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2))) (.ok post),
            exec (initEvm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) P amp T B1 B2 xa
              xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2))) = .ok post ∧
            post.gasLeft = R ∧
            ∃ e : Env, e.supply = some T.toNat ∧ step s e (decodeCall (initSevm msg)) = some o ∧
              RawEffect ⟨0, _, _, .ok post, exc⟩ post e o ∧
              Checkpoint (post.getStor msg.currentTarget) o.state :=
  @Blanc.Lift.Curve3Pool.pool_history_addLiquidity_live_exact

example : ∀ {pool : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {s₀ : State} (trace : ConfiguredHistoryTrace cfg checkpoint future) (installed : some (checkpoint.state.getCode pool).toList = poolSem.image) (initial : Checkpoint (checkpoint.state.getStor pool) s₀) (env : PoolTraceEnv trace pool s₀.coins s₀.token) {msg : Msg} (target : msg.currentTarget = pool) (state : msg.benv.state = future.state),
        ∃ s, PoolHistoryAt trace pool s₀ s ∧
      ∀ {o : Out} {T : B256} {W : Nat → Devm → Prop} {U : Nat} (P : RLIExactCalls)
        (_hcode : (initSevm msg).code = code)
        (_hfork : CoveredFork (initSevm msg).benvStat.fork)
        (_hstatic : (initSevm msg).isStatic = false)
        (_hdepth : (initSevm msg).depth ≠ 0)
        (_hlen : 4 ≤ (initSevm msg).data.length)
        (_hcd : (initSevm msg).data.length < 2 ^ 256)
        (_hsel : Sevm.selector (initSevm msg) = selRemoveLiquidityImbalance)
        (_hstep : step s (rliEnvW (initSevm msg) T.toNat) (decodeCall (initSevm msg)) = some o)
        (_htok : ¬ (initSevm msg).benvStat.rules.isPrecomp
          (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr)
        (_hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
          (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty)
        (_hid : IdReady (initSevm msg) (initDevm msg))
        (_hWc : ∀ j, j ≤ 4 → WClosed (initSevm msg) (W j))
        (_hWb : W 0 (initDevm msg))
        (_hP : RLIExactPremises (initSevm msg) ((initDevm msg).getStor msg.currentTarget) T
          (Nat.toB256 (rliBurnAmt o)) W U P)
        (_hskip : ∀ k : Fin 3, rliAmt (initSevm msg) k.val = 0 → ∀ b, W (k + 1) b → W (k + 2) b),
        ∃ w : RliWords, RliWordsPin (initSevm msg) (initDevm msg) s w ∧
          ∀ R, 66000 + 3 * U ≤ R →
            costImbalance s (rliEnvW (initSevm msg) T.toNat) (argV3 (initSevm msg) 0) + 5 * U ≤
              R + rliExactCost (initSevm msg) (initDevm msg) P T w →
            R + rliExactCost (initSevm msg) (initDevm msg) P T w + 3000 < 2 ^ 256 →
            (∀ post (exc : Exec 0
                (initSevm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) P T w)))
                (initDevm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) P T w)))
                (.ok post)),
              PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
                ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
            ∃ post, ∃ exc : Exec 0
                (initSevm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) P T w)))
                (initDevm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) P T w)))
                (.ok post),
              exec (initEvm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) P T w))) =
                .ok post ∧
              post.gasLeft = R ∧
              RawEffect ⟨0, _, _, .ok post, exc⟩ post (rliEnvW (initSevm msg) T.toNat) o ∧
              Checkpoint (post.getStor msg.currentTarget) o.state ∧ W 4 post :=
  @Blanc.Lift.Curve3Pool.pool_history_removeLiquidityImbalance_live_exact

example : ∀ {pool : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {s₀ : State} (trace : ConfiguredHistoryTrace cfg checkpoint future) (installed : some (checkpoint.state.getCode pool).toList = poolSem.image) (initial : Checkpoint (checkpoint.state.getStor pool) s₀) (env : PoolTraceEnv trace pool s₀.coins s₀.token) {msg : Msg} (target : msg.currentTarget = pool) (state : msg.benv.state = future.state),
        ∃ s, PoolHistoryAt trace pool s₀ s ∧
      ∀ {o : Out} {i : Fin 3} {T : B256} {W W' W'' : Devm → Prop} {U : Nat} (P : OCExactCalls)
        (_hcode : (initSevm msg).code = code)
        (_hfork : CoveredFork (initSevm msg).benvStat.fork)
        (_hstatic : (initSevm msg).isStatic = false)
        (_hdepth : (initSevm msg).depth ≠ 0)
        (_hlen : 4 ≤ (initSevm msg).data.length)
        (_hcd : (initSevm msg).data.length < 2 ^ 256)
        (_hsel : Sevm.selector (initSevm msg) = selRemoveLiquidityOneCoin)
        (_hi : i.val = (ocI (initSevm msg)).toNat)
        (_hstep : step s (ocEnv (initSevm msg) i T.toNat) (decodeCall (initSevm msg)) = some o)
        (_htok : ¬ (initSevm msg).benvStat.rules.isPrecomp
          (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr)
        (_hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
          (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty)
        (_hid : IdReady (initSevm msg) (initDevm msg))
        (_hWc : WClosed (initSevm msg) W)
        (_hW'c : WClosed (initSevm msg) W')
        (_hWb : W (initDevm msg))
        (_hW''c : WClosed (initSevm msg) W'')
        (_hP : OCExactPremises (initSevm msg) (initDevm msg) T (Nat.toB256 (ocPushAmt o)) W W' W'' U P),
        ∃ (amp : Nat) (x0 x1 x2 D0 y r0 r1 r2 y2 : B256) (hi3 : (ocI (initSevm msg)).toNat < 3),
          aChk s (initSevm msg).benvStat.time.toNat = some amp ∧
          xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
          getDChk (V3.mk x0.toNat x1.toNat x2.toNat).get amp 1 = some D0.toNat ∧
          getYDChk amp ⟨(ocI (initSevm msg)).toNat, hi3⟩ (V3.mk x0.toNat x1.toNat x2.toNat).get
            (D0 - ocAmt (initSevm msg) * D0 / T).toNat = some y.toNat ∧
          CwStep (Bytes.toB256 [0] = ocI (initSevm msg)) x0 (D0 - ocAmt (initSevm msg) * D0 / T) D0 y
            (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot)) x0 r0 ∧
          CwStep (Bytes.toB256 [1] = ocI (initSevm msg)) x1 (D0 - ocAmt (initSevm msg) * D0 / T) D0 y
            (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot)) x1 r1 ∧
          CwStep (Bytes.toB256 [2] = ocI (initSevm msg)) x2 (D0 - ocAmt (initSevm msg) * D0 / T) D0 y
            (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot)) x2 r2 ∧
          getYDChk amp ⟨(ocI (initSevm msg)).toNat, hi3⟩ (V3.mk r0.toNat r1.toNat r2.toNat).get
            (D0 - ocAmt (initSevm msg) * D0 / T).toNat = some y2.toNat ∧
          ∀ R, 131000 + 3 * U ≤ R →
          R + ocExactCost (initSevm msg) (initDevm msg) T P amp x0 x1 x2 D0 y r0 r1 r2 y2 + 2000 <
            2 ^ 256 →
          (∀ post (exc : Exec 0 (initSevm (msg.withGas
                (R + ocExactCost (initSevm msg) (initDevm msg) T P amp x0 x1 x2 D0 y r0 r1 r2 y2)))
              (initDevm (msg.withGas
                (R + ocExactCost (initSevm msg) (initDevm msg) T P amp x0 x1 x2 D0 y r0 r1 r2 y2)))
              (.ok post)),
            PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
              ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
          ∃ post, ∃ exc : Exec 0 (initSevm (msg.withGas
                (R + ocExactCost (initSevm msg) (initDevm msg) T P amp x0 x1 x2 D0 y r0 r1 r2 y2)))
              (initDevm (msg.withGas
                (R + ocExactCost (initSevm msg) (initDevm msg) T P amp x0 x1 x2 D0 y r0 r1 r2 y2)))
              (.ok post),
            exec (initEvm (msg.withGas
              (R + ocExactCost (initSevm msg) (initDevm msg) T P amp x0 x1 x2 D0 y r0 r1 r2 y2))) =
              .ok post ∧
            post.gasLeft = R ∧ ∃ T' : Nat,
            RawEffect ⟨0, _, _, .ok post, exc⟩ post (ocEnv (initSevm msg) i T') o ∧
            Checkpoint (post.getStor msg.currentTarget) o.state ∧ W'' post :=
  @Blanc.Lift.Curve3Pool.pool_history_removeLiquidityOneCoin_live_exact

end Blanc.Lift.Curve3Pool

namespace Blanc.Composition.Curve3Pool3CrvHeadlinesExact
open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.ExecutionTrace Blanc.StableSwapNewton
open Blanc.Composition.Curve3Pool3CrvJoint (JointCheckpoint)
open Blanc.Composition.Curve3PoolCalleeLive
open Blanc.Composition.Curve3Pool3CrvHeadlines (C3Ready C3With C3Blind c3Ready_of_history
  c3With_wClosed)
open Blanc.Composition.Curve3Pool3CrvExactAssembly

example : ∀ {pool c3 : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {ps₀ : Curve3Pool.State} {cs₀ : Blanc.Curve3Crv.State} {K₀ : Curve3Crv.Key → Prop} (trace : ConfiguredHistoryTrace cfg checkpoint future) (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image) (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image) (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state) (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace)) (env : PoolTraceEnv trace pool ps₀.coins ps₀.token) (notSystem : pool ≠ systemAddress) {msg : Msg} (target : msg.currentTarget = pool) (state : msg.benv.state = future.state),
        ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 (initDevm msg) ∧
      ∀ {o : Out} {T : B256} {V : Nat → Devm → Prop} {U : Nat}
        (pushD : Nat → Devm → List B256 → Mem → Nat) (pushN : Nat → Devm → List B256 → Mem → Devm)
        (_hcode : (initSevm msg).code = code)
        (_hfork : CoveredFork (initSevm msg).benvStat.fork)
        (_hstatic : (initSevm msg).isStatic = false) (_hdepth : (initSevm msg).depth ≠ 0)
        (_hlen : 4 ≤ (initSevm msg).data.length) (_hcd : (initSevm msg).data.length < 2 ^ 256)
        (_hsel : Sevm.selector (initSevm msg) = selRemoveLiquidity)
        (_hstep : step s (rlEnv (initSevm msg) T) (decodeCall (initSevm msg)) = some o)
        (_htok : ¬ (initSevm msg).benvStat.rules.isPrecomp c3)
        (_hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
          (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty)
        (_hid : IdReady (initSevm msg) (initDevm msg))
        (_hU : 70000 ≤ U)
        (_hT : (Devm.getStor (initDevm msg) c3).get Curve3Crv.vySupplySlot = T)
        (_hburn : BurnFits (Devm.getStor (initDevm msg) c3) pool msg.caller.toB256
          (rlAmt (initSevm msg)))
        (_hVc : ∀ k, k ≤ 3 → WClosed (initSevm msg) (V k)) (_hVb : V 0 (initDevm msg))
        (_hVs : ∀ k, C3Blind c3 (V k))
        (_hpush : ∀ i, i < 3 → MutableCallProfile (initSevm msg)
          (C3With c3 (Devm.getStor (initDevm msg) c3) (V i))
          (C3With c3 (Devm.getStor (initDevm msg) c3) (V (i + 1)))
          (coinAt ((initDevm msg).getStor msg.currentTarget) i)
          (transferSel ++ msg.caller.toB256.toBytes ++
            (balAt ((initDevm msg).getStor msg.currentTarget) i * rlAmt (initSevm msg) / T).toBytes)
          RawCallOk U 0x520 0x44 0x5c0 (pushD i) (pushN i)),
        ∀ R, 167000 + 5 * U ≤ R →
          R + rlExactCost (initSevm msg) (initDevm msg) T (rlC3Calls (initSevm msg) (initDevm msg) pushD pushN) < 2 ^ 256 →
          (∀ post (exc : Exec 0 (initSevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T (rlC3Calls (initSevm msg) (initDevm msg) pushD pushN))))
              (initDevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T (rlC3Calls (initSevm msg) (initDevm msg) pushD pushN)))) (.ok post)),
            PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
              ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
          ∃ post, ∃ exc : Exec 0 (initSevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T (rlC3Calls (initSevm msg) (initDevm msg) pushD pushN))))
              (initDevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T (rlC3Calls (initSevm msg) (initDevm msg) pushD pushN)))) (.ok post),
            exec (initEvm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T (rlC3Calls (initSevm msg) (initDevm msg) pushD pushN)))) =
              .ok post ∧
            post.gasLeft = R ∧
            RawEffect ⟨0, _, _, .ok post, exc⟩ post (rlEnv (initSevm msg) T) o ∧
            Checkpoint (post.getStor msg.currentTarget) o.state :=
  @Blanc.Composition.Curve3Pool3CrvHeadlinesExact.pool_3crv_removeLiquidity_live_exact

example : ∀ {pool c3 : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {ps₀ : Curve3Pool.State} {cs₀ : Blanc.Curve3Crv.State} {K₀ : Curve3Crv.Key → Prop} (trace : ConfiguredHistoryTrace cfg checkpoint future) (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image) (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image) (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state) (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace)) (env : PoolTraceEnv trace pool ps₀.coins ps₀.token) (notSystem : pool ≠ systemAddress) {msg : Msg} (target : msg.currentTarget = pool) (state : msg.benv.state = future.state),
        ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 (initDevm msg) ∧
      ∀ {o : Out} {T B1 B2 : B256} {V : Nat → Devm → Prop} {U : Nat}
        (pullD : Nat → Devm → List B256 → Mem → Nat) (pullN : Nat → Devm → List B256 → Mem → Devm)
        (balBD balAD : Devm → List B256 → Mem → Nat) (balBN balAN : Devm → List B256 → Mem → Devm)
        (_hcode : (initSevm msg).code = code)
        (_hfork : CoveredFork (initSevm msg).benvStat.fork)
        (_hstatic : (initSevm msg).isStatic = false) (_hdepth : (initSevm msg).depth ≠ 0)
        (_hlen : 4 ≤ (initSevm msg).data.length) (_hcd : (initSevm msg).data.length < 2 ^ 256)
        (_hsel : Sevm.selector (initSevm msg) = selAddLiquidity)
        (_hstep : step s (alEnvW (initSevm msg) T.toNat B1.toNat B2.toNat)
          (decodeCall (initSevm msg)) = some o)
        (_htok : ¬ (initSevm msg).benvStat.rules.isPrecomp c3)
        (_hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
          (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty)
        (_hid : IdReady (initSevm msg) (initDevm msg))
        (_hU : 70000 ≤ U)
        (_hT : (Devm.getStor (initDevm msg) c3).get Curve3Crv.vySupplySlot = T)
        (_hmint : MintFits (Devm.getStor (initDevm msg) c3) pool msg.caller.toB256
          (Nat.toB256 (alMintAmt o)))
        (_hVc : ∀ k, k ≤ 3 → WClosed (initSevm msg) (V k)) (_hVb : V 0 (initDevm msg))
        (_hVs : ∀ k, C3Blind c3 (V k))
        (_hskip : ∀ k : Fin 3, alAmt (initSevm msg) k.val = 0 → ∀ b, V k b → V (k + 1) b)
        (_hpull : ∀ k, k < 3 → alAmt (initSevm msg) k ≠ 0 →
          MutableCallProfile (initSevm msg) (C3With c3 (Devm.getStor (initDevm msg) c3) (V k))
            (C3With c3 (Devm.getStor (initDevm msg) c3) (V (k + 1)))
            (coinAt ((initDevm msg).getStor msg.currentTarget) k)
            (transferFromSel ++ msg.caller.toB256.toBytes ++ msg.currentTarget.toB256.toBytes ++
              (alAmt (initSevm msg) k).toBytes) RawCallOk U 0x760 0x64 0x820 (pullD k) (pullN k))
        (_hbalB : alAmt (initSevm msg) 2 ≠ 0 →
          StaticWordCallProfile (initSevm msg) (C3With c3 (Devm.getStor (initDevm msg) c3) (V 2))
            (C3With c3 (Devm.getStor (initDevm msg) c3) (V 2))
            (coinAt ((initDevm msg).getStor msg.currentTarget) 2)
            (balanceOfData msg.currentTarget) B1 U 0x53c 0x24 0x5a0 balBD balBN)
        (_hbalA : alAmt (initSevm msg) 2 ≠ 0 →
          StaticWordCallProfile (initSevm msg) (C3With c3 (Devm.getStor (initDevm msg) c3) (V 3))
            (C3With c3 (Devm.getStor (initDevm msg) c3) (V 3))
            (coinAt ((initDevm msg).getStor msg.currentTarget) 2)
            (balanceOfData msg.currentTarget) B2 U 0x87c 0x24 0x8e0 balAD balAN),
        ∃ (amp v0 v1 v2 : Nat) (xa xb xc : V3) (f0 f1 f2 s0 s1 s2 x0 x1 x2 : B256),
          aChk s (initSevm msg).benvStat.time.toNat = some amp ∧
          xpChk ⟨(alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2
              0).toNat,
            (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2 1).toNat,
            (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2
              2).toNat⟩ = some xb ∧
          getDChk xb.get amp 1 = some v1 ∧
          (T ≠ 0 →
            xpChk ⟨(balAt ((initDevm msg).getStor msg.currentTarget) 0).toNat,
              (balAt ((initDevm msg).getStor msg.currentTarget) 1).toNat,
              (balAt ((initDevm msg).getStor msg.currentTarget) 2).toNat⟩ = some xa ∧
            getDChk xa.get amp 1 = some v0 ∧
            RliFeeIter (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot))
              (((initDevm msg).getStor msg.currentTarget).get adminFeeSlot) (Nat.toB256 v0)
              (Nat.toB256 v1) (balAt ((initDevm msg).getStor msg.currentTarget) 0)
              (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2 0)
              f0 s0 x0 ∧
            RliFeeIter (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot))
              (((initDevm msg).getStor msg.currentTarget).get adminFeeSlot) (Nat.toB256 v0)
              (Nat.toB256 v1) (balAt ((initDevm msg).getStor msg.currentTarget) 1)
              (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2 1)
              f1 s1 x1 ∧
            RliFeeIter (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot))
              (((initDevm msg).getStor msg.currentTarget).get adminFeeSlot) (Nat.toB256 v0)
              (Nat.toB256 v1) (balAt ((initDevm msg).getStor msg.currentTarget) 2)
              (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2 2)
              f2 s2 x2 ∧
            xpChk ⟨x0.toNat, x1.toNat, x2.toNat⟩ = some xc ∧ getDChk xc.get amp 1 = some v2) ∧
          ∀ R, 100000 + 5 * U ≤ R →
          costAddLiquidity s (alEnvW (initSevm msg) T.toNat B1.toNat B2.toNat) (argV3 (initSevm msg) 0) +
              7 * U ≤
            R + alExactCost (initSevm msg) (initDevm msg) (alC3Calls (initSevm msg) (initDevm msg) pullD pullN balBD balAD balBN balAN) amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0
              s1 s2 x0 x1 x2 →
          R + alExactCost (initSevm msg) (initDevm msg) (alC3Calls (initSevm msg) (initDevm msg) pullD pullN balBD balAD balBN balAN) amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1
              s2 x0 x1 x2 + 6000 < 2 ^ 256 →
          (∀ post (exc : Exec 0 (initSevm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) (alC3Calls (initSevm msg) (initDevm msg) pullD pullN balBD balAD balBN balAN)
                amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2)))
              (initDevm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) (alC3Calls (initSevm msg) (initDevm msg) pullD pullN balBD balAD balBN balAN) amp T B1 B2 xa xb
                xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2))) (.ok post)),
            PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
              ∀ c' ∈ Exec.childFrames exc, c'.post.getCode 4 = c'.pre.getCode 4) →
          ∃ post, ∃ exc : Exec 0 (initSevm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) (alC3Calls (initSevm msg) (initDevm msg) pullD pullN balBD balAD balBN balAN)
                amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2)))
              (initDevm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) (alC3Calls (initSevm msg) (initDevm msg) pullD pullN balBD balAD balBN balAN) amp T B1 B2 xa xb
                xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2))) (.ok post),
            exec (initEvm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) (alC3Calls (initSevm msg) (initDevm msg) pullD pullN balBD balAD balBN balAN) amp T B1 B2 xa
              xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2))) = .ok post ∧
            post.gasLeft = R ∧
            ∃ e : Env, e.supply = some T.toNat ∧ step s e (decodeCall (initSevm msg)) = some o ∧
              RawEffect ⟨0, _, _, .ok post, exc⟩ post e o ∧
              Checkpoint (post.getStor msg.currentTarget) o.state :=
  @Blanc.Composition.Curve3Pool3CrvHeadlinesExact.pool_3crv_addLiquidity_live_exact

example : ∀ {pool c3 : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {ps₀ : Curve3Pool.State} {cs₀ : Blanc.Curve3Crv.State} {K₀ : Curve3Crv.Key → Prop} (trace : ConfiguredHistoryTrace cfg checkpoint future) (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image) (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image) (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state) (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace)) (env : PoolTraceEnv trace pool ps₀.coins ps₀.token) (notSystem : pool ≠ systemAddress) {msg : Msg} (target : msg.currentTarget = pool) (state : msg.benv.state = future.state),
        ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 (initDevm msg) ∧
      ∀ {o : Out} {T : B256} {V : Nat → Devm → Prop} {U : Nat}
        (pushD : Nat → Devm → List B256 → Mem → Nat) (pushN : Nat → Devm → List B256 → Mem → Devm)
        (_hcode : (initSevm msg).code = code)
        (_hfork : CoveredFork (initSevm msg).benvStat.fork)
        (_hstatic : (initSevm msg).isStatic = false) (_hdepth : (initSevm msg).depth ≠ 0)
        (_hlen : 4 ≤ (initSevm msg).data.length) (_hcd : (initSevm msg).data.length < 2 ^ 256)
        (_hsel : Sevm.selector (initSevm msg) = selRemoveLiquidityImbalance)
        (_hstep : step s (rliEnvW (initSevm msg) T.toNat) (decodeCall (initSevm msg)) = some o)
        (_htok : ¬ (initSevm msg).benvStat.rules.isPrecomp c3)
        (_hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
          (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty)
        (_hid : IdReady (initSevm msg) (initDevm msg))
        (_hU : 70000 ≤ U)
        (_hT : (Devm.getStor (initDevm msg) c3).get Curve3Crv.vySupplySlot = T)
        (_hburn : BurnFits (Devm.getStor (initDevm msg) c3) pool msg.caller.toB256
          (Nat.toB256 (rliBurnAmt o)))
        (_hVc : ∀ k, k ≤ 3 → WClosed (initSevm msg) (V k)) (_hVb : V 0 (initDevm msg))
        (_hVs : ∀ k, C3Blind c3 (V k))
        (_hskip : ∀ k : Fin 3, rliAmt (initSevm msg) k.val = 0 → ∀ b, V k b → V (k + 1) b)
        (_hpush : ∀ k, k < 3 → rliAmt (initSevm msg) k ≠ 0 →
          MutableCallProfile (initSevm msg)
            (C3With c3 (burnStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256
              (Nat.toB256 (rliBurnAmt o))) (V k))
            (C3With c3 (burnStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256
              (Nat.toB256 (rliBurnAmt o))) (V (k + 1)))
            (((initDevm msg).getStor msg.currentTarget).get (coinsBase + Nat.toB256 k))
            (transferSel ++ msg.caller.toB256.toBytes ++ (rliAmt (initSevm msg) k).toBytes)
            RawCallOk U 0xaa0 0x44 0xb40 (pushD k) (pushN k)),
        ∃ w : RliWords, RliWordsPin (initSevm msg) (initDevm msg) s w ∧
          ∀ R, 66000 + 3 * U ≤ R →
            costImbalance s (rliEnvW (initSevm msg) T.toNat) (argV3 (initSevm msg) 0) + 5 * U ≤
              R + rliExactCost (initSevm msg) (initDevm msg) (rliC3Calls (initSevm msg) (initDevm msg) pushD pushN) T w →
            R + rliExactCost (initSevm msg) (initDevm msg) (rliC3Calls (initSevm msg) (initDevm msg) pushD pushN) T w + 3000 < 2 ^ 256 →
            (∀ post (exc : Exec 0
                (initSevm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) (rliC3Calls (initSevm msg) (initDevm msg) pushD pushN) T w)))
                (initDevm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) (rliC3Calls (initSevm msg) (initDevm msg) pushD pushN) T w)))
                (.ok post)),
              PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
                ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
            ∃ post, ∃ exc : Exec 0
                (initSevm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) (rliC3Calls (initSevm msg) (initDevm msg) pushD pushN) T w)))
                (initDevm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) (rliC3Calls (initSevm msg) (initDevm msg) pushD pushN) T w)))
                (.ok post),
              exec (initEvm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) (rliC3Calls (initSevm msg) (initDevm msg) pushD pushN) T w))) =
                .ok post ∧
              post.gasLeft = R ∧
              RawEffect ⟨0, _, _, .ok post, exc⟩ post (rliEnvW (initSevm msg) T.toNat) o ∧
              Checkpoint (post.getStor msg.currentTarget) o.state ∧ C3With c3 (burnStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256
                (Nat.toB256 (rliBurnAmt o))) (V 3) post :=
  @Blanc.Composition.Curve3Pool3CrvHeadlinesExact.pool_3crv_removeLiquidityImbalance_live_exact

example : ∀ {pool c3 : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {ps₀ : Curve3Pool.State} {cs₀ : Blanc.Curve3Crv.State} {K₀ : Curve3Crv.Key → Prop} (trace : ConfiguredHistoryTrace cfg checkpoint future) (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image) (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image) (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state) (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace)) (env : PoolTraceEnv trace pool ps₀.coins ps₀.token) (notSystem : pool ≠ systemAddress) {msg : Msg} (target : msg.currentTarget = pool) (state : msg.benv.state = future.state),
        ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 (initDevm msg) ∧
      ∀ {o : Out} {i : Fin 3} {T : B256} {V : Nat → Devm → Prop} {U : Nat}
        (pushD : Devm → List B256 → Mem → Nat) (pushN : Devm → List B256 → Mem → Devm)
        (_hcode : (initSevm msg).code = code)
        (_hfork : CoveredFork (initSevm msg).benvStat.fork)
        (_hstatic : (initSevm msg).isStatic = false) (_hdepth : (initSevm msg).depth ≠ 0)
        (_hlen : 4 ≤ (initSevm msg).data.length) (_hcd : (initSevm msg).data.length < 2 ^ 256)
        (_hsel : Sevm.selector (initSevm msg) = selRemoveLiquidityOneCoin)
        (_hi : i.val = (ocI (initSevm msg)).toNat)
        (_hstep : step s (ocEnv (initSevm msg) i T.toNat) (decodeCall (initSevm msg)) = some o)
        (_htok : ¬ (initSevm msg).benvStat.rules.isPrecomp c3)
        (_hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
          (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty)
        (_hid : IdReady (initSevm msg) (initDevm msg))
        (_hU : 70000 ≤ U)
        (_hT : (Devm.getStor (initDevm msg) c3).get Curve3Crv.vySupplySlot = T)
        (_hburn : BurnFits (Devm.getStor (initDevm msg) c3) pool msg.caller.toB256
          (ocAmt (initSevm msg)))
        (_hVc : ∀ k, k ≤ 1 → WClosed (initSevm msg) (V k)) (_hVb : V 0 (initDevm msg))
        (_hVs : C3Blind c3 (V 0))
        (_hpush : MutableCallProfile (initSevm msg)
          (C3With c3 (burnStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256
            (ocAmt (initSevm msg))) (V 0))
          (C3With c3 (burnStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256
            (ocAmt (initSevm msg))) (V 1))
          (((initDevm msg).getStor msg.currentTarget).get (coinsBase + ocI (initSevm msg)))
          (transferSel ++ msg.caller.toB256.toBytes ++ (Nat.toB256 (ocPushAmt o)).toBytes) RawCallOk
          U 0x540 0x44 0x5e0 pushD pushN),
        ∃ (amp : Nat) (x0 x1 x2 D0 y r0 r1 r2 y2 : B256) (hi3 : (ocI (initSevm msg)).toNat < 3),
          aChk s (initSevm msg).benvStat.time.toNat = some amp ∧
          xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
          getDChk (V3.mk x0.toNat x1.toNat x2.toNat).get amp 1 = some D0.toNat ∧
          getYDChk amp ⟨(ocI (initSevm msg)).toNat, hi3⟩ (V3.mk x0.toNat x1.toNat x2.toNat).get
            (D0 - ocAmt (initSevm msg) * D0 / T).toNat = some y.toNat ∧
          CwStep (Bytes.toB256 [0] = ocI (initSevm msg)) x0 (D0 - ocAmt (initSevm msg) * D0 / T) D0 y
            (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot)) x0 r0 ∧
          CwStep (Bytes.toB256 [1] = ocI (initSevm msg)) x1 (D0 - ocAmt (initSevm msg) * D0 / T) D0 y
            (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot)) x1 r1 ∧
          CwStep (Bytes.toB256 [2] = ocI (initSevm msg)) x2 (D0 - ocAmt (initSevm msg) * D0 / T) D0 y
            (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot)) x2 r2 ∧
          getYDChk amp ⟨(ocI (initSevm msg)).toNat, hi3⟩ (V3.mk r0.toNat r1.toNat r2.toNat).get
            (D0 - ocAmt (initSevm msg) * D0 / T).toNat = some y2.toNat ∧
          ∀ R, 131000 + 3 * U ≤ R →
          R + ocExactCost (initSevm msg) (initDevm msg) T (ocC3Calls (initSevm msg) (initDevm msg) pushD pushN) amp x0 x1 x2 D0 y r0 r1 r2 y2 + 2000 <
            2 ^ 256 →
          (∀ post (exc : Exec 0 (initSevm (msg.withGas
                (R + ocExactCost (initSevm msg) (initDevm msg) T (ocC3Calls (initSevm msg) (initDevm msg) pushD pushN) amp x0 x1 x2 D0 y r0 r1 r2 y2)))
              (initDevm (msg.withGas
                (R + ocExactCost (initSevm msg) (initDevm msg) T (ocC3Calls (initSevm msg) (initDevm msg) pushD pushN) amp x0 x1 x2 D0 y r0 r1 r2 y2)))
              (.ok post)),
            PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
              ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
          ∃ post, ∃ exc : Exec 0 (initSevm (msg.withGas
                (R + ocExactCost (initSevm msg) (initDevm msg) T (ocC3Calls (initSevm msg) (initDevm msg) pushD pushN) amp x0 x1 x2 D0 y r0 r1 r2 y2)))
              (initDevm (msg.withGas
                (R + ocExactCost (initSevm msg) (initDevm msg) T (ocC3Calls (initSevm msg) (initDevm msg) pushD pushN) amp x0 x1 x2 D0 y r0 r1 r2 y2)))
              (.ok post),
            exec (initEvm (msg.withGas
              (R + ocExactCost (initSevm msg) (initDevm msg) T (ocC3Calls (initSevm msg) (initDevm msg) pushD pushN) amp x0 x1 x2 D0 y r0 r1 r2 y2))) =
              .ok post ∧
            post.gasLeft = R ∧ ∃ T' : Nat,
            RawEffect ⟨0, _, _, .ok post, exc⟩ post (ocEnv (initSevm msg) i T') o ∧
            Checkpoint (post.getStor msg.currentTarget) o.state ∧ C3With c3 (burnStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256
              (ocAmt (initSevm msg))) (V 1) post :=
  @Blanc.Composition.Curve3Pool3CrvHeadlinesExact.pool_3crv_removeLiquidityOneCoin_live_exact

end Blanc.Composition.Curve3Pool3CrvHeadlinesExact

namespace Blanc.Composition.Curve3Pool3CrvInstance
open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool
open Blanc.Composition.Curve3PoolCalleeLive Blanc.Composition.Curve3PoolCalleeExactProfiles
open Blanc.Composition.Curve3Pool3CrvHeadlines (C3At c3At_burn c3At_mint precomp_false)

example : ∀ {sevm : Sevm} {pre : Devm} {T : B256} (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0) (hc3 : C3Entry sevm pre T) (hcoins : T20Coins sevm pre) (hburn : BurnFits (Devm.getStor pre (tokOf sevm pre)) sevm.currentTarget sevm.caller.toB256 (rlAmt sevm)) (hfits : ∀ k : Fin 3, T20MoveFits (pre.getStor (coinOf sevm pre k)) sevm.currentTarget sevm.caller (balAt (pre.getStor sevm.currentTarget) k * rlAmt sevm / T)),
        (∀ k, k ≤ 3 → WClosed sevm (rlWorld sevm pre k)) ∧ rlWorld sevm pre 0 pre ∧
      ∃ P : RLExactCalls, RLExactPremises sevm pre T (rlWorld sevm pre) 80000 P :=
  @Blanc.Composition.Curve3Pool3CrvInstance.removeLiquidity_exactPremises_satisfiable

example : ∀ {sevm : Sevm} {pre : Devm} {T m : B256} (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0) (hc3 : C3Entry sevm pre T) (hcoins : T20Coins sevm pre) (hmint : MintFits (Devm.getStor pre (tokOf sevm pre)) sevm.currentTarget sevm.caller.toB256 m) (hfits : ∀ k : Fin 3, alAmt sevm k.val ≠ 0 → T20PullFits (pre.getStor (coinOf sevm pre k)) sevm.caller sevm.currentTarget sevm.currentTarget (alAmt sevm k.val)),
        (∀ k, k ≤ 4 → WClosed sevm (alWorld sevm pre m k)) ∧ alWorld sevm pre m 0 pre ∧
      (∀ k : Fin 3, alAmt sevm k.val = 0 → ∀ b, alWorld sevm pre m k b →
        alWorld sevm pre m (k + 1) b) ∧
      ∃ P : ALExactCalls, ALExactPremises sevm (pre.getStor sevm.currentTarget) T
        ((pre.getStor (coinOf sevm pre 2)).get
          (Blanc.Lift.Token20.balSlot sevm.currentTarget))
        ((alFeeStor sevm pre).get (Blanc.Lift.Token20.balSlot sevm.currentTarget))
        m (alWorld sevm pre m) 80000 P :=
  @Blanc.Composition.Curve3Pool3CrvInstance.addLiquidity_exactPremises_satisfiable

example : ∀ {sevm : Sevm} {pre : Devm} {T m : B256} (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0) (hc3 : C3Entry sevm pre T) (hcoins : T20Coins sevm pre) (hburn : BurnFits (Devm.getStor pre (tokOf sevm pre)) sevm.currentTarget sevm.caller.toB256 m) (hfits : ∀ k : Fin 3, rliAmt sevm k.val ≠ 0 → T20MoveFits (pre.getStor (coinOf sevm pre k)) sevm.currentTarget sevm.caller (rliAmt sevm k.val)),
        (∀ j, j ≤ 4 → WClosed sevm (rliWorld sevm pre m j)) ∧ rliWorld sevm pre m 0 pre ∧
      (∀ k : Fin 3, rliAmt sevm k.val = 0 → ∀ b, rliWorld sevm pre m (k + 1) b →
        rliWorld sevm pre m (k + 2) b) ∧
      ∃ P : RLIExactCalls, RLIExactPremises sevm (pre.getStor sevm.currentTarget) T m
        (rliWorld sevm pre m) 80000 P :=
  @Blanc.Composition.Curve3Pool3CrvInstance.removeLiquidityImbalance_exactPremises_satisfiable

example : ∀ {sevm : Sevm} {pre : Devm} {T v : B256} {i : Fin 3} (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0) (hc3 : C3Entry sevm pre T) (hi : i.val = (ocI sevm).toNat) (hcode : pre.getCode (coinOf sevm pre i) = Blanc.Lift.Token20.code) (hprec : ¬ sevm.benvStat.rules.isPrecomp (coinOf sevm pre i)) (hpool : coinOf sevm pre i ≠ sevm.currentTarget) (htok : coinOf sevm pre i ≠ tokOf sevm pre) (hburn : BurnFits (Devm.getStor pre (tokOf sevm pre)) sevm.currentTarget sevm.caller.toB256 (ocAmt sevm)) (hfits : T20MoveFits (pre.getStor (coinOf sevm pre i)) sevm.currentTarget sevm.caller v),
        WClosed sevm (ocWorld sevm pre (Devm.getStor pre (tokOf sevm pre)) i) ∧
      WClosed sevm (ocWorld sevm pre (burnStor (Devm.getStor pre (tokOf sevm pre))
        sevm.caller.toB256 (ocAmt sevm)) i) ∧
      ocWorld sevm pre (Devm.getStor pre (tokOf sevm pre)) i pre ∧ WClosed sevm (fun _ => True) ∧
      ∃ P : OCExactCalls, OCExactPremises sevm pre T v
        (ocWorld sevm pre (Devm.getStor pre (tokOf sevm pre)) i)
        (ocWorld sevm pre (burnStor (Devm.getStor pre (tokOf sevm pre)) sevm.caller.toB256
          (ocAmt sevm)) i) (fun _ => True) 80000 P :=
  @Blanc.Composition.Curve3Pool3CrvInstance.removeLiquidityOneCoin_exactPremises_satisfiable

example : ∀ {sevm : Sevm} {pre : Devm} {i j : Fin 3} {v : B256} (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0) (hcoins : T20Coins sevm pre) (hij : i ≠ j) (hpullFits : T20PullFits (pre.getStor (coinOf sevm pre i)) sevm.caller sevm.currentTarget sevm.currentTarget (exDx sevm)) (hpushFits : T20MoveFits (pre.getStor (coinOf sevm pre j)) sevm.currentTarget sevm.caller v),
        WClosed sevm (exWorld0 sevm pre i j) ∧ WClosed sevm (exWorld1 sevm pre i j) ∧
      WClosed sevm (fun _ => True) ∧ exWorld0 sevm pre i j pre ∧
      ∃ P : ExchangeExactCalls,
        (i = feeIndex →
          StaticWordCallProfile sevm (exWorld0 sevm pre i j) (exWorld0 sevm pre i j)
            ((pre.getStor sevm.currentTarget).get (coinSlot i)) (balanceOfData sevm.currentTarget)
            ((pre.getStor (coinOf sevm pre i)).get
              (Blanc.Lift.Token20.balSlot sevm.currentTarget))
            80000 0x3dc 0x24 0x440 P.balD1 P.balN1 ∧
          StaticWordCallProfile sevm (exWorld1 sevm pre i j) (exWorld1 sevm pre i j)
            ((pre.getStor sevm.currentTarget).get (coinSlot i)) (balanceOfData sevm.currentTarget)
            ((exPulledStor sevm pre i).get
              (Blanc.Lift.Token20.balSlot sevm.currentTarget))
            80000 0x71c 0x24 0x780 P.balD2 P.balN2) ∧
        MutableCallProfile sevm (exWorld0 sevm pre i j) (exWorld1 sevm pre i j)
          ((pre.getStor sevm.currentTarget).get (coinSlot i))
          (transferFromSel ++ sevm.caller.toB256.toBytes ++ sevm.currentTarget.toB256.toBytes ++
            (exDx sevm).toBytes) RawCallOk 80000 0x600 0x64 0x6c0 P.pullD P.pullN ∧
        MutableCallProfile sevm (exWorld1 sevm pre i j) (fun _ => True)
          ((pre.getStor sevm.currentTarget).get (coinSlot j))
          (transferSel ++ sevm.caller.toB256.toBytes ++ v.toBytes) RawCallOk 80000 0xb60 0x44 0xc00
          P.pushD P.pushN :=
  @Blanc.Composition.Curve3Pool3CrvInstance.exchange_exactPremises_satisfiable

end Blanc.Composition.Curve3Pool3CrvInstance

namespace Blanc.Composition.Curve3Pool3CrvLiteralWitness
open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.ExecutionTrace Blanc.StableSwapNewton
open Blanc.Composition.Curve3Pool3CrvJoint (JointCheckpoint)
open Blanc.Composition.Curve3PoolCalleeLive
open Blanc.Composition.Curve3Pool3CrvHeadlines (C3Ready C3With C3Blind)
open Blanc.Composition.Curve3Pool3CrvExactAssembly
open Blanc.Composition.Curve3Pool3CrvHeadlinesExact
open Blanc.Composition.Curve3Pool3CrvInstance

example : ∀ {pool c3 : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {ps₀ : Curve3Pool.State} {cs₀ : Blanc.Curve3Crv.State} {K₀ : Curve3Crv.Key → Prop} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state)
    (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace))
    (env : PoolTraceEnv trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress)
    {msg : Msg} (target : msg.currentTarget = pool) (state : msg.benv.state = future.state)
    {T : B256} (hfork : CoveredFork (initSevm msg).benvStat.fork)
    (hstatic : (initSevm msg).isStatic = false) (hdepth : (initSevm msg).depth ≠ 0)
    (hc3 : C3Entry (initSevm msg) (initDevm msg) T)
    (hcoins : T20Coins (initSevm msg) (initDevm msg))
    (hburn : BurnFits (Devm.getStor (initDevm msg) c3) pool msg.caller.toB256
      (rlAmt (initSevm msg)))
    (hfits : ∀ k : Fin 3, T20MoveFits
      ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) k)) msg.currentTarget
      msg.caller (balAt ((initDevm msg).getStor msg.currentTarget) k * rlAmt (initSevm msg) / T)),
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 (initDevm msg) ∧
      ∃ (V : Nat → Devm → Prop) (U : Nat) (pushD : Nat → Devm → List B256 → Mem → Nat)
        (pushN : Nat → Devm → List B256 → Mem → Devm),
          (¬ (initSevm msg).benvStat.rules.isPrecomp c3 ∧
          (∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
              (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr) ∧
          70000 ≤ U ∧
          (Devm.getStor (initDevm msg) c3).get Curve3Crv.vySupplySlot = T ∧
          BurnFits (Devm.getStor (initDevm msg) c3) pool msg.caller.toB256
              (rlAmt (initSevm msg)) ∧
          (∀ k, k ≤ 3 → WClosed (initSevm msg) (V k)) ∧ V 0 (initDevm msg) ∧
          (∀ k, C3Blind c3 (V k)) ∧
          (∀ i, i < 3 → MutableCallProfile (initSevm msg)
              (C3With c3 (Devm.getStor (initDevm msg) c3) (V i))
              (C3With c3 (Devm.getStor (initDevm msg) c3) (V (i + 1)))
              (coinAt ((initDevm msg).getStor msg.currentTarget) i)
              (transferSel ++ msg.caller.toB256.toBytes ++
                (balAt ((initDevm msg).getStor msg.currentTarget) i * rlAmt (initSevm msg) / T).toBytes)
              RawCallOk U 0x520 0x44 0x5c0 (pushD i) (pushN i))) ∧
      ∀ {o : Out}
        (_hcode : (initSevm msg).code = code)
        (_hlen : 4 ≤ (initSevm msg).data.length) (_hcd : (initSevm msg).data.length < 2 ^ 256)
        (_hsel : Sevm.selector (initSevm msg) = selRemoveLiquidity)
        (_hstep : step s (rlEnv (initSevm msg) T) (decodeCall (initSevm msg)) = some o)
        (_hid : IdReady (initSevm msg) (initDevm msg)),
        ∀ R, 167000 + 5 * U ≤ R →
          R + rlExactCost (initSevm msg) (initDevm msg) T (rlC3Calls (initSevm msg) (initDevm msg) pushD pushN) < 2 ^ 256 →
          (∀ post (exc : Exec 0 (initSevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T (rlC3Calls (initSevm msg) (initDevm msg) pushD pushN))))
              (initDevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T (rlC3Calls (initSevm msg) (initDevm msg) pushD pushN)))) (.ok post)),
            PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
              ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
          ∃ post, ∃ exc : Exec 0 (initSevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T (rlC3Calls (initSevm msg) (initDevm msg) pushD pushN))))
              (initDevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T (rlC3Calls (initSevm msg) (initDevm msg) pushD pushN)))) (.ok post),
            exec (initEvm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T (rlC3Calls (initSevm msg) (initDevm msg) pushD pushN)))) =
              .ok post ∧
            post.gasLeft = R ∧
            RawEffect ⟨0, _, _, .ok post, exc⟩ post (rlEnv (initSevm msg) T) o ∧
            Checkpoint (post.getStor msg.currentTarget) o.state :=
  @Blanc.Composition.Curve3Pool3CrvLiteralWitness.pool_3crv_removeLiquidity_live_exact_literal

example : ∀ {pool c3 : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {ps₀ : Curve3Pool.State} {cs₀ : Blanc.Curve3Crv.State} {K₀ : Curve3Crv.Key → Prop} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state)
    (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace))
    (env : PoolTraceEnv trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress)
    {msg : Msg} (target : msg.currentTarget = pool) (state : msg.benv.state = future.state)
    {T : B256} (hfork : CoveredFork (initSevm msg).benvStat.fork)
    (hstatic : (initSevm msg).isStatic = false) (hdepth : (initSevm msg).depth ≠ 0)
    (hc3 : C3Entry (initSevm msg) (initDevm msg) T)
    (hcoins : T20Coins (initSevm msg) (initDevm msg))
    (hfits : ∀ k : Fin 3, alAmt (initSevm msg) k.val ≠ 0 → T20PullFits
      ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) k)) msg.caller
      msg.currentTarget msg.currentTarget (alAmt (initSevm msg) k.val)),
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 (initDevm msg) ∧
      ∀ {o : Out}, MintFits (Devm.getStor (initDevm msg) c3) pool msg.caller.toB256
        (Nat.toB256 (alMintAmt o)) →
      ∃ (B1 B2 : B256) (V : Nat → Devm → Prop) (U : Nat)
        (pullD : Nat → Devm → List B256 → Mem → Nat) (pullN : Nat → Devm → List B256 → Mem → Devm)
        (balBD balAD : Devm → List B256 → Mem → Nat) (balBN balAN : Devm → List B256 → Mem → Devm),
          (¬ (initSevm msg).benvStat.rules.isPrecomp c3 ∧
          (∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
              (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr) ∧
          70000 ≤ U ∧
          (Devm.getStor (initDevm msg) c3).get Curve3Crv.vySupplySlot = T ∧
          MintFits (Devm.getStor (initDevm msg) c3) pool msg.caller.toB256
              (Nat.toB256 (alMintAmt o)) ∧
          (∀ k, k ≤ 3 → WClosed (initSevm msg) (V k)) ∧ V 0 (initDevm msg) ∧
          (∀ k, C3Blind c3 (V k)) ∧
          (∀ k : Fin 3, alAmt (initSevm msg) k.val = 0 → ∀ b, V k b → V (k + 1) b) ∧
          (∀ k, k < 3 → alAmt (initSevm msg) k ≠ 0 →
              MutableCallProfile (initSevm msg) (C3With c3 (Devm.getStor (initDevm msg) c3) (V k))
                (C3With c3 (Devm.getStor (initDevm msg) c3) (V (k + 1)))
                (coinAt ((initDevm msg).getStor msg.currentTarget) k)
                (transferFromSel ++ msg.caller.toB256.toBytes ++ msg.currentTarget.toB256.toBytes ++
                  (alAmt (initSevm msg) k).toBytes) RawCallOk U 0x760 0x64 0x820 (pullD k) (pullN k)) ∧
          (alAmt (initSevm msg) 2 ≠ 0 →
              StaticWordCallProfile (initSevm msg) (C3With c3 (Devm.getStor (initDevm msg) c3) (V 2))
                (C3With c3 (Devm.getStor (initDevm msg) c3) (V 2))
                (coinAt ((initDevm msg).getStor msg.currentTarget) 2)
                (balanceOfData msg.currentTarget) B1 U 0x53c 0x24 0x5a0 balBD balBN) ∧
          (alAmt (initSevm msg) 2 ≠ 0 →
              StaticWordCallProfile (initSevm msg) (C3With c3 (Devm.getStor (initDevm msg) c3) (V 3))
                (C3With c3 (Devm.getStor (initDevm msg) c3) (V 3))
                (coinAt ((initDevm msg).getStor msg.currentTarget) 2)
                (balanceOfData msg.currentTarget) B2 U 0x87c 0x24 0x8e0 balAD balAN)) ∧
      ∀ (_hcode : (initSevm msg).code = code)
        (_hlen : 4 ≤ (initSevm msg).data.length) (_hcd : (initSevm msg).data.length < 2 ^ 256)
        (_hsel : Sevm.selector (initSevm msg) = selAddLiquidity)
        (_hstep : step s (alEnvW (initSevm msg) T.toNat B1.toNat B2.toNat)
          (decodeCall (initSevm msg)) = some o)
        (_hid : IdReady (initSevm msg) (initDevm msg)),
        ∃ (amp v0 v1 v2 : Nat) (xa xb xc : V3) (f0 f1 f2 s0 s1 s2 x0 x1 x2 : B256),
          aChk s (initSevm msg).benvStat.time.toNat = some amp ∧
          xpChk ⟨(alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2
              0).toNat,
            (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2 1).toNat,
            (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2
              2).toNat⟩ = some xb ∧
          getDChk xb.get amp 1 = some v1 ∧
          (T ≠ 0 →
            xpChk ⟨(balAt ((initDevm msg).getStor msg.currentTarget) 0).toNat,
              (balAt ((initDevm msg).getStor msg.currentTarget) 1).toNat,
              (balAt ((initDevm msg).getStor msg.currentTarget) 2).toNat⟩ = some xa ∧
            getDChk xa.get amp 1 = some v0 ∧
            RliFeeIter (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot))
              (((initDevm msg).getStor msg.currentTarget).get adminFeeSlot) (Nat.toB256 v0)
              (Nat.toB256 v1) (balAt ((initDevm msg).getStor msg.currentTarget) 0)
              (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2 0)
              f0 s0 x0 ∧
            RliFeeIter (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot))
              (((initDevm msg).getStor msg.currentTarget).get adminFeeSlot) (Nat.toB256 v0)
              (Nat.toB256 v1) (balAt ((initDevm msg).getStor msg.currentTarget) 1)
              (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2 1)
              f1 s1 x1 ∧
            RliFeeIter (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot))
              (((initDevm msg).getStor msg.currentTarget).get adminFeeSlot) (Nat.toB256 v0)
              (Nat.toB256 v1) (balAt ((initDevm msg).getStor msg.currentTarget) 2)
              (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2 2)
              f2 s2 x2 ∧
            xpChk ⟨x0.toNat, x1.toNat, x2.toNat⟩ = some xc ∧ getDChk xc.get amp 1 = some v2) ∧
          ∀ R, 100000 + 5 * U ≤ R →
          costAddLiquidity s (alEnvW (initSevm msg) T.toNat B1.toNat B2.toNat) (argV3 (initSevm msg) 0) +
              7 * U ≤
            R + alExactCost (initSevm msg) (initDevm msg) (alC3Calls (initSevm msg) (initDevm msg) pullD pullN balBD balAD balBN balAN) amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0
              s1 s2 x0 x1 x2 →
          R + alExactCost (initSevm msg) (initDevm msg) (alC3Calls (initSevm msg) (initDevm msg) pullD pullN balBD balAD balBN balAN) amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1
              s2 x0 x1 x2 + 6000 < 2 ^ 256 →
          (∀ post (exc : Exec 0 (initSevm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) (alC3Calls (initSevm msg) (initDevm msg) pullD pullN balBD balAD balBN balAN)
                amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2)))
              (initDevm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) (alC3Calls (initSevm msg) (initDevm msg) pullD pullN balBD balAD balBN balAN) amp T B1 B2 xa xb
                xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2))) (.ok post)),
            PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
              ∀ c' ∈ Exec.childFrames exc, c'.post.getCode 4 = c'.pre.getCode 4) →
          ∃ post, ∃ exc : Exec 0 (initSevm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) (alC3Calls (initSevm msg) (initDevm msg) pullD pullN balBD balAD balBN balAN)
                amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2)))
              (initDevm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) (alC3Calls (initSevm msg) (initDevm msg) pullD pullN balBD balAD balBN balAN) amp T B1 B2 xa xb
                xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2))) (.ok post),
            exec (initEvm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) (alC3Calls (initSevm msg) (initDevm msg) pullD pullN balBD balAD balBN balAN) amp T B1 B2 xa
              xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2))) = .ok post ∧
            post.gasLeft = R ∧
            ∃ e : Env, e.supply = some T.toNat ∧ step s e (decodeCall (initSevm msg)) = some o ∧
              RawEffect ⟨0, _, _, .ok post, exc⟩ post e o ∧
              Checkpoint (post.getStor msg.currentTarget) o.state :=
  @Blanc.Composition.Curve3Pool3CrvLiteralWitness.pool_3crv_addLiquidity_live_exact_literal

example : ∀ {pool c3 : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {ps₀ : Curve3Pool.State} {cs₀ : Blanc.Curve3Crv.State} {K₀ : Curve3Crv.Key → Prop} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state)
    (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace))
    (env : PoolTraceEnv trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress)
    {msg : Msg} (target : msg.currentTarget = pool) (state : msg.benv.state = future.state)
    {T : B256} (hfork : CoveredFork (initSevm msg).benvStat.fork)
    (hstatic : (initSevm msg).isStatic = false) (hdepth : (initSevm msg).depth ≠ 0)
    (hc3 : C3Entry (initSevm msg) (initDevm msg) T)
    (hcoins : T20Coins (initSevm msg) (initDevm msg))
    (hfits : ∀ k : Fin 3, rliAmt (initSevm msg) k.val ≠ 0 → T20MoveFits
      ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) k)) msg.currentTarget
      msg.caller (rliAmt (initSevm msg) k.val)),
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 (initDevm msg) ∧
      ∀ {o : Out}, BurnFits (Devm.getStor (initDevm msg) c3) pool msg.caller.toB256
        (Nat.toB256 (rliBurnAmt o)) →
      ∃ (V : Nat → Devm → Prop) (U : Nat) (pushD : Nat → Devm → List B256 → Mem → Nat)
        (pushN : Nat → Devm → List B256 → Mem → Devm),
          (¬ (initSevm msg).benvStat.rules.isPrecomp c3 ∧
          (∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
              (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr) ∧
          70000 ≤ U ∧
          (Devm.getStor (initDevm msg) c3).get Curve3Crv.vySupplySlot = T ∧
          BurnFits (Devm.getStor (initDevm msg) c3) pool msg.caller.toB256
              (Nat.toB256 (rliBurnAmt o)) ∧
          (∀ k, k ≤ 3 → WClosed (initSevm msg) (V k)) ∧ V 0 (initDevm msg) ∧
          (∀ k, C3Blind c3 (V k)) ∧
          (∀ k : Fin 3, rliAmt (initSevm msg) k.val = 0 → ∀ b, V k b → V (k + 1) b) ∧
          (∀ k, k < 3 → rliAmt (initSevm msg) k ≠ 0 →
              MutableCallProfile (initSevm msg)
                (C3With c3 (burnStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256
                  (Nat.toB256 (rliBurnAmt o))) (V k))
                (C3With c3 (burnStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256
                  (Nat.toB256 (rliBurnAmt o))) (V (k + 1)))
                (((initDevm msg).getStor msg.currentTarget).get (coinsBase + Nat.toB256 k))
                (transferSel ++ msg.caller.toB256.toBytes ++ (rliAmt (initSevm msg) k).toBytes)
                RawCallOk U 0xaa0 0x44 0xb40 (pushD k) (pushN k))) ∧
      ∀ (_hcode : (initSevm msg).code = code)
        (_hlen : 4 ≤ (initSevm msg).data.length) (_hcd : (initSevm msg).data.length < 2 ^ 256)
        (_hsel : Sevm.selector (initSevm msg) = selRemoveLiquidityImbalance)
        (_hstep : step s (rliEnvW (initSevm msg) T.toNat) (decodeCall (initSevm msg)) = some o)
        (_hid : IdReady (initSevm msg) (initDevm msg)),
        ∃ w : RliWords, RliWordsPin (initSevm msg) (initDevm msg) s w ∧
          ∀ R, 66000 + 3 * U ≤ R →
            costImbalance s (rliEnvW (initSevm msg) T.toNat) (argV3 (initSevm msg) 0) + 5 * U ≤
              R + rliExactCost (initSevm msg) (initDevm msg) (rliC3Calls (initSevm msg) (initDevm msg) pushD pushN) T w →
            R + rliExactCost (initSevm msg) (initDevm msg) (rliC3Calls (initSevm msg) (initDevm msg) pushD pushN) T w + 3000 < 2 ^ 256 →
            (∀ post (exc : Exec 0
                (initSevm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) (rliC3Calls (initSevm msg) (initDevm msg) pushD pushN) T w)))
                (initDevm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) (rliC3Calls (initSevm msg) (initDevm msg) pushD pushN) T w)))
                (.ok post)),
              PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
                ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
            ∃ post, ∃ exc : Exec 0
                (initSevm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) (rliC3Calls (initSevm msg) (initDevm msg) pushD pushN) T w)))
                (initDevm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) (rliC3Calls (initSevm msg) (initDevm msg) pushD pushN) T w)))
                (.ok post),
              exec (initEvm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) (rliC3Calls (initSevm msg) (initDevm msg) pushD pushN) T w))) =
                .ok post ∧
              post.gasLeft = R ∧
              RawEffect ⟨0, _, _, .ok post, exc⟩ post (rliEnvW (initSevm msg) T.toNat) o ∧
              Checkpoint (post.getStor msg.currentTarget) o.state ∧ C3With c3 (burnStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256
                (Nat.toB256 (rliBurnAmt o))) (V 3) post :=
  @Blanc.Composition.Curve3Pool3CrvLiteralWitness.pool_3crv_removeLiquidityImbalance_live_exact_literal

example : ∀ {pool c3 : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {ps₀ : Curve3Pool.State} {cs₀ : Blanc.Curve3Crv.State} {K₀ : Curve3Crv.Key → Prop} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state)
    (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace))
    (env : PoolTraceEnv trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress)
    {msg : Msg} (target : msg.currentTarget = pool) (state : msg.benv.state = future.state)
    {T : B256} (hfork : CoveredFork (initSevm msg).benvStat.fork)
    (hstatic : (initSevm msg).isStatic = false) (hdepth : (initSevm msg).depth ≠ 0)
    (hc3 : C3Entry (initSevm msg) (initDevm msg) T)
    (hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
      (coinOf (initSevm msg) (initDevm msg) k))
    (hburn : BurnFits (Devm.getStor (initDevm msg) c3) pool msg.caller.toB256
      (ocAmt (initSevm msg))),
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 (initDevm msg) ∧
      ∀ {o : Out} {i : Fin 3} (_hi : i.val = (ocI (initSevm msg)).toNat),
        (initDevm msg).getCode (coinOf (initSevm msg) (initDevm msg) i) =
          Blanc.Lift.Token20.code →
        coinOf (initSevm msg) (initDevm msg) i ≠ msg.currentTarget →
        coinOf (initSevm msg) (initDevm msg) i ≠ c3 →
        T20MoveFits ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) i))
          msg.currentTarget msg.caller (Nat.toB256 (ocPushAmt o)) →
      ∃ (V : Nat → Devm → Prop) (U : Nat) (pushD : Devm → List B256 → Mem → Nat)
        (pushN : Devm → List B256 → Mem → Devm),
          (¬ (initSevm msg).benvStat.rules.isPrecomp c3 ∧
          (∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
              (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr) ∧
          70000 ≤ U ∧
          (Devm.getStor (initDevm msg) c3).get Curve3Crv.vySupplySlot = T ∧
          BurnFits (Devm.getStor (initDevm msg) c3) pool msg.caller.toB256
              (ocAmt (initSevm msg)) ∧
          (∀ k, k ≤ 1 → WClosed (initSevm msg) (V k)) ∧ V 0 (initDevm msg) ∧
          C3Blind c3 (V 0) ∧
          MutableCallProfile (initSevm msg)
              (C3With c3 (burnStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256
                (ocAmt (initSevm msg))) (V 0))
              (C3With c3 (burnStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256
                (ocAmt (initSevm msg))) (V 1))
              (((initDevm msg).getStor msg.currentTarget).get (coinsBase + ocI (initSevm msg)))
              (transferSel ++ msg.caller.toB256.toBytes ++ (Nat.toB256 (ocPushAmt o)).toBytes)
              RawCallOk U 0x540 0x44 0x5e0 pushD pushN) ∧
      ∀ (_hcode : (initSevm msg).code = code)
        (_hlen : 4 ≤ (initSevm msg).data.length) (_hcd : (initSevm msg).data.length < 2 ^ 256)
        (_hsel : Sevm.selector (initSevm msg) = selRemoveLiquidityOneCoin)
        (_hstep : step s (ocEnv (initSevm msg) i T.toNat) (decodeCall (initSevm msg)) = some o)
        (_hid : IdReady (initSevm msg) (initDevm msg)),
        ∃ (amp : Nat) (x0 x1 x2 D0 y r0 r1 r2 y2 : B256) (hi3 : (ocI (initSevm msg)).toNat < 3),
          aChk s (initSevm msg).benvStat.time.toNat = some amp ∧
          xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
          getDChk (V3.mk x0.toNat x1.toNat x2.toNat).get amp 1 = some D0.toNat ∧
          getYDChk amp ⟨(ocI (initSevm msg)).toNat, hi3⟩ (V3.mk x0.toNat x1.toNat x2.toNat).get
            (D0 - ocAmt (initSevm msg) * D0 / T).toNat = some y.toNat ∧
          CwStep (Bytes.toB256 [0] = ocI (initSevm msg)) x0 (D0 - ocAmt (initSevm msg) * D0 / T) D0 y
            (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot)) x0 r0 ∧
          CwStep (Bytes.toB256 [1] = ocI (initSevm msg)) x1 (D0 - ocAmt (initSevm msg) * D0 / T) D0 y
            (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot)) x1 r1 ∧
          CwStep (Bytes.toB256 [2] = ocI (initSevm msg)) x2 (D0 - ocAmt (initSevm msg) * D0 / T) D0 y
            (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot)) x2 r2 ∧
          getYDChk amp ⟨(ocI (initSevm msg)).toNat, hi3⟩ (V3.mk r0.toNat r1.toNat r2.toNat).get
            (D0 - ocAmt (initSevm msg) * D0 / T).toNat = some y2.toNat ∧
          ∀ R, 131000 + 3 * U ≤ R →
          R + ocExactCost (initSevm msg) (initDevm msg) T (ocC3Calls (initSevm msg) (initDevm msg) pushD pushN) amp x0 x1 x2 D0 y r0 r1 r2 y2 + 2000 <
            2 ^ 256 →
          (∀ post (exc : Exec 0 (initSevm (msg.withGas
                (R + ocExactCost (initSevm msg) (initDevm msg) T (ocC3Calls (initSevm msg) (initDevm msg) pushD pushN) amp x0 x1 x2 D0 y r0 r1 r2 y2)))
              (initDevm (msg.withGas
                (R + ocExactCost (initSevm msg) (initDevm msg) T (ocC3Calls (initSevm msg) (initDevm msg) pushD pushN) amp x0 x1 x2 D0 y r0 r1 r2 y2)))
              (.ok post)),
            PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
              ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
          ∃ post, ∃ exc : Exec 0 (initSevm (msg.withGas
                (R + ocExactCost (initSevm msg) (initDevm msg) T (ocC3Calls (initSevm msg) (initDevm msg) pushD pushN) amp x0 x1 x2 D0 y r0 r1 r2 y2)))
              (initDevm (msg.withGas
                (R + ocExactCost (initSevm msg) (initDevm msg) T (ocC3Calls (initSevm msg) (initDevm msg) pushD pushN) amp x0 x1 x2 D0 y r0 r1 r2 y2)))
              (.ok post),
            exec (initEvm (msg.withGas
              (R + ocExactCost (initSevm msg) (initDevm msg) T (ocC3Calls (initSevm msg) (initDevm msg) pushD pushN) amp x0 x1 x2 D0 y r0 r1 r2 y2))) =
              .ok post ∧
            post.gasLeft = R ∧ ∃ T' : Nat,
            RawEffect ⟨0, _, _, .ok post, exc⟩ post (ocEnv (initSevm msg) i T') o ∧
            Checkpoint (post.getStor msg.currentTarget) o.state ∧ C3With c3 (burnStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256
              (ocAmt (initSevm msg))) (V 1) post :=
  @Blanc.Composition.Curve3Pool3CrvLiteralWitness.pool_3crv_removeLiquidityOneCoin_live_exact_literal

example : ∀ {pool c3 : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {ps₀ : Curve3Pool.State} {cs₀ : Blanc.Curve3Crv.State} {K₀ : Curve3Crv.Key → Prop} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state)
    (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace))
    (env : PoolTraceEnv trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress)
    {sevm : Sevm} {pre : Devm} (target : sevm.currentTarget = pool)
    (state : pre.state = future.state)
    {T : B256} (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hc3 : C3Entry sevm pre T)
    (hcoins : T20Coins sevm pre)
    (hburn : BurnFits (Devm.getStor pre c3) pool sevm.caller.toB256 (rlAmt sevm))
    (hfits : ∀ k : Fin 3, T20MoveFits (pre.getStor (coinOf sevm pre k)) sevm.currentTarget
      sevm.caller (balAt (pre.getStor sevm.currentTarget) k * rlAmt sevm / T)),
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 pre ∧
      ∃ (V : Nat → Devm → Prop) (U : Nat),
        (¬ sevm.benvStat.rules.isPrecomp c3 ∧
        (∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
            ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr) ∧
        70000 ≤ U ∧
        (Devm.getStor pre c3).get Curve3Crv.vySupplySlot = T ∧
        BurnFits (Devm.getStor pre c3) pool sevm.caller.toB256 (rlAmt sevm) ∧
        (∀ k, k ≤ 3 → WClosed sevm (V k)) ∧ V 0 pre ∧ (∀ k, C3Blind c3 (V k)) ∧
        (∀ k : Fin 3, CoinPushOkAt sevm (C3With c3 (Devm.getStor pre c3) (V k))
            (C3With c3 (Devm.getStor pre c3) (V (k + 1)))
            ((pre.getStor sevm.currentTarget).get (coinSlot k))
            (balAt (pre.getStor sevm.currentTarget) k * rlAmt sevm / T) U 0x520 0x5c0)) ∧
      ∀ {o : Out} {G : Nat} (_hcode : sevm.code = code)
        (_hlen : 4 ≤ sevm.data.length)
        (_hcd : sevm.data.length < 2 ^ 256)
        (_hsel : Sevm.selector sevm = selRemoveLiquidity)
        (_hstep : step s (rlEnv sevm T) (decodeCall sevm) = some o)
        (_hid : IdReady sevm pre)
        (_hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
          PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
            ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4)
        (_hG : 167000 + 5 * U ≤ G)
        (_hGm : (St pre [] Mem.empty G).gasMeasure < 2 ^ 256),
        ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post),
          RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (rlEnv sevm T) o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state :=
  @Blanc.Composition.Curve3Pool3CrvLiteralWitness.pool_3crv_removeLiquidity_live_entry_literal

example : ∀ {pool c3 : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {ps₀ : Curve3Pool.State} {cs₀ : Blanc.Curve3Crv.State} {K₀ : Curve3Crv.Key → Prop} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state)
    (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace))
    (env : PoolTraceEnv trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress)
    {sevm : Sevm} {pre : Devm} (target : sevm.currentTarget = pool)
    (state : pre.state = future.state)
    {T : B256} (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hc3 : C3Entry sevm pre T)
    (hcoins : T20Coins sevm pre)
    (hfits : ∀ k : Fin 3, alAmt sevm k.val ≠ 0 → T20PullFits (pre.getStor (coinOf sevm pre k))
      sevm.caller sevm.currentTarget sevm.currentTarget (alAmt sevm k.val)),
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 pre ∧
      ∀ {o : Out}, MintFits (Devm.getStor pre c3) pool sevm.caller.toB256
        (Nat.toB256 (alMintAmt o)) →
      ∃ (B1 B2 : B256) (V : Nat → Devm → Prop) (U : Nat),
        (¬ sevm.benvStat.rules.isPrecomp c3 ∧
        (∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
            ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr) ∧
        70000 ≤ U ∧
        (Devm.getStor pre c3).get Curve3Crv.vySupplySlot = T ∧
        MintFits (Devm.getStor pre c3) pool sevm.caller.toB256 (Nat.toB256 (alMintAmt o)) ∧
        (∀ k, k ≤ 3 → WClosed sevm (V k)) ∧ V 0 pre ∧ (∀ k, C3Blind c3 (V k)) ∧
        (∀ k : Fin 3, k ≠ feeIndex → alAmt sevm k.val ≠ 0 →
            CoinPullOkAt sevm (C3With c3 (Devm.getStor pre c3) (V k))
              (C3With c3 (Devm.getStor pre c3) (V (k + 1)))
              ((pre.getStor sevm.currentTarget).get (coinSlot k)) (alAmt sevm k.val) U 0x760 0x820) ∧
        (∀ k : Fin 3, alAmt sevm k.val = 0 → ∀ b, V k b → V (k + 1) b) ∧
        (alAmt sevm 2 ≠ 0 →
            CoinBalOkAt sevm (C3With c3 (Devm.getStor pre c3) (V 2))
              (C3With c3 (Devm.getStor pre c3) (V 2))
              ((pre.getStor sevm.currentTarget).get (coinSlot 2)) B1 U 0x53c 0x5a0 ∧
            CoinPullOkAt sevm (C3With c3 (Devm.getStor pre c3) (V 2))
              (C3With c3 (Devm.getStor pre c3) (V 3))
              ((pre.getStor sevm.currentTarget).get (coinSlot 2)) (alAmt sevm 2) U 0x760 0x820 ∧
            CoinBalOkAt sevm (C3With c3 (Devm.getStor pre c3) (V 3))
              (C3With c3 (Devm.getStor pre c3) (V 3))
              ((pre.getStor sevm.currentTarget).get (coinSlot 2)) B2 U 0x87c 0x8e0)) ∧
      ∀ {G : Nat} (_hcode : sevm.code = code)
        (_hlen : 4 ≤ sevm.data.length)
        (_hcd : sevm.data.length < 2 ^ 256)
        (_hsel : Sevm.selector sevm = selAddLiquidity)
        (_hstep : step s (alEnvW sevm T.toNat B1.toNat B2.toNat) (decodeCall sevm) = some o)
        (_hid : IdReady sevm pre)
        (_hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
          PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
            ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4)
        (_hG : costAddLiquidity s (alEnvW sevm T.toNat B1.toNat B2.toNat) (argV3 sevm 0) + 7 * U ≤
          G)
        (_hGm : (St pre [] Mem.empty G).gasMeasure + 3000 < 2 ^ 256),
        ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post), ∃ e : Env,
          e.supply = some T.toNat ∧ step s e (decodeCall sevm) = some o ∧
          RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post e o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state :=
  @Blanc.Composition.Curve3Pool3CrvLiteralWitness.pool_3crv_addLiquidity_live_entry_literal

example : ∀ {pool c3 : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {ps₀ : Curve3Pool.State} {cs₀ : Blanc.Curve3Crv.State} {K₀ : Curve3Crv.Key → Prop} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state)
    (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace))
    (env : PoolTraceEnv trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress)
    {sevm : Sevm} {pre : Devm} (target : sevm.currentTarget = pool)
    (state : pre.state = future.state)
    {T : B256} (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hc3 : C3Entry sevm pre T)
    (hcoins : T20Coins sevm pre)
    (hfits : ∀ k : Fin 3, rliAmt sevm k.val ≠ 0 → T20MoveFits (pre.getStor (coinOf sevm pre k))
      sevm.currentTarget sevm.caller (rliAmt sevm k.val)),
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 pre ∧
      ∀ {o : Out}, BurnFits (Devm.getStor pre c3) pool sevm.caller.toB256
        (Nat.toB256 (rliBurnAmt o)) →
      ∃ (V : Nat → Devm → Prop) (U : Nat),
        (¬ sevm.benvStat.rules.isPrecomp c3 ∧
        (∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
            ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr) ∧
        70000 ≤ U ∧
        (Devm.getStor pre c3).get Curve3Crv.vySupplySlot = T ∧
        BurnFits (Devm.getStor pre c3) pool sevm.caller.toB256 (Nat.toB256 (rliBurnAmt o)) ∧
        (∀ k, k ≤ 3 → WClosed sevm (V k)) ∧ V 0 pre ∧ (∀ k, C3Blind c3 (V k)) ∧
        (∀ k : Fin 3, rliAmt sevm k.val ≠ 0 →
            CoinPushOkAt sevm
              (C3With c3 (burnStor (Devm.getStor pre c3) sevm.caller.toB256
                (Nat.toB256 (rliBurnAmt o))) (V k))
              (C3With c3 (burnStor (Devm.getStor pre c3) sevm.caller.toB256
                (Nat.toB256 (rliBurnAmt o))) (V (k + 1)))
              ((pre.getStor sevm.currentTarget).get (coinSlot k)) (rliAmt sevm k.val) U 0xaa0 0xb40) ∧
        (∀ k : Fin 3, rliAmt sevm k.val = 0 → ∀ b, V k b → V (k + 1) b)) ∧
      ∀ {G : Nat} (_hcode : sevm.code = code)
        (_hlen : 4 ≤ sevm.data.length)
        (_hcd : sevm.data.length < 2 ^ 256)
        (_hsel : Sevm.selector sevm = selRemoveLiquidityImbalance)
        (_hstep : step s (rliEnvW sevm T.toNat) (decodeCall sevm) = some o)
        (_hid : IdReady sevm pre)
        (_hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
          PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
            ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4)
        (_hG : costImbalance s (rliEnvW sevm T.toNat) (argV3 sevm 0) + 5 * U ≤ G)
        (_hGm : (St pre [] Mem.empty G).gasMeasure + 3000 < 2 ^ 256),
        ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post),
          RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (rliEnvW sevm T.toNat)
            o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state ∧
          C3With c3 (burnStor (Devm.getStor pre c3) sevm.caller.toB256
            (Nat.toB256 (rliBurnAmt o))) (V 3) post :=
  @Blanc.Composition.Curve3Pool3CrvLiteralWitness.pool_3crv_removeLiquidityImbalance_live_entry_literal

example : ∀ {pool c3 : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {ps₀ : Curve3Pool.State} {cs₀ : Blanc.Curve3Crv.State} {K₀ : Curve3Crv.Key → Prop} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state)
    (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace))
    (env : PoolTraceEnv trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress)
    {sevm : Sevm} {pre : Devm} (target : sevm.currentTarget = pool)
    (state : pre.state = future.state)
    {T : B256} (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hc3 : C3Entry sevm pre T)
    (hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp (coinOf sevm pre k))
    (hburn : BurnFits (Devm.getStor pre c3) pool sevm.caller.toB256 (ocAmt sevm)),
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 pre ∧
      ∀ {o : Out} {i : Fin 3} (_hi : i.val = (ocI sevm).toNat),
        pre.getCode (coinOf sevm pre i) = Blanc.Lift.Token20.code →
        coinOf sevm pre i ≠ sevm.currentTarget → coinOf sevm pre i ≠ c3 →
        T20MoveFits (pre.getStor (coinOf sevm pre i)) sevm.currentTarget sevm.caller
          (Nat.toB256 (ocPushAmt o)) →
      ∃ (V : Nat → Devm → Prop) (U : Nat),
        (¬ sevm.benvStat.rules.isPrecomp c3 ∧
        (∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
            ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr) ∧
        70000 ≤ U ∧
        (Devm.getStor pre c3).get Curve3Crv.vySupplySlot = T ∧
        BurnFits (Devm.getStor pre c3) pool sevm.caller.toB256 (ocAmt sevm) ∧
        (∀ k, k ≤ 1 → WClosed sevm (V k)) ∧ V 0 pre ∧ C3Blind c3 (V 0) ∧
        CoinPushOkAt sevm
            (C3With c3 (burnStor (Devm.getStor pre c3) sevm.caller.toB256 (ocAmt sevm)) (V 0))
            (C3With c3 (burnStor (Devm.getStor pre c3) sevm.caller.toB256 (ocAmt sevm)) (V 1))
            ((pre.getStor sevm.currentTarget).get (coinSlot i)) (Nat.toB256 (ocPushAmt o)) U
            0x540 0x5e0) ∧
      ∀ {G : Nat} (_hcode : sevm.code = code)
        (_hlen : 4 ≤ sevm.data.length)
        (_hcd : sevm.data.length < 2 ^ 256)
        (_hsel : Sevm.selector sevm = selRemoveLiquidityOneCoin)
        (_hstep : step s (ocEnv sevm i T.toNat) (decodeCall sevm) = some o)
        (_hid : IdReady sevm pre)
        (_hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
          PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
            ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4)
        (_hG : costOneCoin s (ocEnv sevm i T.toNat) (ocAmt sevm).toNat i + 3 * U ≤ G)
        (_hGm : (St pre [] Mem.empty G).gasMeasure + 2000 < 2 ^ 256),
        ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post), ∃ T' : Nat,
          RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (ocEnv sevm i T') o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state ∧
          C3With c3 (burnStor (Devm.getStor pre c3) sevm.caller.toB256 (ocAmt sevm)) (V 1)
            post :=
  @Blanc.Composition.Curve3Pool3CrvLiteralWitness.pool_3crv_removeLiquidityOneCoin_live_entry_literal

end Blanc.Composition.Curve3Pool3CrvLiteralWitness


namespace Blanc.Lift
open Jaune

example (msg : Msg) (G : Nat) : msg.withGas G = {msg with gas := G} := by
  unfold Jaune.Msg.withGas
  rfl

end Blanc.Lift

namespace Blanc.Lift.Curve3Pool
open Jaune Blanc.Lift Blanc.StableSwapNewton

example (sevm : Sevm) (pre : Devm) (s : State) (w : RliWords) : RliWordsPin sevm pre s w = (
  aChk s sevm.benvStat.time.toNat = some w.amp ∧
    xpChk ⟨(balAt (rliσ sevm pre) 0).toNat, (balAt (rliσ sevm pre) 1).toNat,
      (balAt (rliσ sevm pre) 2).toNat⟩ = some w.xa ∧
    getDChk w.xa.get w.amp 1 = some w.v0 ∧
    xpChk ⟨(rliNew sevm pre 0).toNat, (rliNew sevm pre 1).toNat,
      (rliNew sevm pre 2).toNat⟩ = some w.xb ∧
    getDChk w.xb.get w.amp 1 = some w.v1 ∧
    RliFeeIter (cwFee ((rliσ sevm pre).get feeSlot)) ((rliσ sevm pre).get adminFeeSlot)
      (Nat.toB256 w.v0) (Nat.toB256 w.v1) (balAt (rliσ sevm pre) 0) (rliNew sevm pre 0) w.f0 w.s0
      w.x0 ∧
    RliFeeIter (cwFee ((rliσ sevm pre).get feeSlot)) ((rliσ sevm pre).get adminFeeSlot)
      (Nat.toB256 w.v0) (Nat.toB256 w.v1) (balAt (rliσ sevm pre) 1) (rliNew sevm pre 1) w.f1 w.s1
      w.x1 ∧
    RliFeeIter (cwFee ((rliσ sevm pre).get feeSlot)) ((rliσ sevm pre).get adminFeeSlot)
      (Nat.toB256 w.v0) (Nat.toB256 w.v1) (balAt (rliσ sevm pre) 2) (rliNew sevm pre 2) w.f2 w.s2
      w.x2 ∧
    xpChk ⟨w.x0.toNat, w.x1.toNat, w.x2.toNat⟩ = some w.xc ∧
    getDChk w.xc.get w.amp 1 = some w.v2
    ) := by
  unfold RliWordsPin
  rfl

end Blanc.Lift.Curve3Pool

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

namespace Blanc.Lift.Curve3Crv
open Jaune Blanc.ExecutionTrace Blanc.Lift.Curve3Crv.Creation

-- Curve 3Crv definition: Key.holder (bal)
example (a : Adr) : Key.holder (.bal a) = some a :=
  rfl

-- Curve 3Crv definition: Key.holder (allow)
example (o p : Adr) : Key.holder (.allow o p) = none :=
  rfl

-- Curve 3Crv definition: SupplyConserved
example (stor : Stor) (holders : Finset Adr) :
    SupplyConserved stor holders ↔
      ((stor.get vySupplySlot).toNat = ledgerSumOn holders fun a => stor.get (vyBalSlot a)) :=
  Iff.rfl

-- Curve 3Crv definition: C3crvDeploymentTo.touched
example {checkpoint : BlockChain} (d : C3crvDeploymentTo checkpoint) :
    d.touched = midTouchedKeysIn tokenAddress d.trace :=
  rfl

-- Curve 3Crv definition: C3crvDeploymentTo.holders
example {checkpoint : BlockChain} (d : C3crvDeploymentTo checkpoint) :
    d.holders = (d.touched.filterMap Key.holder).toFinset :=
  rfl

-- Curve 3Crv definition: C3crvDeploymentTo.invocations
example {checkpoint : BlockChain} (d : C3crvDeploymentTo checkpoint) :
    d.invocations = midCommittedInvocationsIn tokenAddress d.trace :=
  rfl

-- Curve 3Crv definition: WriterInvocation.preWord
example (inv : WriterInvocation) (x : B256) :
    inv.preWord x = (Devm.getStor inv.pre tokenAddress).get x :=
  rfl

-- Curve 3Crv definition: WriterInvocation.postWord
example (inv : WriterInvocation) (x : B256) :
    inv.postWord x = (Devm.getStor inv.post tokenAddress).get x :=
  rfl

-- Curve 3Crv definition: OnlyMinterMovesSupply
example (inv : WriterInvocation) :
    OnlyMinterMovesSupply inv ↔
      (inv.postWord vySupplySlot ≠ inv.preWord vySupplySlot →
        inv.sevm.caller.toB256 = inv.preWord vyMinterSlot ∧
          ∃ a v, decodeCall inv.sevm = .mint a v ∨ decodeCall inv.sevm = .burnFrom a v) :=
  Iff.rfl

-- Curve 3Crv definition: OnlyMinterMovesMinter
example (inv : WriterInvocation) :
    OnlyMinterMovesMinter inv ↔
      (inv.postWord vyMinterSlot ≠ inv.preWord vyMinterSlot →
        inv.sevm.caller.toB256 = inv.preWord vyMinterSlot) :=
  Iff.rfl

-- Curve 3Crv definition: TransferFromSpendsAllowance
example (inv : WriterInvocation) :
    TransferFromSpendsAllowance inv ↔
      (∀ f dst v, decodeCall inv.sevm = .transferFrom f dst v →
        inv.sevm.caller.toB256 ≠ inv.preWord vyMinterSlot →
          v ≤ inv.preWord (vyAllowSlot f.toAdr inv.sevm.caller) ∧
            inv.postWord (vyAllowSlot f.toAdr inv.sevm.caller) =
              inv.preWord (vyAllowSlot f.toAdr inv.sevm.caller) - v) :=
  Iff.rfl

-- Curve 3Crv definition: AllowanceMovesAuthorized
example (tracked : List Key) (inv : WriterInvocation) :
    AllowanceMovesAuthorized tracked inv ↔
      (∀ o p, Key.allow o p ∈ tracked →
        inv.postWord (vyAllowSlot o p) ≠ inv.preWord (vyAllowSlot o p) →
          (inv.sevm.caller = o ∧ ∃ w v, decodeCall inv.sevm = .approve w v ∧ w.toAdr = p) ∨
            (inv.sevm.caller = p ∧ inv.sevm.caller.toB256 ≠ inv.preWord vyMinterSlot ∧
              ∃ f dst v, decodeCall inv.sevm = .transferFrom f dst v ∧ f.toAdr = o)) :=
  Iff.rfl

-- Curve 3Crv definition: C3crvFramePolicy
example (tracked : List Key) (inv : WriterInvocation) :
    C3crvFramePolicy tracked inv ↔
      (OnlyMinterMovesSupply inv ∧ OnlyMinterMovesMinter inv ∧ TransferFromSpendsAllowance inv ∧
        AllowanceMovesAuthorized tracked inv) :=
  Iff.rfl

-- Curve 3Crv: c3crv_conserved
example {checkpoint : BlockChain} (d : C3crvDeploymentTo checkpoint) :
    SupplyConserved (checkpoint.state.getStor tokenAddress) d.holders :=
  c3crv_conserved d

-- Curve 3Crv: c3crv_policy
example {checkpoint : BlockChain} (d : C3crvDeploymentTo checkpoint) :
    ∀ inv ∈ d.invocations, C3crvFramePolicy d.touched inv :=
  c3crv_policy d

end Blanc.Lift.Curve3Crv



namespace Blanc.Lift.LidoCircuitBreakerDeployed
open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open scoped BigOperators

-- Lido CircuitBreaker definition: LidoDeploymentTo.HashApart

-- Lido CircuitBreaker: lido_registry_consistent

-- Lido CircuitBreaker: lido_remove_repairs

-- Lido CircuitBreaker constructor: LidoDeploymentTo.mk

-- Lido CircuitBreaker constructor: Creation.DeploymentCut.mk

-- Lido CircuitBreaker: lido_deployment_finite_init

-- Lido CircuitBreaker: Live.lido_live_registryOn

-- Lido CircuitBreaker definition: canonicalAddress

-- Lido CircuitBreaker definition: solRegistryStorage

-- Lido CircuitBreaker definition: solKey

-- Lido CircuitBreaker statement: Blanc.SlotFootprint.checkApartOn_eq_true
example {κ : Type} {slot : κ → B256} {observed : List κ} {foreign : List B256} :
    Blanc.SlotFootprint.checkApartOn slot observed foreign = true ↔
      ∀ w ∈ foreign, ∀ k ∈ observed, slot k ≠ w :=
  Blanc.SlotFootprint.checkApartOn_eq_true

end Blanc.Lift.LidoCircuitBreakerDeployed

namespace Blanc.Lift
open Jaune

-- Root messages definition: settledState (ok)
example (d : Devm) :
    settledState (.ok d) =
      (match d.error with
      | none => some d.state
      | some _ => none) :=
  rfl

-- Root messages definition: settledState (error)
example (e : EvmError × State × AdrSet × Tra) : settledState (.error e) = none :=
  rfl

-- Root messages definition: RootMsg.result (create)
example (m : Fork → State → Msg) (fork : Fork) (W : State) :
    (RootMsg.create m).result fork W = processCreateMessage (m fork W) :=
  rfl

-- Root messages definition: RootMsg.result (call)
example (m : Fork → State → Msg) (fork : Fork) (W : State) :
    (RootMsg.call m).result fork W = processMessage (m fork W) :=
  rfl

-- Root messages definition: runMessages (nil)
example (fork : Fork) (W : State) : runMessages fork W [] = some W :=
  rfl

-- Root messages definition: runMessages (cons)
example (fork : Fork) (W : State) (m : RootMsg) (ms : List RootMsg) :
    runMessages fork W (m :: ms) =
      (settledState (m.result fork W)).bind fun W' => runMessages fork W' ms :=
  rfl

end Blanc.Lift

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach (initialWorld)
open Jaune Blanc.Lift Blanc.Lift.Witness

-- Vyper V− definition: supply
example (W : State) : supply W = storOf W proxyAddr 26 :=
  rfl

-- Vyper V− definition: lpBalance
example (W : State) (h : Adr) : lpBalance W h = storOf W proxyAddr (lpSlot h) :=
  rfl

-- Vyper V− definition: vminusSetup
example :
    vminusSetup =
      [.create implCreateMsg, .create cloneCreateMsg, .call initMsg, .create tokenCreateMsg,
        .create attackerCreateMsg, .call approveMsg, .call addMsg] :=
  rfl

-- Vyper V− definition: LedgerSound
example (W : State) :
    LedgerSound W ↔ (supply W = 2000 ∧ lpBalance W attackerAddr = 2000) :=
  Iff.rfl

-- Vyper V− definition: LedgerBroken
example (W : State) :
    LedgerBroken W ↔ (supply W = 1800 ∧ lpBalance W attackerAddr = 1906) :=
  Iff.rfl

-- Vyper V−: vminus_attack
example (fork : Fork) (hfork : CoveredFork fork) :
    ∃ W₀ W, runMessages fork initialWorld vminusSetup = some W₀ ∧ LedgerSound W₀ ∧
      runMessages fork W₀ [.call violMsg] = some W ∧ LedgerBroken W :=
  vminus_attack fork hfork

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit
open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.LockExclusion
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Fund
open Jaune.Exec.Deriv (ParentPrefix)
open Blanc.Lift.VyperNonreentrantDeployed.Fixed (ActiveRel lockBodies lockL)

-- Vyper V+ definition: supply
example (W : State) : supply W = storOf W proxyAddr 0x16 :=
  rfl

-- Vyper V+ definition: lpBalance
example (W : State) (h : Adr) : lpBalance W h = storOf W proxyAddr (lpSlot h) :=
  rfl

-- Vyper V+ definition: vplusSetup
example :
    vplusSetup =
      [.create implCreateMsg, .create cloneCreateMsg, .call initMsg, .call oracleMsg,
        .create tokenCreateMsg, .create receiverCreateMsg, .call approveMsg, .call addMsg] :=
  rfl

-- Vyper V+ definition: LedgerSound
example (W : State) (n : B256) :
    LedgerSound W n ↔
      (supply W = n ∧ (supply W).toNat = Blanc.ledgerSumOn {creator} (lpBalance W)) :=
  Iff.rfl

-- Vyper V+ definition: ReentryRefused
example (fork : Fork) (W₀ W : State) :
    ReentryRefused fork W₀ W ↔
      (∃ (e : Evm) (out : Execution) (R : Exec 0 e.sta e.dyna out) (F h c q G : Exec.Deriv),
        (Frame.ofCall (removeMsg fork W₀)).enter = .run e ∧ (∃ d, out = .ok d ∧ d.state = W) ∧
        F ∈ Exec.rawFrameRoots R ∧ ActiveRel proxyAddr F h ∧ Spawns h c ∧
        c.sevm.currentTarget = receiverAddr ∧
        q ∈ Exec.rawFrameRoots c.exc ∧ G ∈ Exec.rawFrameRoots q.exc ∧ CPFrame proxyAddr code G ∧
        G.sevm.data = reentryData ∧ (∃ d, G.exn = .error (.revert, d)) ∧
        ¬ lockL.Enters proxyAddr G) :=
  Iff.rfl

-- Vyper V+: vplus_exit
example (fork : Fork) (hfork : CoveredFork fork) :
    ∃ W₀ W, runMessages fork initialWorld vplusSetup = some W₀ ∧ LedgerSound W₀ 2000 ∧
      runMessages fork W₀ [.call removeMsg] = some W ∧ LedgerSound W 1800 ∧
      (W.get receiverAddr).bal = 100 ∧ ReentryRefused fork W₀ W :=
  vplus_exit fork hfork

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit











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
