import Blanc.JointGloasInvariants
import Blanc.Composition.BuilderRequestCarrier
import Blanc.Composition.BuilderRequestPublicGuarantees
import JauneConsensus.Facts.Gloas.FinalizedNotAhead

/-!
# A valid Gloas joint chain for EIP-8282: `ValidJointG`

The frozen definition (Plans `recon/statements.md` §0.6, rev 3.1), with the master decisions of 2026-11-10: a
checkpoint whose system address has no code (`noSystemCode`, the one premise the builder contracts' `Clean` reads;
the 7002 deployment cut forced a Cancun-only checkpoint, final conformance review BLOCKER 1), a kept history from it
to the anchor's built-upon chain, a Gloas joint run from the anchor
(`GJointRun`), the anchor data, the 8282 execution premises over the whole kept history (decision
eip8282-validjointg-8282-premises-20261110), the configuration bounds of design.md §5.1 (with `exitDelayPos`
restored, decision eip8282-g3a-exitdelaypos-and-aux-invariants-20261110), the two registry bounds of G3-12 as
separate named fields over every joint state of the run (N7), and B2's value-clause premises. Every premise is a
field; nothing is hidden.

* `GAnchorInv`: at a Gloas anchor, G3a's state invariants (G3-01, 03, 04, 05, 06, 07, 08; G3-02 is a relation
  between states, with no anchor form), the auxiliaries `LatestBidBuilderActive` and `FutureEmpty`, and G3d's
  `FinalizedNotAhead` (master decision eip8282-finalized-not-ahead-invariant-20261110); at a pre-Gloas anchor
  (no builders, nothing pending) `FinalizedNotAheadF` only.
* `AnchorPendingTrace`: a delivered anchor payload passed the envelope check over the anchor's built-upon chain
  (`verifyEnvelopeG … = .ok (req, post)`), hence is the engine's verdict and an Amsterdam kept step.
* `AnchorBidWitness` (G3-14, option (b)): for every non-empty pending payment, every pending builder withdrawal,
  and a non-self-build latest bid, a signed bid verified under real BLS that it records, the assignment injective
  except the latest bid's own live payment entry.
* `anchorJoint`: the joint-level invariants G3-09..11 (`GJointInv`) at the anchor.

Derived: the joint history `ValidJointG.keptHistory` (the prefix spliced with the run's built-upon blocks), the
builder contracts' `Clean` (`depositClean`, `exitClean`, as R13's `ValidJoint.depositClean`/`exitClean`), and the
joint invariants at every state of the run (`ValidJointG.gJointInv_states`): G3-09 after a pre-Gloas step from the
step itself, and at the crossing from its pre-state through the fork state (`CrossingData.fuluHead`).
-/

namespace Blanc.Lift.BuilderRequest

open Jaune JauneConsensus ExecutionTrace ChainLink Blanc Blanc.Lift.WithdrawalRequest JauneConsensus.Facts.Gloas
open Blanc.Composition.BuilderRequestPublic (CodesKept depositAddr exitAddr)

variable {P : Preset}

/-! ## The anchor data -/

/-- **The anchor invariant** (G3a, at a Gloas anchor). -/
def GAnchorInv : GJointState P → Prop
  | .pre s => Inv.FinalizedNotAheadF s.beacon
  | .gloas b _ _ =>
    Inv.BuilderPubkeysUnique b ∧ Inv.PendingRefsInRange b ∧ Inv.ExitedHaveNoPending b ∧
      Inv.PendingCovered b ∧ Inv.NextBuilderIndexInRange b ∧ Inv.NoLiveWeightOnLatestBid b ∧
      Inv.LatestBidCoherence b ∧ Inv.LatestBidBuilderActive b ∧ Inv.FutureEmpty b ∧
      Inv.FinalizedNotAhead b

/-- **The anchor's pending payload** (design R5): a delivered payload passed the envelope check over the anchor's
built-upon chain. -/
def AnchorPendingTrace (cfg : ChainConfig) (ccfg : Config) (bls : Bool) : GJointState P → Prop
  | .gloas b exec (.delivered e req post) => verifyEnvelopeG cfg ccfg bls b exec e = .ok (req, post)
  | _ => True

/-- A delivered anchor payload is the engine's verdict on the anchor's chain. -/
theorem AnchorPendingTrace.coherent {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {s : GJointState P}
    (h : AnchorPendingTrace cfg ccfg bls s) : ParentCoherent cfg s := by
  rcases s with _ | ⟨b, exec, _ | _ | ⟨e, req, post⟩⟩
  all_goals first | trivial | exact (verifyEnvelopeG_ok_iff.mp h).2.2.2

/-- A signed bid verified under Jaune's real BLS at the state `s`: the builder's pubkey, the builder domain at the
bid's epoch (G3-14 (1)). -/
def BidSigned (s : Gloas.BeaconState P) (β : Gloas.SignedExecutionPayloadBid) : Prop :=
  ∃ pk e dom, Gloas.builderPubkey s β.message.builder_index = .ok pk ∧
    computeEpochAtSlot P β.message.slot = .ok e ∧
    Gloas.getDomain s Gloas.DOMAIN_BEACON_BUILDER (some e) = .ok dom ∧
    blsVerify true pk (computeSigningRoot β.message dom) β.signature = true

/-- Where a witness bid sits: a pending payment, a pending builder withdrawal, or the latest bid. -/
inductive WitnessRef where
  | payment (k : Nat)
  | withdrawal (k : Nat)
  | latest
  deriving DecidableEq

/-- **G3-14 witnesses at a Gloas state** (option (b), data). -/
structure GloasBidWitness (s : Gloas.BeaconState P) : Type where
  /-- The witness bid of each reference, if any. -/
  bid : WitnessRef → Option Gloas.SignedExecutionPayloadBid
  /-- Every non-empty pending payment records a signed bid. -/
  payment : ∀ k p, s.builder_pending_payments.toArray[k]? = some p → p ≠ Gloas.BuilderPendingPayment.empty →
    ∃ β, bid (.payment k) = some β ∧ BidSigned s β ∧ p.withdrawal = Inv.bidWithdrawal β.message
  /-- Every pending builder withdrawal records a signed bid. -/
  withdrawal : ∀ k w, s.builder_pending_withdrawals.toArray[k]? = some w →
    ∃ β, bid (.withdrawal k) = some β ∧ BidSigned s β ∧ w = Inv.bidWithdrawal β.message
  /-- A non-self-build latest bid is a signed bid. -/
  latest : s.latest_execution_payload_bid.builder_index ≠ Gloas.BUILDER_INDEX_SELF_BUILD →
    ∃ β, bid .latest = some β ∧ BidSigned s β ∧ β.message = s.latest_execution_payload_bid
  /-- The witnesses are pairwise distinct, except the latest bid's own live payment entry, whose witness is the
  latest bid's. -/
  injective : ∀ r r' β, bid r = some β → bid r' = some β →
    r = r' ∨ (r = .latest ∧ ∃ k, r' = .payment k ∧ Inv.bidIndex s = some k) ∨
      (r' = .latest ∧ ∃ k, r = .payment k ∧ Inv.bidIndex s = some k)

/-- **The anchor's bid witnesses** (G3-14): none needed at a pre-Gloas anchor. -/
def AnchorBidWitness : GJointState P → Type
  | .pre _ => PUnit
  | .gloas b _ _ => GloasBidWitness b

/-! ## Registry sizes -/

/-- The validator count of a joint state. -/
def _root_.JauneConsensus.GJointState.validatorCount : GJointState P → Nat
  | .pre s => s.beacon.validators.toArray.size
  | .gloas b _ _ => b.validators.toArray.size

/-- The builder count of a joint state (none before Gloas). -/
def _root_.JauneConsensus.GJointState.builderCount : GJointState P → Nat
  | .pre _ => 0
  | .gloas b _ _ => b.builders.toArray.size

/-! ## The valid Gloas joint chain -/

/-- **A valid Gloas joint chain** from a checkpoint holding the builder contracts and no code at the system
address, through `anchor`, to `final`. `bls` is a parameter (B1 and B5(ii) add `bls = true`). -/
structure ValidJointG (cfg : ChainConfig) (ccfg : Config) (bls : Bool) (checkpoint : BlockChain)
    (anchor final : GJointState P) : Type where
  /-- The system address has no code at the checkpoint (the builder contracts' `Clean` reads it). -/
  noSystemCode : checkpoint.state.getCode systemAddress = ByteArray.empty
  /-- The kept history from the checkpoint to the anchor's built-upon chain. -/
  preBlocks : List KeptBlock
  prefixHistory : KeptHistory cfg checkpoint preBlocks anchor.exec
  /-- The Gloas joint run from the anchor. -/
  run : GJointRun cfg ccfg bls anchor final
  /-- The anchor data. -/
  anchorPending : AnchorPendingTrace cfg ccfg bls anchor
  anchorInv : GAnchorInv anchor
  anchorWitness : AnchorBidWitness anchor
  /-- The joint-level invariants G3-09..11 at the anchor. No B row reads it directly: it starts G3-09, which every
  step carries (`GJointRun.gJointInv_all`) and which the crossing's Fulu head relation reads at its pre-state. -/
  anchorJoint : GJointInv cfg anchor
  /-- The builder contracts' code and storage at the checkpoint. -/
  depositInstalled : checkpoint.state.getCode Deposit.Creation.address = Deposit.code
  depositFresh : checkpoint.state.getStor Deposit.Creation.address = Stor.empty
  exitInstalled : checkpoint.state.getCode Exit.Creation.address = Exit.code
  exitFresh : checkpoint.state.getStor Exit.Creation.address = Exit.deployedStorage
  /-- No system-address sender, authority or creation over the kept roots of the whole history. -/
  senders : History.NoSender systemAddress (preBlocks ++ run.blocks)
  authorities : History.NoAuthority systemAddress (preBlocks ++ run.blocks)
  creates : History.NoCreate systemAddress (preBlocks ++ run.blocks)
  /-- The deposit-value and exit-count bounds. -/
  depositBudget : History.paid Deposit.Creation.address (preBlocks ++ run.blocks) ≤ 2 ^ 256
  exitFew : (History.submitted Exit.contract (preBlocks ++ run.blocks)).length ≤ 2 ^ 64
  /-- The configuration bounds (design.md §5.1). -/
  quorumPositive : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT
  inclusionDelay : 1 ≤ P.MIN_ATTESTATION_INCLUSION_DELAY
  exitDelayPos : 0 < ccfg.MIN_BUILDER_WITHDRAWABILITY_DELAY
  exitDelayBelow : ccfg.MIN_BUILDER_WITHDRAWABILITY_DELAY < 2 ^ 63
  slotsPerEpoch : 2 ≤ P.SLOTS_PER_EPOCH
  /-- G3-12, the validator registry bound over every joint state of the run (N7). -/
  validatorsBound : ∀ st ∈ run.states, st.validatorCount ≤ 2 ^ 40
  /-- G3-12, the builder registry bound over every joint state of the run (N7). -/
  buildersBound : ∀ st ∈ run.states, st.builderCount ≤ 2 ^ 40
  /-- B2's value clause (`value_kept`). -/
  roots : HistoryRootsFit (preBlocks ++ run.blocks)
  depositNoSender : History.NoSender depositAddr (preBlocks ++ run.blocks)
  exitNoSender : History.NoSender exitAddr (preBlocks ++ run.blocks)
  creditsFit : HistoryCreditsFit depositAddr (preBlocks ++ run.blocks) ∧
    HistoryCreditsFit exitAddr (preBlocks ++ run.blocks)
  codes : CodesKept cfg checkpoint (preBlocks ++ run.blocks) final.exec

namespace ValidJointG

variable {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {checkpoint : BlockChain} {anchor final : GJointState P}

/-- The joint history's execution side: the prefix, then the run's built-upon payloads. -/
noncomputable abbrev blocks (v : ValidJointG cfg ccfg bls checkpoint anchor final) : List KeptBlock :=
  v.preBlocks ++ v.run.blocks

/-- **The joint history is one kept history** from the checkpoint to the final built-upon chain. -/
theorem keptHistory (v : ValidJointG cfg ccfg bls checkpoint anchor final) :
    KeptHistory cfg checkpoint v.blocks final.exec :=
  v.prefixHistory.append v.run.keptHistory

/-- **The deposit contract's `Clean`** on the joint history; the system address's empty code at the checkpoint. -/
theorem depositClean (v : ValidJointG cfg ccfg bls checkpoint anchor final) :
    Deposit.Indexed.Clean cfg checkpoint v.blocks final.exec :=
  ⟨v.keptHistory, v.depositInstalled, v.depositFresh, v.noSystemCode,
    v.senders, v.authorities, v.creates, v.depositBudget⟩

/-- **The exit contract's `Clean`** on the joint history. -/
theorem exitClean (v : ValidJointG cfg ccfg bls checkpoint anchor final) :
    Exit.Indexed.Clean cfg checkpoint v.blocks final.exec :=
  ⟨v.keptHistory, v.exitInstalled, v.exitFresh, v.noSystemCode,
    v.senders, v.authorities, v.creates, v.exitFew⟩

/-- Every state of the run is coherent: the anchor by its pending trace, every step's post-state outright. -/
theorem coherent (v : ValidJointG cfg ccfg bls checkpoint anchor final) : ParentCoherent cfg final :=
  v.run.coherent v.anchorPending.coherent

end ValidJointG

/-! ## The joint invariants along a run -/

/-- A joint state is a Gloas state. -/
def _root_.JauneConsensus.GJointState.IsGloas : GJointState P → Prop
  | .pre _ => False
  | .gloas .. => True

/-- **G3-09..11 at every state of a run**, from the anchor's: every step carries them
(`GJointRunStep.gJointInv_post`: a pre-Gloas step establishes G3-09 itself, the crossing reads its Fulu head
relation from its pre-state, a Gloas step carries them). -/
theorem GJointRun.gJointInv_all {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {s₀ : GJointState P}
    (h₀ : GJointInv cfg s₀) :
    {s : GJointState P} → (run : GJointRun cfg ccfg bls s₀ s) → ∀ st ∈ run.states, GJointInv cfg st
  | _, .nil, st, hst => by
    simp only [GJointRun.states, GJointRun.steps, List.map_nil, List.mem_singleton] at hst
    exact hst ▸ h₀
  | _, .snoc run D hD, st, hst => by
    have ih := GJointRun.gJointInv_all h₀ run
    simp only [GJointRun.states, GJointRun.steps_snoc, List.map_append, List.map_cons, List.map_nil,
      List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hst
    rcases hst with rfl | hst | rfl
    · exact h₀
    · exact ih st (List.mem_cons_of_mem _ hst)
    · exact D.gJointInv_post (ih _ (hD ▸ run.end_mem_states))

/-- **G3-09..11 at every Gloas state of a run**, from the anchor's. -/
theorem GJointRun.gJointInv {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {s₀ : GJointState P}
    (h₀ : GJointInv cfg s₀) {s : GJointState P} (run : GJointRun cfg ccfg bls s₀ s) :
    ∀ st ∈ run.states, st.IsGloas → GJointInv cfg st :=
  fun st hst _ => GJointRun.gJointInv_all h₀ run st hst

/-- **G3-09..11 at every Gloas state of a valid joint chain.** -/
theorem ValidJointG.gJointInv_states {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {checkpoint : BlockChain}
    {anchor final : GJointState P} (v : ValidJointG cfg ccfg bls checkpoint anchor final) :
    ∀ st ∈ v.run.states, st.IsGloas → GJointInv cfg st :=
  GJointRun.gJointInv v.anchorJoint v.run

end Blanc.Lift.BuilderRequest
