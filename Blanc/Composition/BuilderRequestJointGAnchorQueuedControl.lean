import Blanc.Composition.BuilderRequestJointGAnchorQueued
import JauneConsensus.Facts.Gloas.B5Witnesses

/-!
# Negative control: an anchor whose latest bid is already queued

Goal `eip8282-charge-once-v1`, outcome C5. `ValidJointG.anchor_witness_charged_once_queued` rests on one part of
`GloasBidWitness.injective`: the witness of a pending withdrawal witnesses nothing else (`QueuedSeparate`). This
module shows that part bites.

`queuedAnchor pk` is a minimal-preset Gloas state at slot 24 whose latest block is at slot 8 (two epochs back, so
its payment entry has left the window), whose latest bid `L` pays 5 gwei from builder 0 (pubkey `pk`), and whose
`builder_pending_withdrawals` already holds `L`'s withdrawal: the state after a quorum append of `L`. The
assignment `queuedBid β` gives the one signed bid `β` to both the latest bid and that queued entry.

* `queuedAnchor_inv`: the state satisfies `GAnchorInv`, all ten invariants.
* `queuedAnchor_witness`: for a signed bid `β` of `L` verified at the state, `queuedBid β` meets the `payment`,
  `withdrawal` and `latest` fields of `GloasBidWitness`, and is injective on every pair of references except
  `.latest` with `.withdrawal 0`. It is not `QueuedSeparate`, so it is no `GloasBidWitness`.
* `queuedAnchor_double`: `apply_parent_execution_payload` at the state (the old-parent branch) returns
  `builder_pending_withdrawals = [L's withdrawal, L's withdrawal]`: one bid, in the list twice.
* `queuedAnchor_step_doubles`: on any Gloas step from the state that settles its parent FULL with the parent out of
  the window, the list after `process_parent_execution_payload` holds `L`'s withdrawal at position 0 and at the end
  of the post-slots queue; under `queuedBid β` both are `β`'s.

What this does and does not instantiate. Instantiated: `GAnchorInv`, the three witness fields, injectivity away
from the one pair, and the double append through the real `apply_parent_execution_payload`. The witness part is
stated for an arbitrary builder key `pk` and signed bid `β` under the hypothesis that `β` verifies
(`BidSigned`, real BLS): a closed key pair would need a real signature, which no closed witness here carries. Not
instantiated: a `ValidJointG`, a `GJointRun` or a full block from the state (`queuedAnchor_step_doubles` is
conditional on a step), the anchor's joint invariants `GJointInv`, and a delivered anchor payload with its engine
verdict. The state is not claimed reachable.
-/

namespace Blanc.Lift.BuilderRequest.AnchorQueuedControl

open Jaune JauneConsensus ExecutionTrace Blanc JauneConsensus.Facts JauneConsensus.Facts.Gloas
  JauneConsensus.Facts.Gloas.Inv

/-- The latest bid `L`: builder 0's bid of 5 gwei (Jaune's `B5Witnesses.parentBid`) at slot 8. -/
def L : Gloas.ExecutionPayloadBid := { B5Witnesses.parentBid with slot := U64.lit 8 }

/-- `L`'s withdrawal. -/
abbrev wL : Gloas.BuilderPendingWithdrawal := bidWithdrawal L

/-- Builder 0: active, balance 100 gwei, pubkey `pk`. -/
def queuedBuilder (pk : BLSPubkey) : Gloas.Builder :=
  { pubkey := pk, version := Gloas.PAYLOAD_BUILDER_VERSION, execution_address := L.fee_recipient,
    balance := U64.lit 100, deposit_epoch := U64.zero, withdrawable_epoch := FAR_FUTURE_EPOCH }

/-- The control anchor without its builder registry: Jaune's `B5Witnesses.directState` (slot 24, latest block at
slot 8, every payments entry empty) with latest bid `L` and `L`'s withdrawal already in
`builder_pending_withdrawals`. -/
def queuedCore : Gloas.BeaconState Preset.minimal :=
  { B5Witnesses.directState with
    latest_execution_payload_bid := L
    builder_pending_withdrawals := ⟨#[wL]⟩ }

/-- **The control anchor**: `queuedCore` with builder 0 registered under the key `pk`. -/
def queuedAnchor (pk : BLSPubkey) : Gloas.BeaconState Preset.minimal :=
  { queuedCore with builders := ⟨#[queuedBuilder pk]⟩ }

/-- **The control assignment**: the signed bid `β` witnesses the latest bid and the queued entry 0. -/
def queuedBid (β : Gloas.SignedExecutionPayloadBid) : WitnessRef → Option Gloas.SignedExecutionPayloadBid
  | .latest => some β
  | .withdrawal 0 => some β
  | _ => none

theorem queuedAnchor_builders (pk : BLSPubkey) :
    (queuedAnchor pk).builders.toArray = #[queuedBuilder pk] := rfl

theorem queuedAnchor_queue (pk : BLSPubkey) :
    (queuedAnchor pk).builder_pending_withdrawals.toArray = #[wL] := rfl

theorem queuedAnchor_payments (pk : BLSPubkey) :
    (queuedAnchor pk).builder_pending_payments.toArray =
      Array.replicate 16 Gloas.BuilderPendingPayment.empty := rfl

theorem queuedAnchor_bidIndex (pk : BLSPubkey) : bidIndex (queuedAnchor pk) = none :=
  (by decide +kernel : bidIndex queuedCore = none)

theorem queuedAnchor_builder {pk : BLSPubkey} {i : Nat} {b : Gloas.Builder}
    (h : (queuedAnchor pk).builders.toArray[i]? = some b) : i = 0 ∧ b = queuedBuilder pk := by
  rw [queuedAnchor_builders] at h
  have hi : i < 1 := (Array.getElem?_eq_some_iff.mp h).1
  obtain rfl : i = 0 := by omega
  exact ⟨rfl, (Option.some.inj h).symm⟩

/-- **The control anchor satisfies the anchor invariant.** -/
theorem queuedAnchor_inv (pk : BLSPubkey) (ex : BlockChain) (pa : ParentPayload Preset.minimal) :
    GAnchorInv (GJointState.gloas (queuedAnchor pk) ex pa) := by
  refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ⟨rfl, Or.inr ?_, Or.inl rfl⟩, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro i j bi bj hij hi hj
    have := (queuedAnchor_builder hj).1
    omega
  · intro w hw
    rw [queuedAnchor_queue] at hw
    obtain rfl : w = wL := List.mem_singleton.mp hw
    exact Nat.zero_lt_one
  · intro p hp hne
    rw [queuedAnchor_payments] at hp
    exact absurd (Array.mem_replicate.mp (Array.mem_toList_iff.mp hp)).2 hne
  · intro i b hi hne
    obtain ⟨-, rfl⟩ := queuedAnchor_builder hi
    exact absurd rfl hne
  · intro i b hi
    obtain ⟨rfl, rfl⟩ := queuedAnchor_builder hi
    have hpend : pend (queuedAnchor pk) 0 = 5 := (by decide +kernel : pend queuedCore 0 = 5)
    have hexpo : expo (queuedAnchor pk) 0 ≤ 5 := by
      unfold expo
      split_ifs
      · exact Nat.le_refl 5
      · exact Nat.zero_le 5
    have hbal : (queuedBuilder pk).balance.toNat = 100 := rfl
    omega
  · intro _
    exact Nat.zero_lt_one
  · intro k hk
    rw [queuedAnchor_bidIndex] at hk
    cases hk
  · exact Nat.zero_lt_one
  · intro _
    exact ⟨queuedBuilder pk, rfl, rfl⟩
  · intro j hj _
    have hj' : j < 8 := hj
    show (queuedAnchor pk).builder_pending_payments.toArray[8 + j]? = _
    rw [queuedAnchor_payments, Array.getElem?_replicate]
    exact ite_eq_left (by omega)
  · intro _
    exact (by decide +kernel : queuedCore.builder_pending_payments.toArray[Preset.minimal.SLOTS_PER_EPOCH +
      U64.toNat queuedCore.slot % Preset.minimal.SLOTS_PER_EPOCH]? = some Gloas.BuilderPendingPayment.empty)
  · exact Nat.zero_le _

/-- **The control assignment fails witness injectivity at one pair only.** For a signed bid `β` of `L` verified at
the control anchor, `queuedBid β` meets the `payment`, `withdrawal` and `latest` fields of `GloasBidWitness`, and
is injective on every pair of references other than `.latest` with `.withdrawal 0`; there it gives the one bid `β`
to the latest bid and to the queued entry, so it is not `QueuedSeparate`. -/
theorem queuedAnchor_witness (pk : BLSPubkey) (β : Gloas.SignedExecutionPayloadBid)
    (hβ : BidSigned (queuedAnchor pk) β) (hm : β.message = L) :
    (∀ k p, (queuedAnchor pk).builder_pending_payments.toArray[k]? = some p →
      p ≠ Gloas.BuilderPendingPayment.empty →
      ∃ γ, queuedBid β (.payment k) = some γ ∧ BidSigned (queuedAnchor pk) γ ∧
        p.withdrawal = bidWithdrawal γ.message) ∧
    (∀ k w, (queuedAnchor pk).builder_pending_withdrawals.toArray[k]? = some w →
      ∃ γ, queuedBid β (.withdrawal k) = some γ ∧ BidSigned (queuedAnchor pk) γ ∧
        w = bidWithdrawal γ.message) ∧
    ((queuedAnchor pk).latest_execution_payload_bid.builder_index ≠ Gloas.BUILDER_INDEX_SELF_BUILD →
      ∃ γ, queuedBid β .latest = some γ ∧ BidSigned (queuedAnchor pk) γ ∧
        γ.message = (queuedAnchor pk).latest_execution_payload_bid) ∧
    (∀ r r' γ, queuedBid β r = some γ → queuedBid β r' = some γ →
      r = r' ∨ (r = .latest ∧ r' = .withdrawal 0) ∨ (r = .withdrawal 0 ∧ r' = .latest)) ∧
    queuedBid β .latest = some β ∧ queuedBid β (.withdrawal 0) = some β ∧
    ¬ QueuedSeparate (queuedBid β) := by
  refine ⟨fun k p hp hne => ?_, fun k w hw => ?_, fun _ => ⟨β, rfl, hβ, hm⟩, fun r r' γ hr hr' => ?_, rfl, rfl,
    fun h => ?_⟩
  · rw [queuedAnchor_payments] at hp
    exact absurd (Array.mem_replicate.mp (Array.mem_of_getElem? hp)).2 hne
  · rw [queuedAnchor_queue] at hw
    have hk : k < 1 := (Array.getElem?_eq_some_iff.mp hw).1
    obtain rfl : k = 0 := by omega
    obtain rfl : wL = w := Option.some.inj hw
    exact ⟨β, rfl, hβ, by rw [hm]⟩
  · have ref : ∀ r, queuedBid β r = some γ → r = .latest ∨ r = .withdrawal 0 := by
      intro r h
      rcases r with k | k | _
      · cases h
      · rcases k with _ | k
        · exact Or.inr rfl
        · cases h
      · exact Or.inl rfl
    rcases ref r hr with rfl | rfl <;> rcases ref r' hr' with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inl rfl
  · cases h 0 .latest β rfl rfl

/-- **The control anchor's latest bid pays, is out of the window, and is already queued.** -/
theorem queuedAnchor_queued (pk : BLSPubkey) :
    LatestPays (queuedAnchor pk) ∧
    payIdx ((queuedAnchor pk).latest_block_header.slot.toNat + Preset.minimal.SLOTS_PER_EPOCH)
      (queuedAnchor pk) = none ∧
    (queuedAnchor pk).builder_pending_withdrawals.toArray.toList[0]? =
      some (bidWithdrawal (queuedAnchor pk).latest_execution_payload_bid) :=
  ⟨⟨(by decide +kernel : U64.zero < L.value),
      (by decide +kernel : L.builder_index ≠ Gloas.BUILDER_INDEX_SELF_BUILD)⟩,
    (by decide +kernel : payIdx (queuedCore.latest_block_header.slot.toNat + Preset.minimal.SLOTS_PER_EPOCH)
      queuedCore = none), rfl⟩

/-- The evaluation behind `queuedAnchor_double`, as one closed equation in the builder key (the kernel evaluates
`apply_parent_execution_payload` with the key a variable). -/
theorem queuedAnchor_double_fun :
    (fun pk : BLSPubkey => (Gloas.applyParentExecutionPayload { cfg := Config.minimal } (queuedAnchor pk)
        Gloas.ExecutionRequests.empty).toOption.map
      (fun s => s.builder_pending_withdrawals.toArray)) = fun _ => some #[wL, wL] := by
  kernel_rfl

/-- **The model appends the queued bid again.** `apply_parent_execution_payload` at the control anchor (a FULL
parent older than the previous epoch, no requests) returns `builder_pending_withdrawals` holding `L`'s withdrawal
twice: the entry queued at the anchor and the direct append. -/
theorem queuedAnchor_double (pk : BLSPubkey) :
    (Gloas.applyParentExecutionPayload { cfg := Config.minimal } (queuedAnchor pk)
        Gloas.ExecutionRequests.empty).toOption.map
      (fun s => s.builder_pending_withdrawals.toArray) = some #[wL, wL] :=
  congrFun queuedAnchor_double_fun pk

/-- **Any old-parent FULL step from the control anchor doubles the bid.** On a Gloas step from the control anchor
whose parent settles FULL with its slot out of the window, the list after `process_parent_execution_payload` holds
`L`'s withdrawal at position 0 (queued at the anchor, witness `β` under `queuedBid β`) and at the end of the
post-slots queue (the direct append of the latest bid, witness `β`). -/
theorem queuedAnchor_step_doubles {cfg : ChainConfig} {ccfg : Config} {bls : Bool} (pk : BLSPubkey)
    (D : GloasStepData (P := Preset.minimal) cfg ccfg bls) (hpre : D.preB = queuedAnchor pk)
    {s1 : Gloas.BeaconState Preset.minimal}
    (h1 : Gloas.processParentExecutionPayload (gloasCtx ccfg bls) D.postSlots D.block.message = .ok s1)
    (hfull : parentFull D.postSlots D.block.message = true)
    (hnone : payIdx (D.postSlots.latest_block_header.slot.toNat + Preset.minimal.SLOTS_PER_EPOCH)
      D.postSlots = none) :
    0 < D.postSlots.builder_pending_withdrawals.toArray.toList.length ∧
      s1.builder_pending_withdrawals.toArray.toList[0]? = some wL ∧
      s1.builder_pending_withdrawals.toArray.toList[
        D.postSlots.builder_pending_withdrawals.toArray.toList.length]? = some wL := by
  have h := D.direct_append_duplicates (k := 0) (by decide) h1 hfull hnone
    (by rw [hpre]; exact (queuedAnchor_queued pk).1.1) (by rw [hpre]; exact (queuedAnchor_queued pk).2.2)
  rw [hpre] at h
  exact h

end Blanc.Lift.BuilderRequest.AnchorQueuedControl
