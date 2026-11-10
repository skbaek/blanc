import Blanc.Composition.BuilderRequestJointGPosition
import JauneConsensus.Facts.Gloas.StepB1
import Blanc.Composition.BuilderRequestJointGBalance

/-!
# B1 over a valid Gloas joint chain: registration authorization (`bls = true`)

Goal `eip8282-gloas-cross-layer-v1`, frozen statements rev 3.1 (Plans `recon/statements.md` B1), traces read at the
step's post-slots state (erratum 2026-11-10).

* `ValidJointG.registration_authorization`: every builder record created at a Gloas step of the run came from the
  builder deposit request at deposit-trace position `k`, classified `register i req.amount` under the real BLS;
  positionally the step settles FULL and the request is record `k` of the type-3 records of the payload block it
  builds upon, the deposit contract's committed paid submission occurrence `|emissions before that block| + k`
  (`ValidJointG.deposit_position`); it has the `0xB0` prefix, a signature verifying under
  `DOMAIN_BUILDER_DEPOSIT`, and the fresh record with `execution_address = credentials[12:]`. The post-state clause
  (the record at the step's post-state, with the later same-payload top-ups) is G3d's `registration_post` under
  FinalizedNotAhead along the run (`ValidJointG.registeredRecordKept`).
* `ValidJointG.crossing_builders`: the crossing creates exactly `upgrade_to_gloas`'s builders, balances included,
  all at `FAR_FUTURE_EPOCH`, with `builder_pending_withdrawals` empty (G3c).
* `ValidJointG.crossing_onboarding`: the fork clause, MBS's `jointStepG_crossing_onboarding` at the run's crossing
  step: its builders are exactly `upgrade_to_gloas`'s, all at `FAR_FUTURE_EPOCH`, and the first block creates none.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune JauneConsensus ExecutionTrace ChainLink Blanc JauneConsensus.Facts.Gloas Occurrence

variable {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}

/-! ## The registered record survives the block (G3d), discharged below -/

/-- **G3d: `FinalizedNotAhead`, Jaune `Facts/Gloas/FinalizedNotAhead.lean`** (discharged at `bls = true`:
`ValidJointG.registeredRecordKept`). At every Gloas
step of the run, a builder record created by the step survives the rest of the block unchanged: the step's
post-state holds at index `i` the record the deposit trace ends with. A fresh builder's `deposit_epoch` is the
current epoch, so it is inactive when finalization is not ahead of the current epoch and a same-payload exit
leaves it; nothing is pending for it and the sweep skips it at `FAR_FUTURE_EPOCH`. G3d proves the per-step form
from `FinalizedNotAhead` at the step's pre-state; this is that result over the run's Gloas steps. -/
def RegisteredRecordKept {s₀ s : GJointState P} (run : GJointRun cfg ccfg bls s₀ s) : Prop :=
  ∀ {j : Nat} {D : GloasStepData (P := P) cfg ccfg bls}, run.steps[j]? = some (.gloas D) →
    ∀ {i : Nat} {trD : List (Gloas.BeaconState P)}, builderDepositTrace ccfg bls D.postSlots D.block = .ok trD →
      BuilderCreated D.preB D.postB i →
      D.postB.builders.toArray[i]? = (traceLast D.postSlots trD).builders.toArray[i]?

namespace ValidJointG

variable {checkpoint : BlockChain} {anchor final : GJointState P}

/-- **`RegisteredRecordKept`, discharged** (`bls = true`): G3d's `GStepView.registration_post` at every Gloas step,
its premises FinalizedNotAhead (`fna_pre`, carried from `GAnchorInv` along the run), the G3a invariants
(`gInv_pre`) and the N7 bounds at the post-state. -/
theorem registeredRecordKept (v : ValidJointG cfg ccfg bls checkpoint anchor final) (hbls : bls = true) :
    RegisteredRecordKept v.run := by
  subst hbls
  intro j D stepD i trD hD created
  obtain ⟨-, g3, g4, g5, -, g7, g8, hA, fe⟩ := v.gInv_pre stepD
  obtain ⟨vb, bb⟩ := v.post_bounds stepD
  have hsp : D.postSlots.builders = D.preB.builders := Inv.processSlots_identityStable D.slots
  have hcr : BuilderCreated D.postSlots D.postB i := (builderCreated_congr_left hsp).mpr created
  obtain ⟨k, req, trD', m, m', dom, addr, e, bal, -, hD', -, -, -, -, -, -, -, -, -, -, hlast, hpost, -⟩ :=
    D.view.registration_post v.slotsPerEpoch v.quorumPositive (v.fna_pre stepD) g5 g3 g4 g7 g8 fe hA vb bb hcr
  replace hD' : builderDepositTrace ccfg true D.postSlots D.block = .ok trD' := hD'
  rw [hD] at hD'
  cases hD'
  exact hpost.trans hlast.symm

/-- **B1: registration authorization (`bls = true`).** Every builder record created at a Gloas step `j` of a valid
joint chain (`BuilderCreated`: the pubkey at `i` changed, by append or reuse) came from the builder deposit request
`req` at deposit-trace position `k` of the step block's `parent_execution_requests` (the trace read at the step's
post-slots state):

* at `tr[k]` it is classified `register i req.amount` (a new pubkey with a valid signature), its call running
  `tr[k] → tr[k+1]`;
* positionally, the step settles FULL and `req` is record `k` of the type-3 records of the payload block it builds
  upon, which is the deposit contract's committed paid submission occurrence `|emissions before that block| + k`;
* its credentials carry the `0xB0` prefix and its signature verifies (`blsVerify true`) over the deposit message
  under `DOMAIN_BUILDER_DEPOSIT` (CL:2276-2284);
* `tr[k+1]` holds at `i` the fresh record (`freshBuilder`): `req`'s pubkey, version `PAYLOAD_BUILDER_VERSION` (0), `execution_address = credentials[12:]`,
  balance `req.amount`, `deposit_epoch` the epoch of `tr[k]`'s slot, `withdrawable_epoch = FAR_FUTURE_EPOCH`;
* the step's post-state holds at `i` that record with balance `req.amount` plus the later `0xB0` deposits for its
  pubkey in the same payload (G3d, `registeredRecordKept`). -/
theorem registration_authorization (v : ValidJointG cfg ccfg bls checkpoint anchor final) (hbls : bls = true)
    {j : Nat} {D : GloasStepData (P := P) cfg ccfg bls} (stepD : v.run.steps[j]? = some (.gloas D))
    {i : Nat} (created : BuilderCreated D.preB D.postB i) :
    ∃ (k : Nat) (req : Gloas.BuilderDepositRequest) (tr : List (Gloas.BeaconState P)) (m m' : Gloas.BeaconState P)
      (amount : Gwei) (dom : Domain) (addr : ExecutionAddress) (e : Epoch),
      D.builderDeposits[k]? = some req ∧
      builderDepositTrace ccfg bls D.postSlots D.block = .ok tr ∧ tr[k]? = some m ∧ tr[k + 1]? = some m' ∧
      classifyBuilderDeposit ccfg bls m req = .ok (.register i amount) ∧ amount = req.amount ∧
      (D.isFull ∧ ∃ bi b, v.run.payloadIndex j = bi ∧ v.blocks[v.preBlocks.length + bi]? = some b ∧
        (Deposit.Indexed.blockEmissions b)[k]? = some (Ssz.serialize req) ∧
        (Deposit.Indexed.submissions v.blocks)[(Deposit.Indexed.emissions
          (v.blocks.take (v.preBlocks.length + bi))).length + k]? = some (Ssz.serialize req)) ∧
      req.withdrawal_credentials.toBytes.head? = some 0xB0 ∧
      builderDepositDomain ccfg = some dom ∧
      blsVerify true req.pubkey (computeSigningRoot (builderDepositMessage req) dom) req.signature = true ∧
      Jaune.Bytes.toAdr? (req.withdrawal_credentials.toBytes.drop 12) = some addr ∧
      computeEpochAtSlot P m.slot = .ok e ∧
      m'.builders.toArray[i]? = some (freshBuilder req.pubkey addr req.amount e) ∧
      ∃ b' : Gloas.Builder, D.postB.builders.toArray[i]? = some b' ∧
        b'.pubkey = req.pubkey ∧ b'.version = Gloas.PAYLOAD_BUILDER_VERSION ∧ b'.execution_address = addr ∧
        b'.deposit_epoch = e ∧ b'.withdrawable_epoch = FAR_FUTURE_EPOCH ∧
        b'.balance.toNat = req.amount.toNat +
          (((D.builderDeposits.drop (k + 1)).filter (fun r' => r'.pubkey == req.pubkey &&
            Gloas.isBuilderWithdrawalCredential r'.withdrawal_credentials)).map (·.amount.toNat)).sum := by
  subst hbls
  have hcr : BuilderCreated D.view.postSlots D.postB i := by
    unfold BuilderCreated at created ⊢
    change (D.postB.builders.toArray[i]?).isSome ∧
      (D.postSlots.builders.toArray[i]?).map (·.pubkey) ≠ (D.postB.builders.toArray[i]?).map (·.pubkey)
    rw [Inv.processSlots_identityStable D.slots]
    exact created
  obtain ⟨k, req, tr, m, m', dom, addr, e, bal, hreq, htr, hm, hm', -, hcl, hpre, hdom, hv, haddr, he, hat,
    hlast, hbal⟩ := D.view.registration v.slotsPerEpoch hcr
  have hpost := v.registeredRecordKept rfl stepD htr created
  change (traceLast D.postSlots tr).builders.toArray[i]? = _ at hlast
  rw [hlast] at hpost
  refine ⟨k, req, tr, m, m', req.amount, dom, addr, e, hreq, htr, hm, hm', hcl, rfl, v.deposit_position stepD hreq,
    hpre, hdom, hv, haddr, he, hat, _, hpost, rfl, rfl, rfl, rfl, rfl, hbal⟩

/-- **B1's fork clause, at the run's crossing step.** The crossing's post-slots builders are exactly
`upgrade_to_gloas`'s onboarding (`D.upgraded.builders`), every builder of its post-state has the pubkey of the same
slot of the upgraded state and is at `FAR_FUTURE_EPOCH`, the registry keeps its length, and the first block creates
no record: every builder record after the crossing is one of the onboarding's. -/
theorem crossing_onboarding (v : ValidJointG cfg ccfg bls checkpoint anchor final) {j : Nat}
    {C : CrossingData (P := P) cfg ccfg bls} (_stepC : v.run.steps[j]? = some (.crossing C)) :
    C.postSlots.builders = C.upgraded.builders ∧ BuildersFar C.upgraded ∧ BuildersFar C.postB ∧
      C.postB.builders.toArray.size = C.upgraded.builders.toArray.size ∧
      (∀ j : Nat, (C.postB.builders.toArray[j]?).map (fun c : Gloas.Builder => c.pubkey) =
        (C.upgraded.builders.toArray[j]?).map (fun c : Gloas.Builder => c.pubkey)) ∧
      ∀ i, ¬ BuilderCreated C.postSlots C.postB i := by
  obtain ⟨_, upgraded, ps, post, _, -, hup, hs, hbs, hfu, hfp, hsz, hpk, hnc⟩ :=
    jointStepG_crossing_onboarding (GJointRunStep.crossing C).ok
  injection hs with hp
  subst hp
  obtain rfl : upgraded = C.upgraded := Except.ok.inj (hup.symm.trans C.cross)
  have hcs : C.postSlots.builders = C.upgraded.builders := crossingSlots_builders C.slots
  exact ⟨hcs, hfu, hfp, hsz, hpk, fun i h => hnc i ((builderCreated_congr_left (hbs.trans hcs.symm)).mpr h)⟩

/-- **The crossing step creates exactly `upgrade_to_gloas`'s builders** (statements.md B1 `crossing_builders`,
SF-6; O-a complete): after the first Gloas block the builders are the upgraded state's, balances included, all at
`FAR_FUTURE_EPOCH`, and `builder_pending_withdrawals` is the upgraded state's (empty). -/
theorem crossing_builders (v : ValidJointG cfg ccfg bls checkpoint anchor final) {j : Nat}
    {C : CrossingData (P := P) cfg ccfg bls} (stepC : v.run.steps[j]? = some (.crossing C)) :
    C.postB.builders = C.upgraded.builders ∧
      (∀ b ∈ C.postB.builders.toArray.toList, b.withdrawable_epoch = FAR_FUTURE_EPOCH) ∧
      C.postB.builder_pending_withdrawals = C.upgraded.builder_pending_withdrawals := by
  have hmem : (GJointRunStep.crossing C).postState ∈ v.run.states :=
    List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_of_getElem? stepC))
  obtain ⟨hb, hw⟩ := C.builders_eq v.quorumPositive v.slotsPerEpoch (v.validatorsBound _ hmem)
    (v.buildersBound _ hmem)
  refine ⟨hb, fun b hb' => ?_, hw⟩
  rw [Array.mem_toList_iff] at hb'
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hb'
  exact C.buildersFar i _ (Array.getElem?_eq_getElem hi)

end ValidJointG

end Blanc.Lift.BuilderRequest
