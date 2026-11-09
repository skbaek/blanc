import Blanc.Lift.WithdrawalRequest.IgnoreWitnesses
import JauneConsensus.Facts.WithdrawalsFloor

/-!
# O3 negative controls: each anchor invariant is needed by a P4 clause

The joint crediting clauses of P4 (`Blanc/Lift/WithdrawalRequest/JointCrediting.lean`) use
Jaune's anchor invariant `Facts.AnchorInv st = PendingPartialsCompounding st ∧
ExitImpliesWithdrawable st` at the state `process_withdrawals` reads. This module shows that
each conjunct is load-bearing: for each one, a closed minimal-preset Electra state satisfies the
other conjunct, violates this one, and falsifies the P4 clause that uses it.

* **P4 (3), compounding recipient** (`crediting_loop1_compounding_of_anchorInv`, used by
  `ValidJoint.crediting_loop1_compounding`). The state `ppcState` violates only
  `PendingPartialsCompounding`: its one validator has a 0x01 credential and a pending partial
  withdrawal. `get_expected_withdrawals`'s pending-partial loop checks exit status, effective
  balance and balance, not the credential, so it pays that non-compounding validator
  (`loop1_pays_noncompounding_without_pendingPartialsCompounding`).
* **P4 (2), post-withdrawals floor** (`ValidJoint.crediting_floor`, through
  `Facts.processWithdrawals_floor`). The state `eiwState` violates only
  `ExitImpliesWithdrawable`: its one validator has a 0x02 credential (so its pending partial
  satisfies `PendingPartialsCompounding`), `exit_epoch = FAR_FUTURE_EPOCH` but
  `withdrawable_epoch = 0`. The pending-partial loop pays it, then the sweep finds it fully
  withdrawable and pays the rest, so `process_withdrawals` on the matching payload leaves the
  non-exiting loop-1 payee at balance 0 (`floor_fails_without_exitImpliesWithdrawable`), and
  every other premise of `Facts.processWithdrawals_floor` holds while its conclusion fails
  (`processWithdrawals_floor_fails_without_exitImpliesWithdrawable`).

Both states are built with `IgnoreWitnesses`'s `stateWith` at slot 800 (epoch 100). Every
proof evaluates the concrete state by `rfl`/`decide`.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune JauneConsensus

/-! ## Without `PendingPartialsCompounding`, P4 (3) fails -/

/-- One 0x01 validator (`goodValidator`, effective balance `MIN_ACTIVATION_BALANCE`, never
exiting, `withdrawable_epoch = FAR_FUTURE_EPOCH`) with balance 33 ETH and one due pending
partial withdrawal of a thousand gwei. -/
def ppcState : BeaconState Preset.minimal .electra :=
  stateWith (oneVal goodValidator) (oneBal (U64.lit 33000000000)) (U64.lit 800) onePending

/-- The loop-1 payment of `ppcState`: the pending thousand gwei. -/
def ppcLoop1 : JauneConsensus.Withdrawal :=
  { index := U64.zero, validator_index := U64.zero, address := witAddr, amount := U64.lit 1000 }

/-- The sweep payment of `ppcState`: the excess over `MIN_ACTIVATION_BALANCE`. -/
def ppcSweep : JauneConsensus.Withdrawal :=
  { index := U64.one, validator_index := U64.zero, address := witAddr,
    amount := U64.lit 999999000 }

/-- `get_expected_withdrawals` at `ppcState`: the pending thousand gwei, then the sweep's excess. -/
theorem ppc_expected : getExpectedWithdrawals ppcState = .ok (#[ppcLoop1, ppcSweep], 1) := by
  unfold getExpectedWithdrawals
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  rfl

/-- `ppcState` violates `PendingPartialsCompounding` and keeps `ExitImpliesWithdrawable`, and its
pending-partial loop pays a validator without a compounding credential: the negation of
`crediting_loop1_compounding_of_anchorInv`'s conclusion, on the loop-1 split of
`Facts.loop1_emissions`. -/
theorem loop1_pays_noncompounding_without_pendingPartialsCompounding :
    ¬ Facts.PendingPartialsCompounding ppcState ∧ Facts.ExitImpliesWithdrawable ppcState ∧
    ∃ (ws : Array JauneConsensus.Withdrawal) (processed : Nat),
      getExpectedWithdrawals ppcState = .ok (ws, processed) ∧
      ∃ (ws1 ws2 : Array JauneConsensus.Withdrawal)
        (l : SszList PendingPartialWithdrawal Preset.minimal.PENDING_PARTIAL_WITHDRAWALS_LIMIT),
        ppcState.pendingPartialWithdrawals = .ok l ∧
        ws.toList = ws1.toList ++ ws2.toList ∧
        Facts.Loop1Witness ws1 l.toArray processed ∧
        ∃ w ∈ ws1.toList, ∃ validator,
          ppcState.validators.toArray[w.validator_index.toNat]? = some validator ∧
          hasCompoundingWithdrawalCredential validator = false := by
  refine ⟨?_, ?_, #[ppcLoop1, ppcSweep], 1, ppc_expected, #[ppcLoop1], #[ppcSweep], onePending, rfl, rfl,
    ⟨by decide, by decide, [pendingEntry], List.Sublist.refl _, rfl, ?_⟩,
    ppcLoop1, List.mem_singleton_self _, goodValidator, rfl, by decide⟩
  · intro h
    obtain ⟨v, hv, hc⟩ := h onePending rfl pendingEntry (List.mem_singleton_self _)
    obtain rfl : goodValidator = v := Option.some.inj hv
    exact absurd hc (by decide)
  · intro v hv _
    have hv' : v ∈ [goodValidator] := hv
    rw [List.mem_singleton] at hv'
    subst hv'
    rfl
  · intro i w p hw hp
    rcases i with _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hw hp
      subst hw hp
      exact ⟨rfl, by decide⟩
    · simp only [List.getElem?_cons_succ, List.getElem?_nil, reduceCtorEq] at hp

/-! ## Without `ExitImpliesWithdrawable`, P4 (2) fails -/

/-- A 0x02 validator with effective balance `MIN_ACTIVATION_BALANCE`, `exit_epoch =
FAR_FUTURE_EPOCH` but `withdrawable_epoch = 0`. -/
def eiwValidator : Validator :=
  { witValidator cred02 U64.zero FAR_FUTURE_EPOCH (U64.lit 32000000000) with
    withdrawable_epoch := U64.zero }

/-- `eiwValidator` with balance 33 ETH and one due pending partial withdrawal of a thousand
gwei. -/
def eiwState : BeaconState Preset.minimal .electra :=
  stateWith (oneVal eiwValidator) (oneBal (U64.lit 33000000000)) (U64.lit 800) onePending

/-- The sweep payment of `eiwState`: the whole remaining balance (fully withdrawable). -/
def eiwSweep : JauneConsensus.Withdrawal :=
  { index := U64.one, validator_index := U64.zero, address := witAddr,
    amount := U64.lit 32999999000 }

/-- The withdrawals of `eiwState`: the pending thousand gwei, then the full sweep. -/
def eiwWithdrawals : SszList JauneConsensus.Withdrawal Preset.minimal.MAX_WITHDRAWALS_PER_PAYLOAD :=
  ⟨#[ppcLoop1, eiwSweep], by decide⟩

/-- The execution payload matching `eiwState`: zero fields except its withdrawals. -/
def eiwPayload : ExecutionPayload Preset.minimal :=
  { parent_hash := 0
    fee_recipient := 0
    state_root := 0
    receipts_root := 0
    logs_bloom := baseState.latest_execution_payload_header.logs_bloom
    prev_randao := 0
    block_number := U64.zero
    gas_limit := U64.zero
    gas_used := U64.zero
    timestamp := U64.zero
    extra_data := SszList.empty
    base_fee_per_gas := UIntN.zero
    block_hash := 0
    transactions := SszList.empty
    withdrawals := eiwWithdrawals
    blob_gas_used := U64.zero
    excess_blob_gas := U64.zero }

/-- The state `process_withdrawals` returns on `eiwState` and `eiwPayload`: balance 0, queue
drained, next withdrawal index 2. -/
def eiwPost : BeaconState Preset.minimal .electra :=
  { stateWith (oneVal eiwValidator) (oneBal U64.zero) (U64.lit 800) SszList.empty with
    next_withdrawal_index := U64.lit 2 }

/-- `get_expected_withdrawals` at `eiwState`: the pending thousand gwei, then the full sweep. The
sweep's `for _ in [0:bound]` is rewritten to a list loop, which then evaluates by `rfl`. -/
theorem eiw_expected : getExpectedWithdrawals eiwState = .ok (eiwWithdrawals.toArray, 1) := by
  unfold getExpectedWithdrawals
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  rfl

/-- `process_withdrawals` at `eiwState` on `eiwPayload` returns `eiwPost`. -/
theorem eiw_process : JauneConsensus.processWithdrawals eiwState eiwPayload = .ok eiwPost := by
  unfold JauneConsensus.processWithdrawals
  rw [eiw_expected]
  rfl

/-- `eiwState` keeps `PendingPartialsCompounding`. -/
theorem eiw_pendingPartialsCompounding : Facts.PendingPartialsCompounding eiwState := by
  intro l hl p hp
  injection hl with hl
  subst hl
  have hp' : p ∈ [pendingEntry] := hp
  rw [List.mem_singleton] at hp'
  subst hp'
  exact ⟨eiwValidator, rfl, by decide⟩

/-- `eiwState` violates `ExitImpliesWithdrawable`. -/
theorem eiw_not_exitImpliesWithdrawable : ¬ Facts.ExitImpliesWithdrawable eiwState := by
  intro h
  exact absurd (h eiwValidator (List.mem_singleton_self _) rfl) (by decide)

/-- `eiwState` keeps `PendingPartialsCompounding` and violates `ExitImpliesWithdrawable`, and
`process_withdrawals` on the matching payload leaves a non-exiting loop-1 payee below
`MIN_ACTIVATION_BALANCE`: the negation of `ValidJoint.crediting_floor`'s last clause, with the
rest of its package (expected withdrawals, payload match, post-state, loop-1 split, witness and
floor inputs) holding. -/
theorem floor_fails_without_exitImpliesWithdrawable :
    Facts.PendingPartialsCompounding eiwState ∧ ¬ Facts.ExitImpliesWithdrawable eiwState ∧
    ∃ (ws : Array JauneConsensus.Withdrawal) (processed : Nat),
      getExpectedWithdrawals eiwState = .ok (ws, processed) ∧
      eiwPayload.withdrawals.toArray = ws ∧
      ∃ post, JauneConsensus.processWithdrawals eiwState eiwPayload = .ok post ∧
      ∃ (ws1 ws2 : Array JauneConsensus.Withdrawal)
        (l : SszList PendingPartialWithdrawal Preset.minimal.PENDING_PARTIAL_WITHDRAWALS_LIMIT),
        eiwState.pendingPartialWithdrawals = .ok l ∧
        ws.toList = ws1.toList ++ ws2.toList ∧
        Facts.Loop1Witness ws1 l.toArray processed ∧
        Facts.Loop1Floor eiwState ws1 Preset.minimal.MIN_ACTIVATION_BALANCE ∧
        ∃ w ∈ ws1.toList, ∃ validator,
          eiwState.validators.toArray[w.validator_index.toNat]? = some validator ∧
          validator.exit_epoch = FAR_FUTURE_EPOCH ∧
          ∃ b : U64, post.balances.toArray[w.validator_index.toNat]? = some b ∧
            b.toNat < Preset.minimal.MIN_ACTIVATION_BALANCE := by
  refine ⟨eiw_pendingPartialsCompounding, eiw_not_exitImpliesWithdrawable, _, 1, eiw_expected,
    rfl, eiwPost, eiw_process, #[ppcLoop1], #[eiwSweep], onePending, rfl, rfl,
    ⟨by decide, by decide, [pendingEntry], List.Sublist.refl _, rfl, ?_⟩, ?_,
    ppcLoop1, List.mem_singleton_self _, eiwValidator, rfl, rfl, U64.zero, rfl, by decide⟩
  · intro i w p hw hp
    rcases i with _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hw hp
      subst hw hp
      exact ⟨rfl, by decide⟩
    · simp only [List.getElem?_cons_succ, List.getElem?_nil, reduceCtorEq] at hp
  · intro w hw
    have hw' : w ∈ [ppcLoop1] := hw
    rw [List.mem_singleton] at hw'
    subst hw'
    exact ⟨U64.lit 33000000000, U64.zero, U64.lit 33000000000, rfl, rfl, by decide⟩

/-- Every premise of `Facts.processWithdrawals_floor` except `ExitImpliesWithdrawable` holds at
`eiwState` and `eiwPayload`, and its conclusion fails: validator 0 is not exiting, is paid, and
ends at balance 0. -/
theorem processWithdrawals_floor_fails_without_exitImpliesWithdrawable :
    CFork.atLeast .electra .electra = true ∧
    ¬ Facts.ExitImpliesWithdrawable eiwState ∧
    2 ≤ Preset.minimal.SLOTS_PER_EPOCH ∧
    Preset.minimal.MIN_ACTIVATION_BALANCE ≤ Preset.minimal.MAX_EFFECTIVE_BALANCE_ELECTRA ∧
    getExpectedWithdrawals eiwState = .ok (eiwWithdrawals.toArray, 1) ∧
    JauneConsensus.processWithdrawals eiwState eiwPayload = .ok eiwPost ∧
    ¬ (∀ (i : ValidatorIndex),
      (∃ v, eiwState.validators.toArray[i.toNat]? = some v ∧ v.exit_epoch = FAR_FUTURE_EPOCH) →
      (∃ w ∈ eiwWithdrawals.toArray.toList, w.validator_index = i) →
      ∀ b0 b1 : U64,
        eiwState.balances.get i.toNat "processWithdrawals_floor" = .ok b0 →
        eiwPost.balances.get i.toNat "processWithdrawals_floor" = .ok b1 →
        Preset.minimal.MIN_ACTIVATION_BALANCE ≤ b1.toNat) := by
  refine ⟨rfl, eiw_not_exitImpliesWithdrawable, by decide, by decide, eiw_expected, eiw_process,
    fun h => ?_⟩
  have := h U64.zero ⟨eiwValidator, rfl, rfl⟩ ⟨ppcLoop1, List.mem_cons_self, rfl⟩
    (U64.lit 33000000000) U64.zero rfl rfl
  exact absurd this (by decide)

end Blanc.Lift.WithdrawalRequest
