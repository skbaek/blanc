import Blanc.Composition.BuilderRequestJointGConservation
import JauneConsensus.Facts.Gloas.Onboarding

/-!
# B1's fork step and B7's crossing term over a valid Gloas joint chain

Goal `eip8282-gloas-cross-layer-v1`, frozen statements rev 3.1 (Plans `recon/statements.md` B1 fork step, B7).

* `ValidJointG.crossing_onboards` (B1's standalone fork theorem at run level): at the crossing step `C`, the
  upgraded state's builders and pending deposits meet Jaune's declarative `OnboardingSpec` against the validators
  and pending deposits of the Fulu state `upgrade_to_gloas` reads (`C.atFork`, the pre-state after `process_slots`
  to the fork slot); the partition is unique, validators and balances are unchanged, and the upgraded total is the
  registering (`R`) and top-up (`T`) amounts. It is Jaune's `upgradeToGloas_onboards` at `C.upgrade`.
* `ValidJointG.builder_total_crossing` (B7's crossing term): the upgraded total is the `R` and `T` sum for any
  partition meeting the specification (Jaune's `upgradeToGloas_builder_total`); `builder_total_crossing_post` the
  same for the crossing's post-state under RBM's pending `CrossingBalanceKept`.
* `ValidJointG.builder_total_run_onboarded`: RBM's `ValidJointG.builder_total_run` with the crossing's fork term
  written as that sum (`CrossingData.onboardedCredit`).
-/

namespace Blanc.Lift.BuilderRequest

open Jaune JauneConsensus Blanc JauneConsensus.Facts.Gloas JauneConsensus.Facts.Gloas.Onboarding

variable {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}

/-- The validator pubkeys of the Fulu state the crossing upgrades. -/
def _root_.Blanc.CrossingData.forkValidatorPubkeys (C : CrossingData (P := P) cfg ccfg bls) : List BLSPubkey :=
  C.atFork.validators.toArray.toList.map (·.pubkey)

/-- The pending deposits of the Fulu state the crossing upgrades, in queue order. -/
def _root_.Blanc.CrossingData.forkQueue (C : CrossingData (P := P) cfg ccfg bls) : List PendingDeposit :=
  fuluPendingDeposits C.atFork

/-- The crossing's onboarding partition meets the specification (`R` and `T` named first). -/
theorem _root_.Blanc.CrossingData.onboards (C : CrossingData (P := P) cfg ccfg bls) :
    ∃ (R T K X : List (Fin C.forkQueue.length)),
      OnboardingSpec P (gloasCtx ccfg bls) C.forkValidatorPubkeys C.forkQueue K R T X
        C.upgraded.builders.toArray.toList C.upgraded.pending_deposits.toArray.toList := by
  obtain ⟨K, R, T, X, S, -⟩ := upgradeToGloas_onboards C.upgrade
  exact ⟨R, T, K, X, S⟩

/-- The crossing's fork term as the onboarding specification states it: the sum of the registering (`R`) and top-up
(`T`) amounts of the (unique) onboarding partition. -/
noncomputable def _root_.Blanc.CrossingData.onboardedCredit (C : CrossingData (P := P) cfg ccfg bls) : Nat :=
  let R := Classical.choose C.onboards
  let T := Classical.choose (Classical.choose_spec C.onboards)
  ((R ++ T).map (fun t => C.forkQueue[t].amount.toNat)).sum

/-- `onboardedCredit` is the `R` and `T` sum of every partition meeting the specification. -/
theorem _root_.Blanc.CrossingData.onboardedCredit_eq (C : CrossingData (P := P) cfg ccfg bls)
    {K R T X : List (Fin C.forkQueue.length)}
    (S : OnboardingSpec P (gloasCtx ccfg bls) C.forkValidatorPubkeys C.forkQueue K R T X
      C.upgraded.builders.toArray.toList C.upgraded.pending_deposits.toArray.toList) :
    C.onboardedCredit = ((R ++ T).map (fun t => C.forkQueue[t].amount.toNat)).sum := by
  obtain ⟨K', X', S'⟩ := Classical.choose_spec (Classical.choose_spec C.onboards)
  unfold CrossingData.onboardedCredit
  exact S'.total.symm.trans S.total

/-- `onboardedCredit` is the upgraded state's total builder balance. -/
theorem _root_.Blanc.CrossingData.onboardedCredit_total (C : CrossingData (P := P) cfg ccfg bls) :
    C.onboardedCredit = totalBuilderBalance C.upgraded := by
  obtain ⟨R, T, K, X, S⟩ := C.onboards
  rw [C.onboardedCredit_eq S]
  exact (upgradeToGloas_builder_total S).symm

/-- A run step's builder credits with the crossing's fork term written as the onboarding sum. -/
noncomputable def _root_.Blanc.GJointRunStep.builderCreditOnboarded :
    GJointRunStep (P := P) cfg ccfg bls → Nat
  | .pre _ => 0
  | .crossing C => C.onboardedCredit
  | .gloas D => D.builderCredit

namespace ValidJointG

variable {checkpoint : BlockChain} {anchor final : GJointState P}

/-- **B1 fork theorem, run level.** At the crossing step `C` of a valid joint chain, `upgrade_to_gloas` onboards
builders exactly as the declarative specification says: there is a partition `K/R/T/X` of the pending deposits of
the Fulu state it upgrades (`C.atFork`) meeting `OnboardingSpec` against that state's validator pubkeys, the
upgraded registry and the upgraded pending queue; it is the only one; validators and balances are unchanged; and the
upgraded total builder balance is the `R` and `T` amounts. -/
theorem crossing_onboards (_v : ValidJointG cfg ccfg bls checkpoint anchor final) {j : Nat}
    {C : CrossingData (P := P) cfg ccfg bls} (_stepC : _v.run.steps[j]? = some (.crossing C)) :
    ∃ (K R T X : List (Fin C.forkQueue.length)),
      OnboardingSpec P (gloasCtx ccfg bls) C.forkValidatorPubkeys C.forkQueue K R T X
        C.upgraded.builders.toArray.toList C.upgraded.pending_deposits.toArray.toList ∧
      C.upgraded.validators.toArray.toList = C.atFork.validators.toArray.toList ∧
      C.upgraded.balances.toArray.toList = C.atFork.balances.toArray.toList ∧
      (∀ (K' R' T' X' : List (Fin C.forkQueue.length)),
        OnboardingSpec P (gloasCtx ccfg bls) C.forkValidatorPubkeys C.forkQueue K' R' T' X'
          C.upgraded.builders.toArray.toList C.upgraded.pending_deposits.toArray.toList →
        (K', R', T', X') = (K, R, T, X)) ∧
      totalBuilderBalance C.upgraded = ((R ++ T).map (fun t => C.forkQueue[t].amount.toNat)).sum :=
  upgradeToGloas_onboards C.upgrade

/-- **B7's crossing term.** At the crossing step, the upgraded state's total builder balance is the sum of the
registering and top-up amounts of the onboarding partition. -/
theorem builder_total_crossing (_v : ValidJointG cfg ccfg bls checkpoint anchor final) {j : Nat}
    {C : CrossingData (P := P) cfg ccfg bls} (_stepC : _v.run.steps[j]? = some (.crossing C))
    {K R T X : List (Fin C.forkQueue.length)}
    (S : OnboardingSpec P (gloasCtx ccfg bls) C.forkValidatorPubkeys C.forkQueue K R T X
      C.upgraded.builders.toArray.toList C.upgraded.pending_deposits.toArray.toList) :
    totalBuilderBalance C.upgraded = ((R ++ T).map (fun t => C.forkQueue[t].amount.toNat)).sum :=
  upgradeToGloas_builder_total S

/-- **B7's crossing term at the crossing's post-state** (frozen form `totalBuilderBalance D.postB`), under RBM's
pending `CrossingBalanceKept` (the first Gloas block keeps the total). -/
theorem builder_total_crossing_post (v : ValidJointG cfg ccfg bls checkpoint anchor final)
    (crossing : CrossingBalanceKept v.run) {j : Nat}
    {C : CrossingData (P := P) cfg ccfg bls} (stepC : v.run.steps[j]? = some (.crossing C))
    {K R T X : List (Fin C.forkQueue.length)}
    (S : OnboardingSpec P (gloasCtx ccfg bls) C.forkValidatorPubkeys C.forkQueue K R T X
      C.upgraded.builders.toArray.toList C.upgraded.pending_deposits.toArray.toList) :
    totalBuilderBalance C.postB = ((R ++ T).map (fun t => C.forkQueue[t].amount.toNat)).sum := by
  rw [crossing stepC]
  exact v.builder_total_crossing stepC S

/-- **B7 conservation over the run, with the onboarding fork term.** RBM's `ValidJointG.builder_total_run`, its
crossing credit written as `CrossingData.onboardedCredit`, the registering and top-up amounts of the onboarding
partition (`CrossingData.onboardedCredit_eq`). Same pending hypotheses as `builder_total_run`. -/
theorem builder_total_run_onboarded (v : ValidJointG cfg ccfg bls checkpoint anchor final)
    (registering : RegisteringStepsConserve v.run) (crossing : CrossingBalanceKept v.run) :
    final.totalBuilders + (v.run.steps.map GJointRunStep.builderDebit).sum =
      anchor.totalBuilders + (v.run.steps.map GJointRunStep.builderCreditOnboarded).sum := by
  have hmap : v.run.steps.map GJointRunStep.builderCreditOnboarded =
      v.run.steps.map GJointRunStep.builderCredit := by
    apply List.map_congr_left
    intro C _
    cases C with
    | pre D => rfl
    | crossing C => exact C.onboardedCredit_total
    | gloas D => rfl
  rw [hmap]
  exact v.builder_total_run registering crossing

end ValidJointG

end Blanc.Lift.BuilderRequest
