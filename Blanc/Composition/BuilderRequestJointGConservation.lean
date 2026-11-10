import Blanc.Composition.BuilderRequestJointGBalance
import JauneConsensus.Facts.Gloas.StepB7

/-!
# B7 over a valid Gloas joint chain: separation and conservation

Goal `eip8282-gloas-cross-layer-v1`, frozen statements rev 3.1 (Plans `recon/statements.md` B7), any `bls`, traces
read at the step's post-slots state (erratum 2026-11-10).

* **Separation** (`ValidJointG.builder_separation`): at every Gloas step of the run, the builder deposit and exit
  requests write the builder registry only (every state of both traces keeps the validators, validator balances,
  `pending_deposits` and both builder queues), and the only other builder writer, `process_withdrawals`, changes
  builder balances only (MBS's `GStepView.builderRequests_frame`, `GStepView.builderWriters`). The function-level
  frames of the frozen row are Jaune's (`Facts/Gloas/BuilderFrames.lean`).
* **Conservation per step** (`ValidJointG.builder_total_step`): total builder balance after the step plus the
  builder debits of its `apply_withdrawals` equals the total before plus the builder deposits it credits (top-ups and
  registrations). At a step that registers no fresh record this is MBS's `GStepView.builder_total_noRegister`, its G3a
  premises from RBA's `ValidJointG.gInv_pre` and the N7 bounds; a registering step uses the one pending hypothesis
  `RegisteringStepsConserve` (G3d).
* **Conservation over the run** (`ValidJointG.builder_total_run`): summed over the run, with the crossing's fork term
  (the upgraded state's total, `upgrade_to_gloas`'s onboarding) under the one pending hypothesis
  `CrossingBalanceKept` (G3c, O-a's balance part).
-/

namespace Blanc.Lift.BuilderRequest

open Jaune JauneConsensus ExecutionTrace Blanc JauneConsensus.Facts.Gloas

variable {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}

/-! ## The step's credit and debit terms -/

/-- The registration amounts along a deposit trace: the amounts of the requests whose outcome at their mid-list
state is a registration. -/
def registeredTotal (ccfg : Config) (bls : Bool) :
    List (Gloas.BeaconState P) → List Gloas.BuilderDepositRequest → Nat
  | m :: tr, r :: rs =>
    (match classifyBuilderDeposit ccfg bls m r with
      | .ok (.register _ a) => a.toNat
      | _ => 0) + registeredTotal ccfg bls tr rs
  | _, _ => 0

/-- Without a registration, the registration amounts are zero. -/
theorem registeredTotal_of_noRegister :
    ∀ (tr : List (Gloas.BeaconState P)) (rs : List Gloas.BuilderDepositRequest),
      NoRegister ccfg bls tr rs → registeredTotal ccfg bls tr rs = 0
  | [], _, _ => by simp only [registeredTotal]
  | _ :: _, [], _ => by simp only [registeredTotal]
  | m :: tr, r :: rs, hno => by
    have htail : NoRegister ccfg bls tr rs := fun i => (hno i).2
    simp only [registeredTotal, registeredTotal_of_noRegister tr rs htail, Nat.add_zero]
    cases hc : classifyBuilderDeposit ccfg bls m r with
    | error _ => rfl
    | ok o =>
      cases o with
      | register i a => exact absurd hc ((hno i).1 a)
      | _ => rfl

/-- The builder debits of a Gloas step: what its `apply_withdrawals` routes to the builder slots of its
post-state. -/
def _root_.Blanc.GloasStepData.builderDebit (D : GloasStepData (P := P) cfg ccfg bls) : Nat :=
  match stepWithdrawals ccfg bls D.postSlots D.block.message with
  | .ok ws => builderDebits ws D.postB.builders.toArray.size
  | .error _ => 0

/-- The builder credits of a Gloas step: the top-ups credited to the builder slots of its post-state along the
deposit trace, plus the registration amounts (statements.md's `creditedDeposits`). -/
def _root_.Blanc.GloasStepData.builderCredit (D : GloasStepData (P := P) cfg ccfg bls) : Nat :=
  match builderDepositTrace ccfg bls D.postSlots D.block with
  | .ok tr => builderCredits ccfg bls tr D.builderDeposits D.postB.builders.toArray.size +
      registeredTotal ccfg bls tr D.builderDeposits
  | .error _ => 0

/-- **B7 conservation at a Gloas step.** -/
def _root_.Blanc.GloasStepData.Conserves (D : GloasStepData (P := P) cfg ccfg bls) : Prop :=
  totalBuilderBalance D.postB + D.builderDebit = totalBuilderBalance D.preB + D.builderCredit

/-- The step's deposit loop registers a fresh record somewhere. -/
def _root_.Blanc.GloasStepData.Registers (D : GloasStepData (P := P) cfg ccfg bls) : Prop :=
  ∃ tr, builderDepositTrace ccfg bls D.postSlots D.block = .ok tr ∧ ¬ NoRegister ccfg bls tr D.builderDeposits

/-! ## The pending hypotheses (G3d, G3c) -/

/-- **Pending hypothesis (G3d: `FinalizedNotAhead`, B7 with registrations).** Every Gloas step of the run whose
deposit loop registers a fresh record conserves builder balance (`GloasStepData.Conserves`): G3d's extension of
`GStepView.builder_total_noRegister` to the general step, from `FinalizedNotAhead` at the step's pre-state (a fresh
record keeps its trace balance to the post-state). -/
def RegisteringStepsConserve {s₀ s : GJointState P} (run : GJointRun cfg ccfg bls s₀ s) : Prop :=
  ∀ {j : Nat} {D : GloasStepData (P := P) cfg ccfg bls}, run.steps[j]? = some (.gloas D) → D.Registers →
    D.Conserves

/-- **Pending hypothesis (G3c: the crossing's first-block frames, O-a's balance part).** The first Gloas block of
the run's crossing step keeps total builder balance: the crossing's post-state has the upgraded state's total. -/
def CrossingBalanceKept {s₀ s : GJointState P} (run : GJointRun cfg ccfg bls s₀ s) : Prop :=
  ∀ {j : Nat} {C : CrossingData (P := P) cfg ccfg bls}, run.steps[j]? = some (.crossing C) →
    totalBuilderBalance C.postB = totalBuilderBalance C.upgraded

namespace ValidJointG

variable {checkpoint : BlockChain} {anchor final : GJointState P}

/-! ## Separation -/

/-- **B7 separation at a Gloas step of a valid joint chain.** Every state of the deposit and exit traces (read at
the step's post-slots state) keeps the validators, validator balances, `pending_deposits` and both builder queues of
the first deposit-trace state, whose builders are the post-slots state's; the post-slots state keeps the pre-state's
builders; the parent settlement leaves the builders of the end of the exit trace, the header keeps them, and
`process_withdrawals` keeps every builder's pubkey and `withdrawable_epoch` and the registry's length, writing
builder balances only, up to the post-state's builders. -/
theorem builder_separation (_v : ValidJointG cfg ccfg bls checkpoint anchor final) {j : Nat}
    {D : GloasStepData (P := P) cfg ccfg bls} (_stepD : _v.run.steps[j]? = some (.gloas D)) :
    (∃ (trD trE : List (Gloas.BeaconState P)) (s0 : Gloas.BeaconState P),
      builderDepositTrace ccfg bls D.postSlots D.block = .ok trD ∧
      builderExitTrace ccfg bls D.postSlots D.block = .ok trE ∧ trD[0]? = some s0 ∧
      s0.builders = D.postSlots.builders ∧
      (∀ (k : Nat) (m : Gloas.BeaconState P), trD[k]? = some m → BuilderRequestFrame s0 m) ∧
      (∀ (k : Nat) (m : Gloas.BeaconState P), trE[k]? = some m → BuilderRequestFrame s0 m)) ∧
    D.postSlots.builders = D.preB.builders ∧
    ∃ (trD trE : List (Gloas.BeaconState P)) (s0 s1 s2 s3 : Gloas.BeaconState P),
      builderDepositTrace ccfg bls D.postSlots D.block = .ok trD ∧
      builderExitTrace ccfg bls D.postSlots D.block = .ok trE ∧
      trD[0]? = some s0 ∧ s0.builders = D.postSlots.builders ∧
      Gloas.processParentExecutionPayload (gloasCtx ccfg bls) D.postSlots D.block.message = .ok s1 ∧
      s1.builders = (traceLast D.postSlots trE).builders ∧ s2.builders = s1.builders ∧
      Gloas.processWithdrawals s2 = .ok s3 ∧ BuildersPkWe s2 s3 ∧ Inv.WFrame s2 s3 ∧
      D.postB.builders = s3.builders :=
  ⟨D.view.builderRequests_frame, D.view.builderWriters⟩

/-! ## Conservation per step -/

/-- **B7 conservation at a Gloas step that registers no fresh record**, with no pending hypothesis: MBS's
`GStepView.builder_total_noRegister`, its G3a premises from the anchor and the run (`gInv_pre`) and the N7 bounds at
the post-state. -/
theorem builder_total_step_noRegister (v : ValidJointG cfg ccfg bls checkpoint anchor final) {j : Nat}
    {D : GloasStepData (P := P) cfg ccfg bls} (stepD : v.run.steps[j]? = some (.gloas D))
    {trD : List (Gloas.BeaconState P)} (hD : builderDepositTrace ccfg bls D.postSlots D.block = .ok trD)
    (hno : NoRegister ccfg bls trD D.builderDeposits) : D.Conserves := by
  obtain ⟨-, g3, g4, g5, -, g7, g8, hA, fe⟩ := v.gInv_pre stepD
  obtain ⟨vb, bb⟩ := v.post_bounds stepD
  obtain ⟨ws, hws, heq⟩ := D.view.builder_total_noRegister v.quorumPositive v.slotsPerEpoch g5 g3 g4 g7 g8 fe hA
    vb bb hD hno
  have hsz := D.view.size_noRegister hD hno
  replace hws : stepWithdrawals ccfg bls D.postSlots D.block.message = .ok ws := hws
  unfold GloasStepData.Conserves GloasStepData.builderDebit GloasStepData.builderCredit
  rw [hws, hD]
  dsimp only
  rw [registeredTotal_of_noRegister _ _ hno, Nat.add_zero, hsz]
  exact heq

/-- **B7 conservation at every Gloas step of a valid joint chain**: total builder balance after the step plus the
builder debits of its `apply_withdrawals` equals the total before plus the deposits it credits. A step that
registers no fresh record needs nothing more (`builder_total_step_noRegister`); a registering step uses the pending
hypothesis `RegisteringStepsConserve` (G3d). -/
theorem builder_total_step (v : ValidJointG cfg ccfg bls checkpoint anchor final)
    (registering : RegisteringStepsConserve v.run) {j : Nat}
    {D : GloasStepData (P := P) cfg ccfg bls} (stepD : v.run.steps[j]? = some (.gloas D)) : D.Conserves := by
  obtain ⟨trD, -, hD, -, -⟩ := D.view.traces
  by_cases hno : NoRegister ccfg bls trD D.builderDeposits
  · exact v.builder_total_step_noRegister stepD hD hno
  · exact registering stepD ⟨trD, hD, hno⟩

/-! ## Conservation over the run -/

/-- Total builder balance of a joint state (none before Gloas). -/
def _root_.JauneConsensus.GJointState.totalBuilders : GJointState P → Nat
  | .pre _ => 0
  | .gloas b _ _ => totalBuilderBalance b

/-- A run step's builder debits: a Gloas step's; none otherwise. -/
def _root_.Blanc.GJointRunStep.builderDebit : GJointRunStep (P := P) cfg ccfg bls → Nat
  | .gloas D => D.builderDebit
  | _ => 0

/-- A run step's builder credits: a Gloas step's; at the crossing the fork term, the upgraded state's total (the
onboarding of `upgrade_to_gloas`); none before. -/
def _root_.Blanc.GJointRunStep.builderCredit : GJointRunStep (P := P) cfg ccfg bls → Nat
  | .pre _ => 0
  | .crossing C => totalBuilderBalance C.upgraded
  | .gloas D => D.builderCredit

/-- A run whose every step balances its total between its pre- and post-states balances the run's. -/
theorem _root_.Blanc.GJointRun.total_telescope {s₀ : GJointState P} (f : GJointState P → Nat)
    (d c : GJointRunStep (P := P) cfg ccfg bls → Nat) :
    {s : GJointState P} → (run : GJointRun cfg ccfg bls s₀ s) →
    (∀ C ∈ run.steps, f C.postState + d C = f C.preState + c C) →
    f s + (run.steps.map d).sum = f s₀ + (run.steps.map c).sum
  | _, .nil, _ => by simp only [GJointRun.steps, List.map_nil, List.sum_nil]
  | _, .snoc run C hC, h => by
    have ih := GJointRun.total_telescope f d c run fun C' hC' =>
      h C' (by rw [GJointRun.steps_snoc]; exact List.mem_append_left _ hC')
    have hs := h C (by rw [GJointRun.steps_snoc]; exact List.mem_append_right _ (List.mem_singleton_self _))
    rw [hC] at hs
    simp only [GJointRun.steps_snoc, List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    omega

/-- **B7 conservation over a valid joint chain.** Total builder balance at the run's end plus every builder debit
of the run's Gloas steps equals the total at the anchor plus every credit: the Gloas steps' deposits and the
crossing's fork term. Pending hypotheses: `RegisteringStepsConserve` (G3d) and `CrossingBalanceKept` (G3c). -/
theorem builder_total_run (v : ValidJointG cfg ccfg bls checkpoint anchor final)
    (registering : RegisteringStepsConserve v.run) (crossing : CrossingBalanceKept v.run) :
    final.totalBuilders + (v.run.steps.map GJointRunStep.builderDebit).sum =
      anchor.totalBuilders + (v.run.steps.map GJointRunStep.builderCredit).sum := by
  refine v.run.total_telescope _ _ _ fun C hC => ?_
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hC
  cases C with
  | pre D => rfl
  | crossing C =>
    show totalBuilderBalance C.postB + 0 = 0 + totalBuilderBalance C.upgraded
    rw [crossing hj]
    omega
  | gloas D => exact v.builder_total_step registering hj

end ValidJointG

end Blanc.Lift.BuilderRequest
