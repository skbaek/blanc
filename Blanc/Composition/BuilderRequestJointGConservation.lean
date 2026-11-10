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
  premises from RBA's `ValidJointG.gInv_pre` and the N7 bounds; a registering step is G3d's `GStepView.builder_total`
  under FinalizedNotAhead along the run (`ValidJointG.fna_pre`), its credit term bridged by `builderCreditsAll_split`.
* **Conservation over the run** (`ValidJointG.builder_total_run`): summed over the run, with the crossing's fork term
  (the upgraded state's total, `upgrade_to_gloas`'s onboarding), the first block keeping the upgraded builders
  exactly (G3c's `crossing_builders_eq`, `ValidJointG.crossingBalanceKept`).
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

/-! ## The step-level conservation facts (G3d, G3c), discharged below -/

/-- **G3d: B7 with registrations** (discharged: `ValidJointG.registeringStepsConserve`). Every Gloas step of
the run whose deposit loop registers a fresh record conserves builder balance (`GloasStepData.Conserves`): G3d's extension of
`GStepView.builder_total_noRegister` to the general step, from `FinalizedNotAhead` at the step's pre-state (a fresh
record keeps its trace balance to the post-state). -/
def RegisteringStepsConserve {s₀ s : GJointState P} (run : GJointRun cfg ccfg bls s₀ s) : Prop :=
  ∀ {j : Nat} {D : GloasStepData (P := P) cfg ccfg bls}, run.steps[j]? = some (.gloas D) → D.Registers →
    D.Conserves

/-- **G3c: the crossing's first-block frames, O-a's balance part** (discharged:
`ValidJointG.crossingBalanceKept`). The first Gloas block of the run's crossing step keeps total builder balance: the crossing's post-state has the upgraded state's total. -/
def CrossingBalanceKept {s₀ s : GJointState P} (run : GJointRun cfg ccfg bls s₀ s) : Prop :=
  ∀ {j : Nat} {C : CrossingData (P := P) cfg ccfg bls}, run.steps[j]? = some (.crossing C) →
    totalBuilderBalance C.postB = totalBuilderBalance C.upgraded

/-! ## Discharging `RegisteringStepsConserve` (G3d's `GStepView.builder_total`) -/

/-- The registration amounts credited to slot `i` along a deposit trace. -/
def registeredAt (ccfg : Config) (bls : Bool) (i : Nat) :
    List (Gloas.BeaconState P) → List Gloas.BuilderDepositRequest → Nat
  | m :: tr, r :: rs =>
    (match classifyBuilderDeposit ccfg bls m r with
      | .ok (.register j a) => if j = i then a.toNat else 0
      | _ => 0) + registeredAt ccfg bls i tr rs
  | _, _ => 0

/-- The credits with registrations are the top-ups plus the registrations, slot by slot. -/
theorem creditedAllAt_split (i : Nat) :
    ∀ (tr : List (Gloas.BeaconState P)) (rs : List Gloas.BuilderDepositRequest),
      creditedAllAt ccfg bls i tr rs = creditedAt ccfg bls i tr rs + registeredAt ccfg bls i tr rs
  | [], _ => by simp only [creditedAllAt, creditedAt, registeredAt, add_zero]
  | _ :: _, [] => by simp only [creditedAllAt, creditedAt, registeredAt, add_zero]
  | m :: tr, r :: rs => by
    have ih := creditedAllAt_split i tr rs
    simp only [creditedAllAt, creditedAt, registeredAt]
    cases classifyBuilderDeposit ccfg bls m r with
    | error _ => simp only []; omega
    | ok o =>
      cases o <;> simp only [depositCreditAll, depositCredit] <;> omega

theorem sum_range_ite_eq (j a : Nat) :
    ∀ n, ((List.range n).map (fun i => if j = i then a else 0)).sum = if j < n then a else 0
  | 0 => by simp only [List.range_zero, List.map_nil, List.sum_nil, not_lt_zero, ↓reduceIte]
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_range_ite_eq j a n]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases h1 : j < n
    · have h2 : j < n + 1 := by omega
      have h3 : j ≠ n := by omega
      simp only [h1, ↓reduceIte, h3, add_zero, h2]
    · by_cases h3 : j = n
      · subst h3; simp only [lt_self_iff_false, ↓reduceIte, zero_add, lt_add_iff_pos_right, zero_lt_one]
      · have h2 : ¬ j < n + 1 := by omega
        simp only [h1, ↓reduceIte, h3, add_zero, h2]

theorem sum_range_add (f g : Nat → Nat) (n : Nat) :
    ((List.range n).map (fun i => f i + g i)).sum =
      ((List.range n).map f).sum + ((List.range n).map g).sum := by
  induction n with
  | zero => simp only [List.range_zero, List.map_nil, List.sum_nil, add_zero]
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.sum_append, ih, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    omega

/-- Summed over a registry covering every registered index, the registration credits are
`registeredTotal`. -/
theorem sum_registeredAt (n : Nat) :
    ∀ (tr : List (Gloas.BeaconState P)) (rs : List Gloas.BuilderDepositRequest),
      (∀ (k : Nat) (m : Gloas.BeaconState P) (r : Gloas.BuilderDepositRequest) (j : Nat) (a : U64),
        tr[k]? = some m → rs[k]? = some r →
        classifyBuilderDeposit ccfg bls m r = .ok (.register j a) → j < n) →
      ((List.range n).map (fun i => registeredAt ccfg bls i tr rs)).sum = registeredTotal ccfg bls tr rs
  | [], _, _ => by simp only [registeredAt, List.map_const', List.length_range, List.sum_replicate,
      nsmul_zero, registeredTotal]
  | _ :: _, [], _ => by simp only [registeredAt, List.map_const', List.length_range, List.sum_replicate,
      nsmul_zero, registeredTotal]
  | m :: tr, r :: rs, hreg => by
    have ih := sum_registeredAt n tr rs (fun k m' r' j a h1 h2 h3 => hreg (k + 1) m' r' j a h1 h2 h3)
    simp only [registeredAt, registeredTotal]
    rw [sum_range_add, ih]
    cases hc : classifyBuilderDeposit ccfg bls m r with
    | error _ => simp only [List.map_const', List.length_range, List.sum_replicate, nsmul_zero, zero_add]
    | ok o =>
      cases o with
      | register j a =>
        have hj := hreg 0 m r j a rfl rfl hc
        simp only []
        simp only [sum_range_ite_eq j a.toNat n, hj, ↓reduceIte]
      | _ => simp only [List.map_const', List.length_range, List.sum_replicate, nsmul_zero, zero_add]

/-- `builderCreditsAll` is the top-up credits plus the registration amounts, given every registered index is a
slot of the registry. -/
theorem builderCreditsAll_split {tr : List (Gloas.BeaconState P)} {rs : List Gloas.BuilderDepositRequest} {n : Nat}
    (hreg : ∀ (k : Nat) (m : Gloas.BeaconState P) (r : Gloas.BuilderDepositRequest) (j : Nat) (a : U64),
      tr[k]? = some m → rs[k]? = some r →
      classifyBuilderDeposit ccfg bls m r = .ok (.register j a) → j < n) :
    builderCreditsAll ccfg bls tr rs n = builderCredits ccfg bls tr rs n + registeredTotal ccfg bls tr rs := by
  unfold builderCreditsAll builderCredits
  simp only [creditedAllAt_split]
  rw [sum_range_add, sum_registeredAt n tr rs hreg]

namespace ValidJointG

variable {checkpoint : BlockChain} {anchor final : GJointState P}

/-- A builder registered at a Gloas step of a valid joint chain is a slot of the step's post-state registry (the
fresh record survives the rest of the block, G3d's `GStepView.fresh_survives`). -/
theorem registered_lt (v : ValidJointG cfg ccfg bls checkpoint anchor final) {j : Nat}
    {D : GloasStepData (P := P) cfg ccfg bls} (stepD : v.run.steps[j]? = some (.gloas D))
    {trD : List (Gloas.BeaconState P)} (hD : builderDepositTrace ccfg bls D.postSlots D.block = .ok trD)
    {k : Nat} {m : Gloas.BeaconState P} {r : Gloas.BuilderDepositRequest} {i : Nat} {a : U64}
    (hm : trD[k]? = some m) (hr : D.builderDeposits[k]? = some r)
    (hcl : classifyBuilderDeposit ccfg bls m r = .ok (.register i a)) :
    i < D.postB.builders.toArray.size := by
  obtain ⟨-, g3, g4, g5, -, g7, g8, hA, fe⟩ := v.gInv_pre stepD
  obtain ⟨vb, bb⟩ := v.post_bounds stepD
  obtain ⟨s0, -, hsD⟩ := builderDepositTrace_scan hD
  have htl : traceLast s0 trD = traceLast D.postSlots trD :=
    traceLast_ne_nil (scanM_ok_ne_nil hsD) s0 D.postSlots
  obtain ⟨m1, m1', hm1, hm1', hcall⟩ := scanM_ok_step hsD k r hr
  rw [hm] at hm1; cases hm1
  have hrest := scanM_ok_drop _ (k + 1) hsD hm1'
  obtain ⟨addr, e, bal, -, he, -, hat2, -⟩ :=
    register_then_topUp v.slotsPerEpoch (ctx := { cfg := ccfg, blsActive := bls }) hcl hcall hrest
  rw [htl] at hat2
  obtain ⟨hpostR, -⟩ := D.view.fresh_survives v.slotsPerEpoch v.quorumPositive (v.fna_pre stepD) g5 g3 g4 g7
    g8 fe hA vb bb hD hm hr hcl he hat2 rfl rfl
  exact (Array.getElem?_eq_some_iff.mp hpostR).1

/-- **`RegisteringStepsConserve`, discharged** (G3d's `GStepView.builder_total`, under FinalizedNotAhead along the
run, `fna_pre`): every Gloas step of a valid joint chain conserves builder balance, registering or not. -/
theorem registeringStepsConserve (v : ValidJointG cfg ccfg bls checkpoint anchor final) :
    RegisteringStepsConserve v.run := by
  intro j D stepD _
  obtain ⟨trD, -, hD, -, -⟩ := D.view.traces
  obtain ⟨-, g3, g4, g5, -, g7, g8, hA, fe⟩ := v.gInv_pre stepD
  obtain ⟨vb, bb⟩ := v.post_bounds stepD
  obtain ⟨ws, hws, heq⟩ := D.view.builder_total v.quorumPositive v.slotsPerEpoch (v.fna_pre stepD) g5 g3 g4 g7
    g8 fe hA vb bb hD
  replace hws : stepWithdrawals ccfg bls D.postSlots D.block.message = .ok ws := hws
  replace hD : builderDepositTrace ccfg bls D.postSlots D.block = .ok trD := hD
  unfold GloasStepData.Conserves GloasStepData.builderDebit GloasStepData.builderCredit
  rw [hws, hD]
  dsimp only
  rw [← builderCreditsAll_split (fun k m r i a hm hr hcl => v.registered_lt stepD hD hm hr hcl)]
  exact heq

/-- **`CrossingBalanceKept`, discharged** (G3c's `crossing_builders_eq`): the crossing's post-state has exactly
the upgraded state's builders, so the same total. -/
theorem crossingBalanceKept (v : ValidJointG cfg ccfg bls checkpoint anchor final) :
    CrossingBalanceKept v.run := by
  intro j C stepC
  have hmem : (GJointRunStep.crossing C).postState ∈ v.run.states :=
    List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_of_getElem? stepC))
  have hb := (C.builders_eq v.quorumPositive v.slotsPerEpoch (v.validatorsBound _ hmem)
    (v.buildersBound _ hmem)).1
  unfold totalBuilderBalance
  rw [hb]

end ValidJointG

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
registers no fresh record needs nothing more (`builder_total_step_noRegister`); a registering step uses G3d's
`GStepView.builder_total` under FinalizedNotAhead (`registeringStepsConserve`). -/
theorem builder_total_step (v : ValidJointG cfg ccfg bls checkpoint anchor final) {j : Nat}
    {D : GloasStepData (P := P) cfg ccfg bls} (stepD : v.run.steps[j]? = some (.gloas D)) : D.Conserves := by
  obtain ⟨trD, -, hD, -, -⟩ := D.view.traces
  by_cases hno : NoRegister ccfg bls trD D.builderDeposits
  · exact v.builder_total_step_noRegister stepD hD hno
  · exact v.registeringStepsConserve stepD ⟨trD, hD, hno⟩

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
crossing's fork term (the crossing keeps the upgraded state's builders exactly, `crossingBalanceKept`). -/
theorem builder_total_run (v : ValidJointG cfg ccfg bls checkpoint anchor final) :
    final.totalBuilders + (v.run.steps.map GJointRunStep.builderDebit).sum =
      anchor.totalBuilders + (v.run.steps.map GJointRunStep.builderCredit).sum := by
  refine v.run.total_telescope _ _ _ fun C hC => ?_
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hC
  cases C with
  | pre D => rfl
  | crossing C =>
    show totalBuilderBalance C.postB + 0 = 0 + totalBuilderBalance C.upgraded
    rw [v.crossingBalanceKept hj]
    omega
  | gloas D => exact v.builder_total_step hj

end ValidJointG

end Blanc.Lift.BuilderRequest
