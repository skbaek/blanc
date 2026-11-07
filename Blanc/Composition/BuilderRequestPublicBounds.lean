import Blanc.Composition.BuilderRequestPublicObservers
import Blanc.Lift.BuilderRequest.Deposit.Delivery
import Blanc.Lift.BuilderRequest.Exit.Delivery
import Blanc.Lift.BuilderRequest.LoadBound

/-!
# Builder request contracts: public bounds and context

The griefing bounds (O31/O14/O29), fee dynamics (O18/O32), the loop-premise
elimination (O30), failure classification (O35), progress (O36) and deployment
(O1/O2). List form throughout; the history form of the load bound is open (see
`load_bound_history_open`). The exit-flood instances (O29) share the deposit
burst shape with no 1 ETH floor; the exit conjuncts below state it. Bridges are
`sorry` with `-- DRAFT:` notes.
-/

namespace Blanc.Composition.BuilderRequestPublic

open Jaune Blanc Blanc.Lift.BuilderRequest

/-- **Griefing bound, list form: the fee budget bounds the load.** Under a fee
budget below the wrap, over a clean history from deployed storage, the potential
of the end load is at most the natural-fee budget the submissions paid, so a fee
budget bounds the load and the queue length under any order of submissions and
system calls. -/
def load_bounded_by_fees : Prop :=
  (∀ {start stop : BlockChain} {blocks : List KeptBlock},
    DeployedStart start → HistoryClean blocks →
    depositFeeSum blocks < Backlog.cost 8 0 2893 →
    Backlog.cost 8 0 (storedLoad stop.state depositAddr) ≤ depositFeeSum blocks) ∧
  (∀ {start stop : BlockChain} {blocks : List KeptBlock},
    DeployedStart start → HistoryClean blocks →
    exitFeeSum blocks < Backlog.cost 2 0 2893 →
    Backlog.cost 2 0 (storedLoad stop.state exitAddr) ≤ exitFeeSum blocks)

/-- **Burst instances: the whole ether supply caps the backlog.** With
120,000,000 ETH in fees, deposits number at most 981 and exits at most 975;
at most 16 deposit calls, respectively 61 exit calls, drain the queue. -/
-- DRAFT: numbers are the master's Python, unproven here; prove or correct at compile.
def burst_instances : Prop :=
  Backlog.costEval 8 0 982 > 120000000 * 10 ^ 18 ∧
  Backlog.costEval 2 0 976 > 120000000 * 10 ^ 18 ∧
  (982 + 63) / 64 = 16 ∧ (976 + 15) / 16 = 61

/-- **The load bound over a history: open.** A kept-frame fee observer from
`f.pre`'s storage would keep the fee-only reading without the `history_chain`
existential; until it is written, the history corollary goes through the
frames the chain provides. -/
def load_bound_history_open : Prop := ∃ _ : True, True

/-- **Fee dynamics, list form: excess and count follow the submissions.** From
deployed storage, the end excess and count on either contract never exceed the
number of records submitted: the bytes only grow them by submission. -/
def fee_dynamics_follow_bytes : Prop :=
  (∀ {start stop : BlockChain} {blocks : List KeptBlock},
    DeployedStart start → HistoryClean blocks →
    storedExcess stop.state depositAddr ≤ (depositSubmitted blocks).length ∧
    storedCount stop.state depositAddr ≤ (depositSubmitted blocks).length) ∧
  (∀ {start stop : BlockChain} {blocks : List KeptBlock},
    DeployedStart start → HistoryClean blocks →
    storedExcess stop.state exitAddr ≤ (exitSubmitted blocks).length ∧
    storedCount stop.state exitAddr ≤ (exitSubmitted blocks).length)

/-- **Fee overhang after activation, list form: the drained quote is bounded.**
With the queue fully drained, the end excess is at most the number submitted;
the parametric per-call decay lives in the unit layer. -/
def fee_overhang_after_activation : Prop :=
  (∀ {start stop : BlockChain} {blocks : List KeptBlock} {n : Nat},
    DeployedStart start → HistoryClean blocks → (depositSubmitted blocks).length = n →
    storedCount stop.state depositAddr = 0 → storedExcess stop.state depositAddr ≤ n) ∧
  (∀ {start stop : BlockChain} {blocks : List KeptBlock} {n : Nat},
    DeployedStart start → HistoryClean blocks → (exitSubmitted blocks).length = n →
    storedCount stop.state exitAddr = 0 → storedExcess stop.state exitAddr ≤ n)

/-- **Loop premises eliminated: the fee window needs no `n` or `wordRun`.**
Where the stored excess is at most 2892, the iteration bound (at most 462)
comes out of the message, giving concrete gas numbers. -/
/-- One contract's fee window: at most 462 iterations where excess is at most 2892. -/
def loopBounded (code : ByteArray) (target : B256) : Prop :=
  ∀ {s : Sevm} {b : Devm} {n : Nat} {out : B256}, s.code = code →
    s.benvStat.fork = .amsterdam → (Blanc.Lift.BuilderRequest.storedExcess target s b).toNat ≤ 2892 →
    WordFakeExponential.Run (Blanc.Lift.BuilderRequest.storedExcess target s b) 17 1 17 0 n out →
    n ≤ 462

def loops_need_no_premise : Prop :=
  loopBounded Deposit.code 8 ∧ loopBounded Exit.code 2

/-- Dispatch failures at a contract under covered forks: inhibited and
bad-length frames revert. -/
def dispatchFails (code : ByteArray) (target : B256) (len : Nat) : Prop :=
  ∀ {s : Sevm} {b : Devm} {n : Nat} {out : B256}, s.code = code →
    ∀ _ : CoveredFork s.benvStat.fork, s.caller ≠ systemAddress →
    WordFakeExponential.Run (Blanc.Lift.BuilderRequest.storedExcess target s b) 17 1 17 0 n out →
    (b.getStorVal s.currentTarget 0 = B256.max → FrameReverts s b (revertBound 0)) ∧
    (s.data.length.toB256 ≠ len.toB256 → s.data.length.toB256 ≠ 0 →
      b.getStorVal s.currentTarget 0 ≠ B256.max → FrameReverts s b (revertBound n))

/-- Guard failures at a contract under covered forks: paid-read and
not-admitted frames revert. -/
def guardFails (code : ByteArray) (target : B256) (len : Nat)
    (admit : Bytes → B256 → B256 → Prop) : Prop :=
  ∀ {s : Sevm} {b : Devm} {n : Nat} {out : B256}, s.code = code →
    ∀ _ : CoveredFork s.benvStat.fork, s.caller ≠ systemAddress →
    WordFakeExponential.Run (Blanc.Lift.BuilderRequest.storedExcess target s b) 17 1 17 0 n out →
    (s.data = [] → s.value ≠ 0 → b.getStorVal s.currentTarget 0 ≠ B256.max →
      FrameReverts s b (revertBound n)) ∧
    (s.data.length = len → b.getStorVal s.currentTarget 0 ≠ B256.max →
      ¬ admit s.data s.value (out / (17 : B256)) → FrameReverts s b (revertBound n))

/-- Covered-fork failures at the deposit contract: inhibited, bad-length,
paid-read and not-admitted frames revert. -/
def depositCoveredFails : Prop :=
  dispatchFails Deposit.code 8 184 ∧ guardFails Deposit.code 8 184 Deposit.Admits

/-- Covered-fork failures at the exit contract: inhibited, bad-length,
paid-read and not-admitted frames revert. -/
def exitCoveredFails : Prop :=
  dispatchFails Exit.code 2 48 ∧ guardFails Exit.code 2 48 Exit.Admits

/-- **Failure classification at covered forks, frame form.** The reverting
frames at the forks that run today: inhibited, bad-length, paid-read and
not-admitted, by generalizing the Amsterdam proofs over the steps. No twins. -/
def covered_failures_classified : Prop := depositCoveredFails ∧ exitCoveredFails

/-- Deposit submission progress under covered forks. -/
def depositCoveredSubmit : Prop :=
  ∀ {sevm : Sevm} {b : Devm} {M : Mem} {G n : Nat} {out : B256},
    sevm.code = Deposit.code → ∀ _ : CoveredFork sevm.benvStat.fork,
    sevm.caller ≠ systemAddress → sevm.data.length = 184 → sevm.isStatic = false →
    gCallStipend < G → b.getStorVal sevm.currentTarget 0 ≠ B256.max →
    WordFakeExponential.Run (Blanc.Lift.BuilderRequest.storedExcess 8 sevm b) 17 1 17 0 n out →
    Deposit.Admitted sevm (out / (17 : B256)) →
    Nonempty (Exec 0 sevm (St b [] M (G + Deposit.submissionGas sevm b M n))
      (.ok (Deposit.submissionPost sevm (Deposit.feeBase sevm b) M G)))

/-- Deposit fee-read progress under covered forks. -/
def depositCoveredFeeRead : Prop :=
  ∀ {sevm : Sevm} {b : Devm} {M : Mem} {G n : Nat} {out : B256},
    sevm.code = Deposit.code → ∀ _ : CoveredFork sevm.benvStat.fork,
    M.size % 32 = 0 → sevm.caller ≠ systemAddress → sevm.data = [] → sevm.value = 0 →
    b.getStorVal sevm.currentTarget 0 ≠ B256.max →
    WordFakeExponential.Run (Blanc.Lift.BuilderRequest.storedExcess 8 sevm b) 17 1 17 0 n out →
    Nonempty (Exec 0 sevm (St b [] M (G + UserPath.feeReadGas sevm b M n))
      (.ok (RequestFee.feeGetterPost (Deposit.feeBase sevm b) M (out / (17 : B256)) G)))

/-- Deposit user-arm progress under covered forks: submissions and fee reads. -/
def depositCoveredProgress : Prop := depositCoveredSubmit ∧ depositCoveredFeeRead

/-- Deposit submission progress under Amsterdam. -/
def depositAmsterdamSubmit : Prop :=
  ∀ {sevm : Sevm} {b : Devm} {M : Mem} {G n : Nat} {out : B256},
    sevm.code = Deposit.code → sevm.benvStat.fork = .amsterdam →
    sevm.caller ≠ systemAddress → sevm.data.length = 184 → sevm.isStatic = false →
    gCallStipend < G → b.getStorVal sevm.currentTarget 0 ≠ B256.max →
    WordFakeExponential.Run (Blanc.Lift.BuilderRequest.storedExcess 8 sevm b) 17 1 17 0 n out →
    Deposit.Admitted sevm (out / (17 : B256)) →
    Nonempty (Exec 0 sevm (St b [] M (G + Deposit.submissionGasA sevm b M n))
      (.ok (Deposit.submissionPostA sevm (Deposit.feeBaseA sevm b) M
        (G + Deposit.submissionRepayA sevm b M))))

/-- Deposit fee-read progress under Amsterdam. -/
def depositAmsterdamFeeRead : Prop :=
  ∀ {sevm : Sevm} {b : Devm} {M : Mem} {G n : Nat} {out : B256},
    sevm.code = Deposit.code → sevm.benvStat.fork = .amsterdam →
    M.size % 32 = 0 → sevm.caller ≠ systemAddress → sevm.data = [] → sevm.value = 0 →
    b.getStorVal sevm.currentTarget 0 ≠ B256.max →
    WordFakeExponential.Run (Blanc.Lift.BuilderRequest.storedExcess 8 sevm b) 17 1 17 0 n out →
    Nonempty (Exec 0 sevm (St b [] M (G + UserPath.feeReadGas sevm b M n))
      (.ok (RequestFee.feeGetterPost (Deposit.feeBase sevm b) M (out / (17 : B256)) G)))

/-- Deposit user-arm progress under Amsterdam: submissions and fee reads. -/
def depositAmsterdamProgress : Prop := depositAmsterdamSubmit ∧ depositAmsterdamFeeRead

/-- Exit submission progress under covered forks. -/
def exitCoveredSubmit : Prop :=
  ∀ {sevm : Sevm} {b : Devm} {M : Mem} {G n : Nat} {out : B256},
    sevm.code = Exit.code → ∀ _ : CoveredFork sevm.benvStat.fork,
    sevm.caller ≠ systemAddress → sevm.data.length = 48 → sevm.isStatic = false →
    gCallStipend < G → b.getStorVal sevm.currentTarget 0 ≠ B256.max →
    WordFakeExponential.Run (Blanc.Lift.BuilderRequest.storedExcess 2 sevm b) 17 1 17 0 n out →
    (out / (17 : B256)).toNat ≤ sevm.value.toNat →
    Nonempty (Exec 0 sevm (St b [] M (G + Exit.submissionGas sevm b M n))
      (.ok (Exit.submissionPost sevm (Exit.feeBase sevm b) M G)))

/-- Exit fee-read progress under covered forks. -/
def exitCoveredFeeRead : Prop :=
  ∀ {sevm : Sevm} {b : Devm} {M : Mem} {G n : Nat} {out : B256},
    sevm.code = Exit.code → ∀ _ : CoveredFork sevm.benvStat.fork,
    M.size % 32 = 0 → sevm.caller ≠ systemAddress → sevm.data = [] → sevm.value = 0 →
    b.getStorVal sevm.currentTarget 0 ≠ B256.max →
    WordFakeExponential.Run (Blanc.Lift.BuilderRequest.storedExcess 2 sevm b) 17 1 17 0 n out →
    Nonempty (Exec 0 sevm (St b [] M (G + UserPath.feeReadGas sevm b M n))
      (.ok (RequestFee.feeGetterPost (Exit.feeBase sevm b) M (out / (17 : B256)) G)))

/-- Exit user-arm progress under covered forks: submissions and fee reads. -/
def exitCoveredProgress : Prop := exitCoveredSubmit ∧ exitCoveredFeeRead

/-- Exit submission progress under Amsterdam. -/
def exitAmsterdamSubmit : Prop :=
  ∀ {sevm : Sevm} {b : Devm} {M : Mem} {G n : Nat} {out : B256},
    sevm.code = Exit.code → sevm.benvStat.fork = .amsterdam →
    sevm.caller ≠ systemAddress → sevm.data.length = 48 → sevm.isStatic = false →
    gCallStipend < G → b.getStorVal sevm.currentTarget 0 ≠ B256.max →
    WordFakeExponential.Run (Blanc.Lift.BuilderRequest.storedExcess 2 sevm b) 17 1 17 0 n out →
    (out / (17 : B256)).toNat ≤ sevm.value.toNat →
    Nonempty (Exec 0 sevm (St b [] M (G + Exit.submissionGasA sevm b M n))
      (.ok (Exit.submissionPostA sevm (Exit.feeBaseA sevm b) M
        (G + Exit.submissionRepayA sevm b M))))

/-- Exit fee-read progress under Amsterdam. -/
def exitAmsterdamFeeRead : Prop :=
  ∀ {sevm : Sevm} {b : Devm} {M : Mem} {G n : Nat} {out : B256},
    sevm.code = Exit.code → sevm.benvStat.fork = .amsterdam →
    M.size % 32 = 0 → sevm.caller ≠ systemAddress → sevm.data = [] → sevm.value = 0 →
    b.getStorVal sevm.currentTarget 0 ≠ B256.max →
    WordFakeExponential.Run (Blanc.Lift.BuilderRequest.storedExcess 2 sevm b) 17 1 17 0 n out →
    Nonempty (Exec 0 sevm (St b [] M (G + UserPath.feeReadGas sevm b M n))
      (.ok (RequestFee.feeGetterPost (Exit.feeBase sevm b) M (out / (17 : B256)) G)))

/-- Exit user-arm progress under Amsterdam: submissions and fee reads. -/
def exitAmsterdamProgress : Prop := exitAmsterdamSubmit ∧ exitAmsterdamFeeRead

/-- **Progress, frame form, by arm.** A user-arm frame at either code with stated
gas and value succeeds when its caller is not the system address, under covered
forks and under Amsterdam. The system arm under Amsterdam is proved at the unit
layer and not restated here. -/
def frames_progress_by_arm : Prop :=
  depositCoveredProgress ∧ depositAmsterdamProgress ∧
  exitCoveredProgress ∧ exitAmsterdamProgress

/-- **Deployment, anchored form: the mainnet bytes at the EIP's addresses.**
The factory's CREATE2 addresses compute in Lean to the EIP's addresses, and the
deployed storage is zeroed for deposits and inhibited for exits. -/
def deployment_installed : Prop :=
  Deposit.Creation.address = 0x0000bff46984e3725691fa540a8c7589300d8282 ∧
  Exit.Creation.address = 0x000064d678505ad48f8ccb093bc65613800e8282 ∧
  (Stor.empty.get 0).toNat = 0 ∧ Exit.deployedStorage.get 0 = B256.max

/-! ## Bridges -/

/-- The load bound, from the potential induction. -/
theorem load_bound_bridge : load_bounded_by_fees := by
  -- DRAFT: `LoadBound.potential_le` over the `Chain` gives
  -- `Φ (load end) ≤ Φ (load start) + fees`; `queue_length_le_load` turns load
  -- into queue length. Needs `Backlog.fee_pos`, `Backlog.cost_strictMono` and
  -- the `fakeExp_mono` induction (still `sorry` in LoadBound.lean: no
  -- monotonicity lemma for `fakeExp` was found; check the Jaune pin first).
  sorry

/-- The burst instances, from the evaluated cost. -/
theorem burst_bridge : burst_instances := by
  -- DRAFT: `Backlog.costEval_eq` with `feeEval_eq` (Flood.lean) evaluates the
  -- potential; `budget_cannot_reach` turns a budget below `Φ n` into `n` out
  -- of reach. The master's Python numbers are proved here or corrected.
  sorry

/-- The fee overhang, from excess replay. -/
theorem overhang_bridge : fee_overhang_after_activation := by
  -- DRAFT: `replay_calls_excess` (Delivery.lean) and `prefork_then_calls`
  -- (Deposit/Delivery.lean) give excess `n - 8k` with no later submissions;
  -- the quote is `fakeExp 1 (max 0 (n - 8k)) 17` by `Frame.quote_natural`.
  sorry

/-- Fee dynamics, from the replay and step lemmas. -/
theorem dynamics_bridge : fee_dynamics_follow_bytes := by
  -- DRAFT: `load_replay` and `step_count_le`/`step_excess_lt`
  -- (Delivery.lean): submissions add at most one each, drains never add.
  sorry

/-- Loop premises eliminated, from the generalized fee window. -/
theorem loops_bridge : loops_need_no_premise := by
  -- DRAFT: W18's draft proves the witness and the ≤ 462 bound from the
  -- message; this run did not read it, so the route is unconfirmed.
  sorry

/-- Covered failure classification, from the generalized steps. -/
theorem covered_failures_bridge : covered_failures_classified := by
  -- DRAFT: `frameReverts_*_covered` (RevertCovered.lean). The not-admitted
  -- arms are still `sorry` there: the guard-tail walks must be generalized
  -- over `(v : l.Valid)` in each contract's `Revert.lean`, not copied as
  -- twins (see the file's status note).
  sorry

/-- User-arm progress, from the submission and fee-read walks. -/
theorem progress_bridge : frames_progress_by_arm := by
  -- DRAFT: `progress_submission_covered`, `progress_feeread_covered`,
  -- `progress_submission_amsterdam`, `progress_feeread_amsterdam` and the exit
  -- analogues (Progress.lean); the system arm under Amsterdam is proved there
  -- and not restated in the headline.
  sorry

/-- Deployment, from the creation certificates. -/
theorem deployment_bridge : deployment_installed := by
  -- DRAFT: the address equations compute from the recorded salt and init code
  -- (Creation certs); the storage shape is `deployed_represents` for each
  -- contract. The Safe-route observation gap is recorded in the goal, not here.
  sorry

end Blanc.Composition.BuilderRequestPublic
