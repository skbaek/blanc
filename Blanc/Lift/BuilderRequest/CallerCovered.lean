import Blanc.Lift.BuilderRequest.Progress
import Blanc.Lift.BuilderRequest.Deposit.ChainLink
import Blanc.Lift.BuilderRequest.Exit.ChainLink

/-!
# Caller cover at covered forks for the builder contracts

At covered forks the request fold only holds the Prague general-purpose contracts, so no request
step targets either builder contract (`Linked.unlisted`, proved by `decide` in each contract's
`linked`). `KeptHistory.caller_ne` then leaves no gap: every frame a covered-fork history keeps at
either contract has a caller other than `SYSTEM`. Each kept frame therefore takes the user arm of
the covered-fork progress theorems in `Progress`, with the caller premise discharged here.
-/

namespace Blanc.Lift.BuilderRequest.CallerCovered

open Jaune ChainLink

variable {c : Delivery.Contract} {ty : UInt8}

/-- A covered fork's block issues no request step at the linked contract. -/
theorem covered_request_target_ne (L : Linked c ty) {cfg : ChainConfig} {b : KeptBlock}
    {post : BlockChain} (step : KeptStep cfg b post) (cov : CoveredFork b.fork) :
    ∀ s ∈ b.run.requests, s.target ≠ c.address := by
  intro s hs
  by_cases on : b.benv.stat.rules.header.requestsHash = true
  · have eq := step.body.contracts_eq on
    have mem : (s.type, s.target) ∈ b.benv.stat.rules.requests := by
      rw [eq]
      exact List.mem_map_of_mem hs
    have mem' : (s.type, s.target) ∈ (Fork.ruleSet b.fork).requests := mem
    exact (L.unlisted b.fork cov _ mem').2
  · have nil := step.body.requests_off on
    rw [nil] at hs
    cases hs

/-- Every frame a covered-fork history keeps at the linked contract has a caller other than SYSTEM. -/
theorem covered_caller_ne (L : Linked c ty) {cfg : ChainConfig} {start stop : BlockChain}
    {blocks : List KeptBlock} (h : KeptHistory cfg start blocks stop)
    (cover : ∀ b ∈ blocks, CoveredFork b.fork)
    (empty : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks)
    (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks) :
    ∀ f ∈ History.kept c.address blocks, f.sevm.caller ≠ systemAddress := by
  obtain ⟨outside, others, -⟩ := h.caller_ne (a := c.address) empty L.placed.beacon
    L.placed.history senders authorities creates
  intro f hf
  obtain ⟨b, hb, hfb⟩ := List.mem_flatMap.mp hf
  have split : KeptBlock.keptAt c.address b = b.run.outsideRequests c.address ++
      (requestRootsOf b.run.requests).flatMap (Root.keptAt c.address) := by
    unfold KeptBlock.keptAt BodyRun.roots BodyRun.outsideRequests
    rw [List.flatMap_append]
  rw [split] at hfb
  rcases List.mem_append.mp hfb with h1 | h2
  · exact outside b hb f h1
  · obtain ⟨r, hr, hfr⟩ := List.mem_flatMap.mp h2
    unfold requestRootsOf at hr
    obtain ⟨s, hs, hrs⟩ := List.mem_flatMap.mp hr
    obtain ⟨next, hstep⟩ := h.mem_step b hb
    have ne : s.target ≠ c.address := covered_request_target_ne L hstep (cover b hb) s hs
    exact others b hb s hs ne f (List.mem_flatMap.mpr ⟨r, hrs, hfr⟩)

/-- Every frame a covered-fork history keeps at the deposit contract has a caller other than SYSTEM. -/
theorem deposit_covered_caller_ne {cfg : ChainConfig} {start stop : BlockChain}
    {blocks : List KeptBlock} (h : KeptHistory cfg start blocks stop)
    (cover : ∀ b ∈ blocks, CoveredFork b.fork)
    (empty : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks)
    (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks) :
    ∀ f ∈ History.kept Deposit.contract.address blocks, f.sevm.caller ≠ systemAddress :=
  covered_caller_ne Deposit.linked h cover empty senders authorities creates

/-- Every frame a covered-fork history keeps at the exit contract has a caller other than SYSTEM. -/
theorem exit_covered_caller_ne {cfg : ChainConfig} {start stop : BlockChain}
    {blocks : List KeptBlock} (h : KeptHistory cfg start blocks stop)
    (cover : ∀ b ∈ blocks, CoveredFork b.fork)
    (empty : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks)
    (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks) :
    ∀ f ∈ History.kept Exit.contract.address blocks, f.sevm.caller ≠ systemAddress :=
  covered_caller_ne Exit.linked h cover empty senders authorities creates

/-- A kept deposit frame meeting the submission guards succeeds, at frame level. -/
theorem deposit_progress_submission_of_kept {cfg : ChainConfig} {start stop : BlockChain}
    {blocks : List KeptBlock} (h : KeptHistory cfg start blocks stop)
    (cover : ∀ b ∈ blocks, CoveredFork b.fork)
    (empty : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks)
    (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks) {f : Exec.Frame}
    (hf : f ∈ History.kept Deposit.contract.address blocks) {M : Mem} {G : Nat}
    {iterations : Nat} {finalOutput : B256} (fork : CoveredFork f.sevm.benvStat.fork)
    (hcode : f.sevm.code = Deposit.code) (hlen : f.sevm.data.length = 184)
    (dynamic : f.sevm.isStatic = false) (slack : gCallStipend < G)
    (off : f.pre.getStorVal f.sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 8 f.sevm f.pre) 17 1 17 0 iterations
      finalOutput)
    (admitted : Deposit.Admitted f.sevm (finalOutput / (17 : B256))) :
    Nonempty (Exec 0 f.sevm (St f.pre [] M (G + Deposit.submissionGas f.sevm f.pre M iterations))
      (.ok (Deposit.submissionPost f.sevm (feeBase f.sevm f.pre) M G))) :=
  BuilderRequest.progress_submission_covered hcode fork
    (deposit_covered_caller_ne h cover empty senders authorities creates f hf) hlen dynamic slack
    off wordRun admitted

/-- A kept deposit frame reading the fee with empty calldata and zero value succeeds, at frame level. -/
theorem deposit_progress_feeread_of_kept {cfg : ChainConfig} {start stop : BlockChain}
    {blocks : List KeptBlock} (h : KeptHistory cfg start blocks stop)
    (cover : ∀ b ∈ blocks, CoveredFork b.fork)
    (empty : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks)
    (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks) {f : Exec.Frame}
    (hf : f ∈ History.kept Deposit.contract.address blocks) {M : Mem} {G : Nat}
    {iterations : Nat} {finalOutput : B256} (fork : CoveredFork f.sevm.benvStat.fork)
    (aligned : M.size % 32 = 0) (hcode : f.sevm.code = Deposit.code)
    (zerodata : f.sevm.data = []) (zero : f.sevm.value = 0)
    (off : f.pre.getStorVal f.sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 8 f.sevm f.pre) 17 1 17 0 iterations
      finalOutput) :
    Nonempty (Exec 0 f.sevm
      (St f.pre [] M (G + UserPath.feeReadGas f.sevm f.pre M iterations))
      (.ok (RequestFee.feeGetterPost (feeBase f.sevm f.pre) M (finalOutput / (17 : B256)) G))) :=
  BuilderRequest.progress_feeread_covered hcode fork aligned
    (deposit_covered_caller_ne h cover empty senders authorities creates f hf) zerodata zero off
    wordRun

/-- A kept exit frame meeting the submission guards succeeds, at frame level. -/
theorem exit_progress_submission_of_kept {cfg : ChainConfig} {start stop : BlockChain}
    {blocks : List KeptBlock} (h : KeptHistory cfg start blocks stop)
    (cover : ∀ b ∈ blocks, CoveredFork b.fork)
    (empty : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks)
    (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks) {f : Exec.Frame}
    (hf : f ∈ History.kept Exit.contract.address blocks) {M : Mem} {G : Nat}
    {iterations : Nat} {finalOutput : B256} (fork : CoveredFork f.sevm.benvStat.fork)
    (hcode : f.sevm.code = Exit.code) (hlen : f.sevm.data.length = 48)
    (dynamic : f.sevm.isStatic = false) (slack : gCallStipend < G)
    (off : f.pre.getStorVal f.sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 2 f.sevm f.pre) 17 1 17 0 iterations
      finalOutput)
    (cov : (finalOutput / (17 : B256)).toNat ≤ f.sevm.value.toNat) :
    Nonempty (Exec 0 f.sevm (St f.pre [] M (G + Exit.submissionGas f.sevm f.pre M iterations))
      (.ok (Exit.submissionPost f.sevm (feeBase f.sevm f.pre) M G))) :=
  BuilderRequest.progress_submission_covered_exit hcode fork
    (exit_covered_caller_ne h cover empty senders authorities creates f hf) hlen dynamic slack off
    wordRun cov

/-- A kept exit frame reading the fee with empty calldata and zero value succeeds, at frame level. -/
theorem exit_progress_feeread_of_kept {cfg : ChainConfig} {start stop : BlockChain}
    {blocks : List KeptBlock} (h : KeptHistory cfg start blocks stop)
    (cover : ∀ b ∈ blocks, CoveredFork b.fork)
    (empty : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks)
    (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks) {f : Exec.Frame}
    (hf : f ∈ History.kept Exit.contract.address blocks) {M : Mem} {G : Nat}
    {iterations : Nat} {finalOutput : B256} (fork : CoveredFork f.sevm.benvStat.fork)
    (aligned : M.size % 32 = 0) (hcode : f.sevm.code = Exit.code)
    (zerodata : f.sevm.data = []) (zero : f.sevm.value = 0)
    (off : f.pre.getStorVal f.sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 2 f.sevm f.pre) 17 1 17 0 iterations
      finalOutput) :
    Nonempty (Exec 0 f.sevm
      (St f.pre [] M (G + UserPath.feeReadGas f.sevm f.pre M iterations))
      (.ok (RequestFee.feeGetterPost (feeBase f.sevm f.pre) M (finalOutput / (17 : B256)) G))) :=
  BuilderRequest.progress_feeread_covered_exit hcode fork aligned
    (exit_covered_caller_ne h cover empty senders authorities creates f hf) zerodata zero off
    wordRun

end Blanc.Lift.BuilderRequest.CallerCovered
