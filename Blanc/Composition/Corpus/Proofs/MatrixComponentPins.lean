import Blanc.Lift.BeaconDeposit.HistDeployment
import Blanc.Composition.ConsolidationRequestPublicHeadlines
import Blanc.Composition.BuilderRequestPublicGuarantees
import Blanc.Composition.BuilderRequestPublicFindings
import Blanc.Composition.BuilderRequestPublicBounds
import Blanc.Composition.BuilderRequestFocusedHeadlines
import Blanc.Lift.BuilderRequest.Deposit.SystemCall
import Blanc.Lift.BuilderRequest.Exit.SystemCall
import Blanc.Lift.WithdrawalRequest.HeadlineFee
import Blanc.Lift.WithdrawalRequest.SubmissionBody
import Blanc.Lift.WithdrawalRequest.FeeGetter
import Blanc.Lift.WithdrawalRequest.AmsterdamSystem
import Blanc.Lift.SystemExecution.ConsolidationRequest.AmsterdamSystem
import Blanc.Composition.RequestPhaseAmsterdam
import Blanc.RequestFeeWordBound

/-!
# Distinct G3 component theorems, `W-S5` first divergence, `B-S5` fee domain, and `D-S3` attribution

Goal `protocol-contract-corpus-v1` (rev 6, §14, Wave 3):

1. **`W-S5 / first-divergence`** (`w_s5_first_divergence`): proves exactness on `excess < 2893`
   (`≤ 462` iterations) and strict under-quoting `WordFee output < SpecFee excess` at `excess = 2893`.
2. **`C-S5 / fee-domain`** (`c_s5_fee_domain`): combines `NoWrapDomain` characterization, exactness on
   `excess ≤ 2892`, and universal `quotedFee ≤ SpecFee` upper bound.
3. **`D-S3` recurrence attribution** (`d_s3_omission_breaks_count`): proves from `beacon_deposits`
   that omitting or replaying any committed deposit strictly falsifies `depositCount d.trace`.
4. **Distinct per-side `B` component theorems** (`b_s1_*`, `b_s3_*`, `b_s5_*`, `b_s6_*`, `b_s7_*`,
   `b_s10_*`, plus `b_s9_registration_authorization_credit`, `w_s7_headline`, `c_s7_headline`,
   `w_s10_headline`, `c_s10_headline`).

No `variable` declarations are opened in this file so every theorem has explicit binders only.
-/

namespace Blanc.Composition.Corpus.Proofs.MatrixComponentPins

open Jaune JauneConsensus ExecutionTrace Blanc JauneConsensus.Facts.Gloas
open Blanc.Lift
open Blanc.Lift.BuilderRequest
open ChainLink
open Blanc.Composition.BuilderRequestPublic

/-! ## Section 1: `W-S5 / first-divergence`, `C-S5`, and `D-S3` recurrence attribution -/

/-- **`W-S5 / first-divergence`.** Through excess 2892 (`excess.toNat < 2893`), every executed
word fee-loop trace agrees with `WithdrawalRequest.SpecFee excess` within 462 iterations; at
`excess = 2893`, a run exists (`word_run_2893`) and every executed word trace strictly under-quotes
`WithdrawalRequest.SpecFee excess`. -/
theorem w_s5_first_divergence :
    (∀ {excess : B256} {iterations : Nat} {output : B256},
      excess.toNat < 2893 →
      WordFakeExponential.Run excess 17 1 17 0 iterations output →
      WithdrawalRequest.WordFee output = WithdrawalRequest.SpecFee excess ∧
        iterations ≤ 462) ∧
    (∃ iterations output,
      WordFakeExponential.Run (2893 : Nat).toB256 17 1 17 0 iterations output) ∧
    (∀ {excess : B256} {iterations : Nat} {output : B256},
      excess.toNat = 2893 →
      WordFakeExponential.Run excess 17 1 17 0 iterations output →
      WithdrawalRequest.WordFee output < WithdrawalRequest.SpecFee excess) := by
  refine ⟨?_, ⟨_, _, RequestFeeWord.word_run_2893⟩, ?_⟩
  · intro excess iterations output hlt hrun
    obtain ⟨n, out, hn, hrun', hv, -⟩ := RequestFeeWord.fee_run (e := excess) (by omega)
    obtain ⟨rfl, rfl⟩ := hrun.deterministic hrun'
    exact ⟨hv, hn⟩
  · intro excess iterations output heq hrun
    have hle := WithdrawalRequest.fee_le_spec hrun
    have hb256 : excess = (2893 : Nat).toB256 := by
      rw [← heq, toB256_toNat]
    subst hb256
    have hne := RequestFeeWord.word_fee_ne_natural_2893 hrun
    unfold WithdrawalRequest.WordFee WithdrawalRequest.SpecFee at hle ⊢
    rw [B256.toNat_toB256_of_lt (by decide)]
    rw [B256.toNat_toB256_of_lt (by decide)] at hle
    exact Nat.lt_of_le_of_ne hle hne

/-- **`C-S5 / fee-domain` combined wrapper.** Exact `NoWrapDomain` characterization
(`ConsolidationRequest.fee_eq_spec_iff`), exact fee equality on `excess ≤ 2892`, and universal
`quotedFee ≤ SpecFee` upper bound on all words. -/
theorem c_s5_fee_domain :
    (∀ {excess : B256} {iterations : Nat} {output : B256},
      WordFakeExponential.Run excess 17 1 17 0 iterations output →
      (Blanc.Lift.ConsolidationRequest.WordFee output =
        Blanc.Lift.ConsolidationRequest.SpecFee excess ↔
        RequestFeeWord.NoWrapDomain excess iterations)) ∧
    (∀ {excess : B256}, excess.toNat ≤ 2892 →
      Blanc.Composition.ConsolidationRequestPublic.quotedFee excess =
        Blanc.Composition.ConsolidationRequestPublic.SpecFee excess) ∧
    (∀ excess : B256,
      Blanc.Composition.ConsolidationRequestPublic.quotedFee excess ≤
        Blanc.Composition.ConsolidationRequestPublic.SpecFee excess) :=
  ⟨fun hrun => Blanc.Lift.ConsolidationRequest.fee_eq_spec_iff hrun,
   fun h => Blanc.Composition.ConsolidationRequestPublic.fee_eq_spec_of_le h,
   Blanc.Composition.ConsolidationRequestPublic.fee_le_spec⟩

/-- **`D-S3` recurrence count attribution (`d_s3_omission_breaks_count`).** Over any deployment
history `d : BeaconDeploymentTo B`, `depositCount d.trace` equals the exact committed-deposit count,
so omitting any committed deposit (`xs ++ ys` vs `xs ++ x :: ys`), replaying any committed deposit
(`xs ++ x :: x :: ys`), or substituting any list of different length strictly falsifies `depositCount`. -/
theorem d_s3_omission_breaks_count {B : BlockChain} (d : BeaconDeposit.BeaconDeploymentTo B) :
    BeaconDeposit.depositCount d.trace = (BeaconDeposit.committedDeposits d.trace).length ∧
      (∀ {xs ys : List B256} {x : B256},
        BeaconDeposit.committedDeposits d.trace = xs ++ x :: ys →
        BeaconDeposit.depositCount d.trace ≠ (xs ++ ys).length) ∧
      (∀ {xs ys : List B256} {x : B256},
        BeaconDeposit.committedDeposits d.trace = xs ++ x :: ys →
        BeaconDeposit.depositCount d.trace ≠ (xs ++ x :: x :: ys).length) ∧
      (∀ {candidate : List B256},
        candidate.length ≠ (BeaconDeposit.committedDeposits d.trace).length →
        BeaconDeposit.depositCount d.trace ≠ candidate.length) := by
  have hcount := (BeaconDeposit.beacon_deposits d).1
  refine ⟨hcount, ?_, ?_, ?_⟩
  · intro xs ys x hsplit
    rw [hcount, hsplit, List.length_append, List.length_cons, List.length_append]
    omega
  · intro xs ys x hsplit
    rw [hcount, hsplit, List.length_append, List.length_cons, List.length_append,
      List.length_cons, List.length_cons]
    omega
  · intro candidate hne
    rw [hcount]
    exact hne.symm

/-! ## Section 2: Per-side `B` component theorems (`B-S1`, `B-S3`, `B-S5`, `B-S6`, `B-S7`, `B-S9`, `B-S10`) -/

/-- **`B-S1 / deposit`.** At the end of every `CodesKept` history, the builder deposit contract's
Amsterdam checked system call with empty calldata succeeds from arbitrary storage with exact
`sysState` post-state and within `888,000` regular gas. -/
theorem b_s1_deposit :
    ∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock},
      CodesKept cfg start blocks stop → ∀ benv : Benv,
        benv.state = stop.state → benv.stat.fork = .amsterdam →
        ∃ out, processCheckedSystemTransaction benv depositAddr [] =
            .ok (Blanc.Lift.RequestSystem.sysState Deposit.sysShape benv.state depositAddr, out) ∧
          Blanc.Lift.RequestSystem.RegularGasWithin out.gasLeft 888000 := by
  intro cfg start stop blocks hcodes benv hstate hfork
  have hdep : start.state.getCode depositAddr = Deposit.code := hcodes.deposit
  have nedep : (start.state.getCode depositAddr).toList ≠ [] := by
    rw [hdep]
    decide +kernel
  have nddep : ¬ isValidDelegation (start.state.getCode depositAddr) := by
    rw [hdep]
    decide +kernel
  obtain ⟨-, cdep⟩ := hcodes.linked.chain nedep nddep
  have hinstD : benv.state.getCode depositAddr = Deposit.code := by
    rw [hstate, cdep]
    exact hdep
  exact Deposit.system_call_state hfork hinstD

/-- **`B-S1 / exit`.** At the end of every `CodesKept` history, the builder exit contract's
Amsterdam checked system call with empty calldata succeeds from arbitrary storage with exact
`sysState` post-state and within `161,000` regular gas. -/
theorem b_s1_exit :
    ∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock},
      CodesKept cfg start blocks stop → ∀ benv : Benv,
        benv.state = stop.state → benv.stat.fork = .amsterdam →
        ∃ out, processCheckedSystemTransaction benv exitAddr [] =
            .ok (Blanc.Lift.RequestSystem.sysState Exit.sysShape benv.state exitAddr, out) ∧
          Blanc.Lift.RequestSystem.RegularGasWithin out.gasLeft 161000 := by
  intro cfg start stop blocks hcodes benv hstate hfork
  have hex : start.state.getCode exitAddr = Exit.code := hcodes.exit
  have neex : (start.state.getCode exitAddr).toList ≠ [] := by
    rw [hex]
    decide +kernel
  have ndex : ¬ isValidDelegation (start.state.getCode exitAddr) := by
    rw [hex]
    decide +kernel
  obtain ⟨-, cex⟩ := hcodes.linked.chain neex ndex
  have hinstE : benv.state.getCode exitAddr = Exit.code := by
    rw [hstate, cex]
    exact hex
  exact Exit.system_call_state hfork hinstE

/-- **`B-S3 / deposit`.** Exact prefix delivery and FIFO queue equation for the builder deposit
contract over every clean kept history from deployed storage (requiring no exit-count bound). -/
theorem b_s3_deposit :
    ∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock},
      CodesKept cfg start blocks stop → DeployedStart start → HistoryClean blocks →
      SystemCodeAbsent start → feesPaidAt blocks depositAddr ≤ 2 ^ 256 →
      depositRequests blocks <+: (depositSubmitted blocks).flatMap Deposit.contract.out ∧
        Deposit.Indexed.submissions blocks =
          Deposit.Indexed.emissions blocks ++ Deposit.Indexed.remainingQueue stop := by
  intro cfg start stop blocks hcodes hdep hclean hsys hbudD
  refine ⟨Deposit.history_delivers hcodes.linked hcodes.deposit hdep.depStor
      hsys.code hclean.senders hclean.authorities hclean.creates hbudD,
    Deposit.Indexed.history_fifo ⟨hcodes.linked, hcodes.deposit, hdep.depStor,
      hsys.code, hclean.senders, hclean.authorities, hclean.creates, hbudD⟩⟩

/-- **`B-S3 / exit`.** Exact prefix delivery and FIFO queue equation for the builder exit
contract over every clean kept history from deployed storage (requiring no deposit-fee bound). -/
theorem b_s3_exit :
    ∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock},
      CodesKept cfg start blocks stop → DeployedStart start → HistoryClean blocks →
      SystemCodeAbsent start → (exitSubmitted blocks).length ≤ 2 ^ 64 →
      exitRequests blocks <+: (exitSubmitted blocks).flatMap Exit.contract.out ∧
        Exit.Indexed.submissions blocks =
          Exit.Indexed.emissions blocks ++ Exit.Indexed.remainingQueue stop := by
  intro cfg start stop blocks hcodes hdep hclean hsys hfewE
  refine ⟨Exit.history_delivers hcodes.linked hcodes.exit hdep.exitStor
      hsys.code hclean.senders hclean.authorities hclean.creates hfewE,
    Exit.Indexed.history_fifo ⟨hcodes.linked, hcodes.exit, hdep.exitStor,
      hsys.code, hclean.senders, hclean.authorities, hclean.creates, hfewE⟩⟩

private theorem builder_excess_domain_law (target : B256) :
    (∀ {s : Sevm} {b : Devm} {n : Nat} {out : B256},
      (BuilderRequest.storedExcess target s b).toNat < 2893 →
      WordFakeExponential.Run (BuilderRequest.storedExcess target s b) 17 1 17 0 n out →
      (out / (17 : B256)).toNat =
        fakeExp 1 (BuilderRequest.storedExcess target s b).toNat 17 ∧ n ≤ 462) ∧
    (∀ {s : Sevm} {b : Devm} {n : Nat} {out : B256},
      WordFakeExponential.Run (BuilderRequest.storedExcess target s b) 17 1 17 0 n out →
      (out / (17 : B256)).toNat ≤
        fakeExp 1 (BuilderRequest.storedExcess target s b).toNat 17) ∧
    (∀ {s : Sevm} {b : Devm} {n : Nat} {out : B256},
      (BuilderRequest.storedExcess target s b).toNat = 2893 →
      WordFakeExponential.Run (BuilderRequest.storedExcess target s b) 17 1 17 0 n out →
      (out / (17 : B256)).toNat <
        fakeExp 1 (BuilderRequest.storedExcess target s b).toNat 17) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s b n out hlt hrun
    obtain ⟨n', out', hn', hrun', hv, -⟩ :=
      RequestFeeWord.fee_run (e := BuilderRequest.storedExcess target s b) (by omega)
    obtain ⟨rfl, rfl⟩ := hrun.deterministic hrun'
    exact ⟨hv, hn'⟩
  · intro s b n out hrun
    exact RequestFeeWord.word_fee_le hrun
  · intro s b n out heq hrun
    have hle := RequestFeeWord.word_fee_le hrun
    have hb256 : BuilderRequest.storedExcess target s b = (2893 : Nat).toB256 := by
      rw [← heq, toB256_toNat]
    rw [hb256] at hrun
    have hne := RequestFeeWord.word_fee_ne_natural_2893 hrun
    rw [heq] at hle ⊢
    exact Nat.lt_of_le_of_ne hle hne

/-- **`B-S5 / deposit-fee-domain`.** Deposit contract (`target = 8`) exact fee agreement and
462-iteration bound on `storedExcess 8 < 2893`, universal `≤ fakeExp` upper bound, strict
under-quoting at `storedExcess 8 = 2893`, and non-mutating 32-byte fee-read execution (`feeReadWorks`). -/
theorem b_s5_deposit_fee_domain :
    ((∀ {s : Sevm} {b : Devm} {n : Nat} {out : B256},
      (BuilderRequest.storedExcess 8 s b).toNat < 2893 →
      WordFakeExponential.Run (BuilderRequest.storedExcess 8 s b) 17 1 17 0 n out →
      (out / (17 : B256)).toNat =
        fakeExp 1 (BuilderRequest.storedExcess 8 s b).toNat 17 ∧ n ≤ 462) ∧
    (∀ {s : Sevm} {b : Devm} {n : Nat} {out : B256},
      WordFakeExponential.Run (BuilderRequest.storedExcess 8 s b) 17 1 17 0 n out →
      (out / (17 : B256)).toNat ≤
        fakeExp 1 (BuilderRequest.storedExcess 8 s b).toNat 17) ∧
    (∀ {s : Sevm} {b : Devm} {n : Nat} {out : B256},
      (BuilderRequest.storedExcess 8 s b).toNat = 2893 →
      WordFakeExponential.Run (BuilderRequest.storedExcess 8 s b) 17 1 17 0 n out →
      (out / (17 : B256)).toNat <
        fakeExp 1 (BuilderRequest.storedExcess 8 s b).toNat 17)) ∧
    feeReadWorks depositAddr Deposit.code 8 :=
  ⟨builder_excess_domain_law 8, feeread_bridge.1⟩

/-- **`B-S5 / exit-fee-domain`.** Exit contract (`target = 2`) exact fee agreement and
462-iteration bound on `storedExcess 2 < 2893`, universal `≤ fakeExp` upper bound, strict
under-quoting at `storedExcess 2 = 2893`, and non-mutating 32-byte fee-read execution (`feeReadWorks`). -/
theorem b_s5_exit_fee_domain :
    ((∀ {s : Sevm} {b : Devm} {n : Nat} {out : B256},
      (BuilderRequest.storedExcess 2 s b).toNat < 2893 →
      WordFakeExponential.Run (BuilderRequest.storedExcess 2 s b) 17 1 17 0 n out →
      (out / (17 : B256)).toNat =
        fakeExp 1 (BuilderRequest.storedExcess 2 s b).toNat 17 ∧ n ≤ 462) ∧
    (∀ {s : Sevm} {b : Devm} {n : Nat} {out : B256},
      WordFakeExponential.Run (BuilderRequest.storedExcess 2 s b) 17 1 17 0 n out →
      (out / (17 : B256)).toNat ≤
        fakeExp 1 (BuilderRequest.storedExcess 2 s b).toNat 17) ∧
    (∀ {s : Sevm} {b : Devm} {n : Nat} {out : B256},
      (BuilderRequest.storedExcess 2 s b).toNat = 2893 →
      WordFakeExponential.Run (BuilderRequest.storedExcess 2 s b) 17 1 17 0 n out →
      (out / (17 : B256)).toNat <
        fakeExp 1 (BuilderRequest.storedExcess 2 s b).toNat 17)) ∧
    feeReadWorks exitAddr Exit.code 2 :=
  ⟨builder_excess_domain_law 2, feeread_bridge.2⟩

/-- **`B-S5 / reversible-latch`.** Both builder contracts' nonempty-calldata system latch is
reversed by the next empty-calldata system call (`kill_switch_reversible`), and unlocking from
inhibited storage resets both excess and count to zero (`1` wei quote, `unlock_resets_fee`). -/
theorem b_s5_reversible_latch : kill_switch_reversible ∧ unlock_resets_fee :=
  ⟨kill_switch_bridge, unlock_fee_bridge⟩

/-- **`B-S6 / deposit`.** Deposit contract balance retention (`value_kept` at `depositAddr`) plus
the 1-ETH minimum stake-funding guarantee (`stake_funded`). -/
theorem b_s6_deposit :
    (∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock},
      CodesKept cfg start blocks stop → HistoryRootsFit blocks →
      ChainLink.History.NoSender depositAddr blocks →
      HistoryCreditsFit depositAddr blocks →
      ((start.state.get depositAddr).bal).toNat + feesPaidAt blocks depositAddr ≤
        ((stop.state.get depositAddr).bal).toNat) ∧
    stake_funded :=
  ⟨fun h fits senders credits =>
    value_kept_bridge h fits depositAddr List.mem_cons_self senders credits,
   stake_funded_bridge⟩

/-- **`B-S6 / exit`.** Exit contract balance retention (`value_kept` at `exitAddr`). -/
theorem b_s6_exit :
    ∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock},
      CodesKept cfg start blocks stop → HistoryRootsFit blocks →
      ChainLink.History.NoSender exitAddr blocks →
      HistoryCreditsFit exitAddr blocks →
      ((start.state.get exitAddr).bal).toNat + feesPaidAt blocks exitAddr ≤
        ((stop.state.get exitAddr).bal).toNat :=
  fun h fits senders credits =>
    value_kept_bridge h fits exitAddr (List.mem_cons_of_mem _ List.mem_cons_self) senders credits

/-- **`B-S7 / deposit-acceptance-gas`.** Deposit direct-transaction acceptance and concrete gas
bound (`depositDirectUse`) together with covered-fork and Amsterdam frame progress. -/
theorem b_s7_deposit_acceptance_gas :
    depositDirectUse ∧ depositCoveredProgress ∧ depositAmsterdamProgress :=
  ⟨direct_use_bridge.1, progress_bridge.1, progress_bridge.2.1⟩

/-- **`B-S7 / exit-acceptance-gas`.** Exit direct-transaction acceptance and concrete gas
bound (`exitDirectUse`) together with covered-fork and Amsterdam frame progress. -/
theorem b_s7_exit_acceptance_gas :
    exitDirectUse ∧ exitCoveredProgress ∧ exitAmsterdamProgress :=
  ⟨direct_use_bridge.2, progress_bridge.2.2.1, progress_bridge.2.2.2⟩

/-- **`B-S9 / registration-authorization-credit` combined wrapper.** Couples `ValidJointG.deposit_value`
with `ValidJointG.registration_authorization` (`bls = true`). -/
theorem b_s9_registration_authorization_credit {P : Preset} {cfg : ChainConfig}
    {ccfg : Config} {checkpoint : BlockChain} {anchor final : GJointState P}
    (v : ValidJointG cfg ccfg true checkpoint anchor final) :
    (((checkpoint.state.get depositAddr).bal).toNat + feesPaidAt v.blocks depositAddr ≤
        ((final.exec.state.get depositAddr).bal).toNat ∧
      ((checkpoint.state.get exitAddr).bal).toNat + feesPaidAt v.blocks exitAddr ≤
        ((final.exec.state.get exitAddr).bal).toNat ∧
      ∀ f ∈ keptAt v.blocks depositAddr, ∀ h : f.sevm.data.length = 184,
        Bytes.toNat (Deposit.recordOf f.sevm h).amount * 10 ^ 9 ≤ f.sevm.value.toNat ∧
          ∃ fee : B256, Deposit.Admits f.sevm.data f.sevm.value fee) ∧
    (∀ {j : Nat} {D : GloasStepData (P := P) cfg ccfg true},
      v.run.steps[j]? = some (.gloas D) →
      ∀ {i : Nat}, BuilderCreated D.preB D.postB i →
        ∃ (k : Nat) (req : Gloas.BuilderDepositRequest) (tr : List (Gloas.BeaconState P))
          (m m' : Gloas.BeaconState P) (amount : Gwei) (dom : Domain)
          (addr : ExecutionAddress) (e : Epoch),
          D.builderDeposits[k]? = some req ∧
          builderDepositTrace ccfg true D.postSlots D.block = .ok tr ∧
          tr[k]? = some m ∧ tr[k + 1]? = some m' ∧
          classifyBuilderDeposit ccfg true m req = .ok (.register i amount) ∧
          amount = req.amount ∧
          req.withdrawal_credentials.toBytes.head? = some 0xB0 ∧
          builderDepositDomain ccfg = some dom ∧
          blsVerify true req.pubkey (computeSigningRoot (builderDepositMessage req) dom)
            req.signature = true ∧
          Jaune.Bytes.toAdr? (req.withdrawal_credentials.toBytes.drop 12) = some addr ∧
          computeEpochAtSlot P m.slot = .ok e ∧
          m'.builders.toArray[i]? = some (freshBuilder req.pubkey addr req.amount e)) := by
  refine ⟨v.deposit_value, ?_⟩
  intro j D stepD i created
  obtain ⟨k, req, tr, m, m', amount, dom, addr, e, hreq, htr, hm, hm', hcl, hamt,
    -, hpre, hdom, hv, haddr, he, hat, -⟩ :=
    v.registration_authorization rfl stepD created
  exact ⟨k, req, tr, m, m', amount, dom, addr, e, hreq, htr, hm, hm', hcl, hamt,
    hpre, hdom, hv, haddr, he, hat⟩

/-- **`B-S10 / deposit`.** Deposit Amsterdam checked system-call totality with exact `sysState`
post-state and `888,000` regular-gas bound, paired with four-contract request-phase pass totality
(`next_pass_cannot_fail` and `request_fold_succeeds`). -/
theorem b_s10_deposit :
    (∀ (benv : Benv), benv.stat.fork = .amsterdam →
      runsBuilderCode benv.state depositAddr Deposit.code →
      ∃ out, processCheckedSystemTransaction benv depositAddr [] =
          .ok (Blanc.Lift.RequestSystem.sysState Deposit.sysShape benv.state depositAddr, out) ∧
        Blanc.Lift.RequestSystem.RegularGasWithin out.gasLeft 888000) ∧
    next_pass_cannot_fail ∧ request_fold_succeeds :=
  ⟨fun _ hfork hinst => Deposit.system_call_state hfork hinst, next_pass_bridge, fold_bridge⟩

/-- **`B-S10 / exit`.** Exit Amsterdam checked system-call totality with exact `sysState`
post-state and `161,000` regular-gas bound, paired with four-contract request-phase pass totality
(`next_pass_cannot_fail` and `request_fold_succeeds`). -/
theorem b_s10_exit :
    (∀ (benv : Benv), benv.stat.fork = .amsterdam →
      runsBuilderCode benv.state exitAddr Exit.code →
      ∃ out, processCheckedSystemTransaction benv exitAddr [] =
          .ok (Blanc.Lift.RequestSystem.sysState Exit.sysShape benv.state exitAddr, out) ∧
        Blanc.Lift.RequestSystem.RegularGasWithin out.gasLeft 161000) ∧
    next_pass_cannot_fail ∧ request_fold_succeeds :=
  ⟨fun _ hfork hinst => Exit.system_call_state hfork hinst, next_pass_bridge, fold_bridge⟩

/-- **`W-S7 / headline`.** Canonical withdrawal 56-byte submission and empty-calldata fee-getter
frames both succeed at their exact gas charges under the bytecode's actual word-fee guards. -/
theorem w_s7_headline :
    (∀ {sevm : Sevm} {b : Devm} {M : Mem} {G iterations : Nat} {finalOutput : B256},
      sevm.code = Blanc.withdrawalRequestCode →
      CoveredFork sevm.benvStat.fork →
      sevm.caller ≠ systemAddress →
      sevm.data.length = 56 →
      sevm.isStatic = false →
      gCallStipend < G →
      b.getStorVal sevm.currentTarget 0 ≠ B256.max →
      WordFakeExponential.Run (b.getStorVal sevm.currentTarget 0) 17 1 17 0 iterations finalOutput →
      (finalOutput / (17 : B256)).toNat ≤ sevm.value.toNat →
      Nonempty (Exec 0 sevm (St b [] M (G + WithdrawalRequest.userSubmissionGas sevm b M iterations))
        (.ok (WithdrawalRequest.submissionPost sevm (afterSload sevm b 0) M G)))) ∧
    (∀ {sevm : Sevm} {b : Devm} {M : Mem} {G iterations : Nat} {finalOutput : B256},
      sevm.code = Blanc.withdrawalRequestCode →
      CoveredFork sevm.benvStat.fork →
      M.size % 32 = 0 →
      sevm.caller ≠ systemAddress →
      sevm.data = [] →
      sevm.value = 0 →
      b.getStorVal sevm.currentTarget 0 ≠ B256.max →
      WordFakeExponential.Run (b.getStorVal sevm.currentTarget 0) 17 1 17 0 iterations finalOutput →
      Nonempty (Exec 0 sevm (St b [] M (G + WithdrawalRequest.userFeeGetterGas sevm b M iterations))
        (.ok (RequestFee.feeGetterPost (afterSload sevm b 0) M (finalOutput / (17 : B256)) G)))) :=
  ⟨fun hc hf hu hl hd hs ha hw hp =>
      WithdrawalRequest.exec_submission_exact hc hf hu hl hd hs ha hw hp,
   fun hc hf hm hu he hz ha hw =>
      WithdrawalRequest.exec_fee_getter_exact hc hf hm hu he hz ha hw⟩

/-- **`C-S7 / headline`.** Canonical consolidation 96-byte submission and empty-calldata fee-getter
frames both succeed at their exact gas charges under the bytecode's actual word-fee guards. -/
theorem c_s7_headline :
    (∀ {sevm : Sevm} {b : Devm},
      sevm.currentTarget = Blanc.Composition.ConsolidationRequestPublic.addr →
      sevm.code = Blanc.Composition.ConsolidationRequestPublic.code →
      CoveredFork sevm.benvStat.fork →
      sevm.caller ≠ systemAddress →
      sevm.data.length = 96 →
      sevm.isStatic = false →
      b.getStorVal Blanc.Composition.ConsolidationRequestPublic.addr 0 ≠ B256.max →
      Blanc.Composition.ConsolidationRequestPublic.quotedFee
        (b.getStorVal Blanc.Composition.ConsolidationRequestPublic.addr 0) ≤ sevm.value.toNat →
      Blanc.Composition.ConsolidationRequestPublic.SubmissionLive sevm b) ∧
    (∀ {sevm : Sevm} {b : Devm} {M : Mem} {G iterations : Nat} {output : B256},
      sevm.code = Blanc.Lift.SystemExecution.ConsolidationRequest.code →
      CoveredFork sevm.benvStat.fork →
      M.size % 32 = 0 →
      sevm.caller ≠ systemAddress →
      sevm.data = [] →
      sevm.value = 0 →
      b.getStorVal sevm.currentTarget 0 ≠ B256.max →
      WordFakeExponential.Run (b.getStorVal sevm.currentTarget 0) 17 1 17 0 iterations output →
      Nonempty (Exec 0 sevm (St b [] M (G + Blanc.Lift.RequestFee.PlainUserPath.feeReadGas sevm b M iterations))
        (.ok (RequestFee.feeGetterPost (afterSload sevm b 0) M (output / (17 : B256)) G)))) :=
  ⟨fun ht hc hf hu hl hd ha hp =>
      Blanc.Composition.ConsolidationRequestPublic.submission_live ht hc hf hu hl hd ha hp,
   fun hc hf hm hu he hz ha hw =>
      Blanc.Lift.ConsolidationRequest.exec_fee_read_exact hc hf hm hu he hz ha hw⟩

/-- **`W-S10 / headline`.** Amsterdam withdrawal system-call totality within 163,000 regular gas
paired with the unconditional Amsterdam four-contract request pass (`RequestPhaseAmsterdam.request_pass`). -/
theorem w_s10_headline :
    (∀ {benv : Benv}, benv.stat.fork = .amsterdam →
      benv.state.getCode withdrawalRequestPredeployAddress = withdrawalRequestCode →
      ∃ out, processCheckedSystemTransaction benv withdrawalRequestPredeployAddress [] =
          .ok (Blanc.Lift.RequestSystem.sysState Blanc.Lift.WithdrawalRequest.Amsterdam.sysShape
            benv.state withdrawalRequestPredeployAddress, out) ∧
        Blanc.Lift.RequestSystem.RegularGasWithin out.gasLeft 163000) ∧
    (∀ {benv0 final benv : Benv} {txs : List Tx} {bal0 : BalBuilder}
      {out0 : BlockOutput} {senders : List (Adr × Tx)} {roots : List Blanc.Root}
      (wds : List Jaune.Withdrawal),
      benv0.stat.fork = .amsterdam →
      benv0.state.getCode depositContractAddress = BeaconDeposit.code →
      Blanc.TransactionsRoots txs.putIndex benv0 { BlockOutput.init with bal := bal0 }
        final out0 senders roots →
      benv.stat.fork = .amsterdam →
      benv.state.getCode withdrawalRequestPredeployAddress = withdrawalRequestCode →
      benv.state.getCode consolidationRequestPredeployAddress = consolidationRequestCode →
      benv.state.getCode BuilderRequest.Deposit.Creation.address = BuilderRequest.Deposit.code →
      benv.state.getCode BuilderRequest.Exit.Creation.address = BuilderRequest.Exit.code →
      ∀ (idx : Nat),
        let bout := (withdrawalsPass benv0.stat.rules final out0 wds).2
        let depositRequests := ((roots.flatMap (Blanc.Root.keptAt depositContractAddress)).flatMap
          Blanc.Corpus.Freeze.Deposit.frameRecords).flatten
        let σ1 := Blanc.Composition.RequestPhaseAmsterdam.afterWithdrawals benv.state
        let σ2 := Blanc.Composition.RequestPhaseAmsterdam.afterConsolidations σ1
        let σ3 := Blanc.Composition.RequestPhaseAmsterdam.afterDeposits σ2
        let σ4 := Blanc.Composition.RequestPhaseAmsterdam.afterExits σ3
        ∃ (out1 out2 out3 out4 : MsgCallOutput) (bal' : BalBuilder),
          processCheckedSystemTransaction benv withdrawalRequestPredeployAddress [] = .ok (σ1, out1) ∧
          processCheckedSystemTransaction (benv.withState σ1) consolidationRequestPredeployAddress [] =
            .ok (σ2, out2) ∧
          processCheckedSystemTransaction (benv.withState σ2) BuilderRequest.Deposit.Creation.address [] =
            .ok (σ3, out3) ∧
          processCheckedSystemTransaction (benv.withState σ3) BuilderRequest.Exit.Creation.address [] =
            .ok (σ4, out4) ∧
          processGeneralPurposeRequestsAt idx benv bout =
            .ok (σ4, { bout with
              requests := bout.requests ++ ExecutionTrace.optionalRequestEntry 0 depositRequests ++
                ExecutionTrace.optionalRequestEntry 1 out1.returnData ++
                ExecutionTrace.optionalRequestEntry 2 out2.returnData ++
                ExecutionTrace.optionalRequestEntry 3 out3.returnData ++
                ExecutionTrace.optionalRequestEntry 4 out4.returnData
              bal := bal' })) :=
  ⟨fun hf hi => Blanc.Lift.WithdrawalRequest.Amsterdam.system_call_ok hf hi,
   fun wds hf0 hb htx hf h70 h72 hd he idx =>
      Blanc.Composition.RequestPhaseAmsterdam.request_pass wds hf0 hb htx hf h70 h72 hd he idx⟩

/-- **`C-S10 / headline`.** Amsterdam consolidation system-call totality within 75,000 regular gas
paired with the unconditional Amsterdam four-contract request pass (`RequestPhaseAmsterdam.request_pass`). -/
theorem c_s10_headline :
    (∀ {benv : Benv}, benv.stat.fork = .amsterdam →
      benv.state.getCode consolidationRequestPredeployAddress = consolidationRequestCode →
      ∃ out, processCheckedSystemTransaction benv consolidationRequestPredeployAddress [] =
          .ok (Blanc.Lift.RequestSystem.sysState
            Blanc.Lift.SystemExecution.ConsolidationRequest.Amsterdam.sysShape
            benv.state consolidationRequestPredeployAddress, out) ∧
        Blanc.Lift.RequestSystem.RegularGasWithin out.gasLeft 75000) ∧
    (∀ {benv0 final benv : Benv} {txs : List Tx} {bal0 : BalBuilder}
      {out0 : BlockOutput} {senders : List (Adr × Tx)} {roots : List Blanc.Root}
      (wds : List Jaune.Withdrawal),
      benv0.stat.fork = .amsterdam →
      benv0.state.getCode depositContractAddress = BeaconDeposit.code →
      Blanc.TransactionsRoots txs.putIndex benv0 { BlockOutput.init with bal := bal0 }
        final out0 senders roots →
      benv.stat.fork = .amsterdam →
      benv.state.getCode withdrawalRequestPredeployAddress = withdrawalRequestCode →
      benv.state.getCode consolidationRequestPredeployAddress = consolidationRequestCode →
      benv.state.getCode BuilderRequest.Deposit.Creation.address = BuilderRequest.Deposit.code →
      benv.state.getCode BuilderRequest.Exit.Creation.address = BuilderRequest.Exit.code →
      ∀ (idx : Nat),
        let bout := (withdrawalsPass benv0.stat.rules final out0 wds).2
        let depositRequests := ((roots.flatMap (Blanc.Root.keptAt depositContractAddress)).flatMap
          Blanc.Corpus.Freeze.Deposit.frameRecords).flatten
        let σ1 := Blanc.Composition.RequestPhaseAmsterdam.afterWithdrawals benv.state
        let σ2 := Blanc.Composition.RequestPhaseAmsterdam.afterConsolidations σ1
        let σ3 := Blanc.Composition.RequestPhaseAmsterdam.afterDeposits σ2
        let σ4 := Blanc.Composition.RequestPhaseAmsterdam.afterExits σ3
        ∃ (out1 out2 out3 out4 : MsgCallOutput) (bal' : BalBuilder),
          processCheckedSystemTransaction benv withdrawalRequestPredeployAddress [] = .ok (σ1, out1) ∧
          processCheckedSystemTransaction (benv.withState σ1) consolidationRequestPredeployAddress [] =
            .ok (σ2, out2) ∧
          processCheckedSystemTransaction (benv.withState σ2) BuilderRequest.Deposit.Creation.address [] =
            .ok (σ3, out3) ∧
          processCheckedSystemTransaction (benv.withState σ3) BuilderRequest.Exit.Creation.address [] =
            .ok (σ4, out4) ∧
          processGeneralPurposeRequestsAt idx benv bout =
            .ok (σ4, { bout with
              requests := bout.requests ++ ExecutionTrace.optionalRequestEntry 0 depositRequests ++
                ExecutionTrace.optionalRequestEntry 1 out1.returnData ++
                ExecutionTrace.optionalRequestEntry 2 out2.returnData ++
                ExecutionTrace.optionalRequestEntry 3 out3.returnData ++
                ExecutionTrace.optionalRequestEntry 4 out4.returnData
              bal := bal' })) :=
  ⟨fun hf hi => Blanc.Lift.SystemExecution.ConsolidationRequest.Amsterdam.system_call_ok hf hi,
   fun wds hf0 hb htx hf h70 h72 hd he idx =>
      Blanc.Composition.RequestPhaseAmsterdam.request_pass wds hf0 hb htx hf h70 h72 hd he idx⟩

end Blanc.Composition.Corpus.Proofs.MatrixComponentPins
