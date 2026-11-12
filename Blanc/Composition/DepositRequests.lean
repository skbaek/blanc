import Blanc.Corpus.Freeze.DepositCells
import Blanc.Composition.DepositParse

/-!
# D-S8: Same-block deposit request publication (execution side)

Proves the frozen `D_S8` (`D8`) cell over covered-fork kept histories with the deployed Beacon
Deposit runtime installed at `start.state`:

1. Every record extracted from `b.run.txRoots.flatMap (Root.keptAt depositAddr)` has length 192.
2. `b.output.requests` places the concatenated type-`0x00` deposit records first (when nonempty),
   followed in order by `b.run.requests.flatMap RequestStep.bytes`.
3. No post-execution system-contract request entry carries type byte `0x00`
   (`JauneConsensus.depositRequestType`), since covered forks schedule only types `0x01` and `0x02`.
4. When `preRoots` and `requestRootsOf b.run.requests` keep no frame at `depositAddr`,
   `b.keptAt depositAddr` equals the transaction-phase frames.
-/

namespace Blanc.Composition.DepositRequests

open Jaune Blanc Blanc.Lift.BeaconDeposit
open Blanc.Corpus.Freeze.Deposit

private theorem mem_step_and_code {cfg : ChainConfig} {start stop : BlockChain}
    {blocks : List KeptBlock}
    (kept : KeptHistory cfg start blocks stop)
    (installed : DepositCodeAt start.state) :
    ∀ b ∈ blocks, DepositCodeAt b.parent.state ∧ ∃ next, KeptStep cfg b next := by
  have hc : (start.state.getCode depositAddr).toList ≠ [] := by
    rw [installed]
    exact beaconInstalledCertH.nonempty
  have hd : ¬ isValidDelegation (start.state.getCode depositAddr) := by
    rw [installed]
    exact beaconInstalledCertH.notDelegation
  induction kept with
  | refl => exact fun _ hb => absurd hb List.not_mem_nil
  | @step priorBlocks last post prior step ih =>
      intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact ih b hb
      · rw [List.mem_singleton.mp hb]
        exact ⟨(prior.chain hc hd).2.trans installed, post, step⟩

private theorem frameRecords_length {fr : Exec.Frame}
    (hlogs : ∀ log ∈ depositLogs (frameLogs fr),
      ∃ ev, log = BeaconDeposit.depositEventLog depositAddr ev ∧
        extractDepositData log.data = .ok (depositRecord ev) ∧ (depositRecord ev).length = 192) :
    ∀ r ∈ frameRecords fr, r.length = 192 := by
  intro r hr
  unfold frameRecords at hr
  obtain ⟨log, hlog, hmap⟩ := List.mem_filterMap.mp hr
  obtain ⟨ev, -, hext, hlen⟩ := hlogs log hlog
  rw [hext] at hmap
  cases hmap
  exact hlen

private theorem covered_requests_eq (f : Fork) (hf : CoveredFork f) :
    f.ruleSet.requests = pragueRequests :=
  hf.cases (motive := fun f => f.ruleSet.requests = pragueRequests) rfl rfl rfl rfl

private theorem requestStep_bytes_head_ne_deposit {s : RequestStep}
    (hne : s.type ≠ JauneConsensus.depositRequestType) :
    ∀ entry ∈ s.bytes, entry.head? ≠ some JauneConsensus.depositRequestType := by
  intro entry hentry
  unfold RequestStep.bytes at hentry
  split at hentry
  · obtain rfl := List.mem_singleton.mp hentry
    simp only [List.singleton_append, List.head?_cons, ne_eq, Option.some.injEq]
    exact hne
  · cases hentry

/-- **D-S8.** Execution-side same-block deposit request publication over covered-fork kept histories. -/
theorem d_s8 : D_S8 := by
  intro cfg start stop blocks kept forks installed b hb
  obtain ⟨parentCode, next, step⟩ := mem_step_and_code kept installed b hb
  have hfork : CoveredFork b.fork := forks b hb
  have hshape := Blanc.Corpus.Proofs.Deposit.log_shape kept forks installed b hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨fr, hfr, hrec⟩ := List.mem_flatMap.mp hr
    have hfrKept : fr ∈ b.keptAt depositAddr := by
      unfold KeptBlock.keptAt BodyRun.roots
      rw [List.flatMap_append, List.flatMap_append, List.mem_append, List.mem_append]
      exact Or.inl (Or.inr hfr)
    exact frameRecords_length (hshape fr hfrKept) r hrec
  · have hcBenv : (b.benv.state.getCode depositAddr).toList ≠ [] := by
      change (b.parent.state.getCode depositAddr).toList ≠ []
      rw [parentCode]
      exact beaconInstalledCertH.nonempty
    have hdBenv : ¬ isValidDelegation (b.benv.state.getCode depositAddr) := by
      change ¬ isValidDelegation (b.parent.state.getCode depositAddr)
      rw [parentCode]
      exact beaconInstalledCertH.notDelegation
    have preCode : DepositCodeAt (b.benv.withState b.run.preState).state :=
      (step.body.pre.chain hcBenv hdBenv).2.trans parentCode
    obtain ⟨decoded, -, txRoots⟩ := step.body.transactions
    have hparse := Blanc.Composition.DepositParse.parse_succeeds
      (b.benv.withState b.run.preState) decoded b.run.preBal b.run.txEnv b.run.txOut
      b.run.senders b.run.txRoots b.block.wds hfork preCode txRoots
    obtain ⟨deposits, hparseBody, houtReq⟩ := step.body.requests_eq step.kept.requestsHash
    have hdepEq : deposits =
        ((b.run.txRoots.flatMap (Root.keptAt depositAddr)).flatMap frameRecords).flatten :=
      Except.ok.inj (hparseBody.symm.trans hparse)
    rw [houtReq, hdepEq]
  · intro entry hentry
    obtain ⟨s, hs, hbytes⟩ := List.mem_flatMap.mp hentry
    have hcontracts := step.body.contracts_eq step.kept.requestsHash
    change b.fork.ruleSet.requests = _ at hcontracts
    rw [covered_requests_eq b.fork hfork] at hcontracts
    have hmem : (s.type, s.target) ∈ pragueRequests := by
      rw [hcontracts]
      exact List.mem_map_of_mem hs
    have hne : s.type ≠ JauneConsensus.depositRequestType := by
      simp only [pragueRequests, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
      rcases hmem with ⟨ht, -⟩ | ⟨ht, -⟩ <;> rw [ht] <;> decide
    exact requestStep_bytes_head_ne_deposit hne entry hbytes
  · intro hempty
    rw [List.flatMap_append] at hempty
    obtain ⟨hpre, hreq⟩ := List.append_eq_nil_iff.mp hempty
    unfold KeptBlock.keptAt BodyRun.roots
    rw [List.flatMap_append, List.flatMap_append, hpre, hreq, List.nil_append, List.append_nil]

/-- Alias matching the corpus matrix naming convention. -/
theorem D_S8_proved : D_S8 := d_s8

end Blanc.Composition.DepositRequests
