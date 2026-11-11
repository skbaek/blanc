import Blanc.Lift.BuilderRequest.WordFees
import Blanc.Composition.BuilderRequestJointGFate

/-!
# Actual word request fees bound every request boundary

The budget counts the request FEE quotes of all committed ordinary submissions
in the supplied whole history. Deposit principal, transaction gas, privileged
requests and fee reads contribute nothing. Range premises remain explicit in
the execution core; the joint adapters derive them from existing joint fields.
Delivery remains conditional on the destination and Amsterdam segment existing.
-/

namespace Blanc.Lift.BuilderRequest.ActualFeeBounds

open Jaune Delivery ChainLink Occurrence

private theorem prefix_budget {c : Contract} {xs ys : List (Delivery.Frame c)}
    {g : Delivery.Frame c} {blocks : List KeptBlock}
    (corr : Corresponds c (xs ++ g :: ys) (History.kept c.address blocks)) :
    RequestPhaseOnly xs ∧
    (Delivery.submissions xs).length ≤ (History.submitted c blocks).length ∧
    LoadBound.fees xs ≤ WordFees.actualFeeSum c blocks := by
  refine ⟨fun f hf latch he => corr.requestPhase f (List.mem_append_left _ hf) latch he, ?_, ?_⟩
  · have hs := corr.submissions
    change Delivery.submissions (xs ++ g :: ys) = History.submitted c blocks at hs
    rw [Delivery.submissions_append] at hs
    have hn := congrArg List.length hs
    simp only [List.length_append] at hn
    omega
  · have hfee := WordFees.corresponds_fees corr
    rw [LoadBound.fees, List.map_append, List.sum_append] at hfee
    change (xs.map LoadBound.feePaid).sum ≤ ((History.kept c.address blocks).map (WordFees.frameFee c)).sum
    omega

/-- The explicit execution scope for deposits: the usual installed/fresh history
premises and word range, separate from the actual request-fee budget. -/
theorem deposit_boundary {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}
    (history : KeptHistory cfg start blocks stop)
    (installed : start.state.getCode Deposit.Creation.address = Deposit.code)
    (fresh : start.state.getStor Deposit.Creation.address = Stor.empty)
    (empty : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks)
    (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks)
    (range : 4 + 6 * (History.submitted Deposit.contract blocks).length ≤ 2 ^ 256)
    {budget ceiling : Nat} (fees : WordFees.actualFeeSum Deposit.contract blocks ≤ budget)
    (cost : budget < Backlog.cost 8 0 (ceiling + 1)) (small : ceiling < 2893)
    {pre post : List KeptBlock} {b : KeptBlock} (split : blocks = pre ++ b :: post) :
    (Deposit.Indexed.queueAtRequests b).length ≤ ceiling := by
  have prem : Premises Deposit.contract cfg start blocks stop Deposit.deployedQueue := by
    refine ⟨history, installed, ?_, empty, senders, authorities, creates, ?_, ?_⟩
    · rw [fresh]; exact Deposit.deployed_represents
    · change 4 + 6 * (0 + (History.submitted Deposit.contract blocks).length) ≤ 2 ^ 256
      simpa only [Nat.zero_add] using range
    · change 0 + (History.submitted Deposit.contract blocks).length < 2 ^ 256
      omega
  have block := history_block_with_prefix Deposit.Indexed.reading Deposit.linked prem split
  by_cases am : b.fork = .amsterdam
  · obtain ⟨xs, ys, g, f, corr, _, chain, _, _, _, queue⟩ := block.2 am
    obtain ⟨rp, subs, fee⟩ := prefix_budget corr
    rw [fresh] at chain
    have slots : 4 + 6 * (Delivery.submissions xs).length ≤ 2 ^ 256 := by omega
    have paid : LoadBound.fees xs ≤ budget := fee.trans fees
    have wrap : LoadBound.fees xs < Backlog.cost 8 0 2893 :=
      lt_of_lt_of_le (lt_of_le_of_lt paid cost) (LoadBound.cost_mono (by omega))
    have load := LoadBound.load_le_of_budget (LoadBound.deposit_potential chain slots wrap) paid cost
    have bound := (LoadBound.deposit_queue_le chain rp slots).trans load
    simpa only [Deposit.Indexed.queueAtRequests, queue, List.length_map] using bound
  · simpa only [Deposit.Indexed.queueAtRequests, (block.1.2.1 am).2, List.length_nil] using Nat.zero_le ceiling

/-- The corresponding explicit exit scope starts from the deployed inhibited
storage; no uninhibited-endpoint assumption is added. -/
theorem exit_boundary {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}
    (history : KeptHistory cfg start blocks stop)
    (installed : start.state.getCode Exit.Creation.address = Exit.code)
    (fresh : start.state.getStor Exit.Creation.address = Exit.deployedStorage)
    (empty : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks)
    (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks)
    (range : 4 + 3 * (History.submitted Exit.contract blocks).length ≤ 2 ^ 256)
    {budget ceiling : Nat} (fees : WordFees.actualFeeSum Exit.contract blocks ≤ budget)
    (cost : budget < Backlog.cost 2 0 (ceiling + 1)) (small : ceiling < 2893)
    {pre post : List KeptBlock} {b : KeptBlock} (split : blocks = pre ++ b :: post) :
    (Exit.Indexed.queueAtRequests b).length ≤ ceiling := by
  have prem : Premises Exit.contract cfg start blocks stop Exit.deployedQueue := by
    refine ⟨history, installed, ?_, empty, senders, authorities, creates, ?_, ?_⟩
    · rw [fresh]; exact Exit.deployed_represents
    · change 4 + 3 * (0 + (History.submitted Exit.contract blocks).length) ≤ 2 ^ 256
      simpa only [Nat.zero_add] using range
    · change 0 + (History.submitted Exit.contract blocks).length < 2 ^ 256
      omega
  have block := history_block_with_prefix Exit.Indexed.reading Exit.linked prem split
  by_cases am : b.fork = .amsterdam
  · obtain ⟨xs, ys, g, f, corr, _, chain, _, _, _, queue⟩ := block.2 am
    obtain ⟨rp, subs, fee⟩ := prefix_budget corr
    rw [fresh] at chain
    have slots : 4 + 3 * (Delivery.submissions xs).length ≤ 2 ^ 256 := by omega
    have paid : LoadBound.fees xs ≤ budget := fee.trans fees
    have wrap : LoadBound.fees xs < Backlog.cost 2 0 2893 :=
      lt_of_lt_of_le (lt_of_le_of_lt paid cost) (LoadBound.cost_mono (by omega))
    have load := LoadBound.load_le_of_budget (LoadBound.exit_potential chain slots wrap) paid cost
    have bound := LoadBound.exit_queue_le_of_load chain rp slots load
    simpa only [Exit.Indexed.queueAtRequests, queue, List.length_map] using bound
  · simpa only [Exit.Indexed.queueAtRequests, (block.1.2.1 am).2, List.length_nil] using Nat.zero_le ceiling


variable {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}

/-- Every deposit boundary, using the existing clean history's derived word range. -/
theorem deposit_every_boundary (H : Deposit.Indexed.Clean cfg start blocks stop)
    {budget ceiling : Nat} (fees : WordFees.actualFeeSum Deposit.contract blocks ≤ budget)
    (cost : budget < Backlog.cost 8 0 (ceiling + 1)) (small : ceiling < 2893) :
    ∀ b ∈ blocks, (Deposit.Indexed.queueAtRequests b).length ≤ ceiling := by
  intro b hb
  obtain ⟨pre, post, split⟩ := List.mem_iff_append.mp hb
  have range := H.premises.slots
  change 4 + 6 * (0 + (History.submitted Deposit.contract blocks).length) ≤ 2 ^ 256 at range
  exact deposit_boundary H.history H.installed H.fresh H.noSystemCode H.senders H.authorities H.creates
    (by simpa only [Nat.zero_add] using range) fees cost small split

/-- Every exit boundary, using the existing clean history's derived word range. -/
theorem exit_every_boundary (H : Exit.Indexed.Clean cfg start blocks stop)
    {budget ceiling : Nat} (fees : WordFees.actualFeeSum Exit.contract blocks ≤ budget)
    (cost : budget < Backlog.cost 2 0 (ceiling + 1)) (small : ceiling < 2893) :
    ∀ b ∈ blocks, (Exit.Indexed.queueAtRequests b).length ≤ ceiling := by
  intro b hb
  obtain ⟨pre, post, split⟩ := List.mem_iff_append.mp hb
  have range := H.premises.slots
  change 4 + 3 * (0 + (History.submitted Exit.contract blocks).length) ≤ 2 ^ 256 at range
  exact exit_boundary H.history H.installed H.fresh H.noSystemCode H.senders H.authorities H.creates
    (by simpa only [Nat.zero_add] using range) fees cost small split

/-- 10 ^ 18 wei of actual request fees bounds every deposit request queue by 664. -/
theorem deposit_every_boundary_664 (H : Deposit.Indexed.Clean cfg start blocks stop)
    (fees : WordFees.actualFeeSum Deposit.contract blocks ≤ 10 ^ 18) :
    ∀ b ∈ blocks, (Deposit.Indexed.queueAtRequests b).length ≤ 664 := by
  apply deposit_every_boundary H fees ?_ (by omega)
  rw [← Backlog.costEval_eq (by omega)]
  exact LoadBound.cost_664.2

/-- 100 * 10 ^ 18 wei of actual request fees bounds every deposit request queue by 743. -/
theorem deposit_every_boundary_743 (H : Deposit.Indexed.Clean cfg start blocks stop)
    (fees : WordFees.actualFeeSum Deposit.contract blocks ≤ 100 * 10 ^ 18) :
    ∀ b ∈ blocks, (Deposit.Indexed.queueAtRequests b).length ≤ 743 := by
  apply deposit_every_boundary H fees ?_ (by omega)
  rw [← Backlog.costEval_eq (by omega)]
  exact LoadBound.cost_743.2

/-- 120000000 * 10 ^ 18 wei of actual request fees bounds every deposit request queue by 981. -/
theorem deposit_every_boundary_981 (H : Deposit.Indexed.Clean cfg start blocks stop)
    (fees : WordFees.actualFeeSum Deposit.contract blocks ≤ 120000000 * 10 ^ 18) :
    ∀ b ∈ blocks, (Deposit.Indexed.queueAtRequests b).length ≤ 981 := by
  apply deposit_every_boundary H fees ?_ (by omega)
  rw [← Backlog.costEval_eq (by omega)]
  exact LoadBound.cost_981.2

/-- 10 ^ 18 wei of actual request fees bounds every exit request queue by 658. -/
theorem exit_every_boundary_658 (H : Exit.Indexed.Clean cfg start blocks stop)
    (fees : WordFees.actualFeeSum Exit.contract blocks ≤ 10 ^ 18) :
    ∀ b ∈ blocks, (Exit.Indexed.queueAtRequests b).length ≤ 658 := by
  apply exit_every_boundary H fees ?_ (by omega)
  rw [← Backlog.costEval_eq (by omega)]
  exact Exit.cost_658.2

/-- 100 * 10 ^ 18 wei of actual request fees bounds every exit request queue by 737. -/
theorem exit_every_boundary_737 (H : Exit.Indexed.Clean cfg start blocks stop)
    (fees : WordFees.actualFeeSum Exit.contract blocks ≤ 100 * 10 ^ 18) :
    ∀ b ∈ blocks, (Exit.Indexed.queueAtRequests b).length ≤ 737 := by
  apply exit_every_boundary H fees ?_ (by omega)
  rw [← Backlog.costEval_eq (by omega)]
  exact Exit.cost_737.2

/-- 120000000 * 10 ^ 18 wei of actual request fees bounds every exit request queue by 975. -/
theorem exit_every_boundary_975 (H : Exit.Indexed.Clean cfg start blocks stop)
    (fees : WordFees.actualFeeSum Exit.contract blocks ≤ 120000000 * 10 ^ 18) :
    ∀ b ∈ blocks, (Exit.Indexed.queueAtRequests b).length ≤ 975 := by
  apply exit_every_boundary H fees ?_ (by omega)
  rw [← Backlog.costEval_eq (by omega)]
  exact Exit.cost_975.2


open JauneConsensus

variable {P : Preset} {ccfg : Config} {bls : Bool}
    {checkpoint : BlockChain} {anchor final : GJointState P}

/-- Actual whole-history request fees bound the positional delivery offset.
The destination and Amsterdam segment are supplied; the original four indexed
clauses and conditional built-upon FULL request-codec witness are preserved. -/
theorem deposit_delivery (v : ValidJointG cfg ccfg bls checkpoint anchor final) {budget ceiling : Nat}
    (fees : WordFees.actualFeeSum Deposit.contract v.blocks ≤ budget)
    (cost : budget < Backlog.cost 8 0 (ceiling + 1)) (small : ceiling < 2893)
    {j q : Nat}
    {B D : KeptBlock} {r : Bytes}
    (hB : v.blocks[j]? = some B) (hD : v.blocks[j + q / 64]? = some D)
    (amsterdam : ∀ i ≤ q / 64, ∀ x, v.blocks[j + i]? = some x → x.fork = .amsterdam)
    (queued : (Deposit.Indexed.queueAtRequests B)[q]? = some r) :
    q < ceiling ∧ q / 64 + 1 ≤ (ceiling + 63) / 64 ∧
    (Deposit.Indexed.blockEmissions D)[q % 64]? = some r ∧
    (∀ i ≤ q % 64, (Deposit.Indexed.blockEmissions D)[i]? = (Deposit.Indexed.queueAtRequests B)[64 * (q / 64) + i]?) ∧
    (Deposit.Indexed.submissions v.blocks)[(Deposit.Indexed.emissions (v.blocks.take j)).length + q]? = some r ∧
    (Deposit.Indexed.emissions (v.blocks.take j)).length + q =
      (Deposit.Indexed.emissions (v.blocks.take (j + q / 64))).length + q % 64 ∧
    (v.preBlocks.length ≤ j + q / 64 → ∃ (j' : Nat) (S : GloasStepData (P := P) cfg ccfg bls) (req : _),
      v.run.steps[j']? = some (.gloas S) ∧ S.isFull ∧
      v.run.payloadIndex j' = j + q / 64 - v.preBlocks.length ∧ S.builderDeposits[q % 64]? = some req ∧
      Ssz.serialize req = r) := by
  have bound := deposit_every_boundary v.depositClean fees cost small B (List.mem_iff_getElem?.mpr ⟨j, hB⟩)
  have pos := (List.getElem?_eq_some_iff.mp queued).1
  have hq : q < ceiling := lt_of_lt_of_le pos bound
  refine ⟨hq, by omega, v.latency_indexed_deposit hB hD amsterdam queued⟩

/-- At 120 million ETH of request fees, delivery uses at most 16 payload
positions including the source block, conditional on the existing destination. -/
theorem deposit_delivery_981 (v : ValidJointG cfg ccfg bls checkpoint anchor final) (fees : WordFees.actualFeeSum Deposit.contract v.blocks ≤ 120000000 * 10 ^ 18)
    {j q : Nat}
    {B D : KeptBlock} {r : Bytes}
    (hB : v.blocks[j]? = some B) (hD : v.blocks[j + q / 64]? = some D)
    (amsterdam : ∀ i ≤ q / 64, ∀ x, v.blocks[j + i]? = some x → x.fork = .amsterdam)
    (queued : (Deposit.Indexed.queueAtRequests B)[q]? = some r) :
    q < 981 ∧ q / 64 + 1 ≤ 16 ∧
    (Deposit.Indexed.blockEmissions D)[q % 64]? = some r ∧
    (∀ i ≤ q % 64, (Deposit.Indexed.blockEmissions D)[i]? = (Deposit.Indexed.queueAtRequests B)[64 * (q / 64) + i]?) ∧
    (Deposit.Indexed.submissions v.blocks)[(Deposit.Indexed.emissions (v.blocks.take j)).length + q]? = some r ∧
    (Deposit.Indexed.emissions (v.blocks.take j)).length + q =
      (Deposit.Indexed.emissions (v.blocks.take (j + q / 64))).length + q % 64 ∧
    (v.preBlocks.length ≤ j + q / 64 → ∃ (j' : Nat) (S : GloasStepData (P := P) cfg ccfg bls) (req : _),
      v.run.steps[j']? = some (.gloas S) ∧ S.isFull ∧
      v.run.payloadIndex j' = j + q / 64 - v.preBlocks.length ∧ S.builderDeposits[q % 64]? = some req ∧
      Ssz.serialize req = r) := by
  have cost : (120000000 * 10 ^ 18 : Nat) < Backlog.cost 8 0 (981 + 1) := by
    rw [← Backlog.costEval_eq (by omega)]
    exact LoadBound.cost_981.2
  have delivery := deposit_delivery v fees cost (by omega) hB hD amsterdam queued
  exact ⟨delivery.1, by omega, delivery.2.2⟩

/-- Actual whole-history request fees bound the positional delivery offset.
The destination and Amsterdam segment are supplied; the original four indexed
clauses and conditional built-upon FULL request-codec witness are preserved. -/
theorem exit_delivery (v : ValidJointG cfg ccfg bls checkpoint anchor final) {budget ceiling : Nat}
    (fees : WordFees.actualFeeSum Exit.contract v.blocks ≤ budget)
    (cost : budget < Backlog.cost 2 0 (ceiling + 1)) (small : ceiling < 2893)
    {j q : Nat}
    {B D : KeptBlock} {r : Bytes}
    (hB : v.blocks[j]? = some B) (hD : v.blocks[j + q / 16]? = some D)
    (amsterdam : ∀ i ≤ q / 16, ∀ x, v.blocks[j + i]? = some x → x.fork = .amsterdam)
    (queued : (Exit.Indexed.queueAtRequests B)[q]? = some r) :
    q < ceiling ∧ q / 16 + 1 ≤ (ceiling + 15) / 16 ∧
    (Exit.Indexed.blockEmissions D)[q % 16]? = some r ∧
    (∀ i ≤ q % 16, (Exit.Indexed.blockEmissions D)[i]? = (Exit.Indexed.queueAtRequests B)[16 * (q / 16) + i]?) ∧
    (Exit.Indexed.submissions v.blocks)[(Exit.Indexed.emissions (v.blocks.take j)).length + q]? = some r ∧
    (Exit.Indexed.emissions (v.blocks.take j)).length + q =
      (Exit.Indexed.emissions (v.blocks.take (j + q / 16))).length + q % 16 ∧
    (v.preBlocks.length ≤ j + q / 16 → ∃ (j' : Nat) (S : GloasStepData (P := P) cfg ccfg bls) (req : _),
      v.run.steps[j']? = some (.gloas S) ∧ S.isFull ∧
      v.run.payloadIndex j' = j + q / 16 - v.preBlocks.length ∧ S.builderExits[q % 16]? = some req ∧
      Ssz.serialize req = r) := by
  have bound := exit_every_boundary v.exitClean fees cost small B (List.mem_iff_getElem?.mpr ⟨j, hB⟩)
  have pos := (List.getElem?_eq_some_iff.mp queued).1
  have hq : q < ceiling := lt_of_lt_of_le pos bound
  refine ⟨hq, by omega, v.latency_indexed_exit hB hD amsterdam queued⟩

/-- At 120 million ETH of request fees, delivery uses at most 61 payload
positions including the source block, conditional on the existing destination. -/
theorem exit_delivery_975 (v : ValidJointG cfg ccfg bls checkpoint anchor final) (fees : WordFees.actualFeeSum Exit.contract v.blocks ≤ 120000000 * 10 ^ 18)
    {j q : Nat}
    {B D : KeptBlock} {r : Bytes}
    (hB : v.blocks[j]? = some B) (hD : v.blocks[j + q / 16]? = some D)
    (amsterdam : ∀ i ≤ q / 16, ∀ x, v.blocks[j + i]? = some x → x.fork = .amsterdam)
    (queued : (Exit.Indexed.queueAtRequests B)[q]? = some r) :
    q < 975 ∧ q / 16 + 1 ≤ 61 ∧
    (Exit.Indexed.blockEmissions D)[q % 16]? = some r ∧
    (∀ i ≤ q % 16, (Exit.Indexed.blockEmissions D)[i]? = (Exit.Indexed.queueAtRequests B)[16 * (q / 16) + i]?) ∧
    (Exit.Indexed.submissions v.blocks)[(Exit.Indexed.emissions (v.blocks.take j)).length + q]? = some r ∧
    (Exit.Indexed.emissions (v.blocks.take j)).length + q =
      (Exit.Indexed.emissions (v.blocks.take (j + q / 16))).length + q % 16 ∧
    (v.preBlocks.length ≤ j + q / 16 → ∃ (j' : Nat) (S : GloasStepData (P := P) cfg ccfg bls) (req : _),
      v.run.steps[j']? = some (.gloas S) ∧ S.isFull ∧
      v.run.payloadIndex j' = j + q / 16 - v.preBlocks.length ∧ S.builderExits[q % 16]? = some req ∧
      Ssz.serialize req = r) := by
  have cost : (120000000 * 10 ^ 18 : Nat) < Backlog.cost 2 0 (975 + 1) := by
    rw [← Backlog.costEval_eq (by omega)]
    exact Exit.cost_975.2
  have delivery := exit_delivery v fees cost (by omega) hB hD amsterdam queued
  exact ⟨delivery.1, by omega, delivery.2.2⟩

end Blanc.Lift.BuilderRequest.ActualFeeBounds
