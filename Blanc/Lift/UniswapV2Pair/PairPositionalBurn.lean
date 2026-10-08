import Blanc.Lift.UniswapV2Pair.PairPositionalAdmission
import Blanc.Lift.UniswapV2Pair.BurnPositionalRefinement

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The Burn supply retains the same seven-call canonical result and both
recursively admitted mutable queues, under the original separated universe. -/
theorem pair_admitted_burn_supply {U : WriterKey → Prop}
    (inj : WriterInj U) (apart : WriterApart U) (sem : CodeSem)
    (image : sem.image = some code.toList) :
    PairAdmittedSupply U (fun sevm => Blanc.Sevm.selector sevm = 0x89afcb44) := by
  intro current invocation sevm b post G run K codeEq installed fork freshOutput
    representable selector good sub rep
  have row : ∀ k ∈ [WriterKey.balance sevm.currentTarget], U k := by
    intro k member
    rw [List.mem_singleton] at member
    rw [member]
    exact good.pairRow
  have fresh := Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub row
  have extended := writerExtend_universe sub row
  obtain ⟨result⟩ := burnRaw_source_authentic invocation codeEq fork selector (rep.extend fresh)
    (Or.inr (List.mem_singleton_self _)) run inj apart extended good.mint sem image
    (by rw [installed]; exact image.symm) good.locked good.views
  refine ⟨_, _, _, _, result.keys, ?_, result.admitted, rfl, result.output.symm,
    fun k tracked => result.grown k (Or.inl tracked), result.inside, result.storage⟩
  have admittedEntry := PairEntryAt.burn (root := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩)
    selector
  rw [show (0xffffffffffffffffffffffffffffffffffffffff : B256) = ~~~ addressMask from
    by decide, B256.and_comm, and_mask_word, toAdr_toB256] at admittedEntry
  exact admittedEntry

end Blanc.Lift.UniswapV2Pair
