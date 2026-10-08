import Blanc.Lift.UniswapV2Pair.FeeMintSource

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Every incoming tracked key remains represented after the actual fee
branch, including its conditional finite recipient extension. -/
theorem feeBranchSourceKeys_contains {K : WriterKey → Prop} {st : State}
    {sevm : Sevm} {b : Devm} {w r0 r1 : B256} {key : WriterKey}
    (tracked : K key) : feeBranchSourceKeys K st sevm b w r0 r1 key := by
  unfold feeBranchSourceKeys
  split
  · exact tracked
  · split
    · exact tracked
    · split
      · split
        · exact tracked
        · exact Or.inl tracked
      · exact tracked

theorem lpMintTouched_rows {U : WriterKey → Prop} {a : Adr}
    (row : U (.balance a)) : ∀ k ∈ lpMintTouched a, U k := by
  intro k member
  simp only [lpMintTouched, List.mem_cons, List.not_mem_nil, or_false] at member
  rw [member]
  exact row

theorem feeMintFresh_of_universe {K U : WriterKey → Prop} {feeTo : B256}
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (row : U (.balance feeTo.toAdr)) (st : State) (sevm : Sevm) (b : Devm) (r0 r1 : B256) :
    FeeMintFresh K st sevm b feeTo r0 r1 := by
  intro _ _ _ _
  exact Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub (lpMintTouched_rows row)

theorem pairFeeSourceKeys_sub {K U : WriterKey → Prop} {feeTo : B256}
    (sub : ∀ k, K k → U k) (row : U (.balance feeTo.toAdr))
    (st : State) (sevm : Sevm) (b : Devm) (r0 r1 : B256) :
    ∀ k, feeBranchSourceKeys K st sevm b feeTo r0 r1 k → U k := by
  intro k tracked
  have extended : WriterExtend K (lpMintTouched feeTo.toAdr) k → U k := by
    intro member
    rcases member with old | new
    · exact sub k old
    · exact lpMintTouched_rows row k new
  unfold feeBranchSourceKeys at tracked
  split at tracked
  · exact sub k tracked
  · split at tracked
    · exact sub k tracked
    · split at tracked
      · split at tracked
        · exact sub k tracked
        · exact extended tracked
      · exact sub k tracked

theorem feeBranchSourceFee_unlocked (st : State) (sevm : Sevm) (b : Devm)
    (w r0 r1 : B256) :
    (feeBranchSourceFee st sevm b w r0 r1).state.unlocked = st.unlocked := by
  unfold feeBranchSourceFee
  split
  · rfl
  · split
    · rfl
    · split
      · unfold feeGrowthSourceFee
        split <;> rfl
      · rfl


end Blanc.Lift.UniswapV2Pair
