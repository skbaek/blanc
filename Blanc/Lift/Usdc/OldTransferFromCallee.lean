import Blanc.Lift.Usdc.OldTransferBodyReach

/-! V2/V2.1 actual transfer and subtraction returns with original observations. -/
namespace Blanc.Lift.Usdc.OldTransferFromCallee
open Jaune Blanc Blanc.Lift

/-- Isolate the balance-transfer callee without assuming its caller is store-free.
Either the target is one of its exact observed balance stores, or the same path
returns into the original caller continuation. -/
theorem body_bounded_source_or_return {version : ModernVersion} (old : version ≠ .v2_2)
    {Q : Sevm → Devm → Ninst → Devm → Prop}
    {observe : Conf → Conf → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm} {amount : B256}
    {S : List B256} {M : Mem} {G : Nat} {continuation : SFunc} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe version.cert.prog sevm
      ⟨St b (amount :: recipient.toB256 :: owner.toB256 :: S) M G,
        OldTransferBodyReach.body version, continuation :: K⟩ T)
    (hT : AtSstore T) :
    OldTransferBodyReach.BoundedObservedSource Q observe sevm owner recipient T ∨
      ∃ returned, SFunc.RunP Q version.cert.prog sevm
        (St b (amount :: recipient.toB256 :: owner.toB256 :: S) M G)
        (OldTransferBodyReach.body version) (.returned returned) ∧
        ObservedReach Q observe version.cert.prog sevm
          ⟨St b (amount :: recipient.toB256 :: owner.toB256 :: S) M G,
            OldTransferBodyReach.body version, continuation :: K⟩ ⟨returned, continuation, K⟩ ∧
        ObservedReach Q observe version.cert.prog sevm ⟨returned, continuation, K⟩ T := by
  rcases ObservedReach.split run (S := []) rfl with
    ⟨target, inside, same⟩ | returned
  · have atStore : AtSstore target := by rw [same] at hT; exact hT
    have source := OldTransferBodyReach.body_reach_bounded old erase inside atStore
      (fun _ member => by cases member)
    rcases source with ⟨⟨value, rest, stack, bound⟩, shape, hash⟩ | ⟨stack, shape, hash⟩
    · rw [same]
      exact .inl (.inl ⟨⟨value, rest, stack, bound⟩, shape, hash.below (continuation :: K)⟩)
    · rw [same]
      exact .inl (.inr ⟨stack, shape, hash.below (continuation :: K)⟩)
  · exact .inr returned

def subFreeEntries : ModernVersion → List Nat
  | .v2 => [5, 78, 88, 93]
  | .v2_1 => [6, 76, 86, 91]
  | .v2_2 => []

/-- The actual returning subtraction checks the bound and preserves storage.
No assumed arithmetic bound or store-free caller continuation is needed. -/
theorem subtraction_return {version : ModernVersion} (old : version ≠ .v2_2)
    {Q : Sevm → Devm → Ninst → Devm → Prop}
    {observe : Conf → Conf → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {amount value tag : B256} {S : List B256}
    {M : Mem} {G : Nat} {continuation : SFunc} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe version.cert.prog sevm
      ⟨St b (amount :: value :: tag :: S) M G,
        OldBurnNonIncCallees.entry version, continuation :: K⟩ T)
    (hT : AtSstore T) :
    amount.toNat ≤ value.toNat ∧ ∃ M' G',
      ObservedReach Q observe version.cert.prog sevm
        ⟨St b (amount :: value :: tag :: S) M G,
          OldBurnNonIncCallees.entry version, continuation :: K⟩
        ⟨St b ((value - amount) :: S) M' G', continuation, K⟩ ∧
      ObservedReach Q observe version.cert.prog sevm
        ⟨St b ((value - amount) :: S) M' G', continuation, K⟩ T := by
  obtain ⟨returned, callee, earlier, later⟩ := ObservedReach.return_of_sstoreFree
    (show SstoreFreeSet version.cert.prog (subFreeEntries version) = true from by
      cases version <;> decide +kernel)
    (show (OldBurnNonIncCallees.entry version).sstoreFreeIn (subFreeEntries version) = true from by
      cases version <;> decide +kernel)
    run hT
  obtain ⟨bound, M', G', rfl⟩ := OldBurnNonIncCallees.sub_ret
    (version := version) old (SFunc.RunP.mono erase callee)
  exact ⟨bound, M', G', earlier, later⟩

end Blanc.Lift.Usdc.OldTransferFromCallee
