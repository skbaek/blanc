import Blanc.Lift.ObservedReachSplit
import Blanc.Lift.Usdc.V2TransferReach
import Blanc.Lift.Usdc.OldBurnNonIncCallees

/-! Reuse the V2 transfer body even when transferFrom's allowance write follows it. -/
namespace Blanc.Lift.Usdc.V2TransferFromCallee

open Jaune Blanc Blanc.Lift

/-- Isolate the balance-transfer callee without assuming its caller is store-free.
Either the target is one of its exact observed balance stores, or the same path
returns into the original caller continuation. -/
theorem body_bounded_source_or_return {Q : Sevm → Devm → Ninst → Devm → Prop}
    {observe : Conf → Conf → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm} {amount : B256}
    {S : List B256} {M : Mem} {G : Nat} {continuation : SFunc} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b (amount :: recipient.toB256 :: owner.toB256 :: S) M G,
        ImplV2.t_3ef8_c74, continuation :: K⟩ T)
    (hT : AtSstore T) :
    V2TransferReach.BoundedObservedSource Q observe sevm owner recipient T ∨
      ∃ returned, SFunc.RunP Q ImplV2.cert.prog sevm
        (St b (amount :: recipient.toB256 :: owner.toB256 :: S) M G)
        ImplV2.t_3ef8_c74 (.returned returned) ∧
        ObservedReach Q observe ImplV2.cert.prog sevm
          ⟨St b (amount :: recipient.toB256 :: owner.toB256 :: S) M G,
            ImplV2.t_3ef8_c74, continuation :: K⟩ ⟨returned, continuation, K⟩ ∧
        ObservedReach Q observe ImplV2.cert.prog sevm ⟨returned, continuation, K⟩ T := by
  rcases ObservedReach.split run (S := []) rfl with
    ⟨target, inside, same⟩ | returned
  · have atStore : AtSstore target := by rw [same] at hT; exact hT
    have source := V2TransferReach.body_reach_bounded erase inside atStore
      (fun _ member => by cases member)
    rcases source with ⟨⟨value, rest, stack, bound⟩, shape, hash⟩ | ⟨stack, shape, hash⟩
    · rw [same]
      exact .inl (.inl ⟨⟨value, rest, stack, bound⟩, shape, hash.below (continuation :: K)⟩)
    · rw [same]
      exact .inl (.inr ⟨stack, shape, hash.below (continuation :: K)⟩)
  · exact .inr returned

/-- Preserve the prior source-only callee interface. -/
theorem body_source_or_return {Q : Sevm → Devm → Ninst → Devm → Prop}
    {observe : Conf → Conf → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm} {amount : B256}
    {S : List B256} {M : Mem} {G : Nat} {continuation : SFunc} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b (amount :: recipient.toB256 :: owner.toB256 :: S) M G,
        ImplV2.t_3ef8_c74, continuation :: K⟩ T)
    (hT : AtSstore T) :
    V2TransferReach.ObservedSource Q observe sevm owner recipient T ∨
      ∃ returned, SFunc.RunP Q ImplV2.cert.prog sevm
        (St b (amount :: recipient.toB256 :: owner.toB256 :: S) M G)
        ImplV2.t_3ef8_c74 (.returned returned) ∧
        ObservedReach Q observe ImplV2.cert.prog sevm
          ⟨St b (amount :: recipient.toB256 :: owner.toB256 :: S) M G,
            ImplV2.t_3ef8_c74, continuation :: K⟩ ⟨returned, continuation, K⟩ ∧
        ObservedReach Q observe ImplV2.cert.prog sevm ⟨returned, continuation, K⟩ T := by
  rcases body_bounded_source_or_return erase run hT with source | returned
  · exact .inl source.forget
  · exact .inr returned

/-- The actual returning subtraction checks the bound and preserves storage.
No assumed arithmetic bound or store-free caller continuation is needed. -/
theorem subtraction_return {Q : Sevm → Devm → Ninst → Devm → Prop}
    {observe : Conf → Conf → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {amount value tag : B256} {S : List B256}
    {M : Mem} {G : Nat} {continuation : SFunc} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b (amount :: value :: tag :: S) M G,
        ImplV2.t_4123_c78, continuation :: K⟩ T)
    (hT : AtSstore T) :
    amount.toNat ≤ value.toNat ∧ ∃ M' G',
      ObservedReach Q observe ImplV2.cert.prog sevm
        ⟨St b (amount :: value :: tag :: S) M G,
          ImplV2.t_4123_c78, continuation :: K⟩
        ⟨St b ((value - amount) :: S) M' G', continuation, K⟩ ∧
      ObservedReach Q observe ImplV2.cert.prog sevm
        ⟨St b ((value - amount) :: S) M' G', continuation, K⟩ T := by
  obtain ⟨returned, callee, earlier, later⟩ := ObservedReach.return_of_sstoreFree
    (show SstoreFreeSet ImplV2.cert.prog [5, 78, 88, 93] = true from by decide +kernel)
    (show ImplV2.t_4123_c78.sstoreFreeIn [5, 78, 88, 93] = true from by decide +kernel)
    run hT
  obtain ⟨bound, M', G', rfl⟩ := OldBurnNonIncCallees.sub_ret
    (version := .v2) (by decide) (SFunc.RunP.mono erase callee)
  exact ⟨bound, M', G', earlier, later⟩

end Blanc.Lift.Usdc.V2TransferFromCallee
