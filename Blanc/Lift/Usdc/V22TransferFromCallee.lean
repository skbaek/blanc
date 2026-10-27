import Blanc.Lift.Usdc.V22TransferReach
import Blanc.Lift.Usdc.RefineAdminCallees
import Blanc.Lift.ObservedReachSplit
import Blanc.Lift.FrameWalkKit

/-! Original V2.2 transfer and subtraction returns into a possibly writing caller. -/
namespace Blanc.Lift.Usdc.V22TransferFromCallee
open Jaune Blanc Blanc.Lift

/-- Isolate the actual balance callee while preserving the caller's continuation
and both observed path segments. The balance sources retain their own hashes. -/
theorem body_source_or_return {Q : Sevm → Devm → Ninst → Devm → Prop}
    {observe : Conf → Conf → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm} {amount : B256}
    {S : List B256} {M : Mem} {G : Nat} {continuation : SFunc} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (amount :: recipient.toB256 :: owner.toB256 :: S) M G,
        Impl.t_3f98_c93, continuation :: K⟩ T)
    (hT : AtSstore T) :
    V22TransferReach.ObservedSource Q observe sevm owner recipient T ∨
      ∃ returned, SFunc.RunP Q Impl.cert.prog sevm
        (St b (amount :: recipient.toB256 :: owner.toB256 :: S) M G)
        Impl.t_3f98_c93 (.returned returned) ∧
        ObservedReach Q observe Impl.cert.prog sevm
          ⟨St b (amount :: recipient.toB256 :: owner.toB256 :: S) M G,
            Impl.t_3f98_c93, continuation :: K⟩ ⟨returned, continuation, K⟩ ∧
        ObservedReach Q observe Impl.cert.prog sevm ⟨returned, continuation, K⟩ T := by
  rcases ObservedReach.split run (S := []) rfl with
    ⟨target, inside, same⟩ | returned
  · have atStore : AtSstore target := by rw [same] at hT; exact hT
    have source := V22TransferReach.body_reach_observed erase inside atStore
      (fun _ member => by cases member)
    rcases source with ⟨stack, shape, hash⟩ | ⟨stack, shape, hash⟩
    · rw [same]
      exact .inl (.inl ⟨stack, shape, hash.below (continuation :: K)⟩)
    · rw [same]
      exact .inl (.inr ⟨stack, shape, hash.below (continuation :: K)⟩)
  · exact .inr returned

/-- The original subtraction must return before the selected store, preserving
storage and establishing the actual checked arithmetic bound. -/
theorem subtraction_return {Q : Sevm → Devm → Ninst → Devm → Prop}
    {observe : Conf → Conf → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {amount value tag : B256} {S : List B256}
    {M : Mem} {G : Nat} {continuation : SFunc} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (amount :: value :: tag :: S) M G,
        Impl.t_4163_c100, continuation :: K⟩ T)
    (hT : AtSstore T) :
    amount ≤ value ∧ ∃ G',
      ObservedReach Q observe Impl.cert.prog sevm
        ⟨St b (amount :: value :: tag :: S) M G,
          Impl.t_4163_c100, continuation :: K⟩
        ⟨St b ((value - amount) :: S) M G', continuation, K⟩ ∧
      ObservedReach Q observe Impl.cert.prog sevm
        ⟨St b ((value - amount) :: S) M G', continuation, K⟩ T := by
  obtain ⟨returned, callee, earlier, later⟩ := ObservedReach.return_of_sstoreFree
    (show SstoreFreeSet Impl.cert.prog [100] = true from by decide +kernel)
    (show Impl.t_4163_c100.sstoreFreeIn [100] = true from by decide +kernel) run hT
  obtain ⟨G', rfl, bound⟩ := Impl.sub_ret (SFunc.RunP.mono erase callee)
  exact ⟨B256.not_lt.mp (gtCheck_eq_zero bound), G', earlier, later⟩

end Blanc.Lift.Usdc.V22TransferFromCallee
