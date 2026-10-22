import Blanc.Lift.Usdc.AllowLocality
import Blanc.Lift.Usdc.ImplWs

/-!
# Allowance locality for FiatTokenV2_2

The existing V2_2 write-site certificate supplies the same finite-row locality
interface as the older implementations. The structural table check concerns
the unchanged generated root annotations; it supplies no signature or
initializer-exclusion assumption. The inherited `initializeV2_1` observation
feeds the later direct initializer-effect and zero-preservation proof.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite

/-- V2_2's two permit overloads are owner-keyed; its three dynamic initializers
retain their exact checked exceptions. `initializeV2_1` has no exception. -/
def selV2_2 : SelTable :=
  ⟨selV2T, [0x095ea7b3, 0x39509351, 0xa457c2d7], [0x9fd5a6cf, 0xd505accf],
    [0x3357162b, 0x430239b4, 0xd608ea64]⟩

theorem implV2_2_allowSitesOk :
    (wsRoot ImplWs.implWsAnn).all (allowSiteOk selV2_2) = true := by
  decide +kernel

/-- Every protected allowance write in an actual V2_2 run is non-increasing
or belongs to one of the exact caller, owner or initializer exceptions. -/
theorem implV2_2_allowLocality {pair : Adr} {Tr : Adr → Prop} {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = Impl.code)
    (fork : CoveredFork sevm.benvStat.fork)
    (sep : RowSep 10 pair.toB256 (AllowKey Tr) (wsRoot ImplWs.implWsAnn)
      (WriteSite.Env.root sevm)) :
    SProg.RunP (fun s d n d' => StepIn ⟨0, sevm, pre, .ok post, run⟩ s d n d' ∧
        GuardObs (fun x => ∃ g, Tr g ∧ allowSlot pair g = x)
          (AllowedFrame selV2_2 pair (WriteSite.Env.root sevm)) s d n)
      Impl.cert.prog sevm pre post :=
  allow_locality (by decide) implV2_2_allowSitesOk sep (implRun_ws run code fork)

/-- The inherited `initializeV2_1` path has no increasing protected-row
exception in V2_2 either. The direct initializer-effect proof consumes this
without a version-state, caller, signature or upgrade-origin premise. -/
theorem implV2_2_initializeV2_1_nonInc
    {pair : Adr} {Tr : Adr → Prop} {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = Impl.code)
    (fork : CoveredFork sevm.benvStat.fork)
    (selector : selV2T.eval (WriteSite.Env.root sevm) = 0x2fc81e09)
    (sep : RowSep 10 pair.toB256 (AllowKey Tr) (wsRoot ImplWs.implWsAnn)
      (WriteSite.Env.root sevm)) :
    SProg.RunP (fun s d n d' => StepIn ⟨0, sevm, pre, .ok post, run⟩ s d n d' ∧
        GuardObs (fun x => ∃ g, Tr g ∧ allowSlot pair g = x) False s d n)
      Impl.cert.prog sevm pre post := by
  have excluded : ¬ AllowedFrame selV2_2 pair (WriteSite.Env.root sevm) := by
    rintro (⟨caller, _⟩ | ⟨owner, _⟩ | initializer)
    · change selV2T.eval (WriteSite.Env.root sevm) ∈
        [0x095ea7b3, 0x39509351, 0xa457c2d7] at caller
      rw [selector] at caller
      exact (by decide : (0x2fc81e09 : B256) ∉
        [0x095ea7b3, 0x39509351, 0xa457c2d7]) caller
    · change selV2T.eval (WriteSite.Env.root sevm) ∈ [0x9fd5a6cf, 0xd505accf] at owner
      rw [selector] at owner
      exact (by decide : (0x2fc81e09 : B256) ∉ [0x9fd5a6cf, 0xd505accf]) owner
    · change selV2T.eval (WriteSite.Env.root sevm) ∈
        [0x3357162b, 0x430239b4, 0xd608ea64] at initializer
      rw [selector] at initializer
      exact (by decide : (0x2fc81e09 : B256) ∉
        [0x3357162b, 0x430239b4, 0xd608ea64]) initializer
  refine SProg.RunP.mono ?_ (implV2_2_allowLocality run code fork sep)
  intro s d n d' h
  refine ⟨h.1, ?_⟩
  intro store x v rest stack tracked
  rcases h.2 store x v rest stack tracked with allowed | nonInc
  · exact (excluded allowed).elim
  · exact Or.inr nonInc

end Blanc.Lift.Usdc
