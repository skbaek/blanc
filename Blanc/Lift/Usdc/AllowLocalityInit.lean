import Blanc.Lift.Usdc.AllowLocality

/-!
# Initializer allowance observations

The `initializeV2_1` selector is outside every exception in V2_1's checked
allowance-locality table. Its actual successful runs therefore carry an
unconditional nonincrease observation for the demanded Pair allowance rows.
This is the initializer input to the later chronological zero-preservation
proof. Historical application still needs historical lift soundness.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite

/-- V2_1's `initializeV2_1` has no increasing protected-allowance exception.
The later zero-preservation fold consumes this observation; no initialized
flag, caller restriction, signature exclusion or updater-origin premise enters. -/
theorem implV2_1_initializeV2_1_nonInc
    {pair : Adr} {Tr : Adr → Prop} {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = ImplV2_1.code)
    (fork : CoveredFork sevm.benvStat.fork)
    (selector : selV2T.eval (WriteSite.Env.root sevm) = 0x2fc81e09)
    (sep : RowSep 10 pair.toB256 (AllowKey Tr) (wsRoot ImplV2_1Ws.implWsAnn)
      (WriteSite.Env.root sevm)) :
    SProg.RunP (fun s d n d' => StepIn ⟨0, sevm, pre, .ok post, run⟩ s d n d' ∧
        GuardObs (fun x => ∃ g, Tr g ∧ allowSlot pair g = x) False s d n)
      ImplV2_1.cert.prog sevm pre post := by
  have excluded : ¬ AllowedFrame selV2_1 pair (WriteSite.Env.root sevm) := by
    rintro (⟨caller, _⟩ | ⟨owner, _⟩ | initializer)
    · change selV2T.eval (WriteSite.Env.root sevm) ∈
        [0x095ea7b3, 0x39509351, 0xa457c2d7] at caller
      rw [selector] at caller
      exact (by decide : (0x2fc81e09 : B256) ∉
        [0x095ea7b3, 0x39509351, 0xa457c2d7]) caller
    · change selV2T.eval (WriteSite.Env.root sevm) ∈ [0xd505accf] at owner
      rw [selector] at owner
      exact (by decide : (0x2fc81e09 : B256) ∉ [0xd505accf]) owner
    · change selV2T.eval (WriteSite.Env.root sevm) ∈ [0x3357162b, 0xd608ea64] at initializer
      rw [selector] at initializer
      exact (by decide : (0x2fc81e09 : B256) ∉ [0x3357162b, 0xd608ea64]) initializer
  refine SProg.RunP.mono ?_ (implV2_1_allowLocality run code fork sep)
  intro s d n d' h
  refine ⟨h.1, ?_⟩
  intro store x v rest stack tracked
  rcases h.2 store x v rest stack tracked with allowed | nonInc
  · exact (excluded allowed).elim
  · exact Or.inr nonInc

end Blanc.Lift.Usdc
