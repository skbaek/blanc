import Blanc.Lift.FrameSkip
import Blanc.Lift.UniswapV2Pair.Check

/-! `ric_call_silent` on the Pair's `kLast()` getter: the internal call into entry 43
(`SLOAD` of slot 11) is crossed without walking it.  The hand walk
(`getterScalar_callee_inv`) gives the same shape: two words over the selector, world state
unchanged. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {sel : B256} {r : Seg}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.RunCut cert.prog sevm []
      (St b (Bytes.toB256 [0x13, 0xdd] :: Bytes.toB256 [0x03, 0x9b] :: [sel]) M G)
      (.callNext 43 t_039b_c88) r) :
    (∃ b' y z M' G', b'.state = b.state ∧
        SFunc.RunCut cert.prog sevm [] (St b' [y, z, sel] M' G') t_039b_c88 r) ∨
      (∃ D, D.state = b.state ∧ r = .done (.halted D)) := by
  rcases ric_call_silent (e := ⟨0x13dd, [.ret], 2⟩) (ρ := Bytes.toB256 [0x03, 0x9b])
      (S := [Bytes.toB256 [0x03, 0x9b], sel]) cert_check
      fork (Sk := [43]) (by decide) List.mem_cons_self rfl rfl
      (List.Forall₂.cons rfl List.Forall₂.nil) run with
    ⟨b', Y, M', G', hstate, hlen, cont⟩ | halted
  · match Y, hlen, cont with
    | [y, z], _, cont => exact .inl ⟨b', y, z, M', G', hstate, cont⟩
  · exact .inr halted

end Blanc.Lift.UniswapV2Pair
