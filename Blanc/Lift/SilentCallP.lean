import Blanc.Lift.FrameSkip
import Blanc.Lift.InvWalkWorld

/-!
# Crossing a silent internal call under any step relation (contract-neutral)

`ricP_call_silent`: the `SFunc.RunCutP P` form of `ric_call_silent` (`FrameSkip.lean`), for any
instruction relation `P` that implies Jaune's steps.  A `callNext` into an entry of a `SilentSet`
closure that is also a `NoHaltSet` (so the callee returns), from a walk state whose top words match
the callee's declared frame, continues from a state with the caller's world state and the stack
`Y ++ S.drop e.frame.length`, `Y.length = e.rets`.
-/

namespace Blanc.Lift

open Jaune

theorem ricP_call_silent {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {code : ByteArray} {c : Cert}
    (hc : Cert.check code c = true) {sevm : Sevm} (hfork : CoveredFork sevm.benvStat.fork)
    {Sk Hk : List Nat} (hS : SilentSet c.prog Sk = true) (hH : NoHaltSet c.prog Hk = true)
    {k : Nat} (hkS : k ∈ Sk) (hkH : k ∈ Hk) {e : Entry} {g : SFunc}
    (he : c.entries[k]? = some e) (hg : c.prog[k]? = some g)
    {C : List Nat} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {dd ρ : B256} {f : SFunc}
    {r : Seg} (run : SFunc.RunCutP P c.prog sevm C (St b (dd :: S) M G) (.callNext k f) r)
    (hframe : FrameMatches ρ e.frame (S.take e.frame.length)) :
    ∃ b' Y M' G', b'.state = b.state ∧ Y.length = e.rets ∧
      SFunc.RunCutP P c.prog sevm C (St b' (Y ++ S.drop e.frame.length) M' G') f r := by
  have hgS : g.silent = true ∧ g.refs.all (· ∈ Sk) = true := by
    have h := (List.all_eq_true.mp hS) k hkS
    rw [hg] at h
    simpa only [Bool.and_eq_true] using h
  cases run with
  | callHalt d hget pop callee =>
    rw [hg] at hget
    cases hget
    exact (SFunc.RunP.not_halted_entry hH hkH hg callee rfl).elim
  | callRet d hget pop callee cont =>
    rw [hg] at hget
    cases hget
    rename_i D
    obtain ⟨-, hd⟩ := St.of_pop1 pop
    rw [hd] at callee
    have hstate : D.state = b.state :=
      SFunc.RunP.state_of_silent hP hS hgS.1 hgS.2 callee
    obtain ⟨Y, hY, hlen⟩ := callee.entry_stack_below hP hc hfork he hg
      (List.take_append_drop _ _).symm hframe
    refine ⟨D, Y, D.memory, D.gasLeft, hstate, hlen, ?_⟩
    rw [St.stack] at hY
    rw [← St.self hY rfl]
    exact cont

end Blanc.Lift
