import Blanc.Lift.Curve3Pool.Walk.Kit
import Blanc.Lift.Curve3Pool.Bridge
import Blanc.Lift.Curve3Pool.Callee.A

/-!
# `remove_liquidity_imbalance`, part 3: the bridged `_A` call

From `_A`'s entry (`0xa9`, after the setup's jump) through the internal return: the
walk crosses `_A` with `Bridge.xa_A` and reads off its value contract `Callee/A.a_spec`
(`prog` is the same abbrev as `cert.prog`, so the run plugs in directly).

`xa_rli_callA`: with the storage abstraction, `_A` either halts the frame with no
further child, or returns `A` with `aChk s t = some A.toNat` on top of the caller's
stack, over `aBase`, the entry memory kept off `aWin`, resuming at the return address.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- **`remove_liquidity_imbalance` across `_A`** (see the module note). -/
theorem xa_rli_callA {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {ret : B256} {S : List B256} {s : State}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (ha : Abstracts (b.getStor sevm.currentTarget) s) (hwf : Mem.Wf M)
    (h : XAt sevm post 0xa9 (St b (ret :: S) M G) L) :
    (SFunc.Run cert.prog sevm (St b (ret :: S) M G) t_00a9_c27 (.halted post) ∧ L = []) ∨
    ∃ (d' : Devm) (A : B256) (M' : Mem) (G' : Nat),
      aChk s sevm.benvStat.time.toNat = some A.toNat ∧
      d' = St (aBase sevm b) (A :: S) M' G' ∧
      Mem.KeepsOff M M' aWin ∧ Mem.Wf M' ∧ (M.size % 32 = 0 → M'.size % 32 = 0) ∧
      XAt sevm post ret.toNat d' L := by
  rcases xa_A hcode hfork rfl h with ⟨run, hL⟩ | ⟨d', A, run, hx, hst⟩
  · exact Or.inl ⟨run, hL⟩
  · obtain ⟨d, hr, v, M', G', hd, hamp, hk, hwf', hal⟩ := a_spec hfork ha hwf run
    cases hr
    subst hd
    exact Or.inr ⟨_, _, _, _, hamp, rfl, hk, hwf', hal, hx⟩

end Blanc.Lift.Curve3Pool
