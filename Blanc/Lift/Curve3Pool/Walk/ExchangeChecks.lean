import Blanc.Lift.Curve3Pool.Bridge
import Blanc.Lift.Curve3Pool.Callee.Xp
import Blanc.Lift.Curve3Pool.Callee.GetY

/-!
# `exchange`'s bridged callees

The two internal calls of `exchange`, crossed from the walked frame state with `xa_callee`
(`Bridge.lean`, which takes the certificate's checked trees and so imports `Check.lean`; the
walk segments themselves do not):

* `xa_ex_xpMem`: `_xp_mem(old_balances)` (entry 34, pc `0x3a1`), by `xpMem_spec`;
* `xa_ex_getY`: `get_y(i, j, x, xp)` (entry 252, pc `0x18a4`), by `getY_spec`.

In both cases the callee cannot halt the frame (its spec says every outcome is a return), so
the walk resumes at the return tag in the actual returned state with the same remaining
children.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

theorem xpMem_entry : cert.entries[34]? = some ⟨0x3a1, [.ret, .unk, .unk, .unk], 3⟩ := rfl

theorem xpMem_prog : cert.prog[34]? = some t_03a1_c34 := by decide +kernel

theorem xpMem_mems : mems.getD 34 [] = [] := by decide

theorem xpMem_free :
    t_03a1_c34.execFreeIn [34, 59, 86, 108, 129, 151, 173] = true := by decide +kernel

/-- **`_xp_mem` crossed from a walked state** (`0x3a1`, return tag `ρ`). -/
theorem xa_ex_xpMem {sevm : Sevm} {post b : Devm} {ρ a0 a1 a2 : B256} {S : List B256} {M : Mem}
    {G : Nat} {L : List Exec.Frame} (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork) (hW : Mem.Wf M)
    (h : XAt sevm post 0x3a1 (St b (ρ :: a0 :: a1 :: a2 :: S) M G) L) :
    ∃ x0 x1 x2 M' G', XAt sevm post ρ.toNat (St b (x0 :: x1 :: x2 :: S) M' G') L ∧
      xpChk ⟨a0.toNat, a1.toNat, a2.toNat⟩ = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
      Mem.KeepsOff M M' xpMemWin ∧ Mem.Wf M' := by
  rcases xa_callee xpMem_entry xpMem_prog xpMem_mems xpMem_execFreeSet xpMem_free hcode hfork
      (S := [ρ, a0, a1, a2]) (base := S) rfl
      (List.Forall₂.cons rfl (.cons trivial (.cons trivial (.cons trivial .nil)))) h with
    ⟨run, -⟩ | ⟨d', S', run, hx, -, -⟩
  · obtain ⟨d, hd, -⟩ := xpMem_spec hW run
    cases hd
  · obtain ⟨d, hd, x0, x1, x2, M', G', rfl, hxp, hk, hwf, -⟩ := xpMem_spec hW run
    cases hd
    exact ⟨x0, x1, x2, M', G', hx, hxp, hk, hwf⟩

theorem getY_entry :
    cert.entries[252]? = some ⟨0x18a4, [.ret, .unk, .unk, .unk, .unk, .unk, .unk], 1⟩ := by
  have h : (cert.entries[252]?).map (fun e => (e.pc, e.frame, e.rets)) =
      some (0x18a4, [.ret, .unk, .unk, .unk, .unk, .unk, .unk], 1) := by decide +kernel
  revert h
  generalize cert.entries[252]? = o
  rcases o with _ | ⟨pc, fr, r⟩
  · intro h; cases h
  · intro h
    cases h
    rfl

theorem getY_mems : mems.getD 252 [] = [] := by decide +kernel

/-- **`get_y` crossed from a walked state** (`0x18a4`, return tag `ρ`), over a storage that
abstracts `s`. -/
theorem xa_ex_getY {sevm : Sevm} {post b : Devm} {ρ i j x x0 x1 x2 : B256} {S : List B256}
    {M : Mem} {G : Nat} {L : List Exec.Frame} {s : State} (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork)
    (ha : Abstracts (b.getStor sevm.currentTarget) s) (hW : Mem.Wf M) (hsz : M.size % 32 = 0)
    (h : XAt sevm post 0x18a4 (St b (ρ :: i :: j :: x :: x0 :: x1 :: x2 :: S) M G) L) :
    ∃ v M' G', XAt sevm post ρ.toNat (St (aBase sevm b) (v :: S) M' G') L ∧
      ∃ amp, aChk s sevm.benvStat.time.toNat = some amp ∧
      ∃ (hi : i.toNat < 3) (hj : j.toNat < 3),
        getYChk amp ⟨i.toNat, hi⟩ ⟨j.toNat, hj⟩ x.toNat (V3.mk x0.toNat x1.toNat x2.toNat).get =
          some v.toNat ∧
      Mem.KeepsOff M M' gyWin ∧ Mem.Wf M' ∧ M'.size % 32 = 0 := by
  rcases xa_callee getY_entry t_18a4_c252_prog getY_mems gy_execFreeSet gy_free hcode hfork
      (S := [ρ, i, j, x, x0, x1, x2]) (base := S) rfl
      (List.Forall₂.cons rfl (.cons trivial (.cons trivial (.cons trivial (.cons trivial
        (.cons trivial (.cons trivial .nil))))))) h with
    ⟨run, -⟩ | ⟨d', S', run, hx, -, -⟩
  · obtain ⟨d, hd, -⟩ := getY_spec hfork ha hW hsz run
    cases hd
  · obtain ⟨d, hd, v, M', G', rfl, amp, hamp, hi, hj, hy, hk, -, hwf, hsz'⟩ :=
      getY_spec hfork ha hW hsz run
    cases hd
    exact ⟨v, M', G', hx, amp, hamp, hi, hj, hy, hk, hwf, hsz'⟩

end Blanc.Lift.Curve3Pool
