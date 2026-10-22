import Blanc.Lift.Curve3Pool.Walk.ViewsKit
import Blanc.Lift.ThreeWordFrame
import Blanc.Lift.Curve3Pool.Callee.GetY

/-!
# The `get_dy` views' kit: `get_y` bridged, indexed loads

* `xa_vGetY`: `get_y` (entry 252, pc `0x18a4`) crossed on the derivation and read through
  `getY_spec`, over the views' carrier;
* The generic three-word selection, address arithmetic and indexed-load facts are imported
  from `ThreeWordFrame`; this file only bridges them to the pool model and callees.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

theorem dy_pickWord3_toNat {n : Nat} (hn : n < 3) (a0 a1 a2 : B256) :
    (pickWord3 n a0 a1 a2).toNat = (V3.mk a0.toNat a1.toNat a2.toNat).get ⟨n, hn⟩ := by
  unfold pickWord3 V3.get
  by_cases h0 : n = 0
  · simp only [h0, ↓reduceIte]
  · by_cases h1 : n = 1
    · subst h1; rfl
    · simp only [h0, h1, ↓reduceIte]

section

variable {sevm : Sevm} {post b d : Devm} {ρ : B256} {S : List B256} {M : Mem} {G : Nat}
  {L : List Exec.Frame} {LW : List (Nat × B256)} {s : State}

theorem vk_gy_entry :
    cert.entries[252]? = some ⟨0x18a4, [.ret, .unk, .unk, .unk, .unk, .unk, .unk], 1⟩ := by rfl
theorem vk_gy_mems : mems.getD 252 [] = [] := by decide +kernel

/-- **`get_y` crossed and read** over the carrier: `y` with `getYChk amp i j x xp = some y` on
`S` (`amp = aChk s t`), over `aBase`, the words off `gyWin` kept and `y` at word `0`. -/
theorem xa_vGetY (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) {i j x x0 x1 x2 : B256}
    (ha : Abstracts (b.getStor sevm.currentTarget) s) (hV : VW M LW)
    (h : XAt sevm post 0x18a4 (St b (ρ :: i :: j :: x :: x0 :: x1 :: x2 :: S) M G) L) :
    ∃ v M' G', XAt sevm post ρ.toNat (St (aBase sevm b) (v :: S) M' G') L ∧
      ∃ amp, aChk s sevm.benvStat.time.toNat = some amp ∧
      ∃ (hi : i.toNat < 3) (hj : j.toNat < 3),
        getYChk amp ⟨i.toNat, hi⟩ ⟨j.toNat, hj⟩ x.toNat (V3.mk x0.toNat x1.toNat x2.toNat).get =
          some v.toNat ∧
      VW M' ((0, v) :: wordsOffW gyWin LW) := by
  rcases xa_calleeC hc vk_gy_entry t_18a4_c252_prog vk_gy_mems gy_execFreeSet gy_free hcode
      hfork (S := [ρ, i, j, x, x0, x1, x2]) (base := S) rfl
      (.cons rfl (.cons trivial (.cons trivial (.cons trivial (.cons trivial (.cons trivial
        (.cons trivial .nil))))))) h with
    ⟨run, -⟩ | ⟨d', S', run, hx, -, -⟩
  · obtain ⟨d, he, -⟩ := getY_spec hfork ha hV.wf hV.al run
    cases he
  · obtain ⟨d, he, v, M', G', rfl, amp, hamp, hi, hj, hy, hk, hw0, hwf, hal⟩ :=
      getY_spec hfork ha hV.wf hV.al run
    cases he
    have hV' := hV.keepsOff hk hwf hal
    exact ⟨v, M', G', hx, amp, hamp, hi, hj, hy,
      ⟨Words.cons.mpr ⟨hw0 0 v List.mem_cons_self, hV'.words⟩, hwf, hal⟩⟩

end

end Blanc.Lift.Curve3Pool
