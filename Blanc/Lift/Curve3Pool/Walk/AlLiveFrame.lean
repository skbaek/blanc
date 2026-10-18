import Blanc.Lift.Curve3Pool.Walk.AlLiveMid
import Blanc.Lift.Curve3Pool.Walk.AlLiveFront
import Blanc.Lift.Curve3Pool.Walk.AlLiveD0

/-!
# `add_liquidity`, forward: the whole frame

`rx_al_frame1` (positive supply) and `rx_al_frame0` (first deposit): from the runtime's entry
with an empty stack and memory to a halt, through the dispatcher, the prologue (lock, `_A()`,
`totalSupply()`), `D0` on a positive supply, the deposit loop, `D1`, the fee loop and `D2` or the
first deposit's store, the mint, the event and the lock's release.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

section Frame

variable {sevm : Sevm} {pre : Devm} {s : State} {G U amp : Nat} {T B1 B2 : B256}
  {W : Nat → Devm → Prop} {Wm : Devm → Prop}

/-- The pool's storage once the lock is taken. -/
abbrev alLocked1 (σ : Stor) : Stor := σ.set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1])

/-- The pool's balances as the prologue reads them. -/
abbrev alOld (σ : Stor) : Nat → B256 := fun j => balAt σ j

/-- **`add_liquidity` on a positive supply, forward.** -/
theorem rx_al_frame1 {xa xb xc : V3} {v0 v1 v2 : Nat} {f0 f1 f2 s0 s1 s2 x0 x1 x2 : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selAddLiquidity) (hid : IdReady sevm pre)
    (hWmc : WClosed sevm Wm) (hWb : W 0 pre)
    (ha : Abstracts (pre.getStor sevm.currentTarget) s)
    (hlock : (pre.getStor sevm.currentTarget).get lockSlot = 0) (hval : sevm.value = 0)
    (hkill : (pre.getStor sevm.currentTarget).get isKilledSlot = 0)
    (hA : aChk s sevm.benvStat.time.toNat = some amp)
    (hsup : SupplyOkAt sevm (W 0) (W 0) ((pre.getStor sevm.currentTarget).get tokenSlot) T U
      0x27c 0x2c0)
    (hmf : (pre.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [0x03] /
        (pre.getStor sevm.currentTarget).get feeSlot = Bytes.toB256 [0x03] ∨
      (pre.getStor sevm.currentTarget).get feeSlot = 0)
    (hT : T ≠ 0)
    (hX0 : xpChk ⟨(balAt (pre.getStor sevm.currentTarget) 0).toNat,
      (balAt (pre.getStor sevm.currentTarget) 1).toNat,
      (balAt (pre.getStor sevm.currentTarget) 2).toNat⟩ = some xa)
    (hD0 : getDChk xa.get amp 1 = some v0)
    (hok : AlLoopOk sevm W (alLocked1 (pre.getStor sevm.currentTarget)) T B1 B2
      (alOld (pre.getStor sevm.currentTarget)) U)
    (hXb : xpChk ⟨(alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2 0).toNat,
      (alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2 1).toNat,
      (alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2 2).toNat⟩ = some xb)
    (hD1 : getDChk xb.get amp 1 = some v1) (hlt : Nat.toB256 v0 < Nat.toB256 v1)
    (h0 : RliFeeIter (cwFee ((pre.getStor sevm.currentTarget).get feeSlot))
      ((pre.getStor sevm.currentTarget).get adminFeeSlot) (Nat.toB256 v0) (Nat.toB256 v1)
      (balAt (pre.getStor sevm.currentTarget) 0)
      (alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2 0) f0 s0 x0)
    (h1 : RliFeeIter (cwFee ((pre.getStor sevm.currentTarget).get feeSlot))
      ((pre.getStor sevm.currentTarget).get adminFeeSlot) (Nat.toB256 v0) (Nat.toB256 v1)
      (balAt (pre.getStor sevm.currentTarget) 1)
      (alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2 1) f1 s1 x1)
    (h2 : RliFeeIter (cwFee ((pre.getStor sevm.currentTarget).get feeSlot))
      ((pre.getStor sevm.currentTarget).get adminFeeSlot) (Nat.toB256 v0) (Nat.toB256 v1)
      (balAt (pre.getStor sevm.currentTarget) 2)
      (alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2 2) f2 s2 x2)
    (hXc : xpChk ⟨x0.toNat, x1.toNat, x2.toNat⟩ = some xc)
    (hD2 : getDChk xc.get amp 1 = some v2)
    (hge : ¬ Nat.toB256 v2 < Nat.toB256 v0) (hmul : B256.Nofm T (Nat.toB256 v2 - Nat.toB256 v0))
    (hD00 : Nat.toB256 v0 ≠ 0)
    (hslip : ¬ alMintW T (Nat.toB256 v0) (Nat.toB256 v2) <
      Sevm.dataWord sevm (Bytes.toB256 [0x64]))
    (hadd : ¬ T + alMintW T (Nat.toB256 v0) (Nat.toB256 v2) < T)
    (hmint : MintOkAt sevm (W 3) Wm ((pre.getStor sevm.currentTarget).get tokenSlot)
      (alMintW T (Nat.toB256 v0) (Nat.toB256 v2)) U 0xc7c 0xd00)
    (hG : U * 7 + costGetDMem xa amp + costGetDMem xb amp + costGetDMem xc amp + 400000 ≤ G)
    (hGb : G + 3000 < 2 ^ 256) :
    SFunc.RunEx cert.prog sevm (St pre [] Mem.empty G) t_0000_c0
      (AlEnd sevm (alUnlock (alStor3 (alLocked1 (pre.getStor sevm.currentTarget)) s0 s1 s2))
        f0 f1 f2) := by
  set σ := pre.getStor sevm.currentTarget with hσ
  generalize hca : costGetDMem xa amp = ca at hG
  generalize hcb : costGetDMem xb amp = cb at hG
  generalize hcc : costGetDMem xc amp = cc at hG
  obtain ⟨g0, rfl⟩ : ∃ g, G = g + 315 := ⟨G - 315, by omega⟩
  refine rx_dispatch_al hlen hcd hsel ?_
  refine rx_al_pre (R := g0 - 60000 - U) hfork hstatic hcd ⟨fun _ => rfl, hid, hok.wc 0 (by decide), hWb⟩ ha hlock
    hval hkill hA (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyMem_wf Mem.wf_empty _)
    (vyMem_empty_size _) hsup hmf (by omega) (by omega) ?_
  intro b1 M1 img1 g1 Aw hAw hL1 hR1 hW1 hsz1 wf0 wf1 wf2 wF wAF wAw wT wD0 wb0 wb1 wb2 hg1 hg1'
  subst hAw
  refine ⟨fun h => absurd h hT, fun _ => ?_⟩
  subst hca
  refine rx_al_d0 (R := g1 - costGetDMem xa Aw.toNat - 3000) (S := []) hX0 hD0 hR1 hW1 hsz1
    wf0 wf1 wf2 wF wAF wAw wT wb0 wb1 wb2 (by omega) (by simp only [List.length_nil]; omega) ?_
  intro M2 img2 g2 hR2 hW2 hsz2 vf0 vf1 vf2 vF vAF vAw vT vD0 vb0 vb1 vb2 hg2 hg2'
  subst hcb hcc
  exact rx_al_mid1 (S := []) hfork hstatic hdepth hL1 hWmc hR2 hW2 hsz2
    ⟨vf0, vf1, vf2, vF, vAF, vAw, vT, vD0, vb0, vb1, vb2⟩ hT hok hXb hD1 hlt h0 h1 h2 hXc hD2
    hge hmul hD00 hslip hadd
    (by rw [Stor.get_set_ne _ (by decide)]; exact hmint)
    (by omega) (by omega) (by simp only [List.length_nil]; omega)

/-- **`add_liquidity` on a first deposit, forward.** -/
theorem rx_al_frame0 {xb : V3} {v1 : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selAddLiquidity) (hid : IdReady sevm pre)
    (hWmc : WClosed sevm Wm) (hWb : W 0 pre)
    (ha : Abstracts (pre.getStor sevm.currentTarget) s)
    (hlock : (pre.getStor sevm.currentTarget).get lockSlot = 0) (hval : sevm.value = 0)
    (hkill : (pre.getStor sevm.currentTarget).get isKilledSlot = 0)
    (hA : aChk s sevm.benvStat.time.toNat = some amp)
    (hsup : SupplyOkAt sevm (W 0) (W 0) ((pre.getStor sevm.currentTarget).get tokenSlot) 0 U
      0x27c 0x2c0)
    (hmf : (pre.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [0x03] /
        (pre.getStor sevm.currentTarget).get feeSlot = Bytes.toB256 [0x03] ∨
      (pre.getStor sevm.currentTarget).get feeSlot = 0)
    (hok : AlLoopOk sevm W (alLocked1 (pre.getStor sevm.currentTarget)) 0 B1 B2
      (alOld (pre.getStor sevm.currentTarget)) U)
    (hXb : xpChk ⟨(alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2 0).toNat,
      (alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2 1).toNat,
      (alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2 2).toNat⟩ = some xb)
    (hD1 : getDChk xb.get amp 1 = some v1) (hlt : 0 < Nat.toB256 v1)
    (hslip : ¬ Nat.toB256 v1 < Sevm.dataWord sevm (Bytes.toB256 [0x64]))
    (hadd : ¬ 0 + Nat.toB256 v1 < 0)
    (hmint : MintOkAt sevm (W 3) Wm ((pre.getStor sevm.currentTarget).get tokenSlot)
      (Nat.toB256 v1) U 0xc7c 0xd00)
    (hG : U * 7 + costGetDMem xb amp + 400000 ≤ G)
    (hGb : G + 3000 < 2 ^ 256) :
    SFunc.RunEx cert.prog sevm (St pre [] Mem.empty G) t_0000_c0
      (AlEnd sevm (alUnlock (alStor3 (alLocked1 (pre.getStor sevm.currentTarget))
        (alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2 0)
        (alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2 1)
        (alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2 2))) 0 0 0) := by
  set σ := pre.getStor sevm.currentTarget with hσ
  generalize hcb : costGetDMem xb amp = cb at hG
  obtain ⟨g0, rfl⟩ : ∃ g, G = g + 315 := ⟨G - 315, by omega⟩
  refine rx_dispatch_al hlen hcd hsel ?_
  refine rx_al_pre (R := g0 - 60000 - U) hfork hstatic hcd ⟨fun _ => rfl, hid, hok.wc 0 (by decide), hWb⟩ ha hlock
    hval hkill hA (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyMem_wf Mem.wf_empty _)
    (vyMem_empty_size _) hsup hmf (by omega) (by omega) ?_
  intro b1 M1 img1 g1 Aw hAw hL1 hR1 hW1 hsz1 wf0 wf1 wf2 wF wAF wAw wT wD0 wb0 wb1 wb2 hg1 hg1'
  subst hAw
  refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
  subst hcb
  exact rx_al_mid0 (S := []) hfork hstatic hdepth hL1 hWmc hR1 hW1 hsz1
    ⟨wf0, wf1, wf2, wF, wAF, wAw, wT, wD0, wb0, wb1, wb2⟩ hok hXb hD1 hlt hslip hadd
    (by rw [Stor.get_set_ne _ (by decide)]; exact hmint)
    (by omega) (by omega) (by simp only [List.length_nil]; omega)

end Frame

end Blanc.Lift.Curve3Pool
