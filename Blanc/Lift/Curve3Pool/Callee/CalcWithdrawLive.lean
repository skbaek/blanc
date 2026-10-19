import Blanc.Lift.Curve3Pool.Callee.CalcWithdrawLiveE

/-!
# `_calc_withdraw_one_coin`, forward, composed

`rx_cw_run` composes `rx_cw_a` … `rx_cw_e` and the three fee-loop iterations: entered at
`0x3cca` with `ρ`, `_token_amount` and `i` over `S`, under the backward walk's word checks
(`CwStep` per coin, the checked `get_D`/`get_y_D` results) and the token's `totalSupply()`
answering `T` (`SupplyOkAt`), the function returns `(dy, dy_0 - dy)` over `S` within the
sufficient-gas bound `aGas + costGetD + 2 costGetYD + 33300 + U`. `rx_cw` is the caller's
internal-call idiom around it.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

theorem xpGas_le (sevm : Sevm) (b : Devm) : xpGas sevm b ≤ 7683 := by
  unfold xpGas
  have h1 := sloadCost_le sevm b (balanceSlot 0)
  have h2 := sloadCost_le sevm (afterSload sevm b (balanceSlot 0)) (balanceSlot 1)
  have h3 := sloadCost_le sevm (afterSload sevm (afterSload sevm b (balanceSlot 0))
    (balanceSlot 1)) (balanceSlot 2)
  have e : gasColdSload = 2100 := rfl
  omega

/-! ## The returned memory, canonical

`_xp` may leave its mapping key word `0xc0` changed (`cwD`); every later stage of
`_calc_withdraw_one_coin` writes and restores only above it, and the return tuple's pointer
overwrites it, so the returned memory is a function of the stages' canonical inputs alone. -/

theorem _root_.Blanc.Lift.Mem.EqExcept.writeD {M N : Mem} {D : Nat → Prop} (h : Mem.EqExcept M N D) (n : Nat)
    (xs : Bytes) : Mem.EqExcept (M.write n xs) (N.write n xs) D :=
  (h.write n xs).mono fun _ hi => hi.1

theorem _root_.Blanc.Lift.Mem.EqExcept.restoreMemD {M N : Mem} {D : Nat → Prop} (h : Mem.EqExcept M N D) (c p : Nat)
    (ws : List B256) : Mem.EqExcept (restoreMem c M p ws) (restoreMem c N p ws) D :=
  (h.restoreMem c ws).mono fun _ hi => hi.1

theorem _root_.Blanc.Lift.Mem.EqExcept.saveMemD {M N : Mem} {D : Nat → Prop} (h : Mem.EqExcept M N D) (c lo : Nat) :
    ∀ n, Mem.EqExcept (saveMem M c lo n) (saveMem N c lo n) D
  | 0 => h
  | n + 1 => (h.saveMemD c lo n).writeD _ _

/-- Off `cwD`, a word at or above `0xe0` reads the same. -/
theorem cw_memWord_eq {M N : Mem} (h : Mem.EqExcept M N cwD) {o : Nat} (ho : 0xe0 ≤ o) :
    memWord M o = memWord N o :=
  memWord_congr fun j _ => (h.2.2.2 (o + j) fun hd => by unfold cwD at hd; omega)

theorem cw_exSaved_eq {M N : Mem} (h : Mem.EqExcept M N cwD) (n : Nat) :
    exSaved (memWord M) 0x140 n = exSaved (memWord N) 0x140 n := by
  suffices ∀ n p, 0xe0 ≤ p → exSaved (memWord M) p n = exSaved (memWord N) p n from
    this n 0x140 (by decide)
  intro n
  induction n with
  | zero => intro _ _; show ([] : List B256) = []; rfl
  | succ n ih =>
    intro p hp
    show exSaved (memWord M) (p + 32) n ++ [memWord M p] =
      exSaved (memWord N) (p + 32) n ++ [memWord N p]
    rw [ih (p + 32) (by omega), cw_memWord_eq h hp]

theorem cwCMem_congr {M N : Mem} (h : Mem.EqExcept M N cwD) (x0 x1 x2 Aw D0 a T : B256) :
    Mem.EqExcept (cwCMem M x0 x1 x2 Aw D0 a T) (cwCMem N x0 x1 x2 Aw D0 a T) cwD := by
  unfold cwCMem cwCArgs
  rw [cw_exSaved_eq h]
  exact ((((((((((((((h.saveMemD _ _ _).writeD _ _).writeD _ _).writeD _ _).writeD _ _).writeD _
    _).writeD _ _).writeD _ _).restoreMemD _ _ _).writeD _ _).writeD _ _).writeD _ _).writeD _
    _).writeD _ _).writeD _ _

theorem cwDMem_congr {M N : Mem} (h : Mem.EqExcept M N cwD) (x0 x1 x2 Aw iw D1 y : B256) :
    Mem.EqExcept (cwDMem M x0 x1 x2 Aw iw D1 y) (cwDMem N x0 x1 x2 Aw iw D1 y) cwD := by
  unfold cwDMem cwDArgs
  rw [cw_exSaved_eq h]
  exact (((((((((((((h.saveMemD _ _ _).writeD _ _).writeD _ _).writeD _ _).writeD _ _).writeD _
    _).writeD _ _).writeD _ _).writeD _ _).writeD _ _).restoreMemD _ _ _).writeD _ _).writeD _
    _).writeD _ _

theorem cwItMem_congr {M N : Mem} (h : Mem.EqExcept M N cwD) (k : Nat) (dx r' : B256) :
    Mem.EqExcept (cwItMem M k dx r') (cwItMem N k dx r') cwD := by
  unfold cwItMem
  exact (((h.writeD _ _).writeD _ _).writeD _ _).writeD _ _

/-- `cwEMem`'s input memory of size `0x760` grows at the park, so its result is materialised. -/
theorem cwEMem_full {M : Mem} (hsz : M.size = 0x760) (iw r0 r1 r2 Aw D1 y2 dy0 : B256) :
    Mem.Full (cwEMem M iw r0 r1 r2 Aw D1 y2 dy0) := by
  have h1 : (M.write 0x780 (Bytes.toB256 [1, 64]).toBytes).size = 0x7a0 := by
    rw [Mem.size_write_of_size hsz (by decide) (B256.length_toBytes _)]; decide
  have h2 := saveMem_size (c := 0x780) (lo := 0x140 + 32 * 0) (by rw [h1]) (49 + 1)
  rw [h1] at h2
  have hA : (cwEArgs M iw r0 r1 r2 Aw D1).size = 0x860 := by
    unfold cwEArgs
    rw [Mem.size_write_of_size (Mem.size_write_of_size (Mem.size_write_of_size
      (Mem.size_write_of_size (Mem.size_write_of_size (Mem.size_write_of_size h2 (by decide)
      (B256.length_toBytes _)) (by decide) (B256.length_toBytes _)) (by decide)
      (B256.length_toBytes _)) (by decide) (B256.length_toBytes _)) (by decide)
      (B256.length_toBytes _)) (by decide) (B256.length_toBytes _)]
    decide
  unfold cwEMem
  have hr := Mem.Full.restoreMem 0x780 (p := 0x140 + 32 * 49)
    (exSaved (memWord M) 0x140 (49 + 1)) ((Mem.full_write_word_of_grow
      (μ := (cwEArgs M iw r0 r1 r2 Aw D1).write 0 y2.toBytes) (o := 0x8a0) y2 (by
      rw [Mem.size_write_word_of_add_le (by rw [hA]; decide), hA]; decide)).write 0x780
      (Bytes.toB256 [7, 96]).toBytes)
  exact (((((((hr.write _ _).write _ _).write _ _).write _ _).write _ _).write _ _).write _ _).write
    _ _

/-- Off `cwD` the same `rx_cw_e` memory: `_xp`'s key word is overwritten by the tuple pointer. -/
theorem cwEMem_eq_of {M N : Mem} (h : Mem.EqExcept M N cwD) (hsz : M.size = 0x760)
    (iw r0 r1 r2 Aw D1 y2 dy0 : B256) :
    cwEMem M iw r0 r1 r2 Aw D1 y2 dy0 = cwEMem N iw r0 r1 r2 Aw D1 y2 dy0 := by
  have hN : N.size = 0x760 := h.1 ▸ hsz
  have hfa := cwEMem_full hsz iw r0 r1 r2 Aw D1 y2 dy0
  have hfb := cwEMem_full hN iw r0 r1 r2 Aw D1 y2 dy0
  unfold cwEMem cwEArgs at hfa hfb ⊢
  rw [cw_exSaved_eq h] at hfa ⊢
  refine Mem.EqExcept.eq ((((((((((((((((((((h.writeD _ _).saveMemD _ _ _).writeD _ _).writeD _
    _).writeD _ _).writeD _ _).writeD _ _).writeD _ _).writeD _ _).writeD _ _).writeD _
    _).restoreMemD _ _ _).writeD _ _).writeD _ _).writeD _ _).writeD _ _).write 0xc0
    _).writeD _ _).writeD _ _).writeD _ _) (fun i hi => ?_) hfa hfb
  unfold cwD at hi
  rw [B256.length_toBytes] at hi
  omega

/-- The fee loop's charge: `546` for coin `0` when it is `i` (`576` otherwise); `543` / `573`
for coins `1` and `2`, whose first store no longer grows the memory. -/
def cwFeeCost (iw : B256) : Nat :=
  (if Bytes.toB256 [0] = iw then 546 else 576) + (if Bytes.toB256 [1] = iw then 543 else 573) +
    (if Bytes.toB256 [2] = iw then 543 else 573)

/-- For a valid coin index, the fee loop's charge is `1692`. -/
theorem cwFeeCost_eq {iw : B256} (hi : iw.toNat < 3) : cwFeeCost iw = 1692 := by
  unfold cwFeeCost
  have e : iw = Nat.toB256 iw.toNat := (toB256_toNat iw).symm
  obtain h | h | h : iw.toNat = 0 ∨ iw.toNat = 1 ∨ iw.toNat = 2 := by omega
  all_goals rw [e, h]; decide

/-- **`_calc_withdraw_one_coin`'s charge after its `totalSupply()` call** `d`: the reply test
(`77`), `_xp` (`2585 + xpGas`), `get_D` (`3586 + costGetD`), the first `get_y_D`
(`5344 + costGetYD`), the fee loop (`cwFeeCost`) and the second `get_y_D` (`7684 + costGetYD`). -/
def cwRestCost (sevm : Sevm) (d : Devm) (amp : Nat) (iw x0 x1 x2 D1 r0 r1 r2 : B256) : Nat :=
  77 + (2585 + xpGas sevm d) + (3586 + costGetD x0.toNat x1.toNat x2.toNat amp) +
    (5344 + costGetYD amp iw.toNat x0.toNat x1.toNat x2.toNat D1.toNat) + cwFeeCost iw +
    (7684 + costGetYD amp iw.toNat r0.toNat r1.toNat r2.toNat D1.toNat)

/-- **The memory `_calc_withdraw_one_coin` returns**, from the memory after its `totalSupply()`
reply `Mb`: the stages' canonical memories in order. -/
def cwRunMem (Mb : Mem) (x0 x1 x2 Aw D0 a T iw y r0 r1 r2 y2 : B256) : Mem :=
  cwEMem (cwItMem (cwItMem (cwItMem (cwDMem (cwCMem (cwBMem Mb x0 x1 x2) x0 x1 x2 Aw D0 a T) x0 x1
    x2 Aw iw (D0 - a * D0 / T) y) 0 (cwItDx (Bytes.toB256 [0] = iw) x0 (D0 - a * D0 / T) D0 y) r0)
    1 (cwItDx (Bytes.toB256 [1] = iw) x1 (D0 - a * D0 / T) D0 y) r1) 2
    (cwItDx (Bytes.toB256 [2] = iw) x2 (D0 - a * D0 / T) D0 y) r2) iw r0 r1 r2 Aw
    (D0 - a * D0 / T) y2 ((pickWord3 iw.toNat x0 x1 x2 - y) / pickWord3 iw.toNat cwP1 cwPm cwPm)

/-- **`_calc_withdraw_one_coin`, forward, exactly** (core): `rx_cw_run` over the supply call's
relation premise, the returned state also carrying the call's relation at its literal input, the
exact charges before (`cwACost`) and after (`cwRestCost`) the call, the base `xpBase` and the
literal returned memory `cwRunMem`. -/
theorem rx_cw_runE {sevm : Sevm} {b : Devm} {σ : Stor} {s : State} {S : List B256} {M : Mem}
    {img : Bytes} {G R U amp : Nat} {W : Devm → Prop}
    {ρ a iw T x0 x1 x2 D0 y r0 r1 r2 y2 : B256}
    {E : Devm → List B256 → Mem → Nat → Devm → Prop}
    (hfork : CoveredFork sevm.benvStat.fork) (hL : ExLive sevm W b σ) (ha : Abstracts σ s)
    (hA : aChk s sevm.benvStat.time.toNat = some amp)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x1e0)
    (hsup : StaticWordOkAtE sevm W W (σ.get tokenSlot) totalSupplyData T U 0x2bc 4 0x300 E)
    (hmf : σ.get feeSlot * Bytes.toB256 [0x03] / σ.get feeSlot = Bytes.toB256 [0x03] ∨
      σ.get feeSlot = 0)
    (hi3 : iw.toNat < 3)
    (hX : xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩)
    (hD0 : getDChk (V3.mk x0.toNat x1.toNat x2.toNat).get amp 1 = some D0.toNat)
    (hm : a * D0 / a = D0 ∨ a = 0) (hT0 : T ≠ 0) (hle : ¬ D0 < a * D0 / T)
    (hy : getYDChk amp ⟨iw.toNat, hi3⟩ (V3.mk x0.toNat x1.toNat x2.toNat).get
      (D0 - a * D0 / T).toNat = some y.toNat)
    (hyl : ¬ pickWord3 iw.toNat x0 x1 x2 < y)
    (h0 : CwStep (Bytes.toB256 [0] = iw) x0 (D0 - a * D0 / T) D0 y (cwFee (σ.get feeSlot)) x0 r0)
    (h1 : CwStep (Bytes.toB256 [1] = iw) x1 (D0 - a * D0 / T) D0 y (cwFee (σ.get feeSlot)) x1 r1)
    (h2 : CwStep (Bytes.toB256 [2] = iw) x2 (D0 - a * D0 / T) D0 y (cwFee (σ.get feeSlot)) x2 r2)
    (hy2 : getYDChk amp ⟨iw.toNat, hi3⟩ (V3.mk r0.toNat r1.toNat r2.toNat).get
      (D0 - a * D0 / T).toNat = some y2.toNat)
    (hs0 : ¬ pickWord3 iw.toNat r0 r1 r2 < y2)
    (hs1 : ¬ pickWord3 iw.toNat r0 r1 r2 - y2 < Bytes.toB256 [1])
    (hs2 : ¬ (pickWord3 iw.toNat x0 x1 x2 - y) / pickWord3 iw.toNat cwP1 cwPm cwPm <
      cwDy iw r0 r1 r2 y2)
    (hG : aGas sevm b + costGetD x0.toNat x1.toNat x2.toNat amp +
      costGetYD amp iw.toNat x0.toNat x1.toNat x2.toNat (D0 - a * D0 / T).toNat +
      costGetYD amp iw.toNat r0.toNat r1.toNat r2.toNat (D0 - a * D0 / T).toNat + 33300 + U + R ≤ G)
    (hGb : G < 2 ^ 256) (hroom : S.length + 80 < 1024) :
    SFunc.RunEx cert.prog sevm (St b (ρ :: a :: iw :: S) M G) t_3cca_c36 (fun r =>
      ∃ (b' : Devm) (M' : Mem) (g : Nat), r = .returned (St b' (cwDy iw r0 r1 r2 y2 ::
        ((pickWord3 iw.toNat x0 x1 x2 - y) / pickWord3 iw.toNat cwP1 cwPm cwPm -
          cwDy iw r0 r1 r2 y2) :: S) M' g) ∧
        ExLive sevm W b' σ ∧ Mem.Wf M' ∧ M'.size = 0x920 ∧ R ≤ g ∧ g ≤ G ∧
        ∃ (Gs : Nat) (d : Devm), E (cwSupBase sevm (aBase sevm b)) S
          (cwAMem sevm b σ M ρ a iw amp) Gs d ∧ G = Gs + cwACost sevm b ∧
          d.gasLeft = g + cwRestCost sevm d amp iw x0 x1 x2 (D0 - a * D0 / T) r0 r1 r2 ∧
          b' = xpBase sevm d ∧
          M' = cwRunMem (cwA2Post (cwAMem sevm b σ M ρ a iw amp) d.returnData T) x0 x1 x2
            (Nat.toB256 amp) D0 a T iw y r0 r1 r2 y2) := by
  refine rx_cw_aE (R := 7683 + 2585 + (costGetD x0.toNat x1.toNat x2.toNat amp + 3586 +
      (costGetYD amp iw.toNat x0.toNat x1.toNat x2.toNat (D0 - a * D0 / T).toNat + 5344 +
      (576 + (573 + (573 + (costGetYD amp iw.toNat r0.toNat r1.toNat r2.toNat
        (D0 - a * D0 / T).toNat + 7684 + R)))))))
    hfork hL ha hA hR hW hsz hsup hmf (by omega) hGb (by omega) ?_
  intro b1 M1 img1 g1 Aw hAw hL1 hR1 hW1 hsz1 wa wi wρ wA wF wP1 wPm1 wPm2 wT wc hg1 hg1' Gs d hE
    hGa hdg hb1 hM1
  subst hAw
  refine rx_cw_bE (R := costGetD x0.toNat x1.toNat x2.toNat Aw.toNat + 3586 +
      (costGetYD Aw.toNat iw.toNat x0.toNat x1.toNat x2.toNat (D0 - a * D0 / T).toNat + 5344 +
      (576 + (573 + (573 + (costGetYD Aw.toNat iw.toNat r0.toNat r1.toNat r2.toNat
        (D0 - a * D0 / T).toNat + 7684 + R))))))
    hfork hL1 ha hX hR1 hW1 hsz1 wc (by have := xpGas_le sevm b1; omega) (by omega) ?_
  intro b2 M2 img2 g2 hL2 hR2 hW2 hsz2 hk2 wx0 wx1 wx2 wc2 hg2 hg2' hgb hb2 hMb hFb
  have wa2 := hk2 0 a (by decide) wa
  have wi2 := hk2 1 iw (by decide) wi
  have wρ2 := hk2 2 ρ (by decide) wρ
  have wA2 := hk2 3 Aw (by decide) wA
  have wF2 := hk2 6 _ (by decide) wF
  have wP12 := hk2 7 _ (by decide) wP1
  have wPm12 := hk2 8 _ (by decide) wPm1
  have wPm22 := hk2 9 _ (by decide) wPm2
  have wT2 := hk2 10 T (by decide) wT
  refine rx_cw_cE (R := costGetYD Aw.toNat iw.toNat x0.toNat x1.toNat x2.toNat
      (D0 - a * D0 / T).toNat + 5344 + (576 + (573 + (573 + (costGetYD Aw.toNat iw.toNat
        r0.toNat r1.toNat r2.toNat (D0 - a * D0 / T).toNat + 7684 + R)))))
    hD0 hm hT0 hle hR2 hW2 hsz2 wc2 wa2 wA2 wT2 wx0 wx1 wx2 (by omega) (by omega) ?_
  intro M3 img3 g3 hR3 hW3 hsz3 hk3 wD0 wD1 wr0 wr1 wr2 wc3 hg3 hg3' hgc hMc
  refine rx_cw_dE (R := 576 + (573 + (573 + (costGetYD Aw.toNat iw.toNat r0.toNat r1.toNat
      r2.toNat (D0 - a * D0 / T).toNat + 7684 + R)))) hi3 hy hyl hR3 hW3 hsz3 wc3
    (hk3 3 _ (by decide) wA2) (hk3 1 _ (by decide) wi2) (hk3 15 _ (by decide) wx0)
    (hk3 16 _ (by decide) wx1) (hk3 17 _ (by decide) wx2) wD1 (hk3 7 _ (by decide) wP12)
    (hk3 8 _ (by decide) wPm12) (hk3 9 _ (by decide) wPm22) (by omega) (by omega) ?_
  intro M4 img4 g4 hR4 hW4 hsz4 hk4 wy wd0 wc4 hg4 hg4' hgd hMd
  refine rx_cw_it0E (R := 573 + (573 + (costGetYD Aw.toNat iw.toNat r0.toNat r1.toNat r2.toNat
      (D0 - a * D0 / T).toNat + 7684 + R))) hi3 hR4 hW4 hsz4 wc4
    (hk4 1 _ (by decide) (hk3 1 _ (by decide) wi2)) (hk4 15 _ (by decide) (hk3 15 _ (by decide) wx0))
    (hk4 31 _ (by decide) wD1) (hk4 22 _ (by decide) wD0) wy
    (hk4 6 _ (by decide) (hk3 6 _ (by decide) wF2)) (hk4 32 _ (by decide) wr0) h0
    (by omega) (by omega) ?_
  intro M5 img5 g5 hR5 hW5 hsz5 hk5 wr0' wc5 hg5 hg5' hgi0 hMi0
  -- the words iterations 1 and 2 and the tail read, carried to the loop's entry image
  have vi := hk4 1 _ (by decide) (hk3 1 _ (by decide) wi2)
  have vA := hk4 3 _ (by decide) (hk3 3 _ (by decide) wA2)
  have vρ := hk4 2 _ (by decide) (hk3 2 _ (by decide) wρ2)
  have vx1 := hk4 16 _ (by decide) (hk3 16 _ (by decide) wx1)
  have vx2 := hk4 17 _ (by decide) (hk3 17 _ (by decide) wx2)
  have vD1 := hk4 31 _ (by decide) wD1
  have vD0 := hk4 22 _ (by decide) wD0
  have vF := hk4 6 _ (by decide) (hk3 6 _ (by decide) wF2)
  have vP1 := hk4 7 _ (by decide) (hk3 7 _ (by decide) wP12)
  have vPm1 := hk4 8 _ (by decide) (hk3 8 _ (by decide) wPm12)
  have vPm2 := hk4 9 _ (by decide) (hk3 9 _ (by decide) wPm22)
  have vr1 := hk4 33 _ (by decide) wr1
  have vr2 := hk4 34 _ (by decide) wr2
  -- after iteration 0
  have l0 : ∀ o v, WordAt img4 o v → o + 32 ≤ 0x540 → WordAt img5 o v :=
    fun o v h ho => hk5 o v h (.inl (by omega))
  refine rx_cw_it1E (R := 573 + (costGetYD Aw.toNat iw.toNat r0.toNat r1.toNat r2.toNat
      (D0 - a * D0 / T).toNat + 7684 + R)) hi3 hR5 hW5 hsz5 wc5 (l0 _ _ vi (by decide))
    (l0 _ _ vx1 (by decide)) (l0 _ _ vD1 (by decide)) (l0 _ _ vD0 (by decide))
    (hk5 _ _ wy (.inr ⟨by decide, by decide⟩)) (l0 _ _ vF (by decide))
    (hk5 _ _ vr1 (.inr ⟨by decide, by decide⟩)) h1 (by omega) (by omega) ?_
  intro M6 img6 g6 hR6 hW6 hsz6 hk6 wr1' wc6 hg6 hg6' hgi1 hMi1
  have l1 : ∀ o v, WordAt img5 o v → o + 32 ≤ 0x560 → WordAt img6 o v :=
    fun o v h ho => hk6 o v h (.inl (by omega))
  refine rx_cw_it2E (R := costGetYD Aw.toNat iw.toNat r0.toNat r1.toNat r2.toNat
      (D0 - a * D0 / T).toNat + 7684 + R) hi3 hR6 hW6 hsz6 wc6 (l1 _ _ (l0 _ _ vi (by decide)) (by decide))
    (l1 _ _ (l0 _ _ vx2 (by decide)) (by decide)) (l1 _ _ (l0 _ _ vD1 (by decide)) (by decide))
    (l1 _ _ (l0 _ _ vD0 (by decide)) (by decide))
    (hk6 _ _ (hk5 _ _ wy (.inr ⟨by decide, by decide⟩)) (.inr ⟨by decide, by decide⟩))
    (l1 _ _ (l0 _ _ vF (by decide)) (by decide))
    (hk6 _ _ (hk5 _ _ vr2 (.inr ⟨by decide, by decide⟩)) (.inr ⟨by decide, by decide⟩)) h2
    (by omega) (by omega) ?_
  intro M7 img7 g7 hR7 hW7 hsz7 hk7 wr2' wc7 hg7 hg7' hgi2 hMi2
  have l2 : ∀ o v, WordAt img6 o v → o + 32 ≤ 0x580 → WordAt img7 o v :=
    fun o v h ho => hk7 o v h (.inl (by omega))
  have l012 : ∀ o v, WordAt img4 o v → o + 32 ≤ 0x540 → WordAt img7 o v :=
    fun o v h ho => l2 _ _ (l1 _ _ (l0 _ _ h ho) (by omega)) (by omega)
  refine rx_cw_eE (R := R) hi3 hy2 hs0 hs1 hs2 hR7 hW7 hsz7 (l012 _ _ vA (by decide))
    (l012 _ _ vi (by decide)) (l2 _ _ (l1 _ _ wr0' (by decide)) (by decide))
    (l2 _ _ wr1' (by decide)) wr2' (l012 _ _ vD1 (by decide))
    (hk7 _ _ (hk6 _ _ (hk5 _ _ wd0 (.inr ⟨by decide, by decide⟩)) (.inr ⟨by decide, by decide⟩))
      (.inr ⟨by decide, by decide⟩))
    (l012 _ _ vρ (by decide)) (l012 _ _ vP1 (by decide)) (l012 _ _ vPm1 (by decide))
    (l012 _ _ vPm2 (by decide)) (by omega) (by omega) ?_
  intro M8 g8 hW8 hsz8 hg8 hg8' hge hMe
  refine ⟨b2, M8, g8, rfl, hL2, hW8, hsz8, hg8, by omega, Gs, d, hE, hGa, ?_, by rw [hb2, hb1], ?_⟩
  · rw [hb1] at hgb
    unfold cwRestCost cwFeeCost
    omega
  · rw [toB256_toNat, ← hM1, hMe, hMi2, hMi1, hMi0, hMd, hMc]
    unfold cwRunMem
    refine cwEMem_eq_of (cwItMem_congr (cwItMem_congr (cwItMem_congr (cwDMem_congr
      (cwCMem_congr hMb _ _ _ _ _ _ _) _ _ _ _ _ _ _) _ _ _) _ _ _) _ _ _) ?_ _ _ _ _ _ _ _ _
    rw [hMi2, hMi1, hMi0, hMd, hMc] at hsz7; exact hsz7


/-- **`_calc_withdraw_one_coin`, forward**, from its entry to its return. -/
theorem rx_cw_run {sevm : Sevm} {b : Devm} {σ : Stor} {s : State} {S : List B256} {M : Mem}
    {img : Bytes} {G R U amp : Nat} {W : Devm → Prop}
    {ρ a iw T x0 x1 x2 D0 y r0 r1 r2 y2 : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hL : ExLive sevm W b σ) (ha : Abstracts σ s)
    (hA : aChk s sevm.benvStat.time.toNat = some amp)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x1e0)
    (hsup : SupplyOkAt sevm W W (σ.get tokenSlot) T U 0x2bc 0x300)
    (hmf : σ.get feeSlot * Bytes.toB256 [0x03] / σ.get feeSlot = Bytes.toB256 [0x03] ∨
      σ.get feeSlot = 0)
    (hi3 : iw.toNat < 3)
    (hX : xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩)
    (hD0 : getDChk (V3.mk x0.toNat x1.toNat x2.toNat).get amp 1 = some D0.toNat)
    (hm : a * D0 / a = D0 ∨ a = 0) (hT0 : T ≠ 0) (hle : ¬ D0 < a * D0 / T)
    (hy : getYDChk amp ⟨iw.toNat, hi3⟩ (V3.mk x0.toNat x1.toNat x2.toNat).get
      (D0 - a * D0 / T).toNat = some y.toNat)
    (hyl : ¬ pickWord3 iw.toNat x0 x1 x2 < y)
    (h0 : CwStep (Bytes.toB256 [0] = iw) x0 (D0 - a * D0 / T) D0 y (cwFee (σ.get feeSlot)) x0 r0)
    (h1 : CwStep (Bytes.toB256 [1] = iw) x1 (D0 - a * D0 / T) D0 y (cwFee (σ.get feeSlot)) x1 r1)
    (h2 : CwStep (Bytes.toB256 [2] = iw) x2 (D0 - a * D0 / T) D0 y (cwFee (σ.get feeSlot)) x2 r2)
    (hy2 : getYDChk amp ⟨iw.toNat, hi3⟩ (V3.mk r0.toNat r1.toNat r2.toNat).get
      (D0 - a * D0 / T).toNat = some y2.toNat)
    (hs0 : ¬ pickWord3 iw.toNat r0 r1 r2 < y2)
    (hs1 : ¬ pickWord3 iw.toNat r0 r1 r2 - y2 < Bytes.toB256 [1])
    (hs2 : ¬ (pickWord3 iw.toNat x0 x1 x2 - y) / pickWord3 iw.toNat cwP1 cwPm cwPm <
      cwDy iw r0 r1 r2 y2)
    (hG : aGas sevm b + costGetD x0.toNat x1.toNat x2.toNat amp +
      costGetYD amp iw.toNat x0.toNat x1.toNat x2.toNat (D0 - a * D0 / T).toNat +
      costGetYD amp iw.toNat r0.toNat r1.toNat r2.toNat (D0 - a * D0 / T).toNat + 33300 + U + R ≤ G)
    (hGb : G < 2 ^ 256) (hroom : S.length + 80 < 1024) :
    SFunc.RunEx cert.prog sevm (St b (ρ :: a :: iw :: S) M G) t_3cca_c36 (fun r =>
      ∃ (b' : Devm) (M' : Mem) (g : Nat), r = .returned (St b' (cwDy iw r0 r1 r2 y2 ::
        ((pickWord3 iw.toNat x0 x1 x2 - y) / pickWord3 iw.toNat cwP1 cwPm cwPm -
          cwDy iw r0 r1 r2 y2) :: S) M' g) ∧
        ExLive sevm W b' σ ∧ Mem.Wf M' ∧ M'.size = 0x920 ∧ R ≤ g ∧ g ≤ G) := by
  obtain ⟨r, hr, b', M', g, h1, h2, h3, h4, h5, h6, -⟩ := rx_cw_runE hfork hL ha hA hR hW hsz
    hsup.withE hmf hi3 hX hD0 hm hT0 hle hy hyl h0 h1 h2 hy2 hs0 hs1 hs2 hG hGb hroom
  exact ⟨r, hr, b', M', g, h1, h2, h3, h4, h5, h6⟩

end Blanc.Lift.Curve3Pool
