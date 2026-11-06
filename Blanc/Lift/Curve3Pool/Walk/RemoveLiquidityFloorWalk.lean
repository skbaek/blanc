import Blanc.Lift.ExactCallFloor
import Blanc.Lift.Curve3Pool.Walk.RemoveLiquidityExactSchedule

/-!
# `remove_liquidity`, exact, at the true gas minimum

`rx_rl_frame_floor`: `rx_rl_frame_exact` with the constant headroom `167000 + 5 U` gone. The calls are admitted at
their floors (`MutableFloorProfile`): each needs only what it leaves, and that is the frame's own later charges plus
`R`. The one floor that binds is the last write's: the lock's release needs `gCallStipend < R + its charge`, and its
charge is at least `100`, so `2201 ≤ R` suffices (`rl_lock_sentry`).

`rx_rl_s3F`, `rx_rl_postF` are `rx_rl_s3E`, `rx_rl_postE` with that admission. The prologue and the storage stages
are the existing cores: their demands are small and constant, and the frame's later charges cover them.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- A static floor profile with a uniform bound on its debit answers the relation premise, at bound plus floor. -/
theorem StaticWordFloorProfile.okE {sevm : Sevm} {W W' : Devm → Prop} {t : B256} {data : Bytes}
    {A : B256} {U K C : Nat} {ii is oi : B256} {debit : Devm → List B256 → Mem → Nat}
    {next : Devm → List B256 → Mem → Devm}
    (hp : StaticWordFloorProfile sevm W W' t data A U K ii is oi debit next)
    (hle : ∀ b S M, W b → (M.read ii.toNat is.toNat).1 = data → debit b S M ≤ C) :
    StaticWordOkAtE sevm W W' t data A (C + K) ii is oi (ExactE debit next) := by
  intro b S M G hW hU hG hin hS
  have hd := hle b S M hW hin
  obtain ⟨-, d, hrun, hgas, hnext, out, hpost, hlen, hlt, hA, hW', hid⟩ :=
    hp.sound b S M G ⟨hW, by omega, hG, hin, hS⟩
  exact ⟨d, out, hrun, hpost, hlen, hlt, hA, by omega, by omega, hW', hid, hgas, hnext⟩

/-- An `SSTORE` at its charge, at any gas above the sentry. -/
theorem rxe_sstoreS {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {f : SFunc}
    {Q : Outcome → Prop} {k' v : B256} {G R : Nat} (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hG : G = R + sstoreCost sevm b k' v) (hs : gCallStipend < G)
    (k : SFunc.RunEx fs sevm (St (afterSstore sevm b k' v) S M R) f Q) :
    SFunc.RunEx fs sevm (St b (k' :: v :: S) M G) (.next (.reg .sstore) f) Q := by
  subst hG
  obtain ⟨r, hr, hq⟩ := k
  exact ⟨r, rx_sstore hfork hs hstatic hr, hq⟩

/-- Every `SSTORE` charges at least a warm access. -/
theorem sstoreCost_ge (sevm : Sevm) (b : Devm) (k v : B256) : gasWarmAccess ≤ sstoreCost sevm b k v := by
  unfold sstoreCost sstoreValueCost
  split_ifs <;> simp only [gasWarmAccess, gasStorageSet, gasStorageUpdate, gasColdSload] <;> omega

/-- **The floor that binds**: the last write's sentry, from `2201 ≤ R`. -/
theorem rl_lock_sentry (sevm : Sevm) (b : Devm) (k v : B256) {R : Nat} (hR : 2201 ≤ R) :
    gCallStipend < R + sstoreCost sevm b k v := by
  have h := sstoreCost_ge sevm b k v
  simp only [gCallStipend, gasWarmAccess] at h ⊢
  omega

/-! ## The stage cores at the floor -/

/-- **The transfer call and its tail, at the call's floor**: `rx_rl_s3E` admitted by `MutableFloorProfile`, with
the exact relation. -/
theorem rx_rl_s3F {sevm : Sevm} {b : Devm} {Gx : Nat} {Q : Outcome → Prop} {M : Mem} {img : Bytes}
    {s i : Nat} {T V C : B256} {a : Nat → B256} {W W' : Devm → Prop} {U K : Nat}
    {debit : Devm → List B256 → Mem → Nat} {next : Devm → List B256 → Mem → Devm}
    (hfork : CoveredFork sevm.benvStat.fork) (hi : i < 3) (hdepth : sevm.depth ≠ 0)
    (hid : IdReady sevm b) (hWc : WClosed sevm W) (hWb : W b) (hW'c : WClosed sevm W')
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = s) (hs : s = 0x580 ∨ s = 0x5e0)
    (hL : LoopImg img i T a)
    (hdata : Region img 0x500 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
      Bytes.toB256 [32]).toBytes ++ (transferSel ++ sevm.caller.toB256.toBytes ++ V.toBytes)))
    (hC : (b.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 i) = C)
    (hp : MutableFloorProfile sevm W W' C (transferSel ++ sevm.caller.toB256.toBytes ++ V.toBytes)
      RawCallOk U K 0x520 0x44 0x5c0 debit next) (hK : 2000 ≤ K)
    (hGx : debit (afterSload sevm b (coinsBase + Nat.toB256 i)) [3, 0x2a0]
      (M.write 0xc0 (Bytes.toB256 [0]).toBytes) + K ≤ Gx)
    (hGb : Gx + 1000 < 2 ^ 256)
    (k : ∀ b' M' img' G', W' b' → IdReady sevm b' →
      (∀ x, (b'.getStor sevm.currentTarget).get x = (b.getStor sevm.currentTarget).get x) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x5e0 → LoopImg img' (i + 1) T a →
      ∀ d : Devm, ExactE debit next (afterSload sevm b (coinsBase + Nat.toB256 i)) [3, 0x2a0]
        (M.write 0xc0 (Bytes.toB256 [0]).toBytes) Gx d →
      d.gasLeft = G' + 45 + rawTailCost (min d.returnData.length 32) →
      Devm.EqModGas b' (rawTailBaseNext sevm d [3, 0x2a0] d.memory rlSite) →
      M' = (vyRawMem d.memory 0x5a0 0x3a0 (min d.returnData.length 32)).write 0x2a0
        (Nat.toB256 (i + 1)).toBytes →
      SFunc.RunEx cert.prog sevm (St b' [3, 0x2a0] M' G') (rlNext i) Q) :
    ∀ x y, SFunc.RunEx cert.prog sevm (St b (x :: y :: [3, 0x2a0]) M (Gx + rlS3Cost sevm b i))
      t_2ea7_c0 Q := by
  intro x y
  have hs32 : s % 32 = 0 := by rcases hs with rfl | rfl <;> decide
  have hs0 : 0x580 ≤ s := by rcases hs with rfl | rfl <;> decide
  unfold rlS3Cost
  rw [show Gx + (108 + sloadCost sevm b (coinsBase + Nat.toB256 i)) = Gx + 2 +
    sloadCost sevm b (coinsBase + Nat.toB256 i) + 3 + 36 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 +
    3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 2 + 2 + 1 by omega]
  wrun 6
  xr (rxm_mload (o := 0x500) hR hsz rfl ⟨by omega, hs32⟩ (by hr) ·)
  rw [(Region.word hdata.left).read]
  wrun 3
  xr (rxm_mload (o := 0x2a0) hR hsz rfl ⟨by omega, hs32⟩ (by hr) ·)
  rw [hL.ctr.read]
  wrun 4
  xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
  wrun 3
  refine rxe_mstoreL (o := 0xc0) (c := 3) hR hW hsz rfl
    ⟨by rw [memExtSize_of_le hs32 (by omega), Nat.sub_self]; rfl, hs32⟩ ?_
  intro M hM1 hR hW hsz
  rw [memExtSize_of_le hs32 (by omega)] at hsz
  wrun 2
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz rfl rfl ⟨by omega, hs32⟩ (by hr) (by decide) ·)
  rw [keccak_zero]
  xr (rx_add (by hr) ·)
  xr (rx_sload_sel hfork (by hr) ·)
  rw [getStorVal_eq, hC]
  xr (rx_gas (by hr) ·)
  rw [show Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] + Bytes.toB256 [32] =
      (0x44 : B256) by decide, show Bytes.toB256 [0] = (0 : B256) by decide,
    show Bytes.toB256 [5, 32] = (0x520 : B256) by decide,
    show Bytes.toB256 [5, 192] = (0x5c0 : B256) by decide,
    show Bytes.toB256 [32] = (0x20 : B256) by decide]
  have hin : (M.read 0x520 0x44).1 = transferSel ++ sevm.caller.toB256.toBytes ++ V.toBytes := by
    rw [hR.read]
    exact Region.slice (Region.write_other hdata.right (by simp only [B256.length_toBytes]; omega))
      (by simp only [List.length_append, B256.length_toBytes]; rfl)
  have hGxM : debit (afterSload sevm b (coinsBase + Nat.toB256 i)) [3, 0x2a0] M + K ≤ Gx := by
    rw [hM1]; exact hGx
  obtain ⟨-, d, hrun, hgas, hnext, hpost, hok, hrdlt, hstor, hWd, hidd⟩ :=
    hp.sound _ [3, 0x2a0] M Gx ⟨hWc.sload _ _ hWb, hGxM, by omega, hin, by decide⟩
  have hE : ExactE debit next (afterSload sevm b (coinsBase + Nat.toB256 i)) [3, 0x2a0] M Gx d :=
    ⟨hgas, hnext⟩
  xr (.next hrun ·)
  obtain ⟨hmem, -⟩ := hpost.settled (by decide)
  rw [show (0x520 : B256).toNat = 0x520 by decide, show (0x44 : B256).toNat = 0x44 by decide,
    show (0x5c0 : B256).toNat = 0x5c0 by decide, show (0x20 : B256).toNat = 0x20 by decide] at hmem
  have hd : d = St d (1 :: [3, 0x2a0]) d.memory d.gasLeft := St.self hpost.stack rfl
  rw [hd, rl_tail]
  have hext : (M.extends [(0x520, 0x44), (0x5c0, 0x20)]).size = 0x5e0 := by
    show memExtsSize M.size _ = _
    rw [hsz]; rcases hs with rfl | rfl <;> decide
  have hsz5 : d.memory.size = 0x5e0 := by
    rw [hmem, Mem.size_write_of_le (by rw [hext, List.length_take]; omega), hext]
  have hR5 : Mem.Reads d.memory (Bytes.writeAt (Bytes.writeAt img 0xc0 (Bytes.toB256 [0]).toBytes)
      0x5c0 (d.returnData.take 0x20)) := by
    rw [hmem]; exact (hR.extends _).write (hW.extends _) _ _
  have hW5 : Mem.Wf d.memory := by rw [hmem]; exact (hW.extends _).write _ _
  have htc : rawTailCost (min d.returnData.length 32) ≤ 500 := by
    unfold rawTailCost rawJoinCost rawCheckCost idCost ceilDiv
    split_ifs <;> omega
  obtain ⟨G2, hG2⟩ : ∃ G2, d.gasLeft = G2 + rawTailCost (min d.returnData.length 32) :=
    ⟨d.gasLeft - rawTailCost (min d.returnData.length 32), by omega⟩
  rw [hG2]
  refine SFunc.runEx_iff_runExCut_nil.mpr (rxce_vyRawCallTail_canonical (hidd (hid.afterSload _))
    hdepth (by decide) rl_join (by simp only [List.not_mem_nil, not_false_eq_true]) hrdlt hok
    ?_ (by rw [hsz5]) (by rw [hsz5]; decide) (by rw [hsz5]; decide) (by omega) (by omega) (by hr)
    ?_)
  · rw [show (Bytes.toB256 [rlSite.lh, rlSite.ll]).toNat + 32 = 0x5c0 by decide]
    intro j hj
    exact (rawCall_window hmem rfl j hj).2
  intro b' rd' hsha hcanT
  refine SFunc.runEx_iff_runExCut_nil.mp ?_
  clear hrun
  rw [show (Bytes.toB256 [rlSite.lh, rlSite.ll]).toNat = 0x5a0 by decide,
    show (Bytes.toB256 [rlSite.bh, rlSite.bl]).toNat = 0x3a0 by decide]
  have hn32 : min d.returnData.length 32 ≤ 32 := by omega
  have hR6 : Mem.Reads (vyRawMem d.memory 0x5a0 0x3a0 (min d.returnData.length 32))
      (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0xc0
        (Bytes.toB256 [0]).toBytes) 0x5c0 (d.returnData.take 0x20)) 0x5a0
        (Nat.toB256 (min d.returnData.length 32)).toBytes) 0x3a0 ((Bytes.writeAt (Bytes.writeAt
        (Bytes.writeAt img 0xc0 (Bytes.toB256 [0]).toBytes) 0x5c0 (d.returnData.take 0x20)) 0x5a0
        (Nat.toB256 (min d.returnData.length 32)).toBytes).sliceD 0x5a0
        (min d.returnData.length 32 + 32) 0)) := by
    unfold vyRawMem
    rw [(hR5.write hW5 _ _).read]
    exact (hR5.write hW5 _ _).write (hW5.write _ _) _ _
  have hW6 : Mem.Wf (vyRawMem d.memory 0x5a0 0x3a0 (min d.returnData.length 32)) := by
    unfold vyRawMem; exact (hW5.write _ _).write _ _
  have hsz6 : (vyRawMem d.memory 0x5a0 0x3a0 (min d.returnData.length 32)).size = 0x5e0 := by
    unfold vyRawMem
    have h1 : (d.memory.write 0x5a0 (Nat.toB256 (min d.returnData.length 32)).toBytes).size =
        0x5e0 := by
      rw [Mem.size_write_of_le (by rw [B256.length_toBytes, hsz5]; decide), hsz5]
    rw [(hR5.write hW5 _ _).read, Mem.size_write_of_le (by rw [h1, List.length_sliceD]; omega), h1]
  obtain ⟨G', hG'⟩ : ∃ G', G2 = G' + 45 := ⟨G2 - 45, by omega⟩
  rw [hG']
  have hctr6 : WordAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
      img 0xc0 (Bytes.toB256 [0]).toBytes) 0x5c0 (d.returnData.take 0x20)) 0x5a0
      (Nat.toB256 (min d.returnData.length 32)).toBytes) 0x3a0 ((Bytes.writeAt (Bytes.writeAt
      (Bytes.writeAt img 0xc0 (Bytes.toB256 [0]).toBytes) 0x5c0 (d.returnData.take 0x20)) 0x5a0
      (Nat.toB256 (min d.returnData.length 32)).toBytes).sliceD 0x5a0
      (min d.returnData.length 32 + 32) 0)) 0x2a0 (Nat.toB256 i) := by
    wchain; exact hL.ctr
  xr (fun h => rx_dest (rx_dest h))
  xr (rx_dup (n := 1) rfl (by hr) ·)
  xr (rxm_mload (o := 0x2a0) hR6 hsz6 rfl ⟨by decide, by decide⟩ (by hr) ·)
  rw [hctr6.read]
  wrun 2
  rw [succ_lit hi]
  wrun 2
  refine rxe_mstoreL (o := 0x2a0) (c := 3) hR6 hW6 hsz6 rfl (by decide) ?_
  intro M7 hM7 hR7 hW7 hsz7
  wrun 4
  have hWb' : W' b' := hW'c.sha _ _ _ hsha hWd
  have hidb' : IdReady sevm b' := (hidd (hid.afterSload _)).of_rel
    ⟨hsha.stor, hsha.code, hsha.addrs, hsha.logs, hsha.output, hsha.error⟩
  have hstb' : ∀ x, (b'.getStor sevm.currentTarget).get x = (b.getStor sevm.currentTarget).get x := by
    intro x; rw [hsha.stor, hstor, afterSload_getStor]
  have hLI : LoopImg (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
      img 0xc0 (Bytes.toB256 [0]).toBytes) 0x5c0 (d.returnData.take 0x20)) 0x5a0
      (Nat.toB256 (min d.returnData.length 32)).toBytes) 0x3a0 ((Bytes.writeAt (Bytes.writeAt
      (Bytes.writeAt img 0xc0 (Bytes.toB256 [0]).toBytes) 0x5c0 (d.returnData.take 0x20)) 0x5a0
      (Nat.toB256 (min d.returnData.length 32)).toBytes).sliceD 0x5a0
      (min d.returnData.length 32 + 32) 0)) 0x2a0 (Nat.toB256 (i + 1)).toBytes) (i + 1) T a :=
    ⟨WordAt.write_self _ _ _, by wchain; exact hL.supply,
      fun j hj => by wchain; exact hL.amt j hj⟩
  have hsz7' : M7.size = 0x5e0 := by rw [hsz7]; decide
  rcases (show i + 1 = 3 ∨ i + 1 < 3 by omega) with h3 | h3
  · have hn : rlNext i = t_2f7b_c15 := by unfold rlNext; simp only [h3, ↓reduceIte]
    have e0 : B256.eqCheck (B256.eqCheck 3 (Nat.toB256 (i + 1))) 0 = 0 := by rw [h3]; decide
    rw [e0]
    xr (rx_branchTo_zero ·)
    have := k b' M7 _ G' hWb' hidb' hstb' hR7 hW7 hsz7' hLI d
      (by rw [hM1] at hE; exact hE) (by omega) hcanT hM7
    rwa [hn] at this
  · have hn : rlNext i = t_2cdb_c46 := by unfold rlNext; simp only [show i + 1 ≠ 3 by omega, ↓reduceIte]
    xr (rx_branchTo_succ (by rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> decide)
      rfl ·)
    have := k b' M7 _ G' hWb' hidb' hstb' hR7 hW7 hsz7' hLI d
      (by rw [hM1] at hE; exact hE) (by omega) hcanT hM7
    rwa [hn] at this

/-- **After the loop, at the burn's floor and the lock's sentry**: `rx_rl_postE` admitted by `MutableFloorProfile`,
the gas after the burn named: `R + 3138 + c`, with `c` the lock's charge. -/
theorem rx_rl_postF {sevm : Sevm} {b : Devm} {Gx : Nat} {Q : Outcome → Prop} {M : Mem}
    {img : Bytes} {T : B256} {a : Nat → B256} {W W' : Devm → Prop} {U K R c : Nat}
    {debit : Devm → List B256 → Mem → Nat} {next : Devm → List B256 → Mem → Devm}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hWc : WClosed sevm W) (hWb : W b)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x5e0) (hL : LoopImg img 3 T a)
    (hTa : (rlAmt sevm).toNat ≤ T.toNat)
    (hp : MutableFloorProfile sevm W W' ((b.getStor sevm.currentTarget).get tokenSlot)
      (burnFromSel ++ sevm.caller.toB256.toBytes ++ (rlAmt sevm).toBytes)
      (fun r => 32 ≤ r.length) U K 0x61c 0x44 0x6a0 debit next)
    (hKc : K ≤ R + 3138 + c) (hsentry : gCallStipend < R + c)
    (hc : ∀ d, Devm.EqModGas d (next (afterSload sevm b tokenSlot) [] (rlBurnMem sevm M)) →
      sstoreCost sevm d (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [0]) = c)
    (hGx : Gx = R + 3138 + c + debit (afterSload sevm b tokenSlot) [] (rlBurnMem sevm M))
    (hGb : Gx < 2 ^ 256)
    (hQ : ∀ D, D.gasLeft = R → (∃ L ts data, D.logs = L ++ [⟨sevm.currentTarget, ts, data⟩] ∧
      Bytes.toB256 (data.sliceD 0xc0 32 0) = T - rlAmt sevm) → Q (.halted D)) :
    SFunc.RunEx cert.prog sevm (St b [3, 0x2a0] M (Gx + rlPostCost sevm b)) t_2f7b_c15 Q := by
  unfold rlPostCost
  rw [show Gx + (67 + sloadCost sevm b tokenSlot) = Gx + 2 + sloadCost sevm b tokenSlot + 3 + 3 +
    3 + 7 + 3 + 3 + 3 + 6 + 3 + 2 + 9 + 3 + 3 + 3 + 3 + 3 + 2 + 2 + 1 by omega, ← tokenSlot_lit]
  wrun 8
  refine rxe_mstoreL (o := 0x600) (c := 9) hR hW hsz rfl (by decide) ?_; intro M hM1 hR hW hsz
  wrun 2
  refine rxe_mstoreL (o := 0x620) (c := 6) hR hW hsz rfl (by decide) ?_; intro M hM2 hR hW hsz
  wrun 3
  refine rxe_mstoreL (o := 0x640) (c := 7) hR hW hsz rfl (by decide) ?_; intro M hM3 hR hW hsz
  wrun 3
  xr (rx_sload_sel hfork (by hr) ·)
  rw [tokenSlot_lit, getStorVal_eq]
  xr (rx_gas (by hr) ·)
  rw [show Bytes.toB256 [0] = (0 : B256) by decide,
    show Bytes.toB256 [0x06, 0x1c] = (0x61c : B256) by decide,
    show Bytes.toB256 [0x44] = (0x44 : B256) by decide,
    show Bytes.toB256 [0x06, 0xa0] = (0x6a0 : B256) by decide,
    show Bytes.toB256 [0x20] = (0x20 : B256) by decide]
  have hin : (M.read 0x61c 0x44).1 =
      burnFromSel ++ sevm.caller.toB256.toBytes ++ (rlAmt sevm).toBytes := by
    rw [hR.read, burn_input]
  have hGxM : Gx = R + 3138 + c + debit (afterSload sevm b tokenSlot) [] M := by
    rw [hM3, hM2, hM1]; exact hGx
  obtain ⟨-, d, hrun, hpost0⟩ := hp.sound (afterSload sevm b tokenSlot) [] M Gx
    ⟨hWc.sload _ _ hWb, by omega, hGb, hin, by decide⟩
  obtain ⟨hgas, hnext, hpost, hrd32, hrdlt, -, -, -⟩ := hpost0
  have hcd := hc d (by rw [hM3, hM2, hM1] at hnext; exact hnext)
  xr (.next hrun ·)
  obtain ⟨hmem, -⟩ := hpost.settled (by decide)
  rw [show (0x61c : B256).toNat = 0x61c by decide, show (0x44 : B256).toNat = 0x44 by decide,
    show (0x6a0 : B256).toNat = 0x6a0 by decide, show (0x20 : B256).toNat = 0x20 by decide] at hmem
  have hd : d = St d [1] d.memory d.gasLeft := St.self hpost.stack rfl
  rw [hd]
  have hext : (M.extends [(0x61c, 0x44), (0x6a0, 0x20)]).size = 0x6c0 := by
    show memExtsSize M.size _ = _
    rw [hsz]; decide
  have hsz2 : d.memory.size = 0x6c0 := by
    rw [hmem, Mem.size_write_of_le (by rw [hext, List.length_take]; omega), hext]
  have hR2 := (hR.extends [(0x61c, 0x44), (0x6a0, 0x20)]).write (hW.extends _) 0x6a0
    (d.returnData.take 0x20)
  rw [← hmem] at hR2
  have hW2 : Mem.Wf d.memory := by rw [hmem]; exact (hW.extends _).write _ _
  clear hR hW hsz hext hmem hrun hpost
  obtain ⟨img2, hR, hI⟩ := Mem.Reads.forget hR2
  have f_T : WordAt img2 0x140 T := by rw [hI]; wchain; exact hL.supply
  clear hI hR2
  obtain ⟨G3, hG3⟩ : ∃ G3, d.gasLeft = G3 + 3 + 3 + 2917 + 3 + 3 + 3 + 2 + 6 + 3 + 2 + 3 + 2 +
      3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 7 + 3 + 3 + 3 + 6 + 3 + 3 + 3 +
      6 + 3 + 3 + 3 + 6 + 3 + 3 + 3 + 7 + 3 + 3 + 3 + 6 + 3 + 3 + 3 + 2 + 3 + 2 + 3 + 1 + 10 + 3 +
      3 + 2 + 3 + 1 + 10 + 3 := ⟨d.gasLeft - 3138, by omega⟩
  rw [hG3]
  have hgt : B256.gtCheck (Nat.toB256 d.returnData.length) (Bytes.toB256 [0x1f]) ≠ 0 := by
    apply gtCheck_ne_zero_of_lt
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrdlt,
      show (Bytes.toB256 [0x1f]).toNat = 31 by decide]
    omega
  have hlt : B256.eqCheck (B256.ltCheck T (rlAmt sevm)) 0 ≠ 0 := by
    rw [B256.ltCheck_eq_zero_of_toNat_le hTa]; decide
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by decide) ·)
  wrun 5
  xr (rx_branch_succ hgt ·)
  wrun 6
  xr (rxm_mload (o := 0x1e0) hR hsz2 rfl (by decide) (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x6c0) (c := 6) hR hW2 hsz2 rfl (by decide) ?_; intro M hM4 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x200) hR hsz rfl (by decide) (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x6e0) (c := 7) hR hW hsz rfl (by decide) ?_; intro M hM5 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x220) hR hsz rfl (by decide) (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x700) (c := 6) hR hW hsz rfl (by decide) ?_; intro M hM6 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x240) hR hsz rfl (by decide) (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x720) (c := 6) hR hW hsz rfl (by decide) ?_; intro M hM7 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x260) hR hsz rfl (by decide) (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x740) (c := 6) hR hW hsz rfl (by decide) ?_; intro M hM8 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x280) hR hsz rfl (by decide) (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x760) (c := 7) hR hW hsz rfl (by decide) ?_; intro M hM9 hR hW hsz
  xr (rx_push rfl (by hr) ·)
  obtain ⟨img4, hR, hI⟩ := Mem.Reads.forget hR
  have f_T4 : WordAt img4 0x140 T := by rw [hI]; wchain; exact f_T
  clear hI
  xr (rxm_mload (o := 0x140) hR hsz rfl (by decide) (by hr) ·)
  rw [f_T4.read]
  wrun 7
  xr (rx_branch_succ hlt ·)
  wrun 9
  refine rxe_mstoreL (o := 0x780) (c := 6) hR hW hsz rfl (by decide) ?_; intro M hM10 hR hW hsz
  wrun 4
  xr (rx_log2 (c := 2917) hstatic (by rw [St.extCost_eq hsz]; decide) rfl
    (read_covered_len hsz (by decide) (by decide)) ·)
  wrun 2
  have hG3R : G3 = R + c := by omega
  refine rxe_sstoreS hfork hstatic (R := R) (by
    have e : ∀ l : Log, sstoreCost sevm (d.addLog l) (Bytes.toB256 [255, 255, 255])
        (Bytes.toB256 [0]) = sstoreCost sevm d (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [0]) :=
      fun _ => rfl
    rw [hG3R, ← hcd]
    exact congrArg (R + ·) (e _).symm) (by rw [hG3R]; exact hsentry) ?_
  refine ⟨_, .last rfl, hQ _ rfl ⟨_, _, _, (afterSstore_logs _ _ _ _).trans rfl, ?_⟩⟩
  rw [hR.read, Bytes.sliceD_sliceD_of_le _ _ _ _ _ (by decide),
    show (Bytes.toB256 [0x06, 0xc0]).toNat + 0xc0 = 0x780 by decide]
  exact (congrArg Bytes.toB256 (WordAt.write_self _ _ _)).trans (B256.toB256_toBytes _)

/-! ## The frame -/

/-- **`remove_liquidity`'s five calls at their floors.** The push and burn floor `4900` is the largest a coin's
frame needs behind the 64th its call retains; the supply read's debit is bounded, so the existing prologue takes it
at `5336 + 2400`. -/
structure RLFloorPremises (sevm : Sevm) (pre : Devm) (T : B256) (W : Nat → Devm → Prop) (U : Nat)
    (P : RLExactCalls) : Prop where
  /-- `totalSupply()`, at its floor. -/
  supply : StaticWordFloorProfile sevm (W 0) (W 0) ((pre.getStor sevm.currentTarget).get tokenSlot)
    totalSupplyData T U 2400 0x17c 4 0x1c0 P.supplyDebit P.supplyNext
  /-- `totalSupply()`'s debit is at most `5336`, in any world of the chain's start. -/
  supplyLe : ∀ b S M, W 0 b → (M.read (0x17c : B256).toNat (4 : B256).toNat).1 = totalSupplyData →
    P.supplyDebit b S M ≤ 5336
  /-- Coin `i`'s `transfer`, at its floor. -/
  push : ∀ i, i < 3 → MutableFloorProfile sevm (W i) (W (i + 1))
    (coinAt (pre.getStor sevm.currentTarget) i)
    (transferSel ++ sevm.caller.toB256.toBytes ++
      (balAt (pre.getStor sevm.currentTarget) i * rlAmt sevm / T).toBytes)
    RawCallOk U 4900 0x520 0x44 0x5c0 (P.pushDebit i) (P.pushNext i)
  /-- `burnFrom`, at its floor. -/
  burn : MutableFloorProfile sevm (W 3) (W 4) ((pre.getStor sevm.currentTarget).get tokenSlot)
    (burnFromSel ++ sevm.caller.toB256.toBytes ++ (rlAmt sevm).toBytes)
    (fun r => 32 ≤ r.length) U 4900 0x61c 0x44 0x6a0 P.burnDebit P.burnNext

/-- The floor premises survive a change of static initial gas, with the same data `P`. -/
theorem RLFloorPremises.withStaticGas {sevm : Sevm} {pre : Devm} {T : B256}
    {W : Nat → Devm → Prop} {U : Nat} {P : RLExactCalls}
    (h : RLFloorPremises sevm pre T W U P) (F : Nat) :
    RLFloorPremises {sevm with gas := F} pre T W U P :=
  ⟨h.supply.withStaticGas F, h.supplyLe, fun i hi => (h.push i hi).withStaticGas F,
    h.burn.withStaticGas F⟩

/-- What one iteration charges at least beyond its storage step. -/
theorem rlIterCost_ge (sevm : Sevm) (pre : Devm) (T : B256) (P : RLExactCalls) (i : Nat) (n : Devm)
    (m : Mem) (s1 : Nat) : s1 + 201 ≤ rlIterCost sevm pre T P i n m s1 := by
  have h1 : 108 ≤ rlS3Cost sevm (rlS2Base sevm pre T i n m) i := by unfold rlS3Cost; omega
  have h2 : 48 ≤ rawTailCost (rlReplyLen sevm pre T P i n m) := by
    unfold rawTailCost; split <;> omega
  unfold rlIterCost
  omega

/-- The call and its tail of one iteration, from the payload's end. -/
theorem rx_rl_iterTailF {sevm : Sevm} {pre b2 n : Devm} {G : Nat} {Q : Outcome → Prop}
    {M M2 : Mem} {img2 : Bytes} {s i : Nat} {T : B256} {P : RLExactCalls} {a : Nat → B256}
    {W W' : Devm → Prop} {U : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hi : i < 3) (hdepth : sevm.depth ≠ 0)
    (hid2 : IdReady sevm b2) (hWc : WClosed sevm W) (hWb2 : W b2) (hW'c : WClosed sevm W')
    (hq : Devm.EqModGas b2 (rlS2Base sevm pre T i n M))
    (hC2 : (b2.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 i) =
      coinAt (pre.getStor sevm.currentTarget) i)
    (hR2 : Mem.Reads M2 img2) (hW2 : Mem.Wf M2) (hsz2 : M2.size = s) (hs : s = 0x580 ∨ s = 0x5e0)
    (hL2 : LoopImg img2 i T a)
    (hdata : Region img2 0x500 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
      Bytes.toB256 [32]).toBytes ++ (transferSel ++ sevm.caller.toB256.toBytes ++ (rlV sevm pre T i).toBytes)))
    (hM2' : M2.write 0xc0 (Bytes.toB256 [0]).toBytes = rlPushMem sevm pre T i M)
    (hp : MutableFloorProfile sevm W W' (coinAt (pre.getStor sevm.currentTarget) i)
      (transferSel ++ sevm.caller.toB256.toBytes ++ (rlV sevm pre T i).toBytes)
      RawCallOk U 4900 0x520 0x44 0x5c0 (P.pushDebit i) (P.pushNext i))
    (hG : 4900 ≤ G)
    (hGb : G + 45 + rawTailCost (rlReplyLen sevm pre T P i n M) + rlPushDebit sevm pre T P i n M + 1000 < 2 ^ 256)
    (k : ∀ b' M' img', W' b' → IdReady sevm b' →
      (∀ x, (b'.getStor sevm.currentTarget).get x = (b2.getStor sevm.currentTarget).get x) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x5e0 → LoopImg img' (i + 1) T a →
      Devm.EqModGas b' (rlIterBase sevm pre T P i n M) → M' = rlIterMem sevm pre T P i n M →
      SFunc.RunEx cert.prog sevm (St b' [3, 0x2a0] M' G) (rlNext i) Q) (x y : B256) :
    SFunc.RunEx cert.prog sevm (St b2 (x :: y :: [3, 0x2a0]) M2
      (G + 45 + rawTailCost (rlReplyLen sevm pre T P i n M) + rlPushDebit sevm pre T P i n M +
        rlS3Cost sevm b2 i)) t_2ea7_c0 Q := by
  have hpb : Devm.EqModGas (afterSload sevm b2 (coinsBase + Nat.toB256 i))
      (rlPushBase sevm pre T i n M) := hq.afterSload sevm _
  obtain ⟨hdeb, hnext⟩ := hp.congr [3, 0x2a0] (rlPushMem sevm pre T i M) hpb
  refine rx_rl_s3F hfork hi hdepth hid2 hWc hWb2 hW'c hR2 hW2 hsz2 hs hL2 hdata hC2 hp (by decide)
    (by rw [hM2', hdeb]; unfold rlPushDebit; omega) (by omega) ?_ x y
  intro b' M' img' G' hWb' hid' hst' hR' hW' hsz' hL' d hE hgd hcanT hM'
  rw [hM2'] at hE
  obtain ⟨hEg, hEn⟩ := hE
  have hdN : Devm.EqModGas d (rlPushNext sevm pre T P i n M) := hEn.trans hnext
  have hlen : min d.returnData.length 32 = rlReplyLen sevm pre T P i n M := by
    unfold rlReplyLen; rw [hdN.returnData]
  have hGG : G' = G := by
    rw [hlen] at hgd
    unfold rlPushDebit at *
    omega
  subst hGG
  refine k b' M' img' hWb' hid' hst' hR' hW' hsz' hL' ?_ ?_
  · refine hcanT.trans ?_
    unfold rlIterBase
    rw [hdN.memory]
    exact rawTailBaseNext_congr sevm _ _ rlSite hdN
  · rw [hM', hdN.memory, hlen]; rfl

/-- **One iteration at the floor** (variant A), as `rx_rl_iterA_exact`. -/
theorem rx_rl_iterAF {sevm : Sevm} {pre b n : Devm} {G : Nat} {Q : Outcome → Prop}
    {M : Mem} {img : Bytes} {i : Nat} {T : B256} {P : RLExactCalls} {a : Nat → B256}
    {W W' : Devm → Prop} {U : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hi : i < 3)
    (hdepth : sevm.depth ≠ 0) (hid : IdReady sevm b) (hWc : WClosed sevm W) (hWb : W b)
    (hW'c : WClosed sevm W') (hn : Devm.EqModGas b n)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x2c0) (hL : LoopImg img i T a)
    (hB : (b.getStor sevm.currentTarget).get (balancesBase + Nat.toB256 i) = rlB sevm pre i)
    (hmulw : (B256.eqCheck (rlB sevm pre i * rlAmt sevm / rlB sevm pre i) (rlAmt sevm) |||
      B256.eqCheck (rlB sevm pre i) 0) ≠ 0)
    (hT0 : T ≠ 0)
    (hminw : B256.eqCheck (B256.ltCheck (rlV sevm pre T i) (rlMin sevm i)) 0 ≠ 0)
    (hlew : B256.eqCheck (B256.ltCheck (rlB sevm pre i) (rlV sevm pre T i)) 0 ≠ 0)
    (hC : (b.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 i) =
      coinAt (pre.getStor sevm.currentTarget) i)
    (hp : MutableFloorProfile sevm W W' (coinAt (pre.getStor sevm.currentTarget) i)
      (transferSel ++ sevm.caller.toB256.toBytes ++ (rlV sevm pre T i).toBytes)
      RawCallOk U 4900 0x520 0x44 0x5c0 (P.pushDebit i) (P.pushNext i))
    (hG : 4900 ≤ G)
    (hGb : G + rlIterCost sevm pre T P i n M (rlS1CostA sevm n i (rlB sevm pre i) T + 532) < 2 ^ 256)
    (k : ∀ b' M' img', W' b' → IdReady sevm b' →
      (∀ x, (b'.getStor sevm.currentTarget).get x = ((b.getStor sevm.currentTarget).set
        (balancesBase + Nat.toB256 i) (rlB sevm pre i - rlV sevm pre T i)).get x) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x5e0 →
      LoopImg img' (i + 1) T (Function.update a i (rlV sevm pre T i)) →
      Devm.EqModGas b' (rlIterBase sevm pre T P i n M) → M' = rlIterMem sevm pre T P i n M →
      SFunc.RunEx cert.prog sevm (St b' [3, 0x2a0] M' G) (rlNext i) Q) :
    SFunc.RunEx cert.prog sevm
      (St b [3, 0x2a0] M (G + rlIterCost sevm pre T P i n M
        (rlS1CostA sevm n i (rlB sevm pre i) T + 532))) t_2cdb_c0 Q := by
  have hS1 := rlS1CostA_congr sevm i (rlB sevm pre i) T hn
  have hS1' : 500 ≤ rlS1CostA sevm n i (rlB sevm pre i) T := by unfold rlS1CostA; omega
  have hS3' : 108 ≤ rlS3Cost sevm (rlS2Base sevm pre T i n M) i := by unfold rlS3Cost; omega
  set V := rlV sevm pre T i with hV
  have hS3 : ∀ b2, Devm.EqModGas b2 (rlS2Base sevm pre T i n M) →
      rlS3Cost sevm b2 i = rlS3Cost sevm (rlS2Base sevm pre T i n M) i :=
    fun b2 h => rlS3Cost_congr sevm i h
  unfold rlIterCost at hGb ⊢
  rw [show G + (rlS1CostA sevm n i (rlB sevm pre i) T + 532 +
      rlS3Cost sevm (rlS2Base sevm pre T i n M) i + rlPushDebit sevm pre T P i n M +
      rawTailCost (rlReplyLen sevm pre T P i n M) + 45) =
      (G + 45 + rawTailCost (rlReplyLen sevm pre T P i n M) + rlPushDebit sevm pre T P i n M +
        rlS3Cost sevm (rlS2Base sevm pre T i n M) i) + 532 + rlS1CostA sevm b i (rlB sevm pre i) T
    by rw [hS1]; omega]
  refine rx_rl_s1AL hfork hstatic hi hR hW hsz hL hB hmulw hT0 hminw hlew (by omega) ?_
  intro M1 img1 hM1 hR1 hW1 hsz1 hL1 hv1
  have hWb1 := hWc.sstore _ (balancesBase + Nat.toB256 i) (rlB sevm pre i - V)
    (hWc.sload _ (balancesBase + Nat.toB256 i) (hWc.sload _ (balancesBase + Nat.toB256 i) hWb))
  have hid1 := ((hid.afterSload (balancesBase + Nat.toB256 i)).afterSload
    (balancesBase + Nat.toB256 i)).afterSstore (balancesBase + Nat.toB256 i) (rlB sevm pre i - V)
  have hn1 : Devm.EqModGas (afterSstore sevm (afterSload sevm (afterSload sevm b
      (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i)
      (rlB sevm pre i - V)) (rlS1Base sevm pre T i n) :=
    ((hn.afterSload sevm _).afterSload sevm _).afterSstore sevm _ _
  refine rx_rl_s2AL hi hid1 hdepth hR1 hW1 hsz1 hL1 hv1 (by omega) (by omega) hWc hWb1 ?_
  intro b2 M2 img2 hrel hWb2 hid2 hcan2 hM2 hR2 hW2 hsz2 hL2 hdata x y
  have hq : Devm.EqModGas b2 (rlS2Base sevm pre T i n M) := by
    refine hcan2.trans ?_
    rw [hM1]
    exact rlS2Next_congr sevm _ i V hn1
  have hst2 : ∀ x, (b2.getStor sevm.currentTarget).get x = ((b.getStor sevm.currentTarget).set
      (balancesBase + Nat.toB256 i) (rlB sevm pre i - V)).get x := by
    intro x
    rw [hrel.stor, afterSstore_getStor_self, afterSload_getStor, afterSload_getStor]
  have hC2 : (b2.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 i) =
      coinAt (pre.getStor sevm.currentTarget) i := by
    rw [hst2, Stor.get_set_ne _ (by rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
      decide), hC]
  rw [← hS3 b2 hq]
  have hM2' : M2.write 0xc0 (Bytes.toB256 [0]).toBytes = rlPushMem sevm pre T i M := by
    rw [hM2, hM1]; rfl
  refine rx_rl_iterTailF hfork hi hdepth hid2 hWc hWb2 hW'c hq hC2 hR2 hW2 hsz2 (Or.inl rfl) hL2 hdata
    hM2' hp hG (by omega) ?_ x y
  intro b' M' img' hWb' hid' hst' hR' hW' hsz' hL' hcan hM'
  exact k b' M' img' hWb' hid' (fun x => (hst' x).trans (hst2 x)) hR' hW' hsz' hL' hcan hM'

/-- **One iteration at the floor** (variant B), as `rx_rl_iterB_exact`. -/
theorem rx_rl_iterBF {sevm : Sevm} {pre b n : Devm} {G : Nat} {Q : Outcome → Prop}
    {M : Mem} {img : Bytes} {i : Nat} {T : B256} {P : RLExactCalls} {a : Nat → B256}
    {W W' : Devm → Prop} {U : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hi : i < 3)
    (hdepth : sevm.depth ≠ 0) (hid : IdReady sevm b) (hWc : WClosed sevm W) (hWb : W b)
    (hW'c : WClosed sevm W') (hn : Devm.EqModGas b n)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x5e0) (hL : LoopImg img i T a)
    (hB : (b.getStor sevm.currentTarget).get (balancesBase + Nat.toB256 i) = rlB sevm pre i)
    (hmulw : (B256.eqCheck (rlB sevm pre i * rlAmt sevm / rlB sevm pre i) (rlAmt sevm) |||
      B256.eqCheck (rlB sevm pre i) 0) ≠ 0)
    (hT0 : T ≠ 0)
    (hminw : B256.eqCheck (B256.ltCheck (rlV sevm pre T i) (rlMin sevm i)) 0 ≠ 0)
    (hlew : B256.eqCheck (B256.ltCheck (rlB sevm pre i) (rlV sevm pre T i)) 0 ≠ 0)
    (hC : (b.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 i) =
      coinAt (pre.getStor sevm.currentTarget) i)
    (hp : MutableFloorProfile sevm W W' (coinAt (pre.getStor sevm.currentTarget) i)
      (transferSel ++ sevm.caller.toB256.toBytes ++ (rlV sevm pre T i).toBytes)
      RawCallOk U 4900 0x520 0x44 0x5c0 (P.pushDebit i) (P.pushNext i))
    (hG : 4900 ≤ G)
    (hGb : G + rlIterCost sevm pre T P i n M (rlS1CostB sevm n i (rlB sevm pre i) T + 482) < 2 ^ 256)
    (k : ∀ b' M' img', W' b' → IdReady sevm b' →
      (∀ x, (b'.getStor sevm.currentTarget).get x = ((b.getStor sevm.currentTarget).set
        (balancesBase + Nat.toB256 i) (rlB sevm pre i - rlV sevm pre T i)).get x) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x5e0 →
      LoopImg img' (i + 1) T (Function.update a i (rlV sevm pre T i)) →
      Devm.EqModGas b' (rlIterBase sevm pre T P i n M) → M' = rlIterMem sevm pre T P i n M →
      SFunc.RunEx cert.prog sevm (St b' [3, 0x2a0] M' G) (rlNext i) Q) :
    SFunc.RunEx cert.prog sevm
      (St b [3, 0x2a0] M (G + rlIterCost sevm pre T P i n M
        (rlS1CostB sevm n i (rlB sevm pre i) T + 482))) t_2cdb_c46 Q := by
  have hS1 := rlS1CostB_congr sevm i (rlB sevm pre i) T hn
  have hS1' : 500 ≤ rlS1CostB sevm n i (rlB sevm pre i) T := by unfold rlS1CostB; omega
  have hS3' : 108 ≤ rlS3Cost sevm (rlS2Base sevm pre T i n M) i := by unfold rlS3Cost; omega
  set V := rlV sevm pre T i with hV
  have hS3 : ∀ b2, Devm.EqModGas b2 (rlS2Base sevm pre T i n M) →
      rlS3Cost sevm b2 i = rlS3Cost sevm (rlS2Base sevm pre T i n M) i :=
    fun b2 h => rlS3Cost_congr sevm i h
  unfold rlIterCost at hGb ⊢
  rw [show G + (rlS1CostB sevm n i (rlB sevm pre i) T + 482 +
      rlS3Cost sevm (rlS2Base sevm pre T i n M) i + rlPushDebit sevm pre T P i n M +
      rawTailCost (rlReplyLen sevm pre T P i n M) + 45) =
      (G + 45 + rawTailCost (rlReplyLen sevm pre T P i n M) + rlPushDebit sevm pre T P i n M +
        rlS3Cost sevm (rlS2Base sevm pre T i n M) i) + 482 + rlS1CostB sevm b i (rlB sevm pre i) T
    by rw [hS1]; omega]
  refine rx_rl_s1BL hfork hstatic hi hR hW hsz hL hB hmulw hT0 hminw hlew (by omega) ?_
  intro M1 img1 hM1 hR1 hW1 hsz1 hL1 hv1
  have hWb1 := hWc.sstore _ (balancesBase + Nat.toB256 i) (rlB sevm pre i - V)
    (hWc.sload _ (balancesBase + Nat.toB256 i) (hWc.sload _ (balancesBase + Nat.toB256 i) hWb))
  have hid1 := ((hid.afterSload (balancesBase + Nat.toB256 i)).afterSload
    (balancesBase + Nat.toB256 i)).afterSstore (balancesBase + Nat.toB256 i) (rlB sevm pre i - V)
  have hn1 : Devm.EqModGas (afterSstore sevm (afterSload sevm (afterSload sevm b
      (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i)) (balancesBase + Nat.toB256 i)
      (rlB sevm pre i - V)) (rlS1Base sevm pre T i n) :=
    ((hn.afterSload sevm _).afterSload sevm _).afterSstore sevm _ _
  refine rx_rl_s2BL hi hid1 hdepth hR1 hW1 hsz1 hL1 hv1 (by omega) (by omega) hWc hWb1 ?_
  intro b2 M2 img2 hrel hWb2 hid2 hcan2 hM2 hR2 hW2 hsz2 hL2 hdata x y
  have hq : Devm.EqModGas b2 (rlS2Base sevm pre T i n M) := by
    refine hcan2.trans ?_
    rw [hM1]
    exact rlS2Next_congr sevm _ i V hn1
  have hst2 : ∀ x, (b2.getStor sevm.currentTarget).get x = ((b.getStor sevm.currentTarget).set
      (balancesBase + Nat.toB256 i) (rlB sevm pre i - V)).get x := by
    intro x
    rw [hrel.stor, afterSstore_getStor_self, afterSload_getStor, afterSload_getStor]
  have hC2 : (b2.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 i) =
      coinAt (pre.getStor sevm.currentTarget) i := by
    rw [hst2, Stor.get_set_ne _ (by rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
      decide), hC]
  rw [← hS3 b2 hq]
  have hM2' : M2.write 0xc0 (Bytes.toB256 [0]).toBytes = rlPushMem sevm pre T i M := by
    rw [hM2, hM1]; rfl
  refine rx_rl_iterTailF hfork hi hdepth hid2 hWc hWb2 hW'c hq hC2 hR2 hW2 hsz2 (Or.inr rfl) hL2 hdata
    hM2' hp hG (by omega) ?_ x y
  intro b' M' img' hWb' hid' hst' hR' hW' hsz' hL' hcan hM'
  exact k b' M' img' hWb' hid' (fun x => (hst' x).trans (hst2 x)) hR' hW' hsz' hL' hcan hM'

/-- **`remove_liquidity`, the whole frame forward, at the true minimum.** As `rx_rl_frame_exact`, with the calls at
their floors, for every residual gas `R ≥ 2201`: the frame runs from `R + rlExactCost` to `STOP` with exactly `R`
left, at the same cost, whose functions `P` are fixed first. -/
theorem rx_rl_frame_floor {sevm : Sevm} {pre : Devm} {W : Nat → Devm → Prop} {U : Nat}
    {T : B256} (P : RLExactCalls)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidity) (hid : IdReady sevm pre)
    (hlock : (pre.getStor sevm.currentTarget).get lockSlot = 0) (hval : sevm.value = 0)
    (hWc : ∀ k, k ≤ 3 → WClosed sevm (W k)) (hWb : W 0 pre)
    (hP : RLFloorPremises sevm pre T W U P)
    (hmulw : ∀ i, i < 3 →
      (B256.eqCheck (rlB sevm pre i * rlAmt sevm / rlB sevm pre i) (rlAmt sevm) |||
        B256.eqCheck (rlB sevm pre i) 0) ≠ 0)
    (hT0 : T ≠ 0)
    (hminw : ∀ i, i < 3 → B256.eqCheck (B256.ltCheck (rlV sevm pre T i) (rlMin sevm i)) 0 ≠ 0)
    (hlew : ∀ i, i < 3 → B256.eqCheck (B256.ltCheck (rlB sevm pre i) (rlV sevm pre T i)) 0 ≠ 0)
    (hTa : (rlAmt sevm).toNat ≤ T.toNat)
    {R : Nat} (hR : 2201 ≤ R) (hGb : R + rlExactCost sevm pre T P < 2 ^ 256) :
    SFunc.RunEx cert.prog sevm (St pre [] Mem.empty (R + rlExactCost sevm pre T P)) t_0000_c0
      (fun o => ∃ D, o = .halted D ∧ D.gasLeft = R ∧
        ∃ L ts data, D.logs = L ++ [⟨sevm.currentTarget, ts, data⟩] ∧
          Bytes.toB256 (data.sliceD 0xc0 32 0) = T - rlAmt sevm) := by
  obtain ⟨hsup, hsupLe, hpush, hburn⟩ := hP
  have e0 : rlIter0Cost sevm pre T P = rlIterCost sevm pre T P 0 (rlHead0 sevm pre P)
      (rlHeadMem0 sevm pre T P) (rlS1CostA sevm (rlHead0 sevm pre P) 0 (rlB sevm pre 0) T + 532) :=
    rfl
  have e1 : rlIter1Cost sevm pre T P = rlIterCost sevm pre T P 1 (rlHead1 sevm pre T P)
      (rlHeadMem1 sevm pre T P)
      (rlS1CostB sevm (rlHead1 sevm pre T P) 1 (rlB sevm pre 1) T + 482) := rfl
  have e2 : rlIter2Cost sevm pre T P = rlIterCost sevm pre T P 2 (rlHead2 sevm pre T P)
      (rlHeadMem2 sevm pre T P)
      (rlS1CostB sevm (rlHead2 sevm pre T P) 2 (rlB sevm pre 2) T + 482) := rfl
  have ep : rlPostExactCost sevm pre T P = rlPostCost sevm (rlHead3 sevm pre T P) +
      P.burnDebit (rlBurnBase sevm pre T P) [] (rlBurnMem sevm (rlHeadMem3 sevm pre T P)) + 3138 +
      sstoreCost sevm (P.burnNext (rlBurnBase sevm pre T P) []
        (rlBurnMem sevm (rlHeadMem3 sevm pre T P))) (Bytes.toB256 [255, 255, 255])
        (Bytes.toB256 [0]) := rfl
  have hI0 : 1233 ≤ rlIter0Cost sevm pre T P := by
    rw [e0]
    have h := rlIterCost_ge sevm pre T P 0 (rlHead0 sevm pre P) (rlHeadMem0 sevm pre T P)
      (rlS1CostA sevm (rlHead0 sevm pre P) 0 (rlB sevm pre 0) T + 532)
    have h' : 500 ≤ rlS1CostA sevm (rlHead0 sevm pre P) 0 (rlB sevm pre 0) T := by
      unfold rlS1CostA; omega
    omega
  have hI1 : 1183 ≤ rlIter1Cost sevm pre T P := by
    rw [e1]
    have h := rlIterCost_ge sevm pre T P 1 (rlHead1 sevm pre T P) (rlHeadMem1 sevm pre T P)
      (rlS1CostB sevm (rlHead1 sevm pre T P) 1 (rlB sevm pre 1) T + 482)
    have h' : 500 ≤ rlS1CostB sevm (rlHead1 sevm pre T P) 1 (rlB sevm pre 1) T := by
      unfold rlS1CostB; omega
    omega
  have hI2 : 1183 ≤ rlIter2Cost sevm pre T P := by
    rw [e2]
    have h := rlIterCost_ge sevm pre T P 2 (rlHead2 sevm pre T P) (rlHeadMem2 sevm pre T P)
      (rlS1CostB sevm (rlHead2 sevm pre T P) 2 (rlB sevm pre 2) T + 482)
    have h' : 500 ≤ rlS1CostB sevm (rlHead2 sevm pre T P) 2 (rlB sevm pre 2) T := by
      unfold rlS1CostB; omega
    omega
  have hLock := sstoreCost_ge sevm (P.burnNext (rlBurnBase sevm pre T P) []
    (rlBurnMem sevm (rlHeadMem3 sevm pre T P))) (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [0])
  have hWarm : gasWarmAccess = 100 := rfl
  have hPs : 67 ≤ rlPostCost sevm (rlHead3 sevm pre T P) := by unfold rlPostCost; omega
  unfold rlExactCost at hGb ⊢
  rw [show R + (451 + rlPreCost sevm pre +
      P.supplyDebit (rlSupplyBase sevm pre) [] (rlSupplyMem sevm) + 135 +
      rlIter0Cost sevm pre T P + rlIter1Cost sevm pre T P + rlIter2Cost sevm pre T P +
      rlPostExactCost sevm pre T P) =
    R + P.supplyDebit (rlSupplyBase sevm pre) [] (rlSupplyMem sevm) + 135 +
      rlIter0Cost sevm pre T P + rlIter1Cost sevm pre T P + rlIter2Cost sevm pre T P +
      rlPostExactCost sevm pre T P + rlPreCost sevm pre + 451 by omega]
  refine rx_dispatch_rl hlen hcd hsel ?_
  refine rx_rl_preE (T := T) (U := 5336 + 2400) (E := ExactE P.supplyDebit P.supplyNext) hfork hstatic hcd
    hlock hval (hWc 0 (by decide)) hWb (StaticWordFloorProfile.okE hsup hsupLe) (by omega) (by omega)
    (by omega) ?_
  intro b1 M1 img1 G1 hWb1 hid1 hst1 _ _ hR1 hW1 hsz1 hL1 _ _ hE1 hg1 hM1
  obtain ⟨hEg, hn0⟩ := hE1
  have hG1 : G1 = R + rlIter1Cost sevm pre T P + rlIter2Cost sevm pre T P +
      rlPostExactCost sevm pre T P + rlIter0Cost sevm pre T P := by omega
  have hM1' : M1 = rlHeadMem0 sevm pre T P := by rw [hM1, hn0.memory]; rfl
  subst hM1'
  rw [hG1]
  have hs1 : ∀ x, lockSlot ≠ x →
      (b1.getStor sevm.currentTarget).get x = (pre.getStor sevm.currentTarget).get x :=
    fun x hx => by rw [hst1, Stor.get_set_ne _ hx]
  -- iteration 0
  refine rx_rl_iterAF (i := 0) (n := rlHead0 sevm pre P) (pre := pre) (P := P) hfork hstatic
    (by decide) hdepth (hid1 hid) (hWc 0 (by decide)) hWb1 (hWc 1 (by decide)) hn0 hR1 hW1 hsz1
    hL1 (hs1 _ (by decide)) (hmulw 0 (by decide)) hT0 (hminw 0 (by decide)) (hlew 0 (by decide))
    (hs1 _ (by decide)) (hpush 0 (by decide)) (by omega)
    (by omega) ?_
  intro b2 M2 img2 hWb2 hid2 hst2 hR2 hW2 hsz2 hL2 hn1 hM2
  rw [show rlNext 0 = t_2cdb_c46 by unfold rlNext; rfl]
  have hM2' : M2 = rlHeadMem1 sevm pre T P := hM2
  subst hM2'
  have hs2 : ∀ x, lockSlot ≠ x → balancesBase + Nat.toB256 0 ≠ x →
      (b2.getStor sevm.currentTarget).get x = (pre.getStor sevm.currentTarget).get x :=
    fun x hx hx0 => by rw [hst2, Stor.get_set_ne _ hx0, hs1 _ hx]
  -- iteration 1
  rw [show R + rlIter1Cost sevm pre T P + rlIter2Cost sevm pre T P +
      rlPostExactCost sevm pre T P = R + rlIter2Cost sevm pre T P +
      rlPostExactCost sevm pre T P + rlIter1Cost sevm pre T P by omega]
  refine rx_rl_iterBF (i := 1) (n := rlHead1 sevm pre T P) (pre := pre) (P := P) hfork
    hstatic (by decide) hdepth hid2 (hWc 1 (by decide)) hWb2 (hWc 2 (by decide)) hn1 hR2 hW2 hsz2
    hL2 (hs2 _ (by decide) (by decide)) (hmulw 1 (by decide)) hT0 (hminw 1 (by decide))
    (hlew 1 (by decide)) (hs2 _ (by decide) (by decide)) (hpush 1 (by decide)) (by omega)
    (by omega) ?_
  intro b3 M3 img3 hWb3 hid3 hst3 hR3 hW3 hsz3 hL3 hn2 hM3
  rw [show rlNext 1 = t_2cdb_c46 by unfold rlNext; rfl]
  have hM3' : M3 = rlHeadMem2 sevm pre T P := hM3
  subst hM3'
  have hs3 : ∀ x, lockSlot ≠ x → balancesBase + Nat.toB256 0 ≠ x →
      balancesBase + Nat.toB256 1 ≠ x →
      (b3.getStor sevm.currentTarget).get x = (pre.getStor sevm.currentTarget).get x :=
    fun x hx hx0 hx1 => by rw [hst3, Stor.get_set_ne _ hx1, hs2 _ hx hx0]
  -- iteration 2
  rw [show R + rlIter2Cost sevm pre T P + rlPostExactCost sevm pre T P =
      R + rlPostExactCost sevm pre T P + rlIter2Cost sevm pre T P by omega]
  refine rx_rl_iterBF (i := 2) (n := rlHead2 sevm pre T P) (pre := pre) (P := P) hfork
    hstatic (by decide) hdepth hid3 (hWc 2 (by decide)) hWb3 (hWc 3 (by decide)) hn2 hR3 hW3 hsz3
    hL3 (hs3 _ (by decide) (by decide) (by decide)) (hmulw 2 (by decide)) hT0
    (hminw 2 (by decide)) (hlew 2 (by decide)) (hs3 _ (by decide) (by decide) (by decide))
    (hpush 2 (by decide)) (by omega)
    (by omega) ?_
  intro b4 M4 img4 hWb4 hid4 hst4 hR4 hW4 hsz4 hL4 hn3 hM4
  rw [show rlNext 2 = t_2f7b_c15 by unfold rlNext; rfl]
  have hM4' : M4 = rlHeadMem3 sevm pre T P := hM4
  subst hM4'
  have htok : (b4.getStor sevm.currentTarget).get tokenSlot =
      (pre.getStor sevm.currentTarget).get tokenSlot := by
    rw [hst4, Stor.get_set_ne _ (by decide), hs3 _ (by decide) (by decide) (by decide)]
  -- the burn, the event, the lock's release
  have hn3' : Devm.EqModGas b4 (rlHead3 sevm pre T P) := hn3
  obtain ⟨hdeb, hnext⟩ := hburn.congr [] (rlBurnMem sevm (rlHeadMem3 sevm pre T P))
    (hn3'.afterSload sevm tokenSlot)
  rw [show R + rlPostExactCost sevm pre T P =
      (R + 3138 + sstoreCost sevm (P.burnNext (rlBurnBase sevm pre T P) []
          (rlBurnMem sevm (rlHeadMem3 sevm pre T P))) (Bytes.toB256 [255, 255, 255])
          (Bytes.toB256 [0]) +
        P.burnDebit (rlBurnBase sevm pre T P) [] (rlBurnMem sevm (rlHeadMem3 sevm pre T P))) +
        rlPostCost sevm b4 by
    unfold rlPostExactCost; rw [rlPostCost_congr sevm hn3']; omega]
  refine rx_rl_postF hfork hstatic (hWc 3 (by decide)) hWb4 hR4 hW4 hsz4 hL4 hTa
    (by rw [htok]; exact hburn) (R := R) (c := sstoreCost sevm (P.burnNext (rlBurnBase sevm pre T P) []
      (rlBurnMem sevm (rlHeadMem3 sevm pre T P))) (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [0]))
    (by omega) (rl_lock_sentry sevm _ _ _ hR)
    (fun d hd => (hd.trans hnext).sstoreCost_congr sevm _ _)
    (by rw [hdeb]; rfl) (by omega) ?_
  intro D hD hlogs
  exact ⟨D, rfl, hD, hlogs⟩

end Blanc.Lift.Curve3Pool
