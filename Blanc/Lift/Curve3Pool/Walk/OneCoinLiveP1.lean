import Blanc.Lift.Curve3Pool.Callee.CalcWithdrawLive
import Blanc.Lift.Curve3Pool.Walk.OneCoinRaw

/-!
# `remove_liquidity_one_coin`, forward: the balance store and the burn

`rx_oc_p1` (`t_4491_c0` → `t_45c9_c0`): `(dy, dy_fee)` stored, `dy ≥ min_amount`, `i < 3`,
`balances[i] -= dy + dy_fee · admin_fee / FEE_DENOMINATOR` (checked) stored, and
`token.burnFrom(msg.sender, _token_amount)` answered by `BurnOkAt` (window `0x31c`/`0x3a0`) with
its reply length checked.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- `remove_liquidity_one_coin`'s `i` argument word. -/
abbrev ocI (sevm : Sevm) : B256 := Sevm.dataWord sevm (Bytes.toB256 [0x24])

/-- `remove_liquidity_one_coin`'s `min_amount` argument word. -/
abbrev ocMin (sevm : Sevm) : B256 := Sevm.dataWord sevm (Bytes.toB256 [0x44])

/-- The burn's base: `balances[i]` and `admin_fee` read, `balances[i]` stored, the token slot
read. -/
def ocBurnBase (sevm : Sevm) (b : Devm) (σ : Stor) (dy fee : B256) : Devm :=
  afterSload sevm (afterSstore sevm (afterSload sevm (afterSload sevm b
    (balancesBase + Sevm.dataWord sevm (Bytes.toB256 [36]))) (Bytes.toB256 [3]))
    (balancesBase + Sevm.dataWord sevm (Bytes.toB256 [36]))
    (σ.get (balancesBase + Sevm.dataWord sevm (Bytes.toB256 [36])) -
      (dy + fee * σ.get adminFeeSlot / Bytes.toB256 [2, 84, 11, 228, 0]))) (Bytes.toB256 [5])

/-- `rx_oc_p1`'s charge before the burn: `494` for its instructions, the two reads, the store and
the token slot read, each at its actual world. -/
def ocP1Cost (sevm : Sevm) (b : Devm) (σ : Stor) (dy fee : B256) : Nat :=
  494 + sloadCost sevm b (balancesBase + Sevm.dataWord sevm (Bytes.toB256 [36])) +
    sloadCost sevm (afterSload sevm b (balancesBase + Sevm.dataWord sevm (Bytes.toB256 [36])))
      (Bytes.toB256 [3]) +
    sstoreCost sevm (afterSload sevm (afterSload sevm b
      (balancesBase + Sevm.dataWord sevm (Bytes.toB256 [36]))) (Bytes.toB256 [3]))
      (balancesBase + Sevm.dataWord sevm (Bytes.toB256 [36]))
      (σ.get (balancesBase + Sevm.dataWord sevm (Bytes.toB256 [36])) -
        (dy + fee * σ.get adminFeeSlot / Bytes.toB256 [2, 84, 11, 228, 0])) +
    sloadCost sevm (afterSstore sevm (afterSload sevm (afterSload sevm b
      (balancesBase + Sevm.dataWord sevm (Bytes.toB256 [36]))) (Bytes.toB256 [3]))
      (balancesBase + Sevm.dataWord sevm (Bytes.toB256 [36]))
      (σ.get (balancesBase + Sevm.dataWord sevm (Bytes.toB256 [36])) -
        (dy + fee * σ.get adminFeeSlot / Bytes.toB256 [2, 84, 11, 228, 0]))) (Bytes.toB256 [5])

/-- The burn's memory: `(dy, dy_fee)` stored, the slippage error buffer, the mapping key at
`0xc0`, the `burnFrom(msg.sender, _token_amount)` payload at `0x300 … 0x340`. -/
def ocP1Mem (sevm : Sevm) (M : Mem) (dy fee w1 w2 : B256) : Mem :=
  (((((((((((((M.write 0x220 dy.toBytes).write 0x240 fee.toBytes).write 0x160 w1.toBytes).write 0x140 w2.toBytes).write 0x140 dy.toBytes).write 0x160 fee.toBytes).write 0x260 (Bytes.toB256 [8, 195, 121, 160]).toBytes).write 0x280 (Bytes.toB256 [32]).toBytes).write 0x2a0 (Bytes.toB256 [24]).toBytes).write 0x2c0 (Bytes.toB256 [78, 111, 116, 32, 101, 110, 111, 117, 103, 104, 32, 99, 111, 105, 110, 115, 32, 114, 101, 109, 111, 118, 101, 100, 0, 0, 0, 0, 0, 0, 0, 0]).toBytes).write 0xc0 (Bytes.toB256 [1]).toBytes).write 0x300 (Bytes.toB256 [121, 204, 103, 144]).toBytes).write 0x320 sevm.caller.toB256.toBytes).write 0x340 (Sevm.dataWord sevm (Bytes.toB256 [4])).toBytes

/-- **The balance store and the burn, forward, exactly** (core). -/
theorem rx_oc_p1E {sevm : Sevm} {b : Devm} {σ : Stor} {M : Mem} {img : Bytes} {G R U : Nat}
    {Q : Outcome → Prop} {W W' : Devm → Prop} {dy fee w1 w2 : B256}
    {E : Devm → List B256 → Mem → Nat → Devm → Prop}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W')
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x920)
    (hi3 : (ocI sevm).toNat < 3) (hmin : ¬ dy < ocMin sevm)
    (hma : B256.Nofm fee (σ.get adminFeeSlot))
    (hadd : ¬ dy + fee * σ.get adminFeeSlot / ocDen < dy)
    (hsub : ¬ σ.get (balancesBase + ocI sevm) < dy + fee * σ.get adminFeeSlot / ocDen)
    (hburn : MutCallOkAtE sevm W W' (σ.get tokenSlot)
      (burnFromSel ++ sevm.caller.toB256.toBytes ++ (ocAmt sevm).toBytes) (fun r => 32 ≤ r.length) U
      0x31c 0x44 0x3a0 E)
    (hG : 31000 + U + R ≤ G) (hGb : G < 2 ^ 256)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W' b' (σ.set (balancesBase + ocI sevm) (ocBal σ (ocI sevm) dy fee)) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x920 → WordAt img' 0x140 dy → R ≤ g → g ≤ G →
      ∀ (Gs : Nat) (d : Devm), E (ocBurnBase sevm b σ dy fee) [] (ocP1Mem sevm M dy fee w1 w2) Gs d →
      G = Gs + ocP1Cost sevm b σ dy fee → d.gasLeft = g + 35 → b' = d → M' = d.memory →
      SFunc.RunEx cert.prog sevm (St b' [] M' g) t_45c9_c0 Q) :
    SFunc.RunEx cert.prog sevm (St b [dy, fee, w1, w2] M G) t_4491_c0 Q := by
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 219 := ⟨G - 219, by omega⟩
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x220) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mp1; intro M hMp1 hR hW hsz; rw [show memExtSize 0x920 0x220 32 = 0x920 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x240) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mp2; intro M hMp2 hR hW hsz; rw [show memExtSize 0x920 0x240 32 = 0x920 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x160) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mp3; intro M hMp3 hR hW hsz; rw [show memExtSize 0x920 0x160 32 = 0x920 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x140) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mp4; intro M hMp4 hR hW hsz; rw [show memExtSize 0x920 0x140 32 = 0x920 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mload (o := 0x220) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x140) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mp5; intro M hMp5 hR hW hsz; rw [show memExtSize 0x920 0x140 32 = 0x920 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mload (o := 0x240) hR hsz (cw_off (by decide) (by decide)) (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x160) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mp6; intro M hMp6 hR hW hsz; rw [show memExtSize 0x920 0x160 32 = 0x920 by decide] at hsz
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x260) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mp7; intro M hMp7 hR hW hsz; rw [show memExtSize 0x920 0x260 32 = 0x920 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x280) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mp8; intro M hMp8 hR hW hsz; rw [show memExtSize 0x920 0x280 32 = 0x920 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x2a0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mp9; intro M hMp9 hR hW hsz; rw [show memExtSize 0x920 0x2a0 32 = 0x920 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x2c0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mp10; intro M hMp10 hR hW hsz; rw [show memExtSize 0x920 0x2c0 32 = 0x920 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_calldataload (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x140) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_geGuard hmin) ·)
  -- tree t_4506_c0
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_calldataload (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_lt3_ne hi3) ·)
  -- tree t_4516_c0
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mp11; intro M hMp11 hR hW hsz; rw [show memExtSize 0x920 0xc0 32 = 0x920 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by decide, by decide⟩ (by hrs) (by decide) ·)
  rw [keccak_one]
  xr (rx_add (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_sloadVX hfork (by hrs) (by omega) ?_; intro g2 b2 v2 hb2 hv2 hg21 hg22 g2x; replace hv2 := hL.val hv2; replace hL := hL.sloadE hb2
  subst hv2
  obtain ⟨g3, rfl⟩ : ∃ g, g2 = g + 15 := ⟨g2 - 15, by omega⟩
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x140) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x160) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  refine rxe_sloadVX hfork (by hrs) (by omega) ?_; intro g4 b4 v4 hb4 hv4 hg41 hg42 g4x; replace hv4 := hL.val hv4; replace hL := hL.sloadE hb4
  rw [show Bytes.toB256 [3] = adminFeeSlot by decide] at hv4; subst hv4
  obtain ⟨g5, rfl⟩ : ∃ g, g4 = g + 209 := ⟨g4 - 209, by omega⟩
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_div rfl (by hrs) ·)
  xr (rx_eq rfl (by hrs) ·)
  xr (rx_or rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (B256.mulGuard_of_nofm hma) ·)
  -- tree t_4542_c0
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by decide) ·)
  -- tree t_455a_c0
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_div rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_geGuard hadd) ·)
  -- tree t_456f_c0
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_geGuard hsub) ·)
  -- tree t_4583_c0
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_sub (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_sstoreVX hfork hstatic (by omega) ?_; intro g6 b6 hb6 hg61 hg62 g6x; replace hL := hL.sstoreE hb6
  obtain ⟨g7, rfl⟩ : ∃ g, g6 = g + 49 := ⟨g6 - 49, by omega⟩
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x300) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mp12; intro M hMp12 hR hW hsz; rw [show memExtSize 0x920 0x300 32 = 0x920 by decide] at hsz
  xr (rx_caller (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x320) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mp13; intro M hMp13 hR hW hsz; rw [show memExtSize 0x920 0x320 32 = 0x920 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_calldataload (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x340) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mp14; intro M hMp14 hR hW hsz; rw [show memExtSize 0x920 0x340 32 = 0x920 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_sloadVX hfork (by hrs) (by omega) ?_; intro g8 b8 v8 hb8 hv8 hg81 hg82 g8x; replace hv8 := hL.val hv8; replace hL := hL.sloadE hb8
  obtain ⟨g9, rfl⟩ : ∃ g, g8 = g + 2 := ⟨g8 - 2, by omega⟩
  xr (rx_gas (by hrs) ·)
  rw [show Bytes.toB256 [0] = (0 : B256) by decide,
    show Bytes.toB256 [0x03, 0x1c] = (0x31c : B256) by decide,
    show Bytes.toB256 [0x44] = (0x44 : B256) by decide,
    show Bytes.toB256 [0x03, 0xa0] = (0x3a0 : B256) by decide,
    show Bytes.toB256 [0x20] = (0x20 : B256) by decide]
  have htok : v8 = σ.get tokenSlot := by
    rw [hv8, show Bytes.toB256 [5] = tokenSlot by decide]
    refine Stor.get_set_ne _ ?_ _
    rw [show balancesBase + Sevm.dataWord sevm (Bytes.toB256 [36]) =
      balancesBase + Nat.toB256 (ocI sevm).toNat by rw [toB256_toNat]]
    exact bal_ne_token hi3
  subst htok
  clear hv8
  have hin : (M.read (0x31c : B256).toNat (0x44 : B256).toNat).1 =
      burnFromSel ++ sevm.caller.toB256.toBytes ++ (ocAmt sevm).toBytes := by
    rw [hR.read, show (0x31c : B256).toNat = 0x31c by decide, show (0x44 : B256).toNat = 0x44 by decide]
    exact oc_burn_input _ _ _
  obtain ⟨d, hrun, hpost, hok, hrdlt, hgas, hgle, hstor, hWd, hidd, hE⟩ :=
    hburn b8 [] M g9 hL.w (by omega) (by omega) hin (by hrs)
  xr (.next hrun ·)
  obtain ⟨hmem, -⟩ := hpost.settled (by decide)
  rw [show (0x31c : B256).toNat = 0x31c by decide, show (0x44 : B256).toNat = 0x44 by decide,
    show (0x3a0 : B256).toNat = 0x3a0 by decide, show (0x20 : B256).toNat = 0x20 by decide] at hmem
  have hd : d = St d [1] d.memory d.gasLeft := St.self hpost.stack rfl
  rw [hd]
  have hext : (M.extends [(0x31c, 0x44), (0x3a0, 0x20)]).size = 0x920 := by
    show memExtsSize M.size _ = _
    rw [hsz]; decide
  have hsz5 : d.memory.size = 0x920 := by
    rw [hmem, Mem.size_write_of_le (by rw [hext, List.length_take]; omega), hext]
  have hR5 := (hR.extends [(0x31c, 0x44), (0x3a0, 0x20)]).write (hW.extends _) 0x3a0
    (d.returnData.take 0x20)
  rw [← hmem] at hR5
  have hW5 : Mem.Wf d.memory := by rw [hmem]; exact (hW.extends _).write _ _
  have hLd : ExLive sevm W' d (σ.set (balancesBase + ocI sevm) (ocBal σ (ocI sevm) dy fee)) :=
    ⟨fun x => by rw [hstor]; exact hL.stor x, hidd hL.id, hW'c, hWd⟩
  clear hR hW hsz hext hmem hrun hpost hin
  have hR := hR5; have hW := hW5; have hsz := hsz5
  clear hR5 hW5 hsz5
  obtain ⟨g10, hg10⟩ : ∃ g, d.gasLeft = g + 35 := ⟨d.gasLeft - 35, by omega⟩
  rw [hg10]
  have hgt : B256.gtCheck (Nat.toB256 d.returnData.length) (Bytes.toB256 [0x1f]) ≠ 0 := by
    apply gtCheck_ne_zero_of_lt
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrdlt,
      show (Bytes.toB256 [0x1f]).toNat = 31 by decide]
    omega
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by decide) ·)
  -- tree t_45bc_c0
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_returndatasize (by hrs) ·)
  xr (rx_gt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ hgt ·)
  have hMc : M = ocP1Mem sevm Mp1 dy fee w1 w2 := by
    rw [hMp14, hMp13, hMp12, hMp11, hMp10, hMp9, hMp8, hMp7, hMp6, hMp5, hMp4, hMp3, hMp2, hMp1]
    rfl
  rw [hMc, hb8, hb6, hb4, hb2] at hE
  exact k d d.memory _ g10 hLd hR hW hsz (by wauto) (by omega) (by omega) g9 d hE
    (by unfold ocP1Cost; rw [← hb2, ← hb4, ← hb6]; omega) hg10 rfl rfl


/-- **The balance store and the burn, forward.** -/
theorem rx_oc_p1 {sevm : Sevm} {b : Devm} {σ : Stor} {M : Mem} {img : Bytes} {G R U : Nat}
    {Q : Outcome → Prop} {W W' : Devm → Prop} {dy fee w1 w2 : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W')
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x920)
    (hi3 : (ocI sevm).toNat < 3) (hmin : ¬ dy < ocMin sevm)
    (hma : B256.Nofm fee (σ.get adminFeeSlot))
    (hadd : ¬ dy + fee * σ.get adminFeeSlot / ocDen < dy)
    (hsub : ¬ σ.get (balancesBase + ocI sevm) < dy + fee * σ.get adminFeeSlot / ocDen)
    (hburn : BurnOkAt sevm W W' (σ.get tokenSlot) (ocAmt sevm) U 0x31c 0x3a0)
    (hG : 31000 + U + R ≤ G) (hGb : G < 2 ^ 256)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W' b' (σ.set (balancesBase + ocI sevm) (ocBal σ (ocI sevm) dy fee)) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x920 → WordAt img' 0x140 dy → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' [] M' g) t_45c9_c0 Q) :
    SFunc.RunEx cert.prog sevm (St b [dy, fee, w1, w2] M G) t_4491_c0 Q :=
  rx_oc_p1E hfork hstatic hL hW'c hR hW hsz hi3 hmin hma hadd hsub hburn.withE hG hGb
    fun b' M' img' g h1 h2 h3 h4 h5 h6 h7 _ _ _ _ _ _ _ => k b' M' img' g h1 h2 h3 h4 h5 h6 h7

end Blanc.Lift.Curve3Pool
