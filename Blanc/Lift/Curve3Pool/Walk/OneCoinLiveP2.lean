import Blanc.Lift.Curve3Pool.Walk.OneCoinLiveP1
import Blanc.Lift.Curve3Pool.Walk.ExchangeLivePush
import Blanc.Lift.Curve3Pool.Walk.OneCoinCalls

/-!
# `remove_liquidity_one_coin`, forward: the push, its `raw_call` test, the event, `STOP`

`rx_oc_p2` (`t_45c9_c0` → `STOP`): the `transfer(msg.sender, dy)` payload built with two
identity copies, `coins[i]`, the `CALL` answered by `CoinPushOkAt` (window `0x540`/`0x5e0`),
Vyper's `raw_call` test (`ocPushSite`), `RemoveLiquidityOne` and the lock cleared.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The `raw_call` site of the push: length word at `0x5c0`, copy buffer at `0x3c0`. -/
def ocPushSite : VyRawSite := ⟨0x05, 0xc0, 0x03, 0xc0, 0x46, 0x9d, 0x46, 0xae, 0x46, 0xb0, 0x46,
  0xd5, 0x47, 0x28, 0x46, 0xfe, 0x47, 0x0c, 0x47, 0x27⟩

theorem oc_push_join : cert.prog[21]? =
    some (vyRawCallJoin ocPushSite t_46d1_c21 t_46fa_c21 t_4708_c21 t_4723_c21 t_4728_c21) := by
  decide +kernel

theorem oc_push_tail : (SFunc.next (.push [0x46, 0x9d] (by decide)) (.branch t_4699_c0 t_469d_c0)) =
    vyRawCallTail ocPushSite 21 t_4699_c0 t_46d1_c21 t_46fa_c21 t_4708_c21 t_4723_c21
      t_4728_c21 := rfl

/-- The selector the push payload's first identity copy moves. -/
theorem oc_push_sel (img : Bytes) :
    ((Bytes.writeAt img 0x440 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]).toBytes).sliceD 0x440 4 0).take 4 =
      transferSel := by
  rw [(WordAt.write_self _ _ _).prefix (by decide)]; decide

/-- **The push to `STOP`, forward.** -/
theorem rx_oc_p2 {sevm : Sevm} {b : Devm} {σ : Stor} {G U : Nat} {Q : Outcome → Prop}
    {M : Mem} {img : Bytes} {W W' : Devm → Prop} {dy : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W')
    (hi3 : (ocI sevm).toNat < 3) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x920)
    (hdy : WordAt img 0x140 dy)
    (hpush : CoinPushOkAt sevm W W' (σ.get (coinsBase + ocI sevm)) dy U 0x540 0x5e0)
    (hG : 30000 + U ≤ G) (hGb : G + 2000 < 2 ^ 256)
    (k : ∀ D : Devm, ExLive sevm W' D (σ.set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])) →
      Q (.halted D)) :
    SFunc.RunEx cert.prog sevm (St b [] M G) t_45c9_c0 Q := by
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 584 := ⟨G - 584, by omega⟩
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x420) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x920 0x420 32 = 0x920 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x440) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x920 0x440 32 = 0x920 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_gas (by hr) ·)
  refine rxe_identity (i := 0x440) (n := 0x4) (o := 0x4a0) (z := 0x4) (ext := 0) (X := 118) hL.id hdepth hR hW hsz (by decide) (by decide) (by decide) (by decide) ⟨by decide, by decide, by decide, by decide⟩ rfl (by have : 100 + 0 + 64 * idCost 0x4 = 1252 := (by decide); omega) (by omega) (by hr) ?_; clear hR hW hsz M; intro bI M hsha hR hW hsz; rw [show memExtsSize 0x920 [(0x440, 0x4), (0x4a0, 0x4)] = 0x920 by decide] at hsz; replace hL := hL.sha hsha; clear hsha
  rw [oc_push_sel] at hR
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rxm_mload (o := 0x420) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_dup rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_swap2 ·)
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_caller (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_add (by hr) ·)
  refine rxe_mstore (o := 0x4a4) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x920 0x4a4 32 = 0x920 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x140) hR hsz rfl (by decide) (by hr) ·); try wsimp
  rw [hdy.read]
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_add (by hr) ·)
  refine rxe_mstore (o := 0x4c4) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x920 0x4c4 32 = 0x920 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x480) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x920 0x480 32 = 0x920 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rxm_mload (o := 0x480) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_gas (by hr) ·)
  refine rxe_identity (i := 0x480) (n := 0x64) (o := 0x520) (z := 0x64) (ext := 0) (X := 127) hL.id hdepth hR hW hsz (by decide) (by decide) (by decide) (by decide) ⟨by decide, by decide, by decide, by decide⟩ rfl (by have : 100 + 0 + 64 * idCost 0x64 = 1828 := (by decide); omega) (by omega) (by hr) ?_; clear hR hW hsz M; intro bI M hsha hR hW hsz; rw [show memExtsSize 0x920 [(0x480, 0x64), (0x520, 0x64)] = 0x920 by decide] at hsz; replace hL := hL.sha hsha; clear hsha
  rw [oc_transfer_copy2] at hR
  obtain ⟨img3, hR3, hI⟩ := Mem.Reads.forget hR
  clear hR
  have hR := hR3
  clear hR3
  have hdata : Region img3 0x520 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
      Bytes.toB256 [32]).toBytes ++ (transferSel ++ sevm.caller.toB256.toBytes ++ dy.toBytes)) := by
    rw [hI]; exact Region.write_self _ _ _
  have hdy3 : WordAt img3 0x140 dy := by rw [hI]; wautoH hdy
  clear hI
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by xbr) ·)
  -- tree t_4666_c0
  xr (rx_dest ·)
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x520) hR hsz rfl (by decide) (by hr) ·)
  rw [(Region.word hdata.left).read]
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ex_lt3_ne hi3) ·)
  -- tree t_4686_c0
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x920 0xc0 32 = 0x920 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by decide, by decide⟩ (by hr) (by decide) ·)
  rw [keccak_zero]
  xr (rx_add (by hr) ·)
  refine rxe_sloadV hfork (by hr) (by omega) ?_; intro g2 b2 v2 hb2 hv2 hg21 hg22; replace hv2 := hL.val hv2; replace hL := hL.sloadE hb2
  obtain ⟨g3, rfl⟩ : ∃ g, g2 = g + 2 := ⟨g2 - 2, by omega⟩
  xr (rx_gas (by hr) ·)
  rw [show Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] + Bytes.toB256 [32] =
      (0x44 : B256) by decide, show Bytes.toB256 [0] = (0 : B256) by decide,
    show Bytes.toB256 [5, 64] = (0x540 : B256) by decide,
    show Bytes.toB256 [5, 224] = (0x5e0 : B256) by decide,
    show Bytes.toB256 [32] = (0x20 : B256) by decide]
  subst hv2
  have hin : (M.read 0x540 0x44).1 = transferSel ++ sevm.caller.toB256.toBytes ++ dy.toBytes := by
    rw [hR.read, Bytes.sliceD_writeAt_after _ _ _ _ _ (by simp only [B256.length_toBytes]; omega)]
    exact Region.slice hdata.right (by simp only [List.length_append, B256.length_toBytes]; rfl)
  obtain ⟨d, hrun, hpost, hok, hrdlt, hgas, hgle, hstor, hWd, hidd⟩ :=
    hpush b2 [] M g3 hL.w (by omega) (by omega) hin
  xr (.next hrun ·)
  obtain ⟨hmem, -⟩ := hpost.settled (by decide)
  rw [show (0x540 : B256).toNat = 0x540 by decide, show (0x44 : B256).toNat = 0x44 by decide,
    show (0x5e0 : B256).toNat = 0x5e0 by decide, show (0x20 : B256).toNat = 0x20 by decide] at hmem
  have hd : d = St d [1] d.memory d.gasLeft := St.self hpost.stack rfl
  rw [hd, oc_push_tail]
  have hext : (M.extends [(0x540, 0x44), (0x5e0, 0x20)]).size = 0x920 := by
    show memExtsSize M.size _ = _
    rw [hsz]; decide
  have hsz5 : d.memory.size = 0x920 := by
    rw [hmem, Mem.size_write_of_le (by rw [hext, List.length_take]; omega), hext]
  have hR5 : Mem.Reads d.memory (Bytes.writeAt (Bytes.writeAt img3 192 (Bytes.toB256 [0]).toBytes)
      0x5e0 (d.returnData.take 0x20)) := by
    rw [hmem]; exact (hR.extends _).write (hW.extends _) _ _
  have hW5 : Mem.Wf d.memory := by rw [hmem]; exact (hW.extends _).write _ _
  have htc : rawTailCost (min d.returnData.length 32) ≤ 500 := by
    unfold rawTailCost rawJoinCost rawCheckCost idCost ceilDiv
    split_ifs <;> omega
  obtain ⟨G2, hG2⟩ : ∃ G2, d.gasLeft = G2 + rawTailCost (min d.returnData.length 32) :=
    ⟨d.gasLeft - rawTailCost (min d.returnData.length 32), by omega⟩
  rw [hG2]
  have hLd : ExLive sevm W' d σ :=
    ⟨fun x => by rw [hstor]; exact hL.stor x, hidd hL.id, hW'c, hWd⟩
  refine SFunc.runEx_iff_runExCut_nil.mpr (rxce_vyRawCallTail hLd.id
    hdepth (by decide) oc_push_join (by simp only [List.not_mem_nil, not_false_eq_true]) hrdlt hok
    ?_ (by rw [hsz5]) (by rw [hsz5]; decide) (by rw [hsz5]; decide) (by omega) (by omega) (by hr)
    ?_)
  · rw [show (Bytes.toB256 [ocPushSite.lh, ocPushSite.ll]).toNat + 32 = 0x5e0 by decide]
    intro j hj
    exact (rawCall_window hmem rfl j hj).2
  intro b' rd' hsha
  refine SFunc.runEx_iff_runExCut_nil.mp ?_
  rw [show (Bytes.toB256 [ocPushSite.lh, ocPushSite.ll]).toNat = 0x5c0 by decide,
    show (Bytes.toB256 [ocPushSite.bh, ocPushSite.bl]).toNat = 0x3c0 by decide]
  have hn32 : min d.returnData.length 32 ≤ 32 := by omega
  have hR6 : Mem.Reads (vyRawMem d.memory 0x5c0 0x3c0 (min d.returnData.length 32))
      (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img3 192 (Bytes.toB256 [0]).toBytes)
        0x5e0 (d.returnData.take 0x20)) 0x5c0
        (Nat.toB256 (min d.returnData.length 32)).toBytes) 0x3c0 ((Bytes.writeAt (Bytes.writeAt
        (Bytes.writeAt img3 192 (Bytes.toB256 [0]).toBytes) 0x5e0 (d.returnData.take 0x20)) 0x5c0
        (Nat.toB256 (min d.returnData.length 32)).toBytes).sliceD 0x5c0
        (min d.returnData.length 32 + 32) 0)) := by
    unfold vyRawMem
    rw [(hR5.write hW5 _ _).read]
    exact (hR5.write hW5 _ _).write (hW5.write _ _) _ _
  have hW6 : Mem.Wf (vyRawMem d.memory 0x5c0 0x3c0 (min d.returnData.length 32)) := by
    unfold vyRawMem; exact (hW5.write _ _).write _ _
  have hsz6 : (vyRawMem d.memory 0x5c0 0x3c0 (min d.returnData.length 32)).size = 0x920 := by
    unfold vyRawMem
    have h1 : (d.memory.write 0x5c0 (Nat.toB256 (min d.returnData.length 32)).toBytes).size =
        0x920 := by
      rw [Mem.size_write_of_le (by rw [B256.length_toBytes, hsz5]; decide), hsz5]
    rw [(hR5.write hW5 _ _).read, Mem.size_write_of_le (by rw [h1, List.length_sliceD]; omega), h1]
  obtain ⟨img6, hR, hI⟩ := Mem.Reads.forget hR6
  have hdy6 : WordAt img6 0x140 dy := by
    rw [hI]
    refine WordAt.write_other ?_ (by simp only [List.length_sliceD]; omega)
    wautoH hdy3
  clear hI hR6
  have hW := hW6
  have hsz := hsz6
  replace hL := hLd.sha hsha
  clear hW6 hsz6 hR5 hW5 hmem
  obtain ⟨g8, rfl⟩ : ∃ g, G2 = g + 1679 := ⟨G2 - 1679, by omega⟩
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x620) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro M hR hW hsz; rw [show memExtSize 0x920 0x620 32 = 0x920 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x140) hR hsz rfl (by decide) (by hr) ·); try wsimp
  rw [hdy6.read]
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0x640) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro M hR hW hsz; rw [show memExtSize 0x920 0x640 32 = 0x920 by decide] at hsz
  xr (rx_caller (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_log2 (c := 1637) hstatic (by rw [St.extCost_eq hsz]; decide) rfl (read_covered_len hsz (by decide) (by decide)) ·); 
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_sstoreV hfork hstatic (by omega) ?_; intro g2 b2 hb2 hg21 hg22; replace hL := (hL.addLogE _).sstoreE hb2
  exact ⟨_, .last rfl, k _ (hL.st _ _ _)⟩

end Blanc.Lift.Curve3Pool
