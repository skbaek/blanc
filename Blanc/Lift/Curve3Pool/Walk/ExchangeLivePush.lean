import Blanc.Lift.Curve3Pool.Walk.ExchangeLiveStore

/-!
# `exchange`, forward: the `transfer` push, its `raw_call` test, the event, the lock, `STOP`

`rx_ex_push` is the forward twin of `xa_ex_push`'s call, `xa_ex_tail2` and `xa_ex_log`
(`t_2b49_c1174` → `STOP`): `coins[j]`, the `CALL` answered by `CoinPushOkAt` (input
`0xb60[0 : 0x44]`, output `0xc00[0 : 0x20]`), Vyper's `raw_call` success test,
`TokenExchange`, and the lock cleared.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The `raw_call` site of the push: length word at `0xbe0`, copy buffer at `0x460`. -/
def exPushSite : VyRawSite := ⟨0x0b, 0xe0, 0x04, 0x60, 0x2b, 0x80, 0x2b, 0x91, 0x2b, 0x93, 0x2b,
  0xb8, 0x2c, 0x0b, 0x2b, 0xe1, 0x2b, 0xef, 0x2c, 0x0a⟩

theorem ex_push_join : cert.prog[14]? =
    some (vyRawCallJoin exPushSite t_2bb4_c14 t_2bdd_c14 t_2beb_c14 t_2c06_c14 t_2c0b_c14) := rfl

theorem ex_push_tail : (SFunc.next (.push [0x2b, 0x80] (by decide)) (.branch t_2b7c_c1174 t_2b80_c1174)) =
    vyRawCallTail exPushSite 14 t_2b7c_c1174 t_2bb4_c14 t_2bdd_c14 t_2beb_c14 t_2c06_c14
      t_2c0b_c14 := rfl

/-- **The push to `STOP`, forward.** -/
theorem rx_ex_push {sevm : Sevm} {b : Devm} {σ : Stor} {G U : Nat} {Q : Outcome → Prop}
    {M : Mem} {img : Bytes} {W W' : Devm → Prop} {dyOut : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W')
    (hj : (exJ sevm).toNat < 3) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xbc0)
    (hdata : Region img 0xb40 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
      Bytes.toB256 [32]).toBytes ++ exPushData sevm dyOut))
    (hout : WordAt img 0x920 dyOut)
    (hpush : CoinPushOkAt sevm W W' (σ.get (coinsBase + exJ sevm)) dyOut U 0xb60 0xc00)
    (hG : 30000 + U ≤ G) (hGb : G + 2000 < 2 ^ 256)
    (k : ∀ D : Devm, ExLive sevm W' D (σ.set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])) →
      Q (.halted D)) :
    SFunc.RunEx cert.prog sevm (St b [Bytes.toB256 [32] + (Bytes.toB256 [0] + Bytes.toB256 [4] +
      Bytes.toB256 [32] + Bytes.toB256 [32]), Bytes.toB256 [10, 160]] M G) t_2b49_c1174 Q := by
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 106 := ⟨G - 106, by omega⟩
  xr (rx_dest ·)
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0xb40) hR hsz rfl (by decide) (by hr) ·)
  rw [(Region.word hdata.left).read]
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ex_lt3_ne hj) ·)
  -- tree t_2b69_c1174
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xbc0 0xc0 32 = 0xbc0 by decide] at hsz
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
    show Bytes.toB256 [11, 96] = (0xb60 : B256) by decide,
    show Bytes.toB256 [12, 0] = (0xc00 : B256) by decide,
    show Bytes.toB256 [32] = (0x20 : B256) by decide]
  subst hv2
  have hin : (M.read 0xb60 0x44).1 = transferSel ++ sevm.caller.toB256.toBytes ++
      dyOut.toBytes := by
    rw [hR.read, Bytes.sliceD_writeAt_after _ _ _ _ _ (by simp only [B256.length_toBytes]; omega)]
    exact Region.slice hdata.right (by simp only [List.length_append, B256.length_toBytes]; rfl)
  obtain ⟨d, hrun, hpost, hok, hrdlt, hgas, hgle, hstor, hWd, hidd⟩ :=
    hpush b2 [] M g3 hL.w (by omega) (by omega) hin (by hrs)
  xr (.next hrun ·)
  obtain ⟨hmem, -⟩ := hpost.settled (by decide)
  rw [show (0xb60 : B256).toNat = 0xb60 by decide, show (0x44 : B256).toNat = 0x44 by decide,
    show (0xc00 : B256).toNat = 0xc00 by decide, show (0x20 : B256).toNat = 0x20 by decide] at hmem
  have hd : d = St d [1] d.memory d.gasLeft := St.self hpost.stack rfl
  rw [hd, ex_push_tail]
  have hext : (M.extends [(0xb60, 0x44), (0xc00, 0x20)]).size = 0xc20 := by
    show memExtsSize M.size _ = _
    rw [hsz]; decide
  have hsz5 : d.memory.size = 0xc20 := by
    rw [hmem, Mem.size_write_of_le (by rw [hext, List.length_take]; omega), hext]
  have hR5 : Mem.Reads d.memory (Bytes.writeAt (Bytes.writeAt img 192 (Bytes.toB256 [0]).toBytes)
      0xc00 (d.returnData.take 0x20)) := by
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
    hdepth (by decide) ex_push_join (by simp only [List.not_mem_nil, not_false_eq_true]) hrdlt hok
    ?_ (by rw [hsz5]) (by rw [hsz5]; decide) (by rw [hsz5]; decide) (by omega) (by omega) (by hr)
    ?_)
  · rw [show (Bytes.toB256 [exPushSite.lh, exPushSite.ll]).toNat + 32 = 0xc00 by decide]
    intro j hj
    exact (rawCall_window hmem rfl j hj).2
  intro b' rd' hsha
  refine SFunc.runEx_iff_runExCut_nil.mp ?_
  rw [show (Bytes.toB256 [exPushSite.lh, exPushSite.ll]).toNat = 0xbe0 by decide,
    show (Bytes.toB256 [exPushSite.bh, exPushSite.bl]).toNat = 0x460 by decide]
  have hn32 : min d.returnData.length 32 ≤ 32 := by omega
  have hR6 : Mem.Reads (vyRawMem d.memory 0xbe0 0x460 (min d.returnData.length 32))
      (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 192 (Bytes.toB256 [0]).toBytes)
        0xc00 (d.returnData.take 0x20)) 0xbe0
        (Nat.toB256 (min d.returnData.length 32)).toBytes) 0x460 ((Bytes.writeAt (Bytes.writeAt
        (Bytes.writeAt img 192 (Bytes.toB256 [0]).toBytes) 0xc00 (d.returnData.take 0x20)) 0xbe0
        (Nat.toB256 (min d.returnData.length 32)).toBytes).sliceD 0xbe0
        (min d.returnData.length 32 + 32) 0)) := by
    unfold vyRawMem
    rw [(hR5.write hW5 _ _).read]
    exact (hR5.write hW5 _ _).write (hW5.write _ _) _ _
  have hW6 : Mem.Wf (vyRawMem d.memory 0xbe0 0x460 (min d.returnData.length 32)) := by
    unfold vyRawMem; exact (hW5.write _ _).write _ _
  have hsz6 : (vyRawMem d.memory 0xbe0 0x460 (min d.returnData.length 32)).size = 0xc20 := by
    unfold vyRawMem
    have h1 : (d.memory.write 0xbe0 (Nat.toB256 (min d.returnData.length 32)).toBytes).size =
        0xc20 := by
      rw [Mem.size_write_of_le (by rw [B256.length_toBytes, hsz5]; decide), hsz5]
    rw [(hR5.write hW5 _ _).read, Mem.size_write_of_le (by rw [h1, List.length_sliceD]; omega), h1]
  obtain ⟨img6, hR, hI⟩ := Mem.Reads.forget hR6
  have hout6 : WordAt img6 0x920 dyOut := by rw [hI]; wautoH hout
  clear hI hR6
  have hW := hW6
  have hsz := hsz6
  replace hL := hLd.sha hsha
  clear hW6 hsz6 hR5 hW5 hmem
  obtain ⟨g8, rfl⟩ : ∃ g, G2 = g + 2232 := ⟨G2 - 2232, by omega⟩
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0xc40) (c := 10) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro M hR hW hsz; rw [show memExtSize 0xc20 0xc40 32 = 0xc60 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0xc60) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro M hR hW hsz; rw [show memExtSize 0xc60 0xc60 32 = 0xc80 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0xc80) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro M hR hW hsz; rw [show memExtSize 0xc80 0xc80 32 = 0xca0 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x920) hR hsz rfl (by decide) (by hr) ·)
  wsimp
  rw [hout6.read]
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstore (o := 0xca0) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro M hR hW hsz; rw [show memExtSize 0xca0 0xca0 32 = 0xcc0 by decide] at hsz
  xr (rx_caller (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_log2 (c := 2149) hstatic (by rw [St.extCost_eq hsz]; decide) rfl (read_covered_len hsz (by decide) (by decide)) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_sstoreV hfork hstatic (by omega) ?_; intro g9 b9 hb9 hg91 hg92; replace hL := (hL.addLogE _).sstoreE hb9
  exact ⟨_, .last rfl, k _ (hL.st _ _ _)⟩

end Blanc.Lift.Curve3Pool
