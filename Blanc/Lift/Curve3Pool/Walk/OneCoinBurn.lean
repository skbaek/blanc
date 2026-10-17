import Blanc.Lift.Curve3Pool.Walk.OneCoinPre
import Blanc.Lift.Curve3Pool.Walk.RemoveLiquidityPost

/-!
# `remove_liquidity_one_coin`, part 2: the `burnFrom` call

`xa_oc_burn` (`0x458e` → `0x45d1`): `CurveToken(lp_token).burnFrom(msg.sender, _token_amount)`,
a `CALL` with value `0`, input `0x31c[0 : 0x44]` and output window `0x3a0[0 : 0x20]`, whose
returned data must be at least a word. The memory leaves the views' word carrier for a byte
image here (the identity copies of the push need one), with `dy` at `0x140`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- A carried word read off a byte image of the memory. -/
theorem oc_wordAt {M : Mem} {img : Bytes} {o : Nat} {v : B256} (hR : Mem.Reads M img)
    (hw : memWord M o = v) : WordAt img o v := by
  unfold WordAt
  rw [← hw, memWord, Mem.Reads.read hR,
    Bytes.toBytes_toB256_of_length (List.length_sliceD _ _ _ _)]

/-- The `burnFrom` calldata the three writes leave at `0x31c`. -/
theorem oc_burn_input (img : Bytes) (C A : B256) :
    (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x300
      (Bytes.toB256 [0x79, 0xcc, 0x67, 0x90]).toBytes) 0x320 C.toBytes) 0x340 A.toBytes).sliceD
      0x31c 0x44 0 = burnFromSel ++ C.toBytes ++ A.toBytes := by
  have hsel : Region (Bytes.writeAt img 0x300 (Bytes.toB256 [0x79, 0xcc, 0x67, 0x90]).toBytes)
      0x31c burnFromSel := by
    have := Region.write_self img 0x300 (Bytes.toB256 [0x79, 0xcc, 0x67, 0x90]).toBytes
    rw [burn_sel_bytes] at this
    exact this.right
  refine Region.slice (Region.append' (o' := 0x340) (Region.append' (o' := 0x320) ?_ ?_ (by rfl))
    ?_ (by simp only [List.length_append, B256.length_toBytes]; rfl))
    (by simp only [List.length_append, B256.length_toBytes]; rfl)
  · refine Region.write_other (Region.write_other hsel ?_) ?_ <;>
      simp only [burnFromSel, B256.length_toBytes, List.length_cons, List.length_nil] <;> omega
  · exact Region.write_other (Region.write_self _ _ _) (by simp only [B256.length_toBytes]; omega)
  · exact Region.write_self _ _ _

/-- The `_token_amount` argument word. -/
abbrev ocAmt (sevm : Sevm) : B256 := Sevm.dataWord sevm (Bytes.toB256 [4])

/-- **The burn** (`0x458e` → `0x45d1`). -/
theorem xa_oc_burn {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {dy tw : B256} (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hV : VW M [(0x140, dy)])
    (htw : (b.getStor sevm.currentTarget).get tokenSlot = tw)
    (htok : ¬ sevm.benvStat.rules.isPrecomp tw.toAdr)
    (h : XAt sevm post 0x458e (St b [] M G) L) :
    ∃ c L' d M' img G', L = c :: L' ∧
      ChildOf b d tw.toAdr (burnFromSel ++ sevm.caller.toB256.toBytes ++ (ocAmt sevm).toBytes) 0
        sevm.isStatic c ∧ 32 ≤ c.post.output.length ∧ 0 < sevm.depth ∧
      Mem.Reads M' img ∧ Mem.Wf M' ∧ WordAt img 0x140 dy ∧
      XAt sevm post 0x45d1 (St d [] M' G') L' := by
  have hR := Mem.reads_data M
  have hW := hV.wf
  have hv : WordAt M.data.toList 0x140 dy :=
    oc_wordAt hR (hV.words.memWord List.mem_cons_self)
  clear hV
  xs 0x4590 (.push [0x20] (by decide)) ri_push
  xs 0x4593 (.push [0x03, 0xa0] (by decide)) ri_push
  xs 0x4595 (.push [0x44] (by decide)) ri_push
  xs 0x459a (.push [0x79, 0xcc, 0x67, 0x90] (by decide)) ri_push
  xs 0x459d (.push [0x03, 0x00] (by decide)) ri_push
  xmo 0x459e (.reg .mstore) (ri_mstore_imgAt (o := 0x300) rfl)
  xs 0x459f (.reg .caller) ri_caller
  xs 0x45a2 (.push [0x03, 0x20] (by decide)) ri_push
  xmo 0x45a3 (.reg .mstore) (ri_mstore_imgAt (o := 0x320) rfl)
  xs 0x45a5 (.push [0x04] (by decide)) ri_push
  xs 0x45a6 (.reg .calldataload) ri_calldataload
  xs 0x45a9 (.push [0x03, 0x40] (by decide)) ri_push
  xmo 0x45aa (.reg .mstore) (ri_mstore_imgAt (o := 0x340) rfl)
  xs 0x45ad (.push [0x03, 0x1c] (by decide)) ri_push
  xs 0x45af (.push [0x00] (by decide)) ri_push
  xs 0x45b1 (.push [0x05] (by decide)) ri_push
  xw 0x45b2 (.reg .sload) ri_sload
  rw [tokenSlot_lit, getStorVal_eq, htw] at h
  xs 0x45b3 (.reg .gas) ri_gas_remaining
  replace h := xa_call_img (pc' := 0x45b4) (i := 0x31c) (n := 0x44) (o := 0x3a0) (z := 0x20) hfork
    (atN hcode (by kernel_rfl)) rfl (by decide) (by decide) (by decide) (by decide) hR hW h
  clear hR hW
  obtain ⟨d, flag, L1, h, -, hrd, hk⟩ := h
  rw [oc_burn_input] at hk
  xs 0x45b7 (.push [0x45, 0xbc] (by decide)) ri_push
  xji 0x45b8 0x45bc hw
  · xdead
  obtain ⟨hR, hW, -, hch⟩ := hk hw
  clear hk hw
  rcases hch with ⟨hp, -⟩ | ⟨c, rfl, hdepth, -, hc⟩
  · exact absurd hp htok
  have hc' : ChildOf b d tw.toAdr (burnFromSel ++ sevm.caller.toB256.toBytes ++
      (ocAmt sevm).toBytes) 0 sevm.isStatic c := by
    rw [zero_lit] at hc
    exact hc.congr_left (fun _ => afterSload_getCode _ _ _ _) (fun _ => afterSload_getStor _ _ _ _)
      (afterSload_logs _ _ _) (afterSload_output _ _ _) (afterSload_accessedAddresses _ _ _)
  clear hc
  xjd 0x45bd
  xs 0x45bf (.push [0x1f] (by decide)) ri_push
  xs 0x45c0 (.reg .returndatasize) ri_returndatasize
  xs 0x45c1 (.reg .gt) ri_gt
  xs 0x45c4 (.push [0x45, 0xc9] (by decide)) ri_push
  xji 0x45c5 0x45c9 hw
  · xdead
  have hlen : 32 ≤ c.post.output.length := by
    have := gtCheck_ne_zero hw
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrd,
      show (Bytes.toB256 [0x1f]).toNat = 31 by decide] at this
    rw [hc'.output]; omega
  clear hw
  obtain ⟨img1, hR, hI⟩ := Mem.Reads.forget hR
  have f_v : WordAt img1 0x140 dy := by rw [hI]; wchain; exact hv
  clear hI hv
  xjd 0x45ca
  xs 0x45cc (.push [0x00] (by decide)) ri_push
  xs 0x45cd (.reg .pop) ri_pop
  xs 0x45d0 (.push [0x03, 0xa0] (by decide)) ri_push
  xs 0x45d1 (.reg .pop) ri_pop
  exact ⟨c, _, d, _, img1, _, rfl, hc', hlen, hdepth, hR, hW, f_v, h⟩

end Blanc.Lift.Curve3Pool
