import Blanc.Lift.HistIdentityCall
import Blanc.Lift.Curve3Pool.Walk.OneCoinPre
import Blanc.Lift.Curve3Pool.Walk.RemoveLiquidityPost
import Blanc.Lift.Curve3Pool.Walk.AutoStep

/-!
# `remove_liquidity_one_coin`, part 2: the `burnFrom` call

`xa_oc_burn` (`0x458e` → `0x45d1`): `CurveToken(lp_token).burnFrom(msg.sender, _token_amount)`,
a `CALL` with value `0`, input `0x31c[0 : 0x44]` and output window `0x3a0[0 : 0x20]`, whose
returned data must be at least a word. The memory leaves the views' word carrier for a byte
image here (the identity copies of the push need one), with `dy` at `0x140`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

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
    {dy tw : B256} (hcode : sevm.code = code) (hfork : HistFork sevm.benvStat.fork)
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
    WordAt.of_memWord hR (hV.words.memWord List.mem_cons_self)
  clear hV
  xa 5
  xmo 0x459e (.reg .mstore) (ri_mstore_imgAt (o := 0x300) rfl)
  xa 2
  xmo 0x45a3 (.reg .mstore) (ri_mstore_imgAt (o := 0x320) rfl)
  xa 3
  xmo 0x45aa (.reg .mstore) (ri_mstore_imgAt (o := 0x340) rfl)
  xa 3
  xw 0x45b2 (.reg .sload) ri_sloadF
  rw [tokenSlot_lit, getStorVal_eq, htw] at h
  xs 0x45b3 (.reg .gas) ri_gas_remaining
  replace h := xa_call_imgH (pc' := 0x45b4) (i := 0x31c) (n := 0x44) (o := 0x3a0) (z := 0x20) hfork.stateGas_none
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
    exact hc.congr_left (fun _ => afterSloadH_getCode _ _ _ _) (fun _ => afterSloadH_getStor _ _ _ _)
      (afterSloadH_logs _ _ _) (afterSloadH_output _ _ _) (afterSloadH_accessedAddresses _ _ _)
  clear hc
  xa 5
  xji 0x45c5 0x45c9 hw
  · xdead
  have hlen : 32 ≤ c.post.output.length := by
    have := B256.lt_of_gtCheck_ne_zero hw
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrd,
      show (Bytes.toB256 [0x1f]).toNat = 31 by decide] at this
    rw [hc'.output]; omega
  clear hw
  obtain ⟨img1, hR, hI⟩ := Mem.Reads.forget hR
  have f_v : WordAt img1 0x140 dy := by rw [hI]; wchain; exact hv
  clear hI hv
  xa 5
  exact ⟨c, _, d, _, img1, _, rfl, hc', hlen, hdepth, hR, hW, f_v, h⟩

end Blanc.Lift.Curve3Pool
