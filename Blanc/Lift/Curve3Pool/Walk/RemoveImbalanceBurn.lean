import Blanc.Lift.Curve3Pool.Walk.RemoveImbalancePush
import Blanc.Lift.Curve3Pool.Walk.OneCoinBurn

/-!
# `remove_liquidity_imbalance`, part 7: the `burnFrom` call

`xa_rli_burn` (`0x3719` → the transfer loop's head `0x3769`):
`CurveToken(lp_token).burnFrom(msg.sender, token_amount)`, a `CALL` with value `0`, input
`0x85c[0 : 0x44]` and output window `0x8e0[0 : 0x20]`, whose returned data must be at least a
word; then the loop counter at `0x900` set to `0`. The memory leaves the word carrier for a byte
image here (the transfers' identity copies need one); `RliImg` is what the rest of the frame
reads from it.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The words the frame's tail reads: the burn amount, `D1`, the supply and the three fees. -/
structure RliImg (img : Bytes) (X D1 T f0 f1 f2 : B256) : Prop where
  x : WordAt img 0x780 X
  d1 : WordAt img 0x480 D1
  t : WordAt img 0x140 T
  f0 : WordAt img 0x5a0 f0
  f1 : WordAt img 0x5c0 f1
  f2 : WordAt img 0x5e0 f2

/-- The words survive any change that keeps every word in `[0x140, 0x7a0)`. -/
theorem RliImg.keep {img img' : Bytes} {X D1 T f0 f1 f2 : B256} (h : RliImg img X D1 T f0 f1 f2)
    (hk : ∀ o w, WordAt img o w → 0x140 ≤ o → o + 32 ≤ 0x7a0 → WordAt img' o w) :
    RliImg img' X D1 T f0 f1 f2 :=
  ⟨hk _ _ h.x (by decide) (by decide), hk _ _ h.d1 (by decide) (by decide),
    hk _ _ h.t (by decide) (by decide), hk _ _ h.f0 (by decide) (by decide),
    hk _ _ h.f1 (by decide) (by decide), hk _ _ h.f2 (by decide) (by decide)⟩

/-- The `burnFrom` calldata the three writes leave at `0x85c`. -/
theorem rli_burn_input (img : Bytes) (C A : B256) :
    (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x840
      (Bytes.toB256 [0x79, 0xcc, 0x67, 0x90]).toBytes) 0x860 C.toBytes) 0x880 A.toBytes).sliceD
      0x85c 0x44 0 = burnFromSel ++ C.toBytes ++ A.toBytes := by
  have hsel : Region (Bytes.writeAt img 0x840 (Bytes.toB256 [0x79, 0xcc, 0x67, 0x90]).toBytes)
      0x85c burnFromSel := by
    have := Region.write_self img 0x840 (Bytes.toB256 [0x79, 0xcc, 0x67, 0x90]).toBytes
    rw [burn_sel_bytes] at this
    exact this.right
  refine Region.slice (Region.append' (o' := 0x880) (Region.append' (o' := 0x860) ?_ ?_ (by rfl))
    ?_ (by simp only [List.length_append, B256.length_toBytes]; rfl))
    (by simp only [List.length_append, B256.length_toBytes]; rfl)
  · refine Region.write_other (Region.write_other hsel ?_) ?_ <;>
      simp only [burnFromSel, B256.length_toBytes, List.length_cons, List.length_nil] <;> omega
  · exact Region.write_other (Region.write_self _ _ _) (by simp only [B256.length_toBytes]; omega)
  · exact Region.write_self _ _ _

/-- **The burn** (`0x3719` → `0x3769`). -/
theorem xa_rli_burn {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {X D1 T f0 f1 f2 tw : B256} (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hV : VW M [(0x780, X), (0x480, D1), (0x140, T), (0x5a0, f0), (0x5c0, f1), (0x5e0, f2)])
    (htw : (b.getStor sevm.currentTarget).get tokenSlot = tw)
    (htok : ¬ sevm.benvStat.rules.isPrecomp tw.toAdr)
    (h : XAt sevm post 0x3719 (St b [] M G) L) :
    ∃ c L' d M' img G', L = c :: L' ∧
      ChildOf b d tw.toAdr (burnFromSel ++ sevm.caller.toB256.toBytes ++ X.toBytes) 0
        sevm.isStatic c ∧ 32 ≤ c.post.output.length ∧ 0 < sevm.depth ∧
      Mem.Reads M' img ∧ Mem.Wf M' ∧ RliImg img X D1 T f0 f1 f2 ∧
      WordAt img 0x900 (Nat.toB256 0) ∧
      XAt sevm post 0x3769 (St d [Bytes.toB256 [3], Bytes.toB256 [9, 0]] M' G') L' := by
  have hR := Mem.reads_data M
  have hW := hV.wf
  have hI : RliImg M.data.toList X D1 T f0 f1 f2 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> refine oc_wordAt hR (hV.words.memWord ?_) <;>
      simp only [List.mem_cons, true_or, or_true]
  clear hV
  xjd 0x371a
  xs 0x371c (.push [0x20] (by decide)) ri_push
  xs 0x371f (.push [0x08, 0xe0] (by decide)) ri_push
  xs 0x3721 (.push [0x44] (by decide)) ri_push
  xs 0x3726 (.push [0x79, 0xcc, 0x67, 0x90] (by decide)) ri_push
  xs 0x3729 (.push [0x08, 0x40] (by decide)) ri_push
  xmo 0x372a (.reg .mstore) (ri_mstore_imgAt (o := 0x840) rfl)
  xs 0x372b (.reg .caller) ri_caller
  xs 0x372e (.push [0x08, 0x60] (by decide)) ri_push
  xmo 0x372f (.reg .mstore) (ri_mstore_imgAt (o := 0x860) rfl)
  xs 0x3732 (.push [0x07, 0x80] (by decide)) ri_push
  xmo 0x3733 (.reg .mload) (ri_mload_imgAt (o := 0x780) rfl)
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide), hI.x.read] at h
  xs 0x3736 (.push [0x08, 0x80] (by decide)) ri_push
  xmo 0x3737 (.reg .mstore) (ri_mstore_imgAt (o := 0x880) rfl)
  xs 0x373a (.push [0x08, 0x5c] (by decide)) ri_push
  xs 0x373c (.push [0x00] (by decide)) ri_push
  xs 0x373e (.push [0x05] (by decide)) ri_push
  xw 0x373f (.reg .sload) ri_sload
  rw [tokenSlot_lit, getStorVal_eq, htw] at h
  xs 0x3740 (.reg .gas) ri_gas_remaining
  replace h := xa_call_img (pc' := 0x3741) (i := 0x85c) (n := 0x44) (o := 0x8e0) (z := 0x20) hfork
    (atN hcode (by kernel_rfl)) rfl (by decide) (by decide) (by decide) (by decide) hR hW h
  clear hR hW
  obtain ⟨d, flag, L1, h, -, hrd, hk⟩ := h
  rw [rli_burn_input] at hk
  xs 0x3744 (.push [0x37, 0x49] (by decide)) ri_push
  xji 0x3745 0x3749 hw
  · xdead
  obtain ⟨hR, hW, -, hch⟩ := hk hw
  clear hk hw
  rcases hch with ⟨hp, -⟩ | ⟨c, rfl, hdepth, -, hc⟩
  · exact absurd hp htok
  have hc' : ChildOf b d tw.toAdr (burnFromSel ++ sevm.caller.toB256.toBytes ++ X.toBytes) 0
      sevm.isStatic c := by
    rw [zero_lit] at hc
    exact hc.congr_left (fun _ => afterSload_getCode _ _ _ _) (fun _ => afterSload_getStor _ _ _ _)
      (afterSload_logs _ _ _) (afterSload_output _ _ _) (afterSload_accessedAddresses _ _ _)
  clear hc
  xjd 0x374a
  xs 0x374c (.push [0x1f] (by decide)) ri_push
  xs 0x374d (.reg .returndatasize) ri_returndatasize
  xs 0x374e (.reg .gt) ri_gt
  xs 0x3751 (.push [0x37, 0x56] (by decide)) ri_push
  xji 0x3752 0x3756 hw
  · xdead
  have hlen : 32 ≤ c.post.output.length := by
    have := gtCheck_ne_zero hw
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrd,
      show (Bytes.toB256 [0x1f]).toNat = 31 by decide] at this
    rw [hc'.output]; omega
  clear hw
  xjd 0x3757
  xs 0x3759 (.push [0x00] (by decide)) ri_push
  xs 0x375a (.reg .pop) ri_pop
  xs 0x375d (.push [0x08, 0xe0] (by decide)) ri_push
  xs 0x375e (.reg .pop) ri_pop
  xs 0x3761 (.push [0x09, 0x00] (by decide)) ri_push
  xs 0x3763 (.push [0x00] (by decide)) ri_push
  xs 0x3765 (.push [0x03] (by decide)) ri_push
  xs 0x3766 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x3767 (.reg (.dup 3)) (ri_dup (by rfl))
  xmo 0x3768 (.reg .mstore) (ri_mstore_imgAt (o := 0x900) rfl)
  xs 0x3769 (.reg .add) ri_add
  obtain ⟨img1, hR, hE⟩ := Mem.Reads.forget hR
  have hI1 : RliImg img1 X D1 T f0 f1 f2 := hI.keep fun o w hw _ ho => by rw [hE]; wchain; exact hw
  have hc0 : WordAt img1 0x900 (Nat.toB256 0) := by
    rw [hE, show Nat.toB256 0 = Bytes.toB256 [0] from by decide]; exact WordAt.write_self _ _ _
  rw [show Bytes.toB256 [3] + Bytes.toB256 [0] = Bytes.toB256 [3] from by decide] at h
  exact ⟨c, _, d, _, img1, _, rfl, hc', hlen, hdepth, hR, hW, hI1, hc0, h⟩

end Blanc.Lift.Curve3Pool
