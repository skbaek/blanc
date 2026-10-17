import Blanc.Lift.Curve3Pool.Walk.OneCoinBurn

/-!
# `remove_liquidity_one_coin`, part 3: the `transfer` push and its `raw_call` test

The bytes of `exchange`'s push and test (`xa_ex_push`, `xa_ex_tail2`) at other offsets:

* `xa_oc_push` (`0x45d1` → `0x469d`): the payload `concat(method_id("transfer(address,uint256)"),
  msg.sender, dy)` built at `0x480` with two identity copies, then the `CALL` to `coins[i]` with
  value `0`, input `0x540[0 : 0x44]` and output window `0x5e0[0 : 0x20]`; a zero flag reverts;
* `xa_oc_tail` (`0x469e` → `0x4729`): the `raw_call(…, max_outsize=32)` tail, through `0x3c0`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The `transfer` payload's identity copy at `0x480`. -/
theorem oc_transfer_copy2 (img : Bytes) (E C V : B256) :
    ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x4a0 transferSel) 0x4a4
      C.toBytes) 0x4c4 V.toBytes) 0x480 E.toBytes).sliceD 0x480 100 0).take 100 =
      E.toBytes ++ (transferSel ++ C.toBytes ++ V.toBytes) := by
  refine Region.copy ?_ (by simp only [List.length_append, B256.length_toBytes]; rfl)
    (by simp only [List.length_append, B256.length_toBytes]; rfl)
  refine Region.append' (o' := 0x4a0) (Region.of_word (WordAt.write_self _ _ _))
    (Region.append' (o' := 0x4c4) (Region.append' (o' := 0x4a4) ?_ ?_ (by rfl)) ?_
      (by simp only [List.length_append, B256.length_toBytes]; rfl))
    (by simp only [B256.length_toBytes])
  · refine Region.write_other (Region.write_other (Region.write_other (Region.write_self _ _ _)
      ?_) ?_) ?_ <;> simp only [transferSel, B256.length_toBytes, List.length_cons,
        List.length_nil] <;> omega
  · refine Region.write_other (Region.of_word (WordAt.write_other (WordAt.write_self _ _ _) ?_))
      ?_ <;> simp only [B256.length_toBytes] <;> omega
  · exact Region.write_other (Region.write_self _ _ _) (by simp only [B256.length_toBytes]; omega)

/-- **The push** (`0x45d1` → `0x469e`). -/
theorem xa_oc_push {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {v cw : B256}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hj3 : (exJ sevm).toNat < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hv : WordAt img 0x140 v)
    (hid : IdReady sevm b) (hdepth : 0 < sevm.depth)
    (hcw : (b.getStor sevm.currentTarget).get (coinsBase + exJ sevm) = cw)
    (hcoin : ¬ sevm.benvStat.rules.isPrecomp cw.toAdr)
    (h : XAt sevm post 0x45d1 (St b [] M G) L) :
    ∃ b' c L' d img' G', BaseRel b b' ∧ L = c :: L' ∧
      ChildOf b' d cw.toAdr (exPushData sevm v) 0 sevm.isStatic c ∧
      WordAt img' 0x140 v ∧
      Mem.Reads d.memory (Bytes.writeAt img' 0x5e0 (d.returnData.take 0x20)) ∧
      Mem.Wf d.memory ∧ d.returnData.length < 2 ^ 256 ∧
      XAt sevm post 0x469e (St d [] d.memory G') L' := by
  xs 0x45d3 (.push [0x00] (by decide)) ri_push
  xs 0x45d5 (.push [0x04] (by decide)) ri_push
  xs 0x45d8 (.push [0x04, 0x20] (by decide)) ri_push
  xmo 0x45d9 (.reg .mstore) (ri_mstore_imgAt (o := 0x420) rfl)
  xs 0x45fa (.push [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) ri_push
  xs 0x45fd (.push [0x04, 0x40] (by decide)) ri_push
  xmo 0x45fe (.reg .mstore) (ri_mstore_imgAt (o := 0x440) rfl)
  xs 0x4601 (.push [0x04, 0x20] (by decide)) ri_push
  xs 0x4603 (.push [0x04] (by decide)) ri_push
  xs 0x4604 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x4606 (.push [0x20] (by decide)) ri_push
  xs 0x4607 (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0x460a (.push [0x04, 0x80] (by decide)) ri_push
  xs 0x460b (.reg .add) ri_add
  xs 0x460c (.reg .add) ri_add
  xs 0x460d (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x460f (.push [0x20] (by decide)) ri_push
  xs 0x4610 (.reg (.dup 5)) (ri_dup (by rfl))
  xs 0x4611 (.reg .add) ri_add
  xs 0x4613 (.push [0x00] (by decide)) ri_push
  xs 0x4615 (.push [0x04] (by decide)) ri_push
  xs 0x4616 (.reg .gas) ri_gas_remaining
  obtain ⟨img1, hR, hI⟩ := Mem.Reads.forget hR
  have f_v : WordAt img1 0x140 v := by rw [hI]; wchainT; exact hv
  have f_a40 : WordAt img1 0x420 (Bytes.toB256 [4]) := by rw [hI]; wchainT
  have f_sel : WordAt img1 0x440 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]) := by
    rw [hI]; wchainT
  clear hI hv
  replace h := xa_identity_img (pc' := 0x4617) (i := 0x440) (n := 4) (o := 0x4a0) (z := 4) hid
    (atN hcode (by kernel_rfl)) rfl (by decide) (by decide) (by decide) (by decide) hR hW h
  clear hR hW
  obtain ⟨d, L1, h, hk⟩ := h
  rcases hk with ⟨h0, hgas⟩ | ⟨rfl, b2, G2, M, hsha, rfl, hR, hW⟩
  · have hz := hgas rfl hdepth (by decide)
    obtain ⟨_, s, -⟩ := xa_next (n := .reg .pop) (atN hcode (by kernel_rfl)) (by nofun) h
    exact absurd (gasLeft_of_run_pop s) (by rw [hz]; decide)
  have hsel4 : (img1.sliceD 0x440 4 0).take 4 = transferSel := by
    rw [f_sel.prefix (by decide)]; decide
  rw [hsel4] at hR
  have hb12 : BaseRel b b2 := ⟨hsha.stor, hsha.code, hsha.addrs, hsha.logs, hsha.output, hsha.error⟩
  clear hsha hsel4
  xs 0x4618 (.reg .pop) ri_pop
  xs 0x4619 (.reg .pop) ri_pop
  xs 0x461a (.reg (.dup 0)) (ri_dup (by rfl))
  xmo 0x461b (.reg .mload) (ri_mload_imgAt (o := 0x420) rfl)
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide), f_a40.read] at h
  xs 0x461c (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x461d (.reg .add) ri_add
  xs 0x461e (.reg (.swap 1)) (ri_swap (by rfl))
  xs 0x461f (.reg .pop) ri_pop
  xs 0x4620 (.reg .pop) ri_pop
  xs 0x4621 (.reg .caller) ri_caller
  xs 0x4623 (.push [0x20] (by decide)) ri_push
  xs 0x4624 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x4627 (.push [0x04, 0x80] (by decide)) ri_push
  xs 0x4628 (.reg .add) ri_add
  xs 0x4629 (.reg .add) ri_add
  xmo 0x462a (.reg .mstore) (ri_mstore_imgAt (o := 0x4a4) (by decide))
  xs 0x462c (.push [0x20] (by decide)) ri_push
  xs 0x462d (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x462e (.reg .add) ri_add
  xs 0x462f (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x4630 (.reg .pop) ri_pop
  xs 0x4633 (.push [0x01, 0x40] (by decide)) ri_push
  xmo 0x4634 (.reg .mload) (ri_mload_imgAt (o := 0x140) rfl)
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide), f_v.read] at h
  xs 0x4636 (.push [0x20] (by decide)) ri_push
  xs 0x4637 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x463a (.push [0x04, 0x80] (by decide)) ri_push
  xs 0x463b (.reg .add) ri_add
  xs 0x463c (.reg .add) ri_add
  xmo 0x463d (.reg .mstore) (ri_mstore_imgAt (o := 0x4c4) (by decide))
  xs 0x463f (.push [0x20] (by decide)) ri_push
  xs 0x4640 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x4641 (.reg .add) ri_add
  xs 0x4642 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x4643 (.reg .pop) ri_pop
  xs 0x4644 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x4647 (.push [0x04, 0x80] (by decide)) ri_push
  xmo 0x4648 (.reg .mstore) (ri_mstore_imgAt (o := 0x480) rfl)
  xs 0x464b (.push [0x04, 0x80] (by decide)) ri_push
  xs 0x464c (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x464d (.reg .pop) ri_pop
  xs 0x464e (.reg (.dup 0)) (ri_dup (by rfl))
  xmo 0x464f (.reg .mload) (ri_mload_imgAt (o := 0x480) rfl)
  rw [Bytes.readWord_writeAt_self] at h
  xs 0x4651 (.push [0x20] (by decide)) ri_push
  xs 0x4652 (.reg .add) ri_add
  xs 0x4653 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x4656 (.push [0x05, 0x20] (by decide)) ri_push
  xs 0x4657 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x4658 (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0x465a (.push [0x00] (by decide)) ri_push
  xs 0x465c (.push [0x04] (by decide)) ri_push
  xs 0x465d (.reg .gas) ri_gas_remaining
  replace h := xa_identity_img (pc' := 0x465e) (i := 0x480) (n := 0x64) (o := 0x520) (z := 0x64)
    (hid.of_rel hb12) (atN hcode (by kernel_rfl)) rfl (by decide) (by decide) (by decide)
    (by decide) hR hW h
  clear hR hW
  obtain ⟨d, L2, h, hk⟩ := h
  rcases hk with ⟨h0, -⟩ | ⟨rfl, b3, G3, M, hsha2, rfl, hR, hW⟩
  · rw [St.self h0 rfl] at h
    xs 0x4661 (.push [0x46, 0x66] (by decide)) ri_push
    xji 0x4662 0x4666 hw
    · xdead
    · exact absurd rfl hw
  rw [oc_transfer_copy2] at hR
  have hb23 : BaseRel b2 b3 :=
    ⟨hsha2.stor, hsha2.code, hsha2.addrs, hsha2.logs, hsha2.output, hsha2.error⟩
  clear hsha2
  obtain ⟨img3, hR, hI⟩ := Mem.Reads.forget hR
  have g_v : WordAt img3 0x140 v := by rw [hI]; wchainT; exact f_v
  have g_data : Region img3 0x520 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
      Bytes.toB256 [32]).toBytes ++ (transferSel ++ sevm.caller.toB256.toBytes ++ v.toBytes)) := by
    rw [hI]; exact Region.write_self _ _ _
  clear hI f_v f_a40 f_sel
  xs 0x4661 (.push [0x46, 0x66] (by decide)) ri_push
  xji 0x4662 0x4666 hw
  · exact absurd hw (by decide)
  clear hw
  xjd 0x4667
  xs 0x4668 (.reg .pop) ri_pop
  xs 0x4669 (.reg .pop) ri_pop
  -- the `CALL`
  xs 0x466b (.push [0x20] (by decide)) ri_push
  xs 0x466e (.push [0x05, 0xe0] (by decide)) ri_push
  xs 0x4671 (.push [0x05, 0x20] (by decide)) ri_push
  xmo 0x4672 (.reg .mload) (ri_mload_imgAt (o := 0x520) rfl)
  rw [(Region.word g_data.left).read] at h
  xs 0x4675 (.push [0x05, 0x40] (by decide)) ri_push
  xs 0x4677 (.push [0x00] (by decide)) ri_push
  xs 0x4679 (.push [0x24] (by decide)) ri_push
  xs 0x467a (.reg .calldataload) ri_calldataload
  xs 0x467c (.push [0x03] (by decide)) ri_push
  xs 0x467d (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x467e (.reg .lt) ri_lt
  xs 0x4681 (.push [0x46, 0x86] (by decide)) ri_push
  xji 0x4682 0x4686 hw
  · xdead
  clear hw
  xjd 0x4687
  xs 0x4689 (.push [0x00] (by decide)) ri_push
  xs 0x468b (.push [0xc0] (by decide)) ri_push
  xmo 0x468c (.reg .mstore) (ri_mstore_imgAt (o := 0xc0) rfl)
  xs 0x468e (.push [0x20] (by decide)) ri_push
  xs 0x4690 (.push [0xc0] (by decide)) ri_push
  xmo 0x4691 (.reg .keccak256) (ri_keccak_imgAt (o := 0xc0) (z := 0x20) rfl rfl)
  rw [keccak_zero] at h
  xs 0x4692 (.reg .add) ri_add
  xw 0x4693 (.reg .sload) ri_sload
  rw [getStorVal_eq, hb23.stor, hb12.stor, hcw] at h
  xs 0x4694 (.reg .gas) ri_gas_remaining
  have hin : (Bytes.writeAt img3 0xc0 (Bytes.toB256 [0]).toBytes).sliceD 0x540 0x44 0 =
      exPushData sevm v :=
    Region.slice (Region.write_other g_data.right (by simp only [B256.length_toBytes]; omega))
      (by simp only [List.length_append, B256.length_toBytes]; rfl)
  replace h := xa_call_img (pc' := 0x4695) (i := 0x540) (n := 0x44) (o := 0x5e0) (z := 0x20) hfork
    (atN hcode (by kernel_rfl)) rfl (by decide) (by decide) (by decide) (by decide) hR hW h
  clear hR hW
  obtain ⟨d4, flag, L4, h, _, hrd4, hk⟩ := h
  rw [hin] at hk
  xs 0x4698 (.push [0x46, 0x9d] (by decide)) ri_push
  xji 0x4699 0x469d hw
  · xdead
  obtain ⟨hR, hW, hout4, hch⟩ := hk hw
  clear hk hin hw
  rcases hch with ⟨hp, -⟩ | ⟨c, rfl, -, -, hc⟩
  · exact absurd hp hcoin
  xjd 0x469e
  rw [zero_lit] at hc
  exact ⟨b3, c, L4, d4, _, _, hb12.trans hb23, rfl,
    hc.congr_left (fun _ => afterSload_getCode _ _ _ _) (fun _ => afterSload_getStor _ _ _ _)
      (afterSload_logs _ _ _) (afterSload_output _ _ _) (afterSload_accessedAddresses _ _ _),
    g_v.write_other (by simp only [B256.length_toBytes]; omega), hR, hW, hrd4, h⟩


/-- The `raw_call` test after the `transfer`. -/
theorem xa_oc_tail {sevm : Sevm} {post d : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} (hcode : sevm.code = code) (hid : IdReady sevm d)
    (hR : Mem.Reads M (Bytes.writeAt img 0x5e0 (d.returnData.take 0x20))) (hW : Mem.Wf M)
    (hrd : d.returnData.length < 2 ^ 256)
    (h : XAt sevm post 0x469e (St d [] M G) L) :
    RawCallOk d.returnData ∧ ∃ b6 M6 img6 G7, BaseRel d b6 ∧ Mem.Reads M6 img6 ∧ Mem.Wf M6 ∧
      (∀ o w, WordAt img o w → (o + 32 ≤ 0x3c0 ∨ 0x400 ≤ o) →
        (o + 32 ≤ 0x5c0 ∨ 0x600 ≤ o) → WordAt img6 o w) ∧
      XAt sevm post 0x4729 (St b6 [] M6 G7) L := by
  have hj : ∃ nW G5, nW.toNat = (d.returnData.take 32).length ∧
      XAt sevm post 0x46b1 (St d (nW :: d.returnData.length.toB256 :: Bytes.toB256 [0x20] ::
        []) M G5) L := by
    xs 0x46a0 (.push [0x20] (by decide)) ri_push
    xs 0x46a1 (.reg .returndatasize) ri_returndatasize
    xs 0x46a2 (.reg (.dup 0)) (ri_dup (by rfl))
    xs 0x46a3 (.reg (.dup 2)) (ri_dup (by rfl))
    xs 0x46a4 (.reg .gt) ri_gt
    xs 0x46a5 (.reg .iszero) ri_iszero
    xs 0x46a8 (.push [0x46, 0xae] (by decide)) ri_push
    xji 0x46a9 0x46ae hw
    · xs 0x46aa (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x46ad (.push [0x46, 0xb0] (by decide)) ri_push
      xjmp 0x46b0
      xjd 0x46b1
      refine ⟨_, _, ?_, h⟩
      have hlt := gtCheck_ne_zero (eqCheck_eq_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrd,
        show (Bytes.toB256 [0x20]).toNat = 32 by decide] at hlt
      rw [List.length_take, B256.toNat_toB256_of_lt hrd]
      omega
    · xjd 0x46af
      xs 0x46b0 (.reg (.dup 1)) (ri_dup (by rfl))
      xjd 0x46b1
      refine ⟨_, _, ?_, h⟩
      have hge := gtCheck_eq_zero (eqCheck_ne_zero_eq hw)
      rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrd,
        show (Bytes.toB256 [0x20]).toNat = 32 by decide] at hge
      rw [List.length_take, show (Bytes.toB256 [0x20]).toNat = 32 by decide]
      omega
  obtain ⟨nW, G5, hn, h⟩ := hj
  xs 0x46b2 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x46b3 (.reg .pop) ri_pop
  xs 0x46b4 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x46b5 (.reg .pop) ri_pop
  xs 0x46b8 (.push [0x05, 0xc0] (by decide)) ri_push
  xmo 0x46b9 (.reg .mstore) (ri_mstore_imgAt (o := 0x5c0) rfl)
  xs 0x46bc (.push [0x05, 0xc0] (by decide)) ri_push
  xs 0x46bd (.reg (.dup 0)) (ri_dup (by rfl))
  xmo 0x46be (.reg .mload) (ri_mload_imgAt (o := 0x5c0) rfl)
  rw [(WordAt.write_self _ _ _).read] at h
  xs 0x46c0 (.push [0x20] (by decide)) ri_push
  xs 0x46c1 (.reg .add) ri_add
  xs 0x46c2 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x46c5 (.push [0x03, 0xc0] (by decide)) ri_push
  xs 0x46c6 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x46c7 (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0x46c9 (.push [0x00] (by decide)) ri_push
  xs 0x46cb (.push [0x04] (by decide)) ri_push
  xs 0x46cc (.reg .gas) ri_gas_remaining
  have hn32 : (d.returnData.take 32).length ≤ 32 := by rw [List.length_take]; omega
  have hsz : (Bytes.toB256 [0x20] + nW).toNat = 32 + (d.returnData.take 32).length := by
    rw [B256.toNat_add, hn, show (Bytes.toB256 [0x20]).toNat = 32 by decide]
    exact Nat.mod_eq_of_lt (by omega)
  replace h := xa_identity_img (pc' := 0x46cd) (i := 0x5c0) (n := 32 + (d.returnData.take 32).length)
    (o := 0x3c0) (z := 32 + (d.returnData.take 32).length) hid
    (atN hcode (by kernel_rfl)) rfl (by decide) hsz (by decide) hsz hR hW h
  clear hR hW
  obtain ⟨d, L5, h, hk⟩ := h
  rcases hk with ⟨h0, -⟩ | ⟨rfl, b6, G6, M, hsha3, rfl, hR, hW⟩
  · rw [St.self h0 rfl] at h
    xs 0x46d0 (.push [0x46, 0xd5] (by decide)) ri_push
    xji 0x46d1 0x46d5 hw
    · xdead
    · exact absurd rfl hw
  have r5 : Region (Bytes.writeAt (Bytes.writeAt img 0x5e0 (d.returnData.take 32)) 0x5c0
      nW.toBytes) 0x5c0 (nW.toBytes ++ d.returnData.take 32) :=
    Region.append' (o' := 0x5e0) (Region.write_self _ _ _)
      (Region.write_other (Region.write_self _ _ _) (by simp only [B256.length_toBytes]; omega))
      (by simp only [B256.length_toBytes])
  rw [Region.copy r5 (by simp only [List.length_append, B256.length_toBytes])
    (by simp only [List.length_append, B256.length_toBytes])] at hR
  have hb46 : BaseRel d b6 :=
    ⟨hsha3.stor, hsha3.code, hsha3.addrs, hsha3.logs, hsha3.output, hsha3.error⟩
  clear hsha3 r5
  have e6 := Mem.Reads.forget hR
  clear hR
  obtain ⟨img6, hR, hI⟩ := e6
  have k_keep : ∀ o w, WordAt img o w → (o + 32 ≤ 0x3c0 ∨ 0x400 ≤ o) →
      (o + 32 ≤ 0x5c0 ∨ 0x600 ≤ o) → WordAt img6 o w := by
    intro o w hw h1 h2
    rw [hI]
    refine WordAt.write_other (WordAt.write_other (WordAt.write_other hw ?_) ?_) ?_ <;>
      simp only [B256.length_toBytes, List.length_take, List.length_append] <;> omega
  have k_buf : Region img6 0x3c0 (nW.toBytes ++ d.returnData.take 32) := by
    rw [hI]; exact Region.write_self _ _ _
  clear hI
  xs 0x46d0 (.push [0x46, 0xd5] (by decide)) ri_push
  xji 0x46d1 0x46d5 hw
  · exact absurd hw (by decide)
  clear hw
  xjd 0x46d6
  xs 0x46d7 (.reg .pop) ri_pop
  xs 0x46d8 (.reg .pop) ri_pop
  have kr : Region img6 0x3e0 (d.returnData.take 32) := by
    have := k_buf.right; rwa [B256.length_toBytes] at this
  have kn : WordAt img6 0x3c0 nW := Region.word k_buf.left
  have hj2 : RawCallOk d.returnData ∧ ∃ M7 G7, Mem.Reads M7 img6 ∧ Mem.Wf M7 ∧
      XAt sevm post 0x4729 (St b6 [] M7 G7) L := by
    xs 0x46da (.push [0x00] (by decide)) ri_push
    xs 0x46dd (.push [0x03, 0xc0] (by decide)) ri_push
    xmo 0x46de (.reg .mload) (ri_mload_imgAt (o := 0x3c0) rfl)
    rw [kn.read] at h
    xs 0x46df (.reg .gt) ri_gt
    xs 0x46e0 (.reg .iszero) ri_iszero
    xs 0x46e3 (.push [0x47, 0x28] (by decide)) ri_push
    xji 0x46e4 0x4728 hw
    · have hpos := gtCheck_ne_zero (eqCheck_eq_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0x00]).toNat = 0 by decide] at hpos
      clear hw
      xs 0x46e7 (.push [0x03, 0xc0] (by decide)) ri_push
      xs 0x46e8 (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x46ea (.push [0x20] (by decide)) ri_push
      xs 0x46eb (.reg .add) ri_add
      xmo 0x46ec (.reg .mload) (ri_mload_imgAt (o := 0x3e0) (by decide))
      xs 0x46ee (.push [0x00] (by decide)) ri_push
      xs 0x46ef (.reg (.dup 2)) (ri_dup (by rfl))
      xmo 0x46f0 (.reg .mload) (ri_mload_imgAt (o := 0x3c0) rfl)
      rw [kn.read] at h
      xs 0x46f1 (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x46f3 (.push [0x20] (by decide)) ri_push
      xs 0x46f4 (.reg (.swap 0)) (ri_swap (by rfl))
      xs2 0x46f5 (.reg .sgt) ri_sgt
      xs 0x46f6 (.reg .iszero) ri_iszero
      xs 0x46f9 (.push [0x46, 0xfe] (by decide)) ri_push
      xji 0x46fa 0x46fe hw
      · xdead
      clear hw
      xjd 0x46ff
      xs 0x4700 (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x4701 (.reg (.swap 1)) (ri_swap (by rfl))
      xs 0x4702 (.reg (.swap 0)) (ri_swap (by rfl))
      xs2 0x4703 (.reg .slt) ri_slt
      xs 0x4704 (.reg .iszero) ri_iszero
      xs 0x4707 (.push [0x47, 0x0c] (by decide)) ri_push
      xji 0x4708 0x470c hw
      · xdead
      clear hw
      xjd 0x470d
      xs 0x470e (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x4710 (.push [0x20] (by decide)) ri_push
      xs 0x4711 (.reg .sub) ri_sub
      xs 0x4714 (.push [0x01, 0x00] (by decide)) ri_push
      xs 0x4715 (.reg .exp) ri_exp
      xs 0x4716 (.reg (.dup 2)) (ri_dup (by rfl))
      xs 0x4717 (.reg .div) ri_div
      xs 0x4718 (.reg (.swap 0)) (ri_swap (by rfl))
      xs 0x4719 (.reg .pop) ri_pop
      xs 0x471a (.reg (.swap 0)) (ri_swap (by rfl))
      xs 0x471b (.reg .pop) ri_pop
      xs 0x471c (.reg (.swap 0)) (ri_swap (by rfl))
      xs 0x471d (.reg .pop) ri_pop
      xs 0x471e (.reg .iszero) ri_iszero
      xs 0x471f (.reg .iszero) ri_iszero
      xs 0x4722 (.push [0x47, 0x27] (by decide)) ri_push
      xji 0x4723 0x4727 hq
      · xdead
      xjd 0x4728
      xjd 0x4729
      refine ⟨.inr ?_, _, _, hR, hW, h⟩
      have hq0 := eqCheck_eq_zero (eqCheck_ne_zero_eq hq)
      have hxs : (img6.sliceD 0x3e0 32 0).length = 32 := List.length_sliceD _ _ _ _
      have hquot := rawCheck_quot (len := nW) (by omega) (by omega) hxs rfl
      rw [hn, kr.head (by omega)] at hquot
      rw [show d.returnData.take (min d.returnData.length 32) = d.returnData.take 32 by
        rw [Nat.min_comm, ← List.take_take, List.take_length]]
      rw [← hquot]
      exact fun e => hq0 (B256.toNat_inj _ _ (by rw [e]; rfl))
    · have hz := gtCheck_eq_zero (eqCheck_ne_zero_eq hw)
      rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0x00]).toNat = 0 by decide] at hz
      xjd 0x4729
      refine ⟨.inl ?_, _, _, hR, hW, h⟩
      rw [List.length_take] at hn
      omega
  clear hR hW
  obtain ⟨hok, M7, G7, hR, hW, h⟩ := hj2
  exact ⟨hok, b6, M7, img6, G7, hb46, hR, hW, k_keep, h⟩


/-- The `RemoveLiquidityOne` topic word. -/
abbrev ocTopic : B256 := Bytes.toB256 [0x9e, 0x96, 0xdd, 0x3b, 0x99, 0x7a, 0x2a, 0x25, 0x7e, 0xec,
  0x4d, 0xf9, 0xbb, 0x6e, 0xaf, 0x62, 0x6e, 0x20, 0x6d, 0xf5, 0xf5, 0x43, 0xbd, 0x96, 0x36, 0x82,
  0xd1, 0x43, 0x30, 0x0b, 0xe3, 0x10]

/-- **The event and the lock** (`0x4729` → `STOP`): `RemoveLiquidityOne(msg.sender,
_token_amount, dy)` (`LOG2` over the two words at `0x620`) and the lock cleared. -/
theorem xa_oc_log {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {v : B256} (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hv : WordAt img 0x140 v)
    (h : XAt sevm post 0x4729 (St b [] M G) L) :
    L = [] ∧
      (∀ x, (post.getStor sevm.currentTarget).get x =
        ((b.getStor sevm.currentTarget).set lockSlot 0).get x) ∧
      post.logs = b.logs ++ [⟨sevm.currentTarget, [ocTopic, sevm.caller.toB256],
        (ocAmt sevm).toBytes ++ v.toBytes⟩] ∧
      post.output = b.output := by
  xs 0x472b (.push [0x04] (by decide)) ri_push
  xs 0x472c (.reg .calldataload) ri_calldataload
  xs 0x472f (.push [0x06, 0x20] (by decide)) ri_push
  xmo 0x4730 (.reg .mstore) (ri_mstore_imgAt (o := 0x620) rfl)
  xs 0x4733 (.push [0x01, 0x40] (by decide)) ri_push
  xmo 0x4734 (.reg .mload) (ri_mload_imgAt (o := 0x140) rfl)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint] at h
  rw [hv.read] at h
  xs 0x4737 (.push [0x06, 0x40] (by decide)) ri_push
  xmo 0x4738 (.reg .mstore) (ri_mstore_imgAt (o := 0x640) rfl)
  xs 0x4739 (.reg .caller) ri_caller
  xs 0x475a (.push [0x9e, 0x96, 0xdd, 0x3b, 0x99, 0x7a, 0x2a, 0x25, 0x7e, 0xec, 0x4d, 0xf9, 0xbb, 0x6e, 0xaf, 0x62, 0x6e, 0x20, 0x6d, 0xf5, 0xf5, 0x43, 0xbd, 0x96, 0x36, 0x82, 0xd1, 0x43, 0x30, 0x0b, 0xe3, 0x10] (by decide)) ri_push
  xs 0x475c (.push [0x40] (by decide)) ri_push
  xs 0x475f (.push [0x06, 0x20] (by decide)) ri_push
  obtain ⟨img2, hR2, hI⟩ := Mem.Reads.forget hR
  have hdata : Region img2 0x620 ((ocAmt sevm).toBytes ++ v.toBytes) := by
    rw [hI]
    refine Region.append' (o' := 0x640) ?_ ?_ ?_
    all_goals first
      | simp only [List.length_append, B256.length_toBytes]
      | exact Region.of_word (by wchain)
  clear hI hR
  replace h := xa_nextAt (n := .reg (.log 2)) (pc' := 0x4760) (atN hcode (by kernel_rfl))
    (by nofun) (by rfl) h
  obtain ⟨_, s, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_log2_post s
  clear s
  rw [Mem.Reads.read hR2, show (Bytes.toB256 [0x06, 0x20]).toNat = 0x620 from rfl,
    show (Bytes.toB256 [0x40]).toNat = 0x40 from rfl,
    hdata.slice (by simp only [List.length_append, B256.length_toBytes])] at h
  xs 0x4762 (.push [0x00] (by decide)) ri_push
  xs 0x4766 (.push [0xff, 0xff, 0xff] (by decide)) ri_push
  xw 0x4767 (.reg .sstore) ri_sstore
  obtain ⟨hrun, hL⟩ := xa_halt (l := .stop) (atL hcode (by kernel_rfl)) h
  have hp := (Except.ok.inj hrun).symm
  subst hp hL
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro x
    show ((afterSstore sevm _ _ _).getStor _).get x = _
    rw [afterSstore_getStor_self, lockSlot_lit, zero_lit]
    rfl
  · show (afterSstore sevm _ _ _).logs = _
    rw [afterSstore_logs]
    rfl
  · show (afterSstore sevm _ _ _).output = _
    rw [afterSstore_output]
    rfl

end Blanc.Lift.Curve3Pool
