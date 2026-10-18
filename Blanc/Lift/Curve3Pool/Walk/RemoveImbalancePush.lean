import Blanc.Lift.Curve3Pool.Walk.RemoveImbalanceD2
import Blanc.Lift.Curve3Pool.Walk.ExchangePush

/-!
# `remove_liquidity_imbalance`, part 6: one coin's `transfer`

The bytes of `exchange`'s push and `raw_call` test (`xa_ex_push`, `xa_ex_tail2`) at other
offsets, with the amount read from calldata (`amounts[i]`, `rliAmt`) and the coin index from the
loop counter at `0x900`:

* `xa_rli_push` (`0x378a` → `0x386c`): the payload `concat(method_id("transfer(address,uint256)"),
  msg.sender, amounts[i])` built at `0x9e0` with two identity copies, then the `CALL` to
  `coins[i]` with value `0`, input `0xaa0[0 : 0x44]` and output window `0xb40[0 : 0x20]`;
* `xa_rli_tail` (`0x386c` → `0x38f7`): the `raw_call(…, max_outsize=32)` tail, through `0x920`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- `amounts[k]`, the calldata word. -/
abbrev rliAmt (sevm : Sevm) (k : Nat) : B256 :=
  Sevm.dataWord sevm (Bytes.toB256 [0x20] * Nat.toB256 k + Bytes.toB256 [4])

/-- The `transfer` payload's identity copy at `0x9e0`. -/
theorem rli_transfer_copy2 (img : Bytes) (E C V : B256) :
    ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0xa00 transferSel) 0xa04
      C.toBytes) 0xa24 V.toBytes) 0x9e0 E.toBytes).sliceD 0x9e0 100 0).take 100 =
      E.toBytes ++ (transferSel ++ C.toBytes ++ V.toBytes) := by
  refine Region.copy ?_ (by simp only [List.length_append, B256.length_toBytes]; rfl)
    (by simp only [List.length_append, B256.length_toBytes]; rfl)
  refine Region.append' (o' := 0xa00) (Region.of_word (WordAt.write_self _ _ _))
    (Region.append' (o' := 0xa24) (Region.append' (o' := 0xa04) ?_ ?_ (by rfl)) ?_
      (by simp only [List.length_append, B256.length_toBytes]; rfl))
    (by simp only [B256.length_toBytes])
  · refine Region.write_other (Region.write_other (Region.write_other (Region.write_self _ _ _)
      ?_) ?_) ?_ <;> simp only [transferSel, B256.length_toBytes, List.length_cons,
        List.length_nil] <;> omega
  · refine Region.write_other (Region.of_word (WordAt.write_other (WordAt.write_self _ _ _) ?_))
      ?_ <;> simp only [B256.length_toBytes] <;> omega
  · exact Region.write_other (Region.write_self _ _ _) (by simp only [B256.length_toBytes]; omega)

/-- **The push** of coin `k` (`0x378a` → `0x386c`). -/
theorem xa_rli_push {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {cw : B256} {S : List B256} {k : Nat}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hctr : WordAt img 0x900 (Nat.toB256 k))
    (hid : IdReady sevm b) (hdepth : 0 < sevm.depth)
    (hcw : (b.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 k) = cw)
    (hcoin : ¬ sevm.benvStat.rules.isPrecomp cw.toAdr)
    (h : XAt sevm post 0x378a (St b S M G) L) :
    ∃ b' c L' d img' G', BaseRel b b' ∧ L = c :: L' ∧
      ChildOf b' d cw.toAdr (exPushData sevm (rliAmt sevm k)) 0 sevm.isStatic c ∧
      (∀ o w, WordAt img o w → 0xe0 ≤ o → o + 32 ≤ 0x980 → WordAt img' o w) ∧
      Mem.Reads d.memory (Bytes.writeAt img' 0xb40 (d.returnData.take 0x20)) ∧
      Mem.Wf d.memory ∧ d.returnData.length < 2 ^ 256 ∧
      XAt sevm post 0x386c (St d S d.memory G') L' := by
  xs 0x378c (.push [0x00] (by decide)) ri_push
  xs 0x378e (.push [0x04] (by decide)) ri_push
  xs 0x3791 (.push [0x09, 0x80] (by decide)) ri_push
  xmo 0x3792 (.reg .mstore) (ri_mstore_imgAt (o := 0x980) rfl)
  xs 0x37b3 (.push [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) ri_push
  xs 0x37b6 (.push [0x09, 0xa0] (by decide)) ri_push
  xmo 0x37b7 (.reg .mstore) (ri_mstore_imgAt (o := 0x9a0) rfl)
  xs 0x37ba (.push [0x09, 0x80] (by decide)) ri_push
  xs 0x37bc (.push [0x04] (by decide)) ri_push
  xs 0x37bd (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x37bf (.push [0x20] (by decide)) ri_push
  xs 0x37c0 (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0x37c3 (.push [0x09, 0xe0] (by decide)) ri_push
  xs 0x37c4 (.reg .add) ri_add
  xs 0x37c5 (.reg .add) ri_add
  xs 0x37c6 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x37c8 (.push [0x20] (by decide)) ri_push
  xs 0x37c9 (.reg (.dup 5)) (ri_dup (by rfl))
  xs 0x37ca (.reg .add) ri_add
  xs 0x37cc (.push [0x00] (by decide)) ri_push
  xs 0x37ce (.push [0x04] (by decide)) ri_push
  xs 0x37cf (.reg .gas) ri_gas_remaining
  obtain ⟨img1, hR, hI⟩ := Mem.Reads.forget hR
  have f_k : ∀ o w, WordAt img o w → o + 32 ≤ 0x980 → WordAt img1 o w := fun o w hw ho => by
    rw [hI]; wchainT; exact hw
  have f_c : WordAt img1 0x900 (Nat.toB256 k) := f_k _ _ hctr (by decide)
  have f_a40 : WordAt img1 0x980 (Bytes.toB256 [4]) := by rw [hI]; wchainT
  have f_sel : WordAt img1 0x9a0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]) := by
    rw [hI]; wchainT
  clear hI
  replace h := xa_identity_img (pc' := 0x37d0) (i := 0x9a0) (n := 4) (o := 0xa00) (z := 4) hid
    (atN hcode (by kernel_rfl)) rfl (by decide) (by decide) (by decide) (by decide) hR hW h
  clear hR hW
  obtain ⟨d, L1, h, hk⟩ := h
  rcases hk with ⟨h0, hgas⟩ | ⟨rfl, b2, G2, M, hsha, rfl, hR, hW⟩
  · have hz := hgas rfl hdepth (by decide)
    obtain ⟨_, s, -⟩ := xa_next (n := .reg .pop) (atN hcode (by kernel_rfl)) (by nofun) h
    exact absurd (gasLeft_of_run_pop s) (by rw [hz]; decide)
  have hsel4 : (img1.sliceD 0x9a0 4 0).take 4 = transferSel := by
    rw [f_sel.prefix (by decide)]; decide
  rw [hsel4] at hR
  have hb12 : BaseRel b b2 := ⟨hsha.stor, hsha.code, hsha.addrs, hsha.logs, hsha.output, hsha.error⟩
  clear hsha hsel4
  xs 0x37d1 (.reg .pop) ri_pop
  xs 0x37d2 (.reg .pop) ri_pop
  xs 0x37d3 (.reg (.dup 0)) (ri_dup (by rfl))
  xmo 0x37d4 (.reg .mload) (ri_mload_imgAt (o := 0x980) rfl)
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide), f_a40.read] at h
  xs 0x37d5 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x37d6 (.reg .add) ri_add
  xs 0x37d7 (.reg (.swap 1)) (ri_swap (by rfl))
  xs 0x37d8 (.reg .pop) ri_pop
  xs 0x37d9 (.reg .pop) ri_pop
  xs 0x37da (.reg .caller) ri_caller
  xs 0x37dc (.push [0x20] (by decide)) ri_push
  xs 0x37dd (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x37e0 (.push [0x09, 0xe0] (by decide)) ri_push
  xs 0x37e1 (.reg .add) ri_add
  xs 0x37e2 (.reg .add) ri_add
  xmo 0x37e3 (.reg .mstore) (ri_mstore_imgAt (o := 0xa04) (by decide))
  xs 0x37e5 (.push [0x20] (by decide)) ri_push
  xs 0x37e6 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x37e7 (.reg .add) ri_add
  xs 0x37e8 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x37e9 (.reg .pop) ri_pop
  xs 0x37eb (.push [0x04] (by decide)) ri_push
  xs 0x37ee (.push [0x09, 0x00] (by decide)) ri_push
  xmo 0x37ef (.reg .mload) (ri_mload_imgAt (o := 0x900) rfl)
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide), f_c.read] at h
  xs 0x37f1 (.push [0x03] (by decide)) ri_push
  xs 0x37f2 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x37f3 (.reg .lt) ri_lt
  xs 0x37f6 (.push [0x37, 0xfb] (by decide)) ri_push
  xji 0x37f7 0x37fb hw
  · xdead
  clear hw
  xjd 0x37fc
  xs 0x37fe (.push [0x20] (by decide)) ri_push
  xs 0x37ff (.reg .mul) ri_mul
  xs 0x3800 (.reg .add) ri_add
  xs 0x3801 (.reg .calldataload) ri_calldataload
  xs 0x3803 (.push [0x20] (by decide)) ri_push
  xs 0x3804 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x3807 (.push [0x09, 0xe0] (by decide)) ri_push
  xs 0x3808 (.reg .add) ri_add
  xs 0x3809 (.reg .add) ri_add
  xmo 0x380a (.reg .mstore) (ri_mstore_imgAt (o := 0xa24) (by decide))
  xs 0x380c (.push [0x20] (by decide)) ri_push
  xs 0x380d (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x380e (.reg .add) ri_add
  xs 0x380f (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x3810 (.reg .pop) ri_pop
  xs 0x3811 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x3814 (.push [0x09, 0xe0] (by decide)) ri_push
  xmo 0x3815 (.reg .mstore) (ri_mstore_imgAt (o := 0x9e0) rfl)
  xs 0x3818 (.push [0x09, 0xe0] (by decide)) ri_push
  xs 0x3819 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x381a (.reg .pop) ri_pop
  xs 0x381b (.reg (.dup 0)) (ri_dup (by rfl))
  xmo 0x381c (.reg .mload) (ri_mload_imgAt (o := 0x9e0) rfl)
  rw [Bytes.readWord_writeAt_self] at h
  xs 0x381e (.push [0x20] (by decide)) ri_push
  xs 0x381f (.reg .add) ri_add
  xs 0x3820 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x3823 (.push [0x0a, 0x80] (by decide)) ri_push
  xs 0x3824 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x3825 (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0x3827 (.push [0x00] (by decide)) ri_push
  xs 0x3829 (.push [0x04] (by decide)) ri_push
  xs 0x382a (.reg .gas) ri_gas_remaining
  replace h := xa_identity_img (pc' := 0x382b) (i := 0x9e0) (n := 0x64) (o := 0xa80) (z := 0x64)
    (hid.of_rel hb12) (atN hcode (by kernel_rfl)) rfl (by decide) (by decide) (by decide)
    (by decide) hR hW h
  clear hR hW
  obtain ⟨d, L2, h, hk⟩ := h
  rcases hk with ⟨h0, -⟩ | ⟨rfl, b3, G3, M, hsha2, rfl, hR, hW⟩
  · rw [St.self h0 rfl] at h
    xs 0x382e (.push [0x38, 0x33] (by decide)) ri_push
    xji 0x382f 0x3833 hw
    · xdead
    · exact absurd rfl hw
  rw [rli_transfer_copy2] at hR
  have hb23 : BaseRel b2 b3 :=
    ⟨hsha2.stor, hsha2.code, hsha2.addrs, hsha2.logs, hsha2.output, hsha2.error⟩
  clear hsha2
  obtain ⟨img3, hR, hI⟩ := Mem.Reads.forget hR
  have g_k : ∀ o w, WordAt img o w → o + 32 ≤ 0x980 → WordAt img3 o w := fun o w hw ho => by
    rw [hI]; wchainT; exact f_k o w hw ho
  have g_c : WordAt img3 0x900 (Nat.toB256 k) := g_k _ _ hctr (by decide)
  have g_data : Region img3 0xa80 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
      Bytes.toB256 [32]).toBytes ++ (transferSel ++ sevm.caller.toB256.toBytes ++ (rliAmt sevm k).toBytes)) := by
    rw [hI]; exact Region.write_self _ _ _
  clear hI f_c f_k f_a40 f_sel
  xs 0x382e (.push [0x38, 0x33] (by decide)) ri_push
  xji 0x382f 0x3833 hw
  · exact absurd hw (by decide)
  clear hw
  xjd 0x3834
  xs 0x3835 (.reg .pop) ri_pop
  xs 0x3836 (.reg .pop) ri_pop
  -- the `CALL`
  xs 0x3838 (.push [0x20] (by decide)) ri_push
  xs 0x383b (.push [0x0b, 0x40] (by decide)) ri_push
  xs 0x383e (.push [0x0a, 0x80] (by decide)) ri_push
  xmo 0x383f (.reg .mload) (ri_mload_imgAt (o := 0xa80) rfl)
  rw [(Region.word g_data.left).read] at h
  xs 0x3842 (.push [0x0a, 0xa0] (by decide)) ri_push
  xs 0x3844 (.push [0x00] (by decide)) ri_push
  xs 0x3847 (.push [0x09, 0x00] (by decide)) ri_push
  xmo 0x3848 (.reg .mload) (ri_mload_imgAt (o := 0x900) rfl)
  rw [g_c.read] at h
  xs 0x384a (.push [0x03] (by decide)) ri_push
  xs 0x384b (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x384c (.reg .lt) ri_lt
  xs 0x384f (.push [0x38, 0x54] (by decide)) ri_push
  xji 0x3850 0x3854 hw
  · xdead
  clear hw
  xjd 0x3855
  xs 0x3857 (.push [0x00] (by decide)) ri_push
  xs 0x3859 (.push [0xc0] (by decide)) ri_push
  xmo 0x385a (.reg .mstore) (ri_mstore_imgAt (o := 0xc0) rfl)
  xs 0x385c (.push [0x20] (by decide)) ri_push
  xs 0x385e (.push [0xc0] (by decide)) ri_push
  xmo 0x385f (.reg .keccak256) (ri_keccak_imgAt (o := 0xc0) (z := 0x20) rfl rfl)
  rw [keccak_zero] at h
  xs 0x3860 (.reg .add) ri_add
  xw 0x3861 (.reg .sload) ri_sload
  rw [getStorVal_eq, hb23.stor, hb12.stor, hcw] at h
  xs 0x3862 (.reg .gas) ri_gas_remaining
  have hin : (Bytes.writeAt img3 0xc0 (Bytes.toB256 [0]).toBytes).sliceD 0xaa0 0x44 0 =
      exPushData sevm (rliAmt sevm k) :=
    Region.slice (Region.write_other g_data.right (by simp only [B256.length_toBytes]; omega))
      (by simp only [List.length_append, B256.length_toBytes]; rfl)
  replace h := xa_call_img (pc' := 0x3863) (i := 0xaa0) (n := 0x44) (o := 0xb40) (z := 0x20) hfork
    (atN hcode (by kernel_rfl)) rfl (by decide) (by decide) (by decide) (by decide) hR hW h
  clear hR hW
  obtain ⟨d4, flag, L4, h, _, hrd4, hk⟩ := h
  rw [hin] at hk
  xs 0x3866 (.push [0x38, 0x6b] (by decide)) ri_push
  xji 0x3867 0x386b hw
  · xdead
  obtain ⟨hR, hW, hout4, hch⟩ := hk hw
  clear hk hin hw
  rcases hch with ⟨hp, -⟩ | ⟨c, rfl, -, -, hc⟩
  · exact absurd hp hcoin
  xjd 0x386c
  rw [zero_lit] at hc
  exact ⟨b3, c, L4, d4, _, _, hb12.trans hb23, rfl,
    hc.congr_left (fun _ => afterSload_getCode _ _ _ _) (fun _ => afterSload_getStor _ _ _ _)
      (afterSload_logs _ _ _) (afterSload_output _ _ _) (afterSload_accessedAddresses _ _ _),
    fun o w hw h1 h2 => (g_k o w hw h2).write_other (by simp only [B256.length_toBytes]; omega),
    hR, hW, hrd4, h⟩


/-- The `raw_call` test after the `transfer` (`0x386c` → `0x38f7`). -/
theorem xa_rli_tail {sevm : Sevm} {post d : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {S : List B256} (hcode : sevm.code = code) (hid : IdReady sevm d)
    (hR : Mem.Reads M (Bytes.writeAt img 0xb40 (d.returnData.take 0x20))) (hW : Mem.Wf M)
    (hrd : d.returnData.length < 2 ^ 256)
    (h : XAt sevm post 0x386c (St d S M G) L) :
    RawCallOk d.returnData ∧ ∃ b6 M6 img6 G7, BaseRel d b6 ∧ Mem.Reads M6 img6 ∧ Mem.Wf M6 ∧
      (∀ o w, WordAt img o w → (o + 32 ≤ 0x920 ∨ 0x960 ≤ o) →
        (o + 32 ≤ 0xb20 ∨ 0xb60 ≤ o) → WordAt img6 o w) ∧
      XAt sevm post 0x38f7 (St b6 S M6 G7) L := by
  have hj : ∃ nW G5, nW.toNat = (d.returnData.take 32).length ∧
      XAt sevm post 0x387f (St d (nW :: d.returnData.length.toB256 :: Bytes.toB256 [0x20] ::
        S) M G5) L := by
    xs 0x386e (.push [0x20] (by decide)) ri_push
    xs 0x386f (.reg .returndatasize) ri_returndatasize
    xs 0x3870 (.reg (.dup 0)) (ri_dup (by rfl))
    xs 0x3871 (.reg (.dup 2)) (ri_dup (by rfl))
    xs 0x3872 (.reg .gt) ri_gt
    xs 0x3873 (.reg .iszero) ri_iszero
    xs 0x3876 (.push [0x38, 0x7c] (by decide)) ri_push
    xji 0x3877 0x387c hw
    · xs 0x3878 (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x387b (.push [0x38, 0x7e] (by decide)) ri_push
      xjmp 0x387e
      xjd 0x387f
      refine ⟨_, _, ?_, h⟩
      have hlt := gtCheck_ne_zero (ne_of_eqCheck_eq_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrd,
        show (Bytes.toB256 [0x20]).toNat = 32 by decide] at hlt
      rw [List.length_take, B256.toNat_toB256_of_lt hrd]
      omega
    · xjd 0x387d
      xs 0x387e (.reg (.dup 1)) (ri_dup (by rfl))
      xjd 0x387f
      refine ⟨_, _, ?_, h⟩
      have hge := gtCheck_eq_zero (eqCheck_ne_zero_eq hw)
      rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrd,
        show (Bytes.toB256 [0x20]).toNat = 32 by decide] at hge
      rw [List.length_take, show (Bytes.toB256 [0x20]).toNat = 32 by decide]
      omega
  obtain ⟨nW, G5, hn, h⟩ := hj
  xs 0x3880 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x3881 (.reg .pop) ri_pop
  xs 0x3882 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x3883 (.reg .pop) ri_pop
  xs 0x3886 (.push [0x0b, 0x20] (by decide)) ri_push
  xmo 0x3887 (.reg .mstore) (ri_mstore_imgAt (o := 0xb20) rfl)
  xs 0x388a (.push [0x0b, 0x20] (by decide)) ri_push
  xs 0x388b (.reg (.dup 0)) (ri_dup (by rfl))
  xmo 0x388c (.reg .mload) (ri_mload_imgAt (o := 0xb20) rfl)
  rw [(WordAt.write_self _ _ _).read] at h
  xs 0x388e (.push [0x20] (by decide)) ri_push
  xs 0x388f (.reg .add) ri_add
  xs 0x3890 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x3893 (.push [0x09, 0x20] (by decide)) ri_push
  xs 0x3894 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x3895 (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0x3897 (.push [0x00] (by decide)) ri_push
  xs 0x3899 (.push [0x04] (by decide)) ri_push
  xs 0x389a (.reg .gas) ri_gas_remaining
  have hn32 : (d.returnData.take 32).length ≤ 32 := by rw [List.length_take]; omega
  have hsz : (Bytes.toB256 [0x20] + nW).toNat = 32 + (d.returnData.take 32).length := by
    rw [B256.toNat_add, hn, show (Bytes.toB256 [0x20]).toNat = 32 by decide]
    exact Nat.mod_eq_of_lt (by omega)
  replace h := xa_identity_img (pc' := 0x389b) (i := 0xb20) (n := 32 + (d.returnData.take 32).length)
    (o := 0x920) (z := 32 + (d.returnData.take 32).length) hid
    (atN hcode (by kernel_rfl)) rfl (by decide) hsz (by decide) hsz hR hW h
  clear hR hW
  obtain ⟨d, L5, h, hk⟩ := h
  rcases hk with ⟨h0, -⟩ | ⟨rfl, b6, G6, M, hsha3, rfl, hR, hW⟩
  · rw [St.self h0 rfl] at h
    xs 0x389e (.push [0x38, 0xa3] (by decide)) ri_push
    xji 0x389f 0x38a3 hw
    · xdead
    · exact absurd rfl hw
  have r5 : Region (Bytes.writeAt (Bytes.writeAt img 0xb40 (d.returnData.take 32)) 0xb20
      nW.toBytes) 0xb20 (nW.toBytes ++ d.returnData.take 32) :=
    Region.append' (o' := 0xb40) (Region.write_self _ _ _)
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
  have k_keep : ∀ o w, WordAt img o w → (o + 32 ≤ 0x920 ∨ 0x960 ≤ o) →
      (o + 32 ≤ 0xb20 ∨ 0xb60 ≤ o) → WordAt img6 o w := by
    intro o w hw h1 h2
    rw [hI]
    refine WordAt.write_other (WordAt.write_other (WordAt.write_other hw ?_) ?_) ?_ <;>
      simp only [B256.length_toBytes, List.length_take, List.length_append] <;> omega
  have k_buf : Region img6 0x920 (nW.toBytes ++ d.returnData.take 32) := by
    rw [hI]; exact Region.write_self _ _ _
  clear hI
  xs 0x389e (.push [0x38, 0xa3] (by decide)) ri_push
  xji 0x389f 0x38a3 hw
  · exact absurd hw (by decide)
  clear hw
  xjd 0x38a4
  xs 0x38a5 (.reg .pop) ri_pop
  xs 0x38a6 (.reg .pop) ri_pop
  have kr : Region img6 0x940 (d.returnData.take 32) := by
    have := k_buf.right; rwa [B256.length_toBytes] at this
  have kn : WordAt img6 0x920 nW := Region.word k_buf.left
  have hj2 : RawCallOk d.returnData ∧ ∃ M7 G7, Mem.Reads M7 img6 ∧ Mem.Wf M7 ∧
      XAt sevm post 0x38f7 (St b6 S M7 G7) L := by
    xs 0x38a8 (.push [0x00] (by decide)) ri_push
    xs 0x38ab (.push [0x09, 0x20] (by decide)) ri_push
    xmo 0x38ac (.reg .mload) (ri_mload_imgAt (o := 0x920) rfl)
    rw [kn.read] at h
    xs 0x38ad (.reg .gt) ri_gt
    xs 0x38ae (.reg .iszero) ri_iszero
    xs 0x38b1 (.push [0x38, 0xf6] (by decide)) ri_push
    xji 0x38b2 0x38f6 hw
    · have hpos := gtCheck_ne_zero (ne_of_eqCheck_eq_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0x00]).toNat = 0 by decide] at hpos
      clear hw
      xs 0x38b5 (.push [0x09, 0x20] (by decide)) ri_push
      xs 0x38b6 (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x38b8 (.push [0x20] (by decide)) ri_push
      xs 0x38b9 (.reg .add) ri_add
      xmo 0x38ba (.reg .mload) (ri_mload_imgAt (o := 0x940) (by decide))
      xs 0x38bc (.push [0x00] (by decide)) ri_push
      xs 0x38bd (.reg (.dup 2)) (ri_dup (by rfl))
      xmo 0x38be (.reg .mload) (ri_mload_imgAt (o := 0x920) rfl)
      rw [kn.read] at h
      xs 0x38bf (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x38c1 (.push [0x20] (by decide)) ri_push
      xs 0x38c2 (.reg (.swap 0)) (ri_swap (by rfl))
      xs2 0x38c3 (.reg .sgt) ri_sgt
      xs 0x38c4 (.reg .iszero) ri_iszero
      xs 0x38c7 (.push [0x38, 0xcc] (by decide)) ri_push
      xji 0x38c8 0x38cc hw
      · xdead
      clear hw
      xjd 0x38cd
      xs 0x38ce (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x38cf (.reg (.swap 1)) (ri_swap (by rfl))
      xs 0x38d0 (.reg (.swap 0)) (ri_swap (by rfl))
      xs2 0x38d1 (.reg .slt) ri_slt
      xs 0x38d2 (.reg .iszero) ri_iszero
      xs 0x38d5 (.push [0x38, 0xda] (by decide)) ri_push
      xji 0x38d6 0x38da hw
      · xdead
      clear hw
      xjd 0x38db
      xs 0x38dc (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x38de (.push [0x20] (by decide)) ri_push
      xs 0x38df (.reg .sub) ri_sub
      xs 0x38e2 (.push [0x01, 0x00] (by decide)) ri_push
      xs 0x38e3 (.reg .exp) ri_exp
      xs 0x38e4 (.reg (.dup 2)) (ri_dup (by rfl))
      xs 0x38e5 (.reg .div) ri_div
      xs 0x38e6 (.reg (.swap 0)) (ri_swap (by rfl))
      xs 0x38e7 (.reg .pop) ri_pop
      xs 0x38e8 (.reg (.swap 0)) (ri_swap (by rfl))
      xs 0x38e9 (.reg .pop) ri_pop
      xs 0x38ea (.reg (.swap 0)) (ri_swap (by rfl))
      xs 0x38eb (.reg .pop) ri_pop
      xs 0x38ec (.reg .iszero) ri_iszero
      xs 0x38ed (.reg .iszero) ri_iszero
      xs 0x38f0 (.push [0x38, 0xf5] (by decide)) ri_push
      xji 0x38f1 0x38f5 hq
      · xdead
      xjd 0x38f6
      xjd 0x38f7
      refine ⟨.inr ?_, _, _, hR, hW, h⟩
      have hq0 := ne_of_eqCheck_eq_zero (eqCheck_ne_zero_eq hq)
      have hxs : (img6.sliceD 0x940 32 0).length = 32 := List.length_sliceD _ _ _ _
      have hquot := rawCheck_quot (len := nW) (by omega) (by omega) hxs rfl
      rw [hn, kr.head (by omega)] at hquot
      rw [show d.returnData.take (min d.returnData.length 32) = d.returnData.take 32 by
        rw [Nat.min_comm, ← List.take_take, List.take_length]]
      rw [← hquot]
      exact fun e => hq0 (B256.toNat_inj _ _ (by rw [e]; rfl))
    · have hz := gtCheck_eq_zero (eqCheck_ne_zero_eq hw)
      rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0x00]).toNat = 0 by decide] at hz
      xjd 0x38f7
      refine ⟨.inl ?_, _, _, hR, hW, h⟩
      rw [List.length_take] at hn
      omega
  clear hR hW
  obtain ⟨hok, M7, G7, hR, hW, h⟩ := hj2
  exact ⟨hok, b6, M7, img6, G7, hb46, hR, hW, k_keep, h⟩

end Blanc.Lift.Curve3Pool
