import Blanc.Lift.Curve3Pool.Walk.RemoveImbalanceD2
import Blanc.Lift.Curve3Pool.Walk.ExchangePush
import Blanc.Lift.Curve3Pool.Walk.AutoStep

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
  xa 3
  xmo 0x3792 (.reg .mstore) (ri_mstore_imgAt (o := 0x980) rfl)
  xa 2
  xmo 0x37b7 (.reg .mstore) (ri_mstore_imgAt (o := 0x9a0) rfl)
  xa 15
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
  xa 3
  xmo 0x37d4 (.reg .mload) (ri_mload_imgAt (o := 0x980) rfl)
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide), f_a40.read] at h
  xa 11
  xmo 0x37e3 (.reg .mstore) (ri_mstore_imgAt (o := 0xa04) (by decide))
  xa 7
  xmo 0x37ef (.reg .mload) (ri_mload_imgAt (o := 0x900) rfl)
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide), f_c.read] at h
  xa 4
  xji 0x37f7 0x37fb hw
  · xdead
  clear hw
  xa 10
  xmo 0x380a (.reg .mstore) (ri_mstore_imgAt (o := 0xa24) (by decide))
  xa 7
  xmo 0x3815 (.reg .mstore) (ri_mstore_imgAt (o := 0x9e0) rfl)
  xa 4
  xmo 0x381c (.reg .mload) (ri_mload_imgAt (o := 0x9e0) rfl)
  rw [Bytes.readWord_writeAt_self] at h
  xa 9
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
  xa 3
  -- the `CALL`
  xa 3
  xmo 0x383f (.reg .mload) (ri_mload_imgAt (o := 0xa80) rfl)
  rw [(Region.word g_data.left).read] at h
  xa 3
  xmo 0x3848 (.reg .mload) (ri_mload_imgAt (o := 0x900) rfl)
  rw [g_c.read] at h
  xa 4
  xji 0x3850 0x3854 hw
  · xdead
  clear hw
  xa 3
  xmo 0x385a (.reg .mstore) (ri_mstore_imgAt (o := 0xc0) rfl)
  xa 2
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
    xa 7
    xji 0x3877 0x387c hw
    · xs 0x3878 (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x387b (.push [0x38, 0x7e] (by decide)) ri_push
      xjmp 0x387e
      xjd 0x387f
      refine ⟨_, _, ?_, h⟩
      have hlt := B256.lt_of_gtCheck_ne_zero (ne_of_eqCheck_eq_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrd,
        show (Bytes.toB256 [0x20]).toNat = 32 by decide] at hlt
      rw [List.length_take, B256.toNat_toB256_of_lt hrd]
      omega
    · xjd 0x387d
      xa 2
      refine ⟨_, _, ?_, h⟩
      have hge := gtCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrd,
        show (Bytes.toB256 [0x20]).toNat = 32 by decide] at hge
      rw [List.length_take, show (Bytes.toB256 [0x20]).toNat = 32 by decide]
      omega
  obtain ⟨nW, G5, hn, h⟩ := hj
  xa 5
  xmo 0x3887 (.reg .mstore) (ri_mstore_imgAt (o := 0xb20) rfl)
  xa 2
  xmo 0x388c (.reg .mload) (ri_mload_imgAt (o := 0xb20) rfl)
  rw [(WordAt.write_self _ _ _).read] at h
  xa 9
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
  xa 3
  have kr : Region img6 0x940 (d.returnData.take 32) := by
    have := k_buf.right; rwa [B256.length_toBytes] at this
  have kn : WordAt img6 0x920 nW := Region.word k_buf.left
  have hj2 : RawCallOk d.returnData ∧ ∃ M7 G7, Mem.Reads M7 img6 ∧ Mem.Wf M7 ∧
      XAt sevm post 0x38f7 (St b6 S M7 G7) L := by
    xa 2
    xmo 0x38ac (.reg .mload) (ri_mload_imgAt (o := 0x920) rfl)
    rw [kn.read] at h
    xa 3
    xji 0x38b2 0x38f6 hw
    · have hpos := B256.lt_of_gtCheck_ne_zero (ne_of_eqCheck_eq_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0x00]).toNat = 0 by decide] at hpos
      clear hw
      xa 4
      xmo 0x38ba (.reg .mload) (ri_mload_imgAt (o := 0x940) (by decide))
      xa 2
      xmo 0x38be (.reg .mload) (ri_mload_imgAt (o := 0x920) rfl)
      rw [kn.read] at h
      xa 6
      xji 0x38c8 0x38cc hw
      · xdead
      clear hw
      xa 7
      xji 0x38d6 0x38da hw
      · xdead
      clear hw
      xa 5
      xs 0x38e3 (.reg .exp) ri_exp
      xa 11
      xji 0x38f1 0x38f5 hq
      · xdead
      xa 2
      refine ⟨.inr ?_, _, _, hR, hW, h⟩
      have hq0 := ne_of_eqCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hq)
      have hxs : (img6.sliceD 0x940 32 0).length = 32 := List.length_sliceD _ _ _ _
      have hquot := rawCheck_quot (len := nW) (by omega) (by omega) hxs rfl
      rw [hn, kr.head (by omega)] at hquot
      rw [show d.returnData.take (min d.returnData.length 32) = d.returnData.take 32 by
        rw [Nat.min_comm, ← List.take_take, List.take_length]]
      rw [← hquot]
      exact fun e => hq0 (B256.toNat_inj _ _ (by rw [e]; rfl))
    · have hz := gtCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0x00]).toNat = 0 by decide] at hz
      xjd 0x38f7
      refine ⟨.inl ?_, _, _, hR, hW, h⟩
      rw [List.length_take] at hn
      omega
  clear hR hW
  obtain ⟨hok, M7, G7, hR, hW, h⟩ := hj2
  exact ⟨hok, b6, M7, img6, G7, hb46, hR, hW, k_keep, h⟩

end Blanc.Lift.Curve3Pool
