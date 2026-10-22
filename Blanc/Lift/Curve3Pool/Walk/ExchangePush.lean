import Blanc.Lift.Curve3Pool.Walk.ExchangeMid

/-!
# `exchange`, part 7: the `transfer` push, the event and the lock

* `xa_ex_push` (`0x2ab4` → the `raw_call` tail at `0x2b81`): the payload
  `concat(method_id("transfer(address,uint256)"), msg.sender, dy)` built at `0xaa0` with two
  identity copies, then the `CALL` to `coins[j]` with value `0`, input `0xb60[0 : 0x44]` and
  output window `0xc00[0 : 0x20]`; a zero flag reverts;
* `xa_ex_log` (`0x2c0c` → `STOP`): `TokenExchange(msg.sender, i, dx, j, dy)` (`LOG2` over the
  four words at `0xc40`) and the lock cleared.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The `transfer` payload's identity copy at `0xaa0`. -/
theorem transfer_copy2 (img : Bytes) (E C V : B256) :
    ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0xac0 transferSel) 0xac4
      C.toBytes) 0xae4 V.toBytes) 0xaa0 E.toBytes).sliceD 0xaa0 100 0).take 100 =
      E.toBytes ++ (transferSel ++ C.toBytes ++ V.toBytes) := by
  refine Region.copy ?_ (by simp only [List.length_append, B256.length_toBytes]; rfl)
    (by simp only [List.length_append, B256.length_toBytes]; rfl)
  refine Region.append' (o' := 0xac0) (Region.of_word (WordAt.write_self _ _ _))
    (Region.append' (o' := 0xae4) (Region.append' (o' := 0xac4) ?_ ?_ (by rfl)) ?_
      (by simp only [List.length_append, B256.length_toBytes]; rfl))
    (by simp only [B256.length_toBytes])
  · refine Region.write_other (Region.write_other (Region.write_other (Region.write_self _ _ _)
      ?_) ?_) ?_ <;> simp only [transferSel, B256.length_toBytes, List.length_cons,
        List.length_nil] <;> omega
  · refine Region.write_other (Region.of_word (WordAt.write_other (WordAt.write_self _ _ _) ?_))
      ?_ <;> simp only [B256.length_toBytes] <;> omega
  · exact Region.write_other (Region.write_self _ _ _) (by simp only [B256.length_toBytes]; omega)

/-- The `transfer` calldata. -/
abbrev exPushData (sevm : Sevm) (v : B256) : Bytes :=
  transferSel ++ sevm.caller.toB256.toBytes ++ v.toBytes

/-- **The push** (`0x2ab4` → `0x2b81`). -/
theorem xa_ex_push {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {v cw : B256}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hj3 : (exJ sevm).toNat < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hv : WordAt img 0x920 v)
    (hid : IdReady sevm b) (hdepth : 0 < sevm.depth)
    (hcw : (b.getStor sevm.currentTarget).get (coinsBase + exJ sevm) = cw)
    (hcoin : ¬ sevm.benvStat.rules.isPrecomp cw.toAdr)
    (h : XAt sevm post 0x2ab4 (St b [] M G) L) :
    ∃ b' c L' d img' G', BaseRel b b' ∧ L = c :: L' ∧
      ChildOf b' d cw.toAdr (exPushData sevm v) 0 sevm.isStatic c ∧
      WordAt img' 0x920 v ∧
      Mem.Reads d.memory (Bytes.writeAt img' 0xc00 (d.returnData.take 0x20)) ∧
      Mem.Wf d.memory ∧ d.returnData.length < 2 ^ 256 ∧
      XAt sevm post 0x2b81 (St d [] d.memory G') L' := by
  xs 0x2ab6 (.push [0x00] (by decide)) ri_push
  xs 0x2ab8 (.push [0x04] (by decide)) ri_push
  xs 0x2abb (.push [0x0a, 0x40] (by decide)) ri_push
  xmo 0x2abc (.reg .mstore) (ri_mstore_imgAt (o := 0xa40) rfl)
  xs 0x2add (.push [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) ri_push
  xs 0x2ae0 (.push [0x0a, 0x60] (by decide)) ri_push
  xmo 0x2ae1 (.reg .mstore) (ri_mstore_imgAt (o := 0xa60) rfl)
  xs 0x2ae4 (.push [0x0a, 0x40] (by decide)) ri_push
  xs 0x2ae6 (.push [0x04] (by decide)) ri_push
  xs 0x2ae7 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2ae9 (.push [0x20] (by decide)) ri_push
  xs 0x2aea (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0x2aed (.push [0x0a, 0xa0] (by decide)) ri_push
  xs 0x2aee (.reg .add) ri_add
  xs 0x2aef (.reg .add) ri_add
  xs 0x2af0 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2af2 (.push [0x20] (by decide)) ri_push
  xs 0x2af3 (.reg (.dup 5)) (ri_dup (by rfl))
  xs 0x2af4 (.reg .add) ri_add
  xs 0x2af6 (.push [0x00] (by decide)) ri_push
  xs 0x2af8 (.push [0x04] (by decide)) ri_push
  xs 0x2af9 (.reg .gas) ri_gas_remaining
  obtain ⟨img1, hR, hI⟩ := Mem.Reads.forget hR
  have f_v : WordAt img1 0x920 v := by rw [hI]; wchainT; exact hv
  have f_a40 : WordAt img1 0xa40 (Bytes.toB256 [4]) := by rw [hI]; wchainT
  have f_sel : WordAt img1 0xa60 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]) := by
    rw [hI]; wchainT
  clear hI hv
  replace h := xa_identity_img (pc' := 0x2afa) (i := 0xa60) (n := 4) (o := 0xac0) (z := 4) hid
    (atN hcode (by kernel_rfl)) rfl (by decide) (by decide) (by decide) (by decide) hR hW h
  clear hR hW
  obtain ⟨d, L1, h, hk⟩ := h
  rcases hk with ⟨h0, hgas⟩ | ⟨rfl, b2, G2, M, hsha, rfl, hR, hW⟩
  · have hz := hgas rfl hdepth (by decide)
    obtain ⟨_, s, -⟩ := xa_next (n := .reg .pop) (atN hcode (by kernel_rfl)) (by nofun) h
    exact absurd (gasLeft_of_run_pop s) (by rw [hz]; decide)
  have hsel4 : (img1.sliceD 0xa60 4 0).take 4 = transferSel := by
    rw [f_sel.prefix (by decide)]; decide
  rw [hsel4] at hR
  have hb12 : BaseRel b b2 := ⟨hsha.stor, hsha.code, hsha.addrs, hsha.logs, hsha.output, hsha.error⟩
  clear hsha hsel4
  xs 0x2afb (.reg .pop) ri_pop
  xs 0x2afc (.reg .pop) ri_pop
  xs 0x2afd (.reg (.dup 0)) (ri_dup (by rfl))
  xmo 0x2afe (.reg .mload) (ri_mload_imgAt (o := 0xa40) rfl)
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide), f_a40.read] at h
  xs 0x2aff (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2b00 (.reg .add) ri_add
  xs 0x2b01 (.reg (.swap 1)) (ri_swap (by rfl))
  xs 0x2b02 (.reg .pop) ri_pop
  xs 0x2b03 (.reg .pop) ri_pop
  xs 0x2b04 (.reg .caller) ri_caller
  xs 0x2b06 (.push [0x20] (by decide)) ri_push
  xs 0x2b07 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2b0a (.push [0x0a, 0xa0] (by decide)) ri_push
  xs 0x2b0b (.reg .add) ri_add
  xs 0x2b0c (.reg .add) ri_add
  xmo 0x2b0d (.reg .mstore) (ri_mstore_imgAt (o := 0xac4) (by decide))
  xs 0x2b0f (.push [0x20] (by decide)) ri_push
  xs 0x2b10 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x2b11 (.reg .add) ri_add
  xs 0x2b12 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2b13 (.reg .pop) ri_pop
  xs 0x2b16 (.push [0x09, 0x20] (by decide)) ri_push
  xmo 0x2b17 (.reg .mload) (ri_mload_imgAt (o := 0x920) rfl)
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide), f_v.read] at h
  xs 0x2b19 (.push [0x20] (by decide)) ri_push
  xs 0x2b1a (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2b1d (.push [0x0a, 0xa0] (by decide)) ri_push
  xs 0x2b1e (.reg .add) ri_add
  xs 0x2b1f (.reg .add) ri_add
  xmo 0x2b20 (.reg .mstore) (ri_mstore_imgAt (o := 0xae4) (by decide))
  xs 0x2b22 (.push [0x20] (by decide)) ri_push
  xs 0x2b23 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x2b24 (.reg .add) ri_add
  xs 0x2b25 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2b26 (.reg .pop) ri_pop
  xs 0x2b27 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2b2a (.push [0x0a, 0xa0] (by decide)) ri_push
  xmo 0x2b2b (.reg .mstore) (ri_mstore_imgAt (o := 0xaa0) rfl)
  xs 0x2b2e (.push [0x0a, 0xa0] (by decide)) ri_push
  xs 0x2b2f (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2b30 (.reg .pop) ri_pop
  xs 0x2b31 (.reg (.dup 0)) (ri_dup (by rfl))
  xmo 0x2b32 (.reg .mload) (ri_mload_imgAt (o := 0xaa0) rfl)
  rw [Bytes.readWord_writeAt_self] at h
  xs 0x2b34 (.push [0x20] (by decide)) ri_push
  xs 0x2b35 (.reg .add) ri_add
  xs 0x2b36 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2b39 (.push [0x0b, 0x40] (by decide)) ri_push
  xs 0x2b3a (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2b3b (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0x2b3d (.push [0x00] (by decide)) ri_push
  xs 0x2b3f (.push [0x04] (by decide)) ri_push
  xs 0x2b40 (.reg .gas) ri_gas_remaining
  replace h := xa_identity_img (pc' := 0x2b41) (i := 0xaa0) (n := 0x64) (o := 0xb40) (z := 0x64)
    (hid.of_rel hb12) (atN hcode (by kernel_rfl)) rfl (by decide) (by decide) (by decide)
    (by decide) hR hW h
  clear hR hW
  obtain ⟨d, L2, h, hk⟩ := h
  rcases hk with ⟨h0, -⟩ | ⟨rfl, b3, G3, M, hsha2, rfl, hR, hW⟩
  · rw [St.self h0 rfl] at h
    xs 0x2b44 (.push [0x2b, 0x49] (by decide)) ri_push
    xji 0x2b45 0x2b49 hw
    · xdead
    · exact absurd rfl hw
  rw [transfer_copy2] at hR
  have hb23 : BaseRel b2 b3 :=
    ⟨hsha2.stor, hsha2.code, hsha2.addrs, hsha2.logs, hsha2.output, hsha2.error⟩
  clear hsha2
  obtain ⟨img3, hR, hI⟩ := Mem.Reads.forget hR
  have g_v : WordAt img3 0x920 v := by rw [hI]; wchainT; exact f_v
  have g_data : Region img3 0xb40 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
      Bytes.toB256 [32]).toBytes ++ (transferSel ++ sevm.caller.toB256.toBytes ++ v.toBytes)) := by
    rw [hI]; exact Region.write_self _ _ _
  clear hI f_v f_a40 f_sel
  xs 0x2b44 (.push [0x2b, 0x49] (by decide)) ri_push
  xji 0x2b45 0x2b49 hw
  · exact absurd hw (by decide)
  clear hw
  xjd 0x2b4a
  xs 0x2b4b (.reg .pop) ri_pop
  xs 0x2b4c (.reg .pop) ri_pop
  -- the `CALL`
  xs 0x2b4e (.push [0x20] (by decide)) ri_push
  xs 0x2b51 (.push [0x0c, 0x00] (by decide)) ri_push
  xs 0x2b54 (.push [0x0b, 0x40] (by decide)) ri_push
  xmo 0x2b55 (.reg .mload) (ri_mload_imgAt (o := 0xb40) rfl)
  rw [(Region.word g_data.left).read] at h
  xs 0x2b58 (.push [0x0b, 0x60] (by decide)) ri_push
  xs 0x2b5a (.push [0x00] (by decide)) ri_push
  xs 0x2b5c (.push [0x24] (by decide)) ri_push
  xs 0x2b5d (.reg .calldataload) ri_calldataload
  xs 0x2b5f (.push [0x03] (by decide)) ri_push
  xs 0x2b60 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x2b61 (.reg .lt) ri_lt
  xs 0x2b64 (.push [0x2b, 0x69] (by decide)) ri_push
  xji 0x2b65 0x2b69 hw
  · xdead
  clear hw
  xjd 0x2b6a
  xs 0x2b6c (.push [0x00] (by decide)) ri_push
  xs 0x2b6e (.push [0xc0] (by decide)) ri_push
  xmo 0x2b6f (.reg .mstore) (ri_mstore_imgAt (o := 0xc0) rfl)
  xs 0x2b71 (.push [0x20] (by decide)) ri_push
  xs 0x2b73 (.push [0xc0] (by decide)) ri_push
  xmo 0x2b74 (.reg .keccak256) (ri_keccak_imgAt (o := 0xc0) (z := 0x20) rfl rfl)
  rw [keccak_zero] at h
  xs 0x2b75 (.reg .add) ri_add
  xw 0x2b76 (.reg .sload) ri_sload
  rw [getStorVal_eq, hb23.stor, hb12.stor, hcw] at h
  xs 0x2b77 (.reg .gas) ri_gas_remaining
  have hin : (Bytes.writeAt img3 0xc0 (Bytes.toB256 [0]).toBytes).sliceD 0xb60 0x44 0 =
      exPushData sevm v :=
    Region.slice (Region.write_other g_data.right (by simp only [B256.length_toBytes]; omega))
      (by simp only [List.length_append, B256.length_toBytes]; rfl)
  replace h := xa_call_img (pc' := 0x2b78) (i := 0xb60) (n := 0x44) (o := 0xc00) (z := 0x20) hfork
    (atN hcode (by kernel_rfl)) rfl (by decide) (by decide) (by decide) (by decide) hR hW h
  clear hR hW
  obtain ⟨d4, flag, L4, h, _, hrd4, hk⟩ := h
  rw [hin] at hk
  xs 0x2b7b (.push [0x2b, 0x80] (by decide)) ri_push
  xji 0x2b7c 0x2b80 hw
  · xdead
  obtain ⟨hR, hW, hout4, hch⟩ := hk hw
  clear hk hin hw
  rcases hch with ⟨hp, -⟩ | ⟨c, rfl, -, -, hc⟩
  · exact absurd hp hcoin
  xjd 0x2b81
  rw [zero_lit] at hc
  exact ⟨b3, c, L4, d4, _, _, hb12.trans hb23, rfl,
    hc.congr_left (fun _ => afterSload_getCode _ _ _ _) (fun _ => afterSload_getStor _ _ _ _)
      (afterSload_logs _ _ _) (afterSload_output _ _ _) (afterSload_accessedAddresses _ _ _),
    g_v.write_other (by simp only [B256.length_toBytes]; omega), hR, hW, hrd4, h⟩

/-- The `TokenExchange` topic word. -/
abbrev exTopic : B256 := Bytes.toB256 [0x8b, 0x3e, 0x96, 0xf2, 0xb8, 0x89, 0xfa, 0x77, 0x1c, 0x53,
  0xc9, 0x81, 0xb4, 0x0d, 0xaf, 0x00, 0x5f, 0x63, 0xf6, 0x37, 0xf1, 0x86, 0x9f, 0x70, 0x70, 0x52,
  0xd1, 0x5a, 0x3d, 0xd9, 0x71, 0x40]

/-- **The event and the lock** (`0x2c0c` → `STOP`). -/
theorem xa_ex_log {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {v : B256} (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hv : WordAt img 0x920 v)
    (h : XAt sevm post 0x2c0c (St b [] M G) L) :
    L = [] ∧
      (∀ x, (post.getStor sevm.currentTarget).get x =
        ((b.getStor sevm.currentTarget).set lockSlot 0).get x) ∧
      post.logs = b.logs ++ [⟨sevm.currentTarget, [exTopic, sevm.caller.toB256],
        (exI sevm).toBytes ++ (exDx sevm).toBytes ++ (exJ sevm).toBytes ++ v.toBytes⟩] ∧
      post.output = b.output := by
  xs 0x2c0e (.push [0x04] (by decide)) ri_push
  xs 0x2c0f (.reg .calldataload) ri_calldataload
  xs 0x2c12 (.push [0x0c, 0x40] (by decide)) ri_push
  xmo 0x2c13 (.reg .mstore) (ri_mstore_imgAt (o := 0xc40) rfl)
  xs 0x2c15 (.push [0x44] (by decide)) ri_push
  xs 0x2c16 (.reg .calldataload) ri_calldataload
  xs 0x2c19 (.push [0x0c, 0x60] (by decide)) ri_push
  xmo 0x2c1a (.reg .mstore) (ri_mstore_imgAt (o := 0xc60) rfl)
  xs 0x2c1c (.push [0x24] (by decide)) ri_push
  xs 0x2c1d (.reg .calldataload) ri_calldataload
  xs 0x2c20 (.push [0x0c, 0x80] (by decide)) ri_push
  xmo 0x2c21 (.reg .mstore) (ri_mstore_imgAt (o := 0xc80) rfl)
  xs 0x2c24 (.push [0x09, 0x20] (by decide)) ri_push
  xmo 0x2c25 (.reg .mload) (ri_mload_imgAt (o := 0x920) rfl)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint] at h
  rw [hv.read] at h
  xs 0x2c28 (.push [0x0c, 0xa0] (by decide)) ri_push
  xmo 0x2c29 (.reg .mstore) (ri_mstore_imgAt (o := 0xca0) rfl)
  xs 0x2c2a (.reg .caller) ri_caller
  xs 0x2c4b (.push [0x8b, 0x3e, 0x96, 0xf2, 0xb8, 0x89, 0xfa, 0x77, 0x1c, 0x53, 0xc9, 0x81, 0xb4, 0x0d, 0xaf, 0x00, 0x5f, 0x63, 0xf6, 0x37, 0xf1, 0x86, 0x9f, 0x70, 0x70, 0x52, 0xd1, 0x5a, 0x3d, 0xd9, 0x71, 0x40] (by decide)) ri_push
  xs 0x2c4d (.push [0x80] (by decide)) ri_push
  xs 0x2c50 (.push [0x0c, 0x40] (by decide)) ri_push
  obtain ⟨img2, hR2, hI⟩ := Mem.Reads.forget hR
  have hdata : Region img2 0xc40 ((exI sevm).toBytes ++ (exDx sevm).toBytes ++ (exJ sevm).toBytes ++
      v.toBytes) := by
    rw [hI]
    refine Region.append' (o' := 0xca0) (Region.append' (o' := 0xc80)
      (Region.append' (o' := 0xc60) ?_ ?_ ?_) ?_ ?_) ?_ ?_
    all_goals first
      | simp only [List.length_append, B256.length_toBytes]
      | exact Region.of_word (by wchain)
  clear hI hR
  replace h := xa_nextAt (n := .reg (.log 2)) (pc' := 0x2c51) (atN hcode (by kernel_rfl))
    (by nofun) (by rfl) h
  obtain ⟨_, s, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_log2_post s
  clear s
  rw [Mem.Reads.read hR2, show (Bytes.toB256 [0x0c, 0x40]).toNat = 0xc40 from rfl,
    show (Bytes.toB256 [0x80]).toNat = 0x80 from rfl,
    hdata.slice (by simp only [List.length_append, B256.length_toBytes])] at h
  xs 0x2c53 (.push [0x00] (by decide)) ri_push
  xs 0x2c57 (.push [0xff, 0xff, 0xff] (by decide)) ri_push
  xw 0x2c58 (.reg .sstore) ri_sstore
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
