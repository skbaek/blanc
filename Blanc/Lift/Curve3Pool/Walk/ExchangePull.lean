import Blanc.Lift.Curve3Pool.Walk.ExchangeMid

/-!
# `exchange`, part 3: the `transferFrom` pull

From `0x2517`: the `raw_call` payload `concat(method_id("transferFrom(address,address,uint256)"),
msg.sender, self, dx)` built at `0x520` with two identity-precompile copies (the second checked),
then the `CALL` to `input_coin` with value `0`, input `0x600[0 : 0x64]` and output window
`0x6c0[0 : 0x20]`; a zero flag reverts (`xa_ex_pull`, up to the `raw_call` tail at `0x25dc`).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The `transferFrom` payload's identity copy: the length word, then the selector, the sender,
the pool and the amount, as the five writes left them. -/
theorem transferFrom_copy (img : Bytes) (E C1 C2 V : B256) :
    ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x540
      transferFromSel) 0x544 C1.toBytes) 0x564 C2.toBytes) 0x584 V.toBytes) 0x520
      E.toBytes).sliceD 0x520 0x84 0).take 0x84 =
      E.toBytes ++ (transferFromSel ++ C1.toBytes ++ C2.toBytes ++ V.toBytes) := by
  refine Region.copy ?_ (by simp only [List.length_append, B256.length_toBytes]; rfl)
    (by simp only [List.length_append, B256.length_toBytes]; rfl)
  refine Region.append' (o' := 0x540) (Region.of_word (WordAt.write_self _ _ _))
    (Region.append' (o' := 0x584) (Region.append' (o' := 0x564)
      (Region.append' (o' := 0x544) ?_ ?_ (by rfl)) ?_
      (by simp only [List.length_append, B256.length_toBytes]; rfl)) ?_
      (by simp only [List.length_append, B256.length_toBytes]; rfl))
    (by simp only [B256.length_toBytes])
  · refine Region.write_other (Region.write_other (Region.write_other (Region.write_other
      (Region.write_self _ _ _) ?_) ?_) ?_) ?_ <;>
      simp only [transferFromSel, B256.length_toBytes, List.length_cons, List.length_nil] <;> omega
  · refine Region.write_other (Region.write_other (Region.write_other (Region.write_self _ _ _)
      ?_) ?_) ?_ <;> simp only [B256.length_toBytes] <;> omega
  · refine Region.write_other (Region.write_other (Region.write_self _ _ _) ?_) ?_ <;>
      simp only [B256.length_toBytes] <;> omega
  · exact Region.write_other (Region.write_self _ _ _) (by simp only [B256.length_toBytes]; omega)

/-- The `transferFrom` calldata. -/
abbrev exPullData (sevm : Sevm) : Bytes :=
  transferFromSel ++ sevm.caller.toB256.toBytes ++ sevm.currentTarget.toB256.toBytes ++
    (exDx sevm).toBytes

set_option hygiene false in
/-- The pull payload's middle (`0x255e` → `0x25b3`): the sender, the pool and `dx` written after
the selector copy, the length word, and the operands of the checked identity copy. -/
macro "ex_pull_mid" : tactic => `(tactic| (
    xs 0x255f (.reg .pop) ri_pop
    xs 0x2560 (.reg .pop) ri_pop
    xs 0x2561 (.reg (.dup 0)) (ri_dup (by rfl))
    xmo 0x2562 (.reg .mload) (ri_mload_imgAt (o := 0x4c0) rfl)
    first
      | rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide), f_4c0.read] at h
      | rw [f_4c0.read] at h
    xs 0x2563 (.reg (.dup 2)) (ri_dup (by rfl))
    xs 0x2564 (.reg .add) ri_add
    xs 0x2565 (.reg (.swap 1)) (ri_swap (by rfl))
    xs 0x2566 (.reg .pop) ri_pop
    xs 0x2567 (.reg .pop) ri_pop
    xs 0x2568 (.reg .caller) ri_caller
    xs 0x256a (.push [0x20] (by decide)) ri_push
    xs 0x256b (.reg (.dup 2)) (ri_dup (by rfl))
    xs 0x256e (.push [0x05, 0x20] (by decide)) ri_push
    xs 0x256f (.reg .add) ri_add
    xs 0x2570 (.reg .add) ri_add
    xmo 0x2571 (.reg .mstore) (ri_mstore_imgAt (o := 0x544) (by decide))
    xs 0x2573 (.push [0x20] (by decide)) ri_push
    xs 0x2574 (.reg (.dup 1)) (ri_dup (by rfl))
    xs 0x2575 (.reg .add) ri_add
    xs 0x2576 (.reg (.swap 0)) (ri_swap (by rfl))
    xs 0x2577 (.reg .pop) ri_pop
    xs 0x2578 (.reg .address) ri_address
    xs 0x257a (.push [0x20] (by decide)) ri_push
    xs 0x257b (.reg (.dup 2)) (ri_dup (by rfl))
    xs 0x257e (.push [0x05, 0x20] (by decide)) ri_push
    xs 0x257f (.reg .add) ri_add
    xs 0x2580 (.reg .add) ri_add
    xmo 0x2581 (.reg .mstore) (ri_mstore_imgAt (o := 0x564) (by decide))
    xs 0x2583 (.push [0x20] (by decide)) ri_push
    xs 0x2584 (.reg (.dup 1)) (ri_dup (by rfl))
    xs 0x2585 (.reg .add) ri_add
    xs 0x2586 (.reg (.swap 0)) (ri_swap (by rfl))
    xs 0x2587 (.reg .pop) ri_pop
    xs 0x2589 (.push [0x44] (by decide)) ri_push
    xs 0x258a (.reg .calldataload) ri_calldataload
    xs 0x258c (.push [0x20] (by decide)) ri_push
    xs 0x258d (.reg (.dup 2)) (ri_dup (by rfl))
    xs 0x2590 (.push [0x05, 0x20] (by decide)) ri_push
    xs 0x2591 (.reg .add) ri_add
    xs 0x2592 (.reg .add) ri_add
    xmo 0x2593 (.reg .mstore) (ri_mstore_imgAt (o := 0x584) (by decide))
    xs 0x2595 (.push [0x20] (by decide)) ri_push
    xs 0x2596 (.reg (.dup 1)) (ri_dup (by rfl))
    xs 0x2597 (.reg .add) ri_add
    xs 0x2598 (.reg (.swap 0)) (ri_swap (by rfl))
    xs 0x2599 (.reg .pop) ri_pop
    xs 0x259a (.reg (.dup 0)) (ri_dup (by rfl))
    xs 0x259d (.push [0x05, 0x20] (by decide)) ri_push
    xmo 0x259e (.reg .mstore) (ri_mstore_imgAt (o := 0x520) rfl)
    xs 0x25a1 (.push [0x05, 0x20] (by decide)) ri_push
    xs 0x25a2 (.reg (.swap 0)) (ri_swap (by rfl))
    xs 0x25a3 (.reg .pop) ri_pop
    xs 0x25a4 (.reg (.dup 0)) (ri_dup (by rfl))
    xmo 0x25a5 (.reg .mload) (ri_mload_imgAt (o := 0x520) rfl)
    rw [Bytes.readWord_writeAt_self] at h
    xs 0x25a7 (.push [0x20] (by decide)) ri_push
    xs 0x25a8 (.reg .add) ri_add
    xs 0x25a9 (.reg (.dup 0)) (ri_dup (by rfl))
    xs 0x25ac (.push [0x05, 0xe0] (by decide)) ri_push
    xs 0x25ad (.reg (.dup 2)) (ri_dup (by rfl))
    xs 0x25ae (.reg (.dup 4)) (ri_dup (by rfl))
    xs 0x25b0 (.push [0x00] (by decide)) ri_push
    xs 0x25b2 (.push [0x04] (by decide)) ri_push
    xs 0x25b3 (.reg .gas) ri_gas_remaining))

/-- **The pull** (`0x2517` → the `raw_call` tail at `0x25dc`). -/
theorem xa_ex_pull {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {B X : Nat → B256} {D C : B256}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hF : ExFrame img B X D C)
    (hid : IdReady sevm b) (hcoin : ¬ sevm.benvStat.rules.isPrecomp C.toAdr)
    (h : XAt sevm post 0x2517 (St b [] M G) L) :
    0 < sevm.depth ∧ ∃ b' c L' d img' G', BaseRel b b' ∧ L = c :: L' ∧
      ChildOf b' d C.toAdr (exPullData sevm) 0 sevm.isStatic c ∧
      ExFrame img' B X D C ∧
      Mem.Reads d.memory (Bytes.writeAt img' 0x6c0 (d.returnData.take 0x20)) ∧
      Mem.Wf d.memory ∧ d.returnData.length < 2 ^ 256 ∧
      XAt sevm post 0x25dc (St d [] d.memory G') L' := by
  xjd 0x2518
  xs 0x251a (.push [0x00] (by decide)) ri_push
  xs 0x251c (.push [0x04] (by decide)) ri_push
  xs 0x251f (.push [0x04, 0xc0] (by decide)) ri_push
  xmo 0x2520 (.reg .mstore) (ri_mstore_imgAt (o := 0x4c0) rfl)
  xs 0x2541 (.push [0x23, 0xb8, 0x72, 0xdd, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) ri_push
  xs 0x2544 (.push [0x04, 0xe0] (by decide)) ri_push
  xmo 0x2545 (.reg .mstore) (ri_mstore_imgAt (o := 0x4e0) rfl)
  xs 0x2548 (.push [0x04, 0xc0] (by decide)) ri_push
  xs 0x254a (.push [0x04] (by decide)) ri_push
  xs 0x254b (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x254d (.push [0x20] (by decide)) ri_push
  xs 0x254e (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0x2551 (.push [0x05, 0x20] (by decide)) ri_push
  xs 0x2552 (.reg .add) ri_add
  xs 0x2553 (.reg .add) ri_add
  xs 0x2554 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2556 (.push [0x20] (by decide)) ri_push
  xs 0x2557 (.reg (.dup 5)) (ri_dup (by rfl))
  xs 0x2558 (.reg .add) ri_add
  xs 0x255a (.push [0x00] (by decide)) ri_push
  xs 0x255c (.push [0x04] (by decide)) ri_push
  xs 0x255d (.reg .gas) ri_gas_remaining
  obtain ⟨img1, hR, hI⟩ := Mem.Reads.forget hR
  have f_F : ExFrame img1 B X D C := hF.mono fun o v hv ho => by
    rw [hI]; exact (hv.write_other (by simp only [B256.length_toBytes]; omega)).write_other
      (by simp only [B256.length_toBytes]; omega)
  have f_4c0 : WordAt img1 0x4c0 (Bytes.toB256 [4]) := by rw [hI]; wchain
  have f_sel : WordAt img1 0x4e0 (Bytes.toB256 [0x23, 0xb8, 0x72, 0xdd, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]) := by
    rw [hI]; wchain
  clear hI hF
  by_cases hd0 : sevm.depth = 0
  · obtain ⟨L1, M, G2, h, hR, hW⟩ := xa_identity_depth0 hid hd0 (atN hcode (by kernel_rfl)) rfl hR hW h
    ex_pull_mid
    obtain ⟨L2, M, G3, h, -, -⟩ := xa_identity_depth0 (hid.of_rel (BaseRel.withReturnData _ _)) hd0
      (atN hcode (by kernel_rfl)) rfl hR hW h
    xs 0x25b7 (.push [0x25, 0xbc] (by decide)) ri_push
    xji 0x25b8 0x25bc hw
    · xdead
    · exact absurd rfl hw
  have hdepth : 0 < sevm.depth := Nat.pos_of_ne_zero hd0
  replace h := xa_identity_img (pc' := 0x255e) (i := 0x4e0) (n := 4) (o := 0x540) (z := 4) hid
    (atN hcode (by kernel_rfl)) rfl (by decide) (by decide) (by decide) (by decide) hR hW h
  clear hR hW
  obtain ⟨d, L1, h, hk⟩ := h
  rcases hk with ⟨h0, hgas⟩ | ⟨rfl, b2, G2, M, hsha, rfl, hR, hW⟩
  · have hz := hgas rfl hdepth (by decide)
    obtain ⟨_, s, -⟩ := xa_next (n := .reg .pop) (atN hcode (by kernel_rfl)) (by nofun) h
    exact absurd (gasLeft_of_run_pop s) (by rw [hz]; decide)
  have hsel4 : (img1.sliceD 0x4e0 4 0).take 4 = transferFromSel := by
    rw [f_sel.prefix (by decide)]; decide
  rw [hsel4] at hR
  have hb12 : BaseRel b b2 := ⟨hsha.stor, hsha.code, hsha.addrs, hsha.logs, hsha.output, hsha.error⟩
  clear hsha hsel4
  ex_pull_mid
  replace h := xa_identity_img (pc' := 0x25b4) (i := 0x520) (n := 0x84) (o := 0x5e0) (z := 0x84)
    (hid.of_rel hb12) (atN hcode (by kernel_rfl)) rfl (by decide) (by decide) (by decide)
    (by decide) hR hW h
  clear hR hW
  obtain ⟨d, L2, h, hk⟩ := h
  rcases hk with ⟨h0, -⟩ | ⟨rfl, b3, G3, M, hsha2, rfl, hR, hW⟩
  · rw [St.self h0 rfl] at h
    xs 0x25b7 (.push [0x25, 0xbc] (by decide)) ri_push
    xji 0x25b8 0x25bc hw
    · xdead
    · exact absurd rfl hw
  rw [transferFrom_copy] at hR
  have hb23 : BaseRel b2 b3 :=
    ⟨hsha2.stor, hsha2.code, hsha2.addrs, hsha2.logs, hsha2.output, hsha2.error⟩
  clear hsha2
  obtain ⟨img3, hR, hI⟩ := Mem.Reads.forget hR
  have g_F : ExFrame img3 B X D C := f_F.mono fun o v hv ho => by
    rw [hI]
    refine WordAt.write_other (WordAt.write_other (WordAt.write_other (WordAt.write_other
      (WordAt.write_other (WordAt.write_other hv ?_) ?_) ?_) ?_) ?_) ?_ <;>
      simp only [B256.length_toBytes, transferFromSel, List.length_append, List.length_cons,
        List.length_nil] <;> omega
  have g_C : WordAt img3 0x3a0 C := g_F.coin
  have g_data : Region img3 0x5e0 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
      Bytes.toB256 [32] + Bytes.toB256 [32]).toBytes ++ (transferFromSel ++
      sevm.caller.toB256.toBytes ++ sevm.currentTarget.toB256.toBytes ++ (exDx sevm).toBytes)) := by
    rw [hI]; exact Region.write_self _ _ _
  clear hI f_F f_4c0 f_sel
  xs 0x25b7 (.push [0x25, 0xbc] (by decide)) ri_push
  xji 0x25b8 0x25bc hw
  · exact absurd hw (by decide)
  clear hw
  xjd 0x25bd
  xs 0x25be (.reg .pop) ri_pop
  xs 0x25bf (.reg .pop) ri_pop
  -- the `CALL`
  xs 0x25c1 (.push [0x20] (by decide)) ri_push
  xs 0x25c4 (.push [0x06, 0xc0] (by decide)) ri_push
  xs 0x25c7 (.push [0x05, 0xe0] (by decide)) ri_push
  xmo 0x25c8 (.reg .mload) (ri_mload_imgAt (o := 0x5e0) rfl)
  rw [(Region.word g_data.left).read] at h
  xs 0x25cb (.push [0x06, 0x00] (by decide)) ri_push
  xs 0x25cd (.push [0x00] (by decide)) ri_push
  xs 0x25d0 (.push [0x03, 0xa0] (by decide)) ri_push
  xmo 0x25d1 (.reg .mload) (ri_mload_imgAt (o := 0x3a0) rfl)
  rw [g_C.read] at h
  xs 0x25d2 (.reg .gas) ri_gas_remaining
  have hin : img3.sliceD 0x600 0x64 0 = exPullData sevm :=
    Region.slice g_data.right (by simp only [List.length_append, B256.length_toBytes]; rfl)
  replace h := xa_call_img (pc' := 0x25d3) (i := 0x600) (n := 0x64) (o := 0x6c0) (z := 0x20) hfork
    (atN hcode (by kernel_rfl)) rfl (by decide) (by decide) (by decide) (by decide) hR hW h
  clear hR hW
  obtain ⟨d4, flag, L4, h, _, hrd4, hk⟩ := h
  rw [hin] at hk
  xs 0x25d6 (.push [0x25, 0xdb] (by decide)) ri_push
  xji 0x25d7 0x25db hw
  · xdead
  obtain ⟨hR, hW, hout4, hch⟩ := hk hw
  clear hk hin hw
  rcases hch with ⟨hp, -⟩ | ⟨c, rfl, -, -, hc⟩
  · exact absurd hp hcoin
  xjd 0x25dc
  rw [zero_lit] at hc
  exact ⟨hdepth, b3, c, L4, d4, img3, _, hb12.trans hb23, rfl,
    hc.congr_left (fun _ => rfl) (fun _ => rfl) rfl rfl rfl, g_F, hR, hW, hrd4, h⟩

end Blanc.Lift.Curve3Pool
