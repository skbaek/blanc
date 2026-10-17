import Blanc.Lift.Curve3Pool.Walk.ExchangePre
import Blanc.Lift.Curve3Pool.Walk.AdminBalances

/-!
# `exchange`, part 2: after `_xp_mem`, up to the pull

From `_xp_mem`'s return tag (`0x2458`): `xp` parked at `0x320`, the nine frame words restored,
`xp` copied to `0x200`, `dx_w_fee = dx` at `0x380`, `input_coin = coins[i]` at `0x3a0` (with the
`i < 3` check), then the `i == FEE_INDEX` test (`xa_ex_xp`); for `i == 2`, the first
`balanceOf(self)` `STATICCALL` with its answer at `0x380` (`xa_ex_bal1`).

`ExFrame` is the frame's memory that the rest of the walk reads: `rates` at `0x140`,
`old_balances` at `0x1a0`, `xp` at `0x200`, `dx_w_fee` at `0x380` and `input_coin` at `0x3a0`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- `RATES[k]` as the runtime pushes it. -/
abbrev exRate (k : Nat) : B256 := if k = 0 then exR0 else exR1

/-- Three words as a function of the index. -/
abbrev exW3 (a b c : B256) (k : Nat) : B256 := if k = 0 then a else if k = 1 then b else c

/-- `i`, the first argument word. -/
abbrev exI (sevm : Sevm) : B256 := Sevm.dataWord sevm (Bytes.toB256 [0x04])

/-- `j`, the second argument word. -/
abbrev exJ (sevm : Sevm) : B256 := Sevm.dataWord sevm (Bytes.toB256 [0x24])

/-- `dx`, the third argument word. -/
abbrev exDx (sevm : Sevm) : B256 := Sevm.dataWord sevm (Bytes.toB256 [0x44])

/-- `min_dy`, the fourth argument word. -/
abbrev exMinDy (sevm : Sevm) : B256 := Sevm.dataWord sevm (Bytes.toB256 [0x64])

/-- The frame words of `exchange` the walk reads after `_xp_mem`. -/
structure ExFrame (img : Bytes) (B X : Nat → B256) (D C : B256) : Prop where
  rate : ∀ k, k < 3 → WordAt img (0x140 + 32 * k) (exRate k)
  old : ∀ k, k < 3 → WordAt img (0x1a0 + 32 * k) (B k)
  xp : ∀ k, k < 3 → WordAt img (0x200 + 32 * k) (X k)
  dx : WordAt img 0x380 D
  coin : WordAt img 0x3a0 C

theorem ExFrame.mono {img img' : Bytes} {B X : Nat → B256} {D C : B256}
    (h : ExFrame img B X D C) (hk : ∀ o v, WordAt img o v → o + 32 ≤ 0x3c0 → WordAt img' o v) :
    ExFrame img' B X D C :=
  ⟨fun k hk' => hk _ _ (h.rate k hk') (by omega), fun k hk' => hk _ _ (h.old k hk') (by omega),
    fun k hk' => hk _ _ (h.xp k hk') (by omega), hk _ _ h.dx (by omega),
    hk _ _ h.coin (by omega)⟩

/-- An array element's offset: `base + 32 * k` for an index word `k < 3`. -/
theorem ex_off {k bw : B256} {base : Nat} (hk : k.toNat < 3) (hb : bw.toNat = base)
    (hb' : base < 2 ^ 255) :
    (Bytes.toB256 [0x20] * k + bw).toNat = base + 32 * k.toNat := by
  rw [B256.toNat_add, B256.toNat_mul, hb, show (Bytes.toB256 [0x20]).toNat = 32 by decide]
  show (32 * k.toNat % 2 ^ 256 + base) % 2 ^ 256 = base + 32 * k.toNat
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem ex_lt3 {k : B256} (h : B256.ltCheck k (Bytes.toB256 [0x03]) ≠ 0) : k.toNat < 3 := by
  by_contra hn
  exact h (ltCheck_eq_zero_of_le (by
    rw [show (Bytes.toB256 [0x03]).toNat = 3 by decide]; omega))

/-- **After `_xp_mem`** (`0x2458` → the `i == 2` test). -/
theorem xa_ex_xp {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {x0 x1 x2 z0 z1 z2 B0 B1 B2 : B256}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (h : XAt sevm post 0x2458 (St b [x0, x1, x2, z2, z1, z0, B2, B1, B0, exR1, exR1, exR0,
      Bytes.toB256 [2, 0]] M G) L) :
    (exI sevm).toNat < 3 ∧ ∃ M' img' G', Mem.Reads M' img' ∧ Mem.Wf M' ∧
      ExFrame img' (exW3 B0 B1 B2) (exW3 x0 x1 x2) (exDx sevm)
        ((b.getStor sevm.currentTarget).get (coinsBase + exI sevm)) ∧
      ((exI sevm ≠ 2 ∧ XAt sevm post 0x2517
          (St (afterSload sevm b (coinsBase + exI sevm)) [] M' G') L) ∨
        (exI sevm = 2 ∧ XAt sevm post 0x24d8
          (St (afterSload sevm b (coinsBase + exI sevm)) [] M' G') L)) := by
  xjd 0x2459
  xs 0x245c (.push [0x03, 0x20] (by decide)) ri_push
  xmo 0x245d (.reg .mstore) (ri_mstore_imgAt (o := 0x320) rfl)
  xs 0x2460 (.push [0x03, 0x40] (by decide)) ri_push
  xmo 0x2461 (.reg .mstore) (ri_mstore_imgAt (o := 0x340) rfl)
  xs 0x2464 (.push [0x03, 0x60] (by decide)) ri_push
  xmo 0x2465 (.reg .mstore) (ri_mstore_imgAt (o := 0x360) rfl)
  xs 0x2468 (.push [0x02, 0x40] (by decide)) ri_push
  xmo 0x2469 (.reg .mstore) (ri_mstore_imgAt (o := 0x240) rfl)
  xs 0x246c (.push [0x02, 0x20] (by decide)) ri_push
  xmo 0x246d (.reg .mstore) (ri_mstore_imgAt (o := 0x220) rfl)
  xs 0x2470 (.push [0x02, 0x00] (by decide)) ri_push
  xmo 0x2471 (.reg .mstore) (ri_mstore_imgAt (o := 0x200) rfl)
  xs 0x2474 (.push [0x01, 0xe0] (by decide)) ri_push
  xmo 0x2475 (.reg .mstore) (ri_mstore_imgAt (o := 0x1e0) rfl)
  xs 0x2478 (.push [0x01, 0xc0] (by decide)) ri_push
  xmo 0x2479 (.reg .mstore) (ri_mstore_imgAt (o := 0x1c0) rfl)
  xs 0x247c (.push [0x01, 0xa0] (by decide)) ri_push
  xmo 0x247d (.reg .mstore) (ri_mstore_imgAt (o := 0x1a0) rfl)
  xs 0x2480 (.push [0x01, 0x80] (by decide)) ri_push
  xmo 0x2481 (.reg .mstore) (ri_mstore_imgAt (o := 0x180) rfl)
  xs 0x2484 (.push [0x01, 0x60] (by decide)) ri_push
  xmo 0x2485 (.reg .mstore) (ri_mstore_imgAt (o := 0x160) rfl)
  xs 0x2488 (.push [0x01, 0x40] (by decide)) ri_push
  xmo 0x2489 (.reg .mstore) (ri_mstore_imgAt (o := 0x140) rfl)
  xs 0x248c (.push [0x03, 0x20] (by decide)) ri_push
  xs 0x248d (.reg (.dup 0)) (ri_dup (by rfl))
  xmo 0x248e (.reg .mload) (ri_mload_imgAt (o := 0x320) rfl)
  xs 0x248f (.reg (.dup 2)) (ri_dup (by rfl))
  xmo 0x2490 (.reg .mstore) (ri_mstore_imgAt (o := 0x200) rfl)
  xs 0x2491 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2493 (.push [0x20] (by decide)) ri_push
  xs 0x2494 (.reg .add) ri_add
  xmo 0x2495 (.reg .mload) (ri_mload_imgAt (o := 0x340) (by decide))
  xs 0x2496 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2498 (.push [0x20] (by decide)) ri_push
  xs 0x2499 (.reg .add) ri_add
  xmo 0x249a (.reg .mstore) (ri_mstore_imgAt (o := 0x220) (by decide))
  xs 0x249b (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x249d (.push [0x40] (by decide)) ri_push
  xs 0x249e (.reg .add) ri_add
  xmo 0x249f (.reg .mload) (ri_mload_imgAt (o := 0x360) (by decide))
  xs 0x24a0 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x24a2 (.push [0x40] (by decide)) ri_push
  xs 0x24a3 (.reg .add) ri_add
  xmo 0x24a4 (.reg .mstore) (ri_mstore_imgAt (o := 0x240) (by decide))
  xs 0x24a5 (.reg .pop) ri_pop
  xs 0x24a6 (.reg .pop) ri_pop
  xs 0x24a8 (.push [0x44] (by decide)) ri_push
  xs 0x24a9 (.reg .calldataload) ri_calldataload
  xs 0x24ac (.push [0x03, 0x80] (by decide)) ri_push
  xmo 0x24ad (.reg .mstore) (ri_mstore_imgAt (o := 0x380) rfl)
  xs 0x24af (.push [0x04] (by decide)) ri_push
  xs 0x24b0 (.reg .calldataload) ri_calldataload
  xs 0x24b2 (.push [0x03] (by decide)) ri_push
  xs 0x24b3 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x24b4 (.reg .lt) ri_lt
  xs 0x24b7 (.push [0x24, 0xbc] (by decide)) ri_push
  xji 0x24b8 0x24bc hw
  · xdead
  have hi3 := ex_lt3 hw
  clear hw
  refine ⟨hi3, ?_⟩
  xjd 0x24bd
  xs 0x24bf (.push [0x00] (by decide)) ri_push
  xs 0x24c1 (.push [0xc0] (by decide)) ri_push
  xmo 0x24c2 (.reg .mstore) (ri_mstore_imgAt (o := 0xc0) rfl)
  xs 0x24c4 (.push [0x20] (by decide)) ri_push
  xs 0x24c6 (.push [0xc0] (by decide)) ri_push
  xmo 0x24c7 (.reg .keccak256) (ri_keccak_imgAt (o := 0xc0) (z := 0x20) rfl rfl)
  rw [keccak_zero] at h
  xs 0x24c8 (.reg .add) ri_add
  xw 0x24c9 (.reg .sload) ri_sload
  rw [getStorVal_eq] at h
  xs 0x24cc (.push [0x03, 0xa0] (by decide)) ri_push
  xmo 0x24cd (.reg .mstore) (ri_mstore_imgAt (o := 0x3a0) rfl)
  xs 0x24cf (.push [0x02] (by decide)) ri_push
  xs 0x24d1 (.push [0x04] (by decide)) ri_push
  xs 0x24d2 (.reg .calldataload) ri_calldataload
  xs 0x24d3 (.reg .eq) ri_eq
  xs 0x24d4 (.reg .iszero) ri_iszero
  xs 0x24d7 (.push [0x25, 0x17] (by decide)) ri_push
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_self]
    at hR
  obtain ⟨img1, hR1, hI⟩ := Mem.Reads.forget hR
  have hF : ExFrame img1 (exW3 B0 B1 B2) (exW3 x0 x1 x2) (exDx sevm)
      ((b.getStor sevm.currentTarget).get (coinsBase + exI sevm)) := by
    refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, ?_, ?_⟩
    · obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      all_goals (rw [hI]; wchain)
    · obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      all_goals (rw [hI]; wchain)
    · obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      all_goals (rw [hI]; wchain)
    · rw [hI]; wchain
    · rw [hI]; wchain
  clear hI hR
  xji 0x24d8 0x2517 hw
  · exact ⟨_, _, _, hR1, hW, hF, .inr ⟨(isNe_fall hw).trans (by decide), h⟩⟩
  · exact ⟨_, _, _, hR1, hW, hF,
      .inl ⟨fun e => isNe_jump hw (e.trans (by decide)), h⟩⟩

theorem bal_sel_bytes :
    (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes = List.replicate 28 0 ++ balanceOfSel := by
  decide

/-- The `balanceOf(self)` calldata the two writes leave at `o + 0x1c`. -/
theorem bal_input (img : Bytes) (A : B256) (o : Nat) :
    (Bytes.writeAt (Bytes.writeAt img o (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) (o + 0x20)
      A.toBytes).sliceD (o + 0x1c) 0x24 0 = balanceOfSel ++ A.toBytes := by
  have hsel : Region (Bytes.writeAt img o (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes)
      (o + 0x1c) balanceOfSel := by
    have := Region.write_self img o (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes
    rw [bal_sel_bytes] at this
    exact this.right
  refine Region.slice (Region.append' (o' := o + 0x20) ?_ ?_ (by
      simp only [balanceOfSel, List.length_cons, List.length_nil]))
    (by simp only [List.length_append, B256.length_toBytes, balanceOfSel, List.length_cons,
      List.length_nil])
  · exact Region.write_other hsel (by simp only [balanceOfSel, B256.length_toBytes,
      List.length_cons, List.length_nil]; omega)
  · exact Region.write_self _ _ _

theorem ex_slice_take {img : Bytes} {o : Nat} {out : Bytes} (h : 32 ≤ out.length) :
    (Bytes.writeAt img o (out.take 32)).sliceD o 32 0 = out.take 32 := by
  rw [Bytes.sliceD_writeAt_inside _ _ _ _ _ (le_refl _) (by rw [List.length_take]; omega),
    Nat.sub_self]
  exact List.sliceD_zero_of_length (by rw [List.length_take]; omega)

/-- What a `balanceOf(self)` child of the frame is. -/
structure ExBal (sevm : Sevm) (b d : Devm) (C : B256) (c : Exec.Frame) : Prop where
  target : c.sevm.currentTarget = C.toAdr
  data : c.sevm.data = balanceOfData sevm.currentTarget
  static : c.sevm.isStatic = true
  len : 32 ≤ c.post.output.length
  logs : c.post.logs = []
  codePre : ∀ a, c.pre.getCode a = b.getCode a
  codePost : ∀ a, d.getCode a = c.post.getCode a
  stor : ∀ a, d.getStor a = b.getStor a
  dlogs : d.logs = b.logs
  output : d.output = b.output
  acc : Devm.AccGrow b d
  code : ∀ a, b.getCode a ≠ .empty → d.getCode a = b.getCode a

/-- **The first `balanceOf(self)`** (`0x24d8` → `0x2517`), for `i == 2`: the next remaining
child is the static call to `input_coin`, at least a word back, its first word at `0x380`. -/
theorem xa_ex_bal1 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {B X : Nat → B256} {D C : B256}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hF : ExFrame img B X D C)
    (hcoin : ¬ sevm.benvStat.rules.isPrecomp C.toAdr)
    (h : XAt sevm post 0x24d8 (St b [] M G) L) :
    ∃ c L' d M' img' G', L = c :: L' ∧ 0 < sevm.depth ∧ ExBal sevm b d C c ∧
      Mem.Reads M' img' ∧ Mem.Wf M' ∧
      ExFrame img' B X (Bytes.toB256 (c.post.output.take 32)) C ∧
      XAt sevm post 0x2517 (St d [] M' G') L' := by
  xs 0x24da (.push [0x20] (by decide)) ri_push
  xs 0x24dd (.push [0x04, 0x40] (by decide)) ri_push
  xs 0x24df (.push [0x24] (by decide)) ri_push
  xs 0x24e4 (.push [0x70, 0xa0, 0x82, 0x31] (by decide)) ri_push
  xs 0x24e7 (.push [0x03, 0xc0] (by decide)) ri_push
  xmo 0x24e8 (.reg .mstore) (ri_mstore_imgAt (o := 0x3c0) rfl)
  xs 0x24e9 (.reg .address) ri_address
  xs 0x24ec (.push [0x03, 0xe0] (by decide)) ri_push
  xmo 0x24ed (.reg .mstore) (ri_mstore_imgAt (o := 0x3e0) rfl)
  xs 0x24f0 (.push [0x03, 0xdc] (by decide)) ri_push
  xs 0x24f3 (.push [0x03, 0xa0] (by decide)) ri_push
  xmo 0x24f4 (.reg .mload) (ri_mload_imgAt (o := 0x3a0) rfl)
  rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by decide),
    Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by decide), hF.coin.read] at h
  xs 0x24f5 (.reg .gas) ri_gas_remaining
  replace h := xa_staticcall_img (pc' := 0x24f6) (i := 0x3dc) (n := 0x24) (o := 0x440) (z := 0x20)
    hfork (atN hcode (by kernel_rfl)) rfl rfl rfl rfl rfl hR hW h
  clear hR hW
  obtain ⟨d1, flag, out, M1, L1, h, _, hR, hW, hrd, hob, hstor, hlogs, hk⟩ := h
  xs 0x24f9 (.push [0x24, 0xfe] (by decide)) ri_push
  xji 0x24fa 0x24fe hw
  · xdead
  rcases hk hw with ⟨hpre, -⟩ | ⟨c, hL, hdepth, hout, hacc, hcodeK, htgt, hdata, hstat, hcout,
    hclogs, hcpre, hcpost⟩
  · exact absurd hpre hcoin
  clear hk
  xjd 0x24ff
  xs 0x2501 (.push [0x1f] (by decide)) ri_push
  xs 0x2502 (.reg .returndatasize) ri_returndatasize
  xs 0x2503 (.reg .gt) ri_gt
  xs 0x2506 (.push [0x25, 0x0b] (by decide)) ri_push
  xji 0x2507 0x250b hw2
  · xdead
  have hlen : 32 ≤ out.length := by
    have e := gtCheck_ne_zero hw2
    rw [hrd, B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hob] at e
    exact e
  clear hw2
  xjd 0x250c
  xs 0x250e (.push [0x00] (by decide)) ri_push
  xs 0x250f (.reg .pop) ri_pop
  xs 0x2512 (.push [0x04, 0x40] (by decide)) ri_push
  xmo 0x2513 (.reg .mload) (ri_mload_imgAt (o := 0x440) rfl)
  rw [ex_slice_take hlen] at h
  xs 0x2516 (.push [0x03, 0x80] (by decide)) ri_push
  xmo 0x2517 (.reg .mstore) (ri_mstore_imgAt (o := 0x380) rfl)
  refine ⟨c, L1, d1, _, _, _, hL, hdepth, ⟨htgt, ?_, hstat, by rw [hcout]; exact hlen, hclogs,
    hcpre, hcpost, hstor, hlogs, hout, hacc, hcodeK⟩, hR, hW, ?_, h⟩
  · rw [hdata, show (0x3dc : Nat) = 0x3c0 + 0x1c from rfl, show (0x3e0 : Nat) = 0x3c0 + 0x20 from rfl,
      bal_input]
    rfl
  · rw [← hcout]
    refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, WordAt.write_self _ _ _, ?_⟩
    · refine WordAt.write_other (WordAt.write_other (WordAt.write_other (WordAt.write_other
        (hF.rate k hk) ?_) ?_) ?_) ?_ <;> simp only [B256.length_toBytes, List.length_take] <;> omega
    · refine WordAt.write_other (WordAt.write_other (WordAt.write_other (WordAt.write_other
        (hF.old k hk) ?_) ?_) ?_) ?_ <;> simp only [B256.length_toBytes, List.length_take] <;> omega
    · refine WordAt.write_other (WordAt.write_other (WordAt.write_other (WordAt.write_other
        (hF.xp k hk) ?_) ?_) ?_) ?_ <;> simp only [B256.length_toBytes, List.length_take] <;> omega
    · refine WordAt.write_other (WordAt.write_other (WordAt.write_other (WordAt.write_other
        hF.coin ?_) ?_) ?_) ?_ <;> simp only [B256.length_toBytes, List.length_take] <;> omega

end Blanc.Lift.Curve3Pool
