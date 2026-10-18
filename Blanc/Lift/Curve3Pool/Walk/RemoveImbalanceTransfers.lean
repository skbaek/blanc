import Blanc.Lift.Curve3Pool.Walk.RemoveImbalanceBurn

/-!
# `remove_liquidity_imbalance`, part 8: the transfer loop, the event and the lock

* `xa_rli_iter` (`0x3769` → `0x38f7`, coin `k` symbolic): `if amounts[k] != 0`, the `transfer`
  to `coins[k]` and its `raw_call` test (`xa_rli_push`, `xa_rli_tail`), crossing that child
  with the frame's per-child premises;
* `xa_rli_next` (`0x38f7` → the loop head or past the loop): the counter at `0x900` advanced;
* `xa_rli_log` (`0x390b` → `STOP`): `RemoveLiquidityImbalance(msg.sender, amounts, fees, D1,
  token_supply - token_amount)` (`LOG2` over the eight words at `0xb80`, the last checked) and
  the lock cleared.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

section

variable {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem} {img : Bytes}
  {X D1 T f0 f1 f2 : B256}

/-- **One transfer iteration** (`0x3769` → `0x38f7`) for coin `k`. -/
theorem xa_rli_iter {b0 : Devm} {σ : Stor} {k : Nat}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hB : ExBase sevm b0 b σ) (hpc : b0.getCode sevm.currentTarget ≠ .empty)
    (hkeep : ∀ c ∈ L, ∀ x, (c.post.getStor sevm.currentTarget).get x =
      (c.pre.getStor sevm.currentTarget).get x)
    (hidk : ∀ c ∈ L, c.post.getCode 4 = c.pre.getCode 4) (hdepth : 0 < sevm.depth)
    (hcoin : rliAmt sevm k ≠ 0 →
      ¬ sevm.benvStat.rules.isPrecomp (σ.get (coinsBase + Nat.toB256 k)).toAdr)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hI : RliImg img X D1 T f0 f1 f2)
    (hctr : WordAt img 0x900 (Nat.toB256 k))
    (h : XAt sevm post 0x3769 (St b [Bytes.toB256 [3], Bytes.toB256 [9, 0]] M G) L) :
    ∃ (Lc L' : List Exec.Frame) (b' : Devm) (M' : Mem) (img' : Bytes) (G' : Nat),
      L = Lc ++ L' ∧ ExBase sevm b0 b' σ ∧ b'.logs = b.logs ++ Lc.flatMap (fun c => c.post.logs) ∧
      ((rliAmt sevm k = 0 ∧ Lc = []) ∨
        (rliAmt sevm k ≠ 0 ∧ ∃ c, Lc = [c] ∧
          c.sevm.currentTarget = (σ.get (coinsBase + Nat.toB256 k)).toAdr ∧
          c.sevm.data = exPushData sevm (rliAmt sevm k) ∧ c.sevm.value = 0 ∧
          c.sevm.isStatic = sevm.isStatic ∧ RawCallOk c.post.output)) ∧
      Mem.Reads M' img' ∧ Mem.Wf M' ∧ RliImg img' X D1 T f0 f1 f2 ∧
      WordAt img' 0x900 (Nat.toB256 k) ∧
      XAt sevm post 0x38f7 (St b' [Bytes.toB256 [3], Bytes.toB256 [9, 0]] M' G') L' := by
  xjd 0x376a
  xs 0x376c (.push [0x00] (by decide)) ri_push
  xs 0x376e (.push [0x04] (by decide)) ri_push
  xs 0x3771 (.push [0x09, 0x00] (by decide)) ri_push
  xmo 0x3772 (.reg .mload) (ri_mload_imgAt (o := 0x900) rfl)
  rw [hctr.read] at h
  xs 0x3774 (.push [0x03] (by decide)) ri_push
  xs 0x3775 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x3776 (.reg .lt) ri_lt
  xs 0x3779 (.push [0x37, 0x7e] (by decide)) ri_push
  xji 0x377a 0x377e hw
  · xdead
  clear hw
  xjd 0x377f
  xs 0x3781 (.push [0x20] (by decide)) ri_push
  xs 0x3782 (.reg .mul) ri_mul
  xs 0x3783 (.reg .add) ri_add
  xs 0x3784 (.reg .calldataload) ri_calldataload
  xs 0x3785 (.reg .xor) ri_xor
  xs 0x3786 (.reg .iszero) ri_iszero
  xs 0x3789 (.push [0x38, 0xf7] (by decide)) ri_push
  xji 0x378a 0x38f7 hw
  · -- `amounts[k] != 0`: the transfer
    have hne : rliAmt sevm k ≠ 0 := by
      have e := ne_of_eqCheck_eq_zero hw
      rwa [zero_lit, B256.xor_zero] at e
    clear hw
    obtain ⟨bq, c, L1, d, img1, G1, hbq, rfl, hcq, hkp, hR1, hW1, hrd, h⟩ :=
      xa_rli_push hcode hfork hR hW hctr hB.id hdepth (hB.stor _) (hcoin hne) h
    have hBq := (hB.rel hbq).child hcq hpc (hkeep c List.mem_cons_self)
      (hidk c List.mem_cons_self)
    obtain ⟨hok, b6, M6, img6, G7, hb6, hR6, hW6, hk6, h⟩ := xa_rli_tail hcode hBq.id hR1 hW1 hrd h
    refine ⟨[c], L1, b6, M6, img6, G7, rfl, hBq.rel hb6, ?_, .inr ⟨hne, c, rfl, hcq.target,
      hcq.data, hcq.value, hcq.isStatic, hcq.output ▸ hok⟩, hR6, hW6,
      hI.keep fun o w hw h1 h2 => hk6 o w (hkp o w hw (by omega) (by omega)) (by omega) (by omega),
      hk6 _ _ (hkp _ _ hctr (by decide) (by decide)) (by decide) (by decide), h⟩
    rw [hb6.logs, hcq.logs, hbq.logs]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  · -- `amounts[k] == 0`: skipped
    have he : rliAmt sevm k = 0 := by
      have e := eqCheck_ne_zero_eq hw
      rwa [zero_lit, B256.xor_zero] at e
    exact ⟨[], L, b, M, img, _, rfl, hB, by simp only [List.flatMap_nil, List.append_nil],
      .inl ⟨he, rfl⟩, hR, hW, hI, hctr, h⟩

/-- **One transfer iteration under the conditional keep** (`0x3769` → `0x38f7`) for coin `k`:
the same conclusion as `xa_rli_iter` when only the children at neither the pool nor `4` are
known to keep the pool (`RlKeepC`, which every frame at depth `1` satisfies), given that coin
`k` is neither. -/
theorem xa_rli_iterC {b0 : Devm} {σ : Stor} {k : Nat}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hB : ExBase sevm b0 b σ) (hpc : b0.getCode sevm.currentTarget ≠ .empty)
    (hcoinne : (σ.get (coinsBase + Nat.toB256 k)).toAdr ≠ sevm.currentTarget ∧
      (σ.get (coinsBase + Nat.toB256 k)).toAdr ≠ 4)
    (hK : RlKeepC sevm L) (hdepth : 0 < sevm.depth)
    (hcoin : rliAmt sevm k ≠ 0 →
      ¬ sevm.benvStat.rules.isPrecomp (σ.get (coinsBase + Nat.toB256 k)).toAdr)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hI : RliImg img X D1 T f0 f1 f2)
    (hctr : WordAt img 0x900 (Nat.toB256 k))
    (h : XAt sevm post 0x3769 (St b [Bytes.toB256 [3], Bytes.toB256 [9, 0]] M G) L) :
    ∃ (Lc L' : List Exec.Frame) (b' : Devm) (M' : Mem) (img' : Bytes) (G' : Nat),
      L = Lc ++ L' ∧ ExBase sevm b0 b' σ ∧ b'.logs = b.logs ++ Lc.flatMap (fun c => c.post.logs) ∧
      ((rliAmt sevm k = 0 ∧ Lc = []) ∨
        (rliAmt sevm k ≠ 0 ∧ ∃ c, Lc = [c] ∧
          c.sevm.currentTarget = (σ.get (coinsBase + Nat.toB256 k)).toAdr ∧
          c.sevm.data = exPushData sevm (rliAmt sevm k) ∧ c.sevm.value = 0 ∧
          c.sevm.isStatic = sevm.isStatic ∧ RawCallOk c.post.output)) ∧
      Mem.Reads M' img' ∧ Mem.Wf M' ∧ RliImg img' X D1 T f0 f1 f2 ∧
      WordAt img' 0x900 (Nat.toB256 k) ∧
      XAt sevm post 0x38f7 (St b' [Bytes.toB256 [3], Bytes.toB256 [9, 0]] M' G') L' := by
  xjd 0x376a
  xs 0x376c (.push [0x00] (by decide)) ri_push
  xs 0x376e (.push [0x04] (by decide)) ri_push
  xs 0x3771 (.push [0x09, 0x00] (by decide)) ri_push
  xmo 0x3772 (.reg .mload) (ri_mload_imgAt (o := 0x900) rfl)
  rw [hctr.read] at h
  xs 0x3774 (.push [0x03] (by decide)) ri_push
  xs 0x3775 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x3776 (.reg .lt) ri_lt
  xs 0x3779 (.push [0x37, 0x7e] (by decide)) ri_push
  xji 0x377a 0x377e hw
  · xdead
  clear hw
  xjd 0x377f
  xs 0x3781 (.push [0x20] (by decide)) ri_push
  xs 0x3782 (.reg .mul) ri_mul
  xs 0x3783 (.reg .add) ri_add
  xs 0x3784 (.reg .calldataload) ri_calldataload
  xs 0x3785 (.reg .xor) ri_xor
  xs 0x3786 (.reg .iszero) ri_iszero
  xs 0x3789 (.push [0x38, 0xf7] (by decide)) ri_push
  xji 0x378a 0x38f7 hw
  · -- `amounts[k] != 0`: the transfer
    have hne : rliAmt sevm k ≠ 0 := by
      have e := eqCheck_eq_zero hw
      rwa [zero_lit, B256.xor_zero] at e
    clear hw
    obtain ⟨bq, c, L1, d, img1, G1, hbq, rfl, hcq, hkp, hR1, hW1, hrd, h⟩ :=
      xa_rli_push hcode hfork hR hW hctr hB.id hdepth (hB.stor _) (hcoin hne) h
    have hkc := hK c List.mem_cons_self (by rw [hcq.target]; exact hcoinne.1)
      (by rw [hcq.target]; exact hcoinne.2)
    have hBq := (hB.rel hbq).child hcq hpc hkc.1 hkc.2
    obtain ⟨hok, b6, M6, img6, G7, hb6, hR6, hW6, hk6, h⟩ := xa_rli_tail hcode hBq.id hR1 hW1 hrd h
    refine ⟨[c], L1, b6, M6, img6, G7, rfl, hBq.rel hb6, ?_, .inr ⟨hne, c, rfl, hcq.target,
      hcq.data, hcq.value, hcq.isStatic, hcq.output ▸ hok⟩, hR6, hW6,
      hI.keep fun o w hw h1 h2 => hk6 o w (hkp o w hw (by omega) (by omega)) (by omega) (by omega),
      hk6 _ _ (hkp _ _ hctr (by decide) (by decide)) (by decide) (by decide), h⟩
    rw [hb6.logs, hcq.logs, hbq.logs]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  · -- `amounts[k] == 0`: skipped
    have he : rliAmt sevm k = 0 := by
      have e := eqCheck_ne_zero_eq hw
      rwa [zero_lit, B256.xor_zero] at e
    exact ⟨[], L, b, M, img, _, rfl, hB, by simp only [List.flatMap_nil, List.append_nil],
      .inl ⟨he, rfl⟩, hR, hW, hI, hctr, h⟩

/-- **The counter advanced** (`0x38f7`): back to the loop head, or past the loop. -/
theorem xa_rli_next {k : Nat} (hcode : sevm.code = code)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hI : RliImg img X D1 T f0 f1 f2)
    (hctr : WordAt img 0x900 (Nat.toB256 k))
    (h : XAt sevm post 0x38f7 (St b [Bytes.toB256 [3], Bytes.toB256 [9, 0]] M G) L) :
    ∃ (M' : Mem) (img' : Bytes) (G' : Nat), Mem.Reads M' img' ∧ Mem.Wf M' ∧
      RliImg img' X D1 T f0 f1 f2 ∧ WordAt img' 0x900 (Bytes.toB256 [1] + Nat.toB256 k) ∧
      ((Bytes.toB256 [1] + Nat.toB256 k ≠ Bytes.toB256 [3] ∧
        XAt sevm post 0x3769 (St b [Bytes.toB256 [3], Bytes.toB256 [9, 0]] M' G') L) ∨
       (Bytes.toB256 [1] + Nat.toB256 k = Bytes.toB256 [3] ∧
        XAt sevm post 0x390b (St b [] M' G') L)) := by
  xjd 0x38f8
  xjd 0x38f9
  xs 0x38fa (.reg (.dup 1)) (ri_dup (by rfl))
  xmo 0x38fb (.reg .mload) (ri_mload_imgAt (o := 0x900) rfl)
  rw [hctr.read] at h
  xs 0x38fd (.push [0x01] (by decide)) ri_push
  xs 0x38fe (.reg .add) ri_add
  xs 0x38ff (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x3900 (.reg (.dup 3)) (ri_dup (by rfl))
  xmo 0x3901 (.reg .mstore) (ri_mstore_imgAt (o := 0x900) rfl)
  obtain ⟨img1, hR, hE⟩ := Mem.Reads.forget hR
  have hI1 : RliImg img1 X D1 T f0 f1 f2 := hI.keep fun o w hw _ ho => by rw [hE]; wchain; exact hw
  have hc1 : WordAt img1 0x900 (Bytes.toB256 [1] + Nat.toB256 k) := by
    rw [hE]; exact WordAt.write_self _ _ _
  xs 0x3902 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x3903 (.reg .eq) ri_eq
  xs 0x3904 (.reg .iszero) ri_iszero
  xs 0x3907 (.push [0x37, 0x69] (by decide)) ri_push
  xji 0x3908 0x3769 hw
  · have he := eqCheck_ne_zero_eq (ne_of_eqCheck_eq_zero hw)
    xjd 0x3909
    xs 0x390a (.reg .pop) ri_pop
    xs 0x390b (.reg .pop) ri_pop
    exact ⟨_, img1, _, hR, hW, hI1, hc1, .inr ⟨he.symm, h⟩⟩
  · have hne := ne_of_eqCheck_eq_zero (eqCheck_ne_zero_eq hw)
    exact ⟨_, img1, _, hR, hW, hI1, hc1, .inl ⟨Ne.symm hne, h⟩⟩

/-- The `RemoveLiquidityImbalance` topic word. -/
abbrev rliTopic : B256 := Bytes.toB256 [0x17, 0x35, 0x99, 0xdb, 0xf9, 0xc6, 0xca, 0x6f, 0x7c,
  0x3b, 0x59, 0x0d, 0xf0, 0x7a, 0xe9, 0x8a, 0x45, 0xd7, 0x4f, 0xf5, 0x40, 0x65, 0x50, 0x51, 0x41,
  0xe7, 0xde, 0x6c, 0x46, 0xa6, 0x24, 0xc2]

/-- **The event and the lock** (`0x390b` → `STOP`). -/
theorem xa_rli_log (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hI : RliImg img X D1 T f0 f1 f2)
    (h : XAt sevm post 0x390b (St b [] M G) L) :
    ¬ T < X ∧ L = [] ∧
      (∀ x, (post.getStor sevm.currentTarget).get x =
        ((b.getStor sevm.currentTarget).set lockSlot 0).get x) ∧
      post.logs = b.logs ++ [⟨sevm.currentTarget, [rliTopic, sevm.caller.toB256],
        (Sevm.dataWord sevm (Bytes.toB256 [4])).toBytes ++
        (Sevm.dataWord sevm (Bytes.toB256 [0x24])).toBytes ++
        (Sevm.dataWord sevm (Bytes.toB256 [0x44])).toBytes ++
        f0.toBytes ++ f1.toBytes ++ f2.toBytes ++ D1.toBytes ++ (T - X).toBytes⟩] ∧
      post.output = b.output := by
  xs 0x390d (.push [0x04] (by decide)) ri_push
  xs 0x390e (.reg .calldataload) ri_calldataload
  xs 0x3911 (.push [0x0b, 0x80] (by decide)) ri_push
  xmo 0x3912 (.reg .mstore) (ri_mstore_imgAt (o := 0xb80) rfl)
  xs 0x3914 (.push [0x24] (by decide)) ri_push
  xs 0x3915 (.reg .calldataload) ri_calldataload
  xs 0x3918 (.push [0x0b, 0xa0] (by decide)) ri_push
  xmo 0x3919 (.reg .mstore) (ri_mstore_imgAt (o := 0xba0) rfl)
  xs 0x391b (.push [0x44] (by decide)) ri_push
  xs 0x391c (.reg .calldataload) ri_calldataload
  xs 0x391f (.push [0x0b, 0xc0] (by decide)) ri_push
  xmo 0x3920 (.reg .mstore) (ri_mstore_imgAt (o := 0xbc0) rfl)
  xs 0x3923 (.push [0x05, 0xa0] (by decide)) ri_push
  xmo 0x3924 (.reg .mload) (ri_mload_imgAt (o := 0x5a0) rfl)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint] at h
  rw [hI.f0.read] at h
  xs 0x3927 (.push [0x0b, 0xe0] (by decide)) ri_push
  xmo 0x3928 (.reg .mstore) (ri_mstore_imgAt (o := 0xbe0) rfl)
  xs 0x392b (.push [0x05, 0xc0] (by decide)) ri_push
  xmo 0x392c (.reg .mload) (ri_mload_imgAt (o := 0x5c0) rfl)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint] at h
  rw [hI.f1.read] at h
  xs 0x392f (.push [0x0c, 0x00] (by decide)) ri_push
  xmo 0x3930 (.reg .mstore) (ri_mstore_imgAt (o := 0xc00) rfl)
  xs 0x3933 (.push [0x05, 0xe0] (by decide)) ri_push
  xmo 0x3934 (.reg .mload) (ri_mload_imgAt (o := 0x5e0) rfl)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint] at h
  rw [hI.f2.read] at h
  xs 0x3937 (.push [0x0c, 0x20] (by decide)) ri_push
  xmo 0x3938 (.reg .mstore) (ri_mstore_imgAt (o := 0xc20) rfl)
  xs 0x393b (.push [0x04, 0x80] (by decide)) ri_push
  xmo 0x393c (.reg .mload) (ri_mload_imgAt (o := 0x480) rfl)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint] at h
  rw [hI.d1.read] at h
  xs 0x393f (.push [0x0c, 0x40] (by decide)) ri_push
  xmo 0x3940 (.reg .mstore) (ri_mstore_imgAt (o := 0xc40) rfl)
  xs 0x3943 (.push [0x01, 0x40] (by decide)) ri_push
  xmo 0x3944 (.reg .mload) (ri_mload_imgAt (o := 0x140) rfl)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint] at h
  rw [hI.t.read] at h
  xs 0x3947 (.push [0x07, 0x80] (by decide)) ri_push
  xmo 0x3948 (.reg .mload) (ri_mload_imgAt (o := 0x780) rfl)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint] at h
  rw [hI.x.read] at h
  xs 0x3949 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x394a (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x394b (.reg .lt) ri_lt
  xs 0x394c (.reg .iszero) ri_iszero
  xs 0x394f (.push [0x39, 0x54] (by decide)) ri_push
  xji 0x3950 0x3954 hw
  · xdead
  have hTX := ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hw)
  clear hw
  xjd 0x3955
  xs 0x3956 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x3957 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x3958 (.reg .sub) ri_sub
  xs 0x3959 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x395a (.reg .pop) ri_pop
  xs 0x395b (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x395c (.reg .pop) ri_pop
  xs 0x395f (.push [0x0c, 0x60] (by decide)) ri_push
  xmo 0x3960 (.reg .mstore) (ri_mstore_imgAt (o := 0xc60) rfl)
  xs 0x3961 (.reg .caller) ri_caller
  xs 0x3982 (.push [0x17, 0x35, 0x99, 0xdb, 0xf9, 0xc6, 0xca, 0x6f, 0x7c, 0x3b, 0x59, 0x0d, 0xf0,
    0x7a, 0xe9, 0x8a, 0x45, 0xd7, 0x4f, 0xf5, 0x40, 0x65, 0x50, 0x51, 0x41, 0xe7, 0xde, 0x6c,
    0x46, 0xa6, 0x24, 0xc2] (by decide)) ri_push
  xs 0x3985 (.push [0x01, 0x00] (by decide)) ri_push
  xs 0x3988 (.push [0x0b, 0x80] (by decide)) ri_push
  obtain ⟨img2, hR2, hE⟩ := Mem.Reads.forget hR
  have hdata : Region img2 0xb80 ((Sevm.dataWord sevm (Bytes.toB256 [4])).toBytes ++
      (Sevm.dataWord sevm (Bytes.toB256 [0x24])).toBytes ++
      (Sevm.dataWord sevm (Bytes.toB256 [0x44])).toBytes ++
      f0.toBytes ++ f1.toBytes ++ f2.toBytes ++ D1.toBytes ++ (T - X).toBytes) := by
    rw [hE]
    refine Region.append' (o' := 0xc60) (Region.append' (o' := 0xc40)
      (Region.append' (o' := 0xc20) (Region.append' (o' := 0xc00) (Region.append' (o' := 0xbe0)
      (Region.append' (o' := 0xbc0) (Region.append' (o' := 0xba0) ?_ ?_ ?_) ?_ ?_) ?_ ?_) ?_ ?_)
      ?_ ?_) ?_ ?_) ?_ ?_
    all_goals first
      | simp only [List.length_append, B256.length_toBytes]
      | exact Region.of_word (by wchain)
  clear hE hR
  replace h := xa_nextAt (n := .reg (.log 2)) (pc' := 0x3989) (atN hcode (by kernel_rfl))
    (by nofun) (by rfl) h
  obtain ⟨_, s, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_log2_post s
  clear s
  rw [Mem.Reads.read hR2, show (Bytes.toB256 [0x0b, 0x80]).toNat = 0xb80 from rfl,
    show (Bytes.toB256 [0x01, 0x00]).toNat = 0x100 from rfl,
    hdata.slice (by simp only [List.length_append, B256.length_toBytes])] at h
  xs 0x398b (.push [0x00] (by decide)) ri_push
  xs 0x398f (.push [0xff, 0xff, 0xff] (by decide)) ri_push
  xw 0x3990 (.reg .sstore) ri_sstore
  obtain ⟨hrun, hL⟩ := xa_halt (l := .stop) (atL hcode (by kernel_rfl)) h
  have hp := (Except.ok.inj hrun).symm
  subst hp hL
  refine ⟨hTX, rfl, ?_, ?_, ?_⟩
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

end

end Blanc.Lift.Curve3Pool
