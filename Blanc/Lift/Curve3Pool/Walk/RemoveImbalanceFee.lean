import Blanc.Lift.Curve3Pool.Walk.Kit

/-!
# `remove_liquidity_imbalance`, part 2: the fee numerator and the `_A` call setup

From the supply check's landing (`0x30c5`) to the internal `_A` call's jump (`0x312a`):
`fee * 3` with its checked-mul guard (reverting on overflow), the discarded `/ 8`
quotient, the numerator stored at `0x1e0`, `admin_fee` stored at `0x200`, and the
eight words `0x140 … 0x220` pushed for the `_A` call.

`xa_rli_feeA` (`0x30c5` → `0x3104`): the fee and admin-fee words read from storage,
`A3 = F * 3` with `(A3 / F = 3 ∨ F = 0)`, and the memory image with `A3` at `0x1e0`
and `AF` at `0x200`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- **`remove_liquidity_imbalance` fee numerator** (see the module note). -/
theorem xa_rli_feeA {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (h : XAt sevm post 0x30c5 (St b [] M G) L) :
    ∃ (F A3 Q AF : B256) (M1 : Mem) (G1 : Nat) (img1 : Bytes),
      F = b.getStorVal sevm.currentTarget (Bytes.toB256 [0x02]) ∧
      A3 = F * Bytes.toB256 [0x03] ∧
      (A3 / F = Bytes.toB256 [0x03] ∨ F = 0) ∧
      Q = A3 / Bytes.toB256 [0x08] ∧
      AF = (afterSload sevm b (Bytes.toB256 [0x02])).getStorVal sevm.currentTarget
        (Bytes.toB256 [0x03]) ∧
      Mem.Reads M1 img1 ∧ Mem.Wf M1 ∧
      WordAt img1 0x1e0 Q ∧ WordAt img1 0x200 AF ∧
      XAt sevm post 0x3104
        (St (afterSload sevm (afterSload sevm b (Bytes.toB256 [0x02])) (Bytes.toB256 [0x03]))
          [] M1 G1) L := by
  xjd 0x30c6
  xs 0x30c8 (.push [0x02] (by decide)) ri_push
  xw 0x30c9 (.reg .sload) ri_sload
  xs 0x30cb (.push [0x03] (by decide)) ri_push
  xs 0x30cc (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x30cd (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x30ce (.reg .mul) ri_mul
  xs 0x30cf (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x30d0 (.reg .iszero) ri_iszero
  xs 0x30d1 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x30d2 (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0x30d3 (.reg (.dup 3)) (ri_dup (by rfl))
  xs 0x30d4 (.reg .div) ri_div
  xs 0x30d5 (.reg .eq) ri_eq
  xs 0x30d6 (.reg .or) ri_or
  xs 0x30d9 (.push [0x30, 0xde] (by decide)) ri_push
  xji 0x30da 0x30de hchk
  · xdead
  xjd 0x30df
  xs 0x30e0 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x30e1 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x30e2 (.reg .pop) ri_pop
  xs 0x30e3 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x30e4 (.reg .pop) ri_pop
  xs 0x30e5 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x30e6 (.reg .pop) ri_pop
  xs 0x30e8 (.push [0x08] (by decide)) ri_push
  xs 0x30e9 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x30ea (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x30ed (.push [0x30, 0xf2] (by decide)) ri_push
  xji 0x30ee 0x30f2 hw8
  · exact absurd hw8 (by decide)
  xjd 0x30f3
  xs 0x30f4 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x30f5 (.reg .div) ri_div
  xs 0x30f6 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x30f7 (.reg .pop) ri_pop
  xs 0x30f8 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x30f9 (.reg .pop) ri_pop
  xs 0x30fc (.push [0x01, 0xe0] (by decide)) ri_push
  xmo 0x30fd (.reg .mstore) (ri_mstore_imgAt (o := 0x1e0) rfl)
  xs 0x30ff (.push [0x03] (by decide)) ri_push
  xw 0x3100 (.reg .sload) ri_sload
  xs 0x3103 (.push [0x02, 0x00] (by decide)) ri_push
  xmo 0x3104 (.reg .mstore) (ri_mstore_imgAt (o := 0x200) rfl)
  refine ⟨b.getStorVal sevm.currentTarget (Bytes.toB256 [0x02]),
    b.getStorVal sevm.currentTarget (Bytes.toB256 [0x02]) * Bytes.toB256 [0x03],
    b.getStorVal sevm.currentTarget (Bytes.toB256 [0x02]) * Bytes.toB256 [0x03] /
      Bytes.toB256 [0x08],
    (afterSload sevm b (Bytes.toB256 [0x02])).getStorVal sevm.currentTarget (Bytes.toB256 [0x03]),
    M, _, _,
    rfl, rfl, (or_ne_zero hchk).imp eqCheck_ne_zero_eq eqCheck_ne_zero_eq, rfl, rfl,
    hR, hW, ?_, ?_, h⟩
  · exact WordAt.write_other (WordAt.write_self _ _ _) (Or.inl (by decide))
  · exact WordAt.write_self _ _ _

/-- `PC` at `0x3126`, pinned: it pushes the literal pc word (a run forgets the pc,
so the inversion goes through `Evm.step`, where the machine pc is present). -/
theorem xa_rli_pc3126 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {S : List B256}
    {M : Mem} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x3126 (St b S M G) L) :
    ∃ G', XAt sevm post 0x3127 (St b (Nat.toB256 0x3126 :: S) M G') L := by
  have hat : Ninst.At sevm.code 0x3126 (.reg .pc) := atN hcode (by kernel_rfl)
  have hn : ∀ x : Xinst, (Ninst.reg .pc) ≠ Ninst.exec x := by nofun
  have hstep : Evm.step ⟨0x3126, sevm, St b S M G⟩ =
      Ninst.step ⟨0x3126, sevm, St b S M G⟩ (.reg .pc) := Evm.step_next hat
  obtain ⟨exc, rfl, hg⟩ := h
  cases exc with
  | halt h => cases Ninst.step_ne_halt_ok (hstep.symm.trans h)
  | cont h next =>
    have hs : Ninst.step ⟨0x3126, sevm, St b S M G⟩ (.reg .pc) = .cont _ _ :=
      hstep.symm.trans h
    have e1 : Ninst.step ⟨0x3126, sevm, St b S M G⟩ (.reg .pc) =
        Step.ofExecution (0x3126 + Ninst.size (.reg .pc))
          (Rinst.run ⟨0x3126, sevm, St b S M G⟩ .pc) := rfl
    rw [e1] at hs
    have e2 : Rinst.run ⟨0x3126, sevm, St b S M G⟩ .pc =
        pushItem (Nat.toB256 0x3126) gBase (St b S M G) := rfl
    rw [e2] at hs
    have esz : Ninst.size (.reg .pc) = 1 := rfl
    rw [esz] at hs
    have e3 : 0x3126 + 1 = 0x3127 := rfl
    rw [e3] at hs
    have hok : ∃ dd, pushItem (Nat.toB256 0x3126) gBase (St b S M G) = .ok dd := by
      cases hpi : pushItem (Nat.toB256 0x3126) gBase (St b S M G)
      · rw [hpi] at hs
        cases hs
      · exact ⟨_, rfl⟩
    obtain ⟨dd, hpi⟩ := hok
    rw [hpi] at hs
    cases hs
    rename_i V
    have hp := Devm.pushBurn_of_pushItem hpi
    have hst : V.stack = Nat.toB256 0x3126 :: S := by
      have h2 := hp.stack
      simpa only [Stack.Push, Split, St.stack, List.cons_append, List.nil_append] using h2
    have e := St.of_stackRel hp
    rw [hst] at e
    obtain ⟨G', e'⟩ : ∃ G', V = St b (Nat.toB256 0x3126 :: S) M G' := ⟨_, e⟩
    subst e'
    have hx := XAt.of_exec next (lt_of_lt_of_le (gas_cont h) (le_of_lt hg))
    exact ⟨_, hx⟩
  | doneOk h _ _ _ =>
    obtain ⟨x, hx, -⟩ := Ninst.step_spawn_inv (hstep.symm.trans h)
    exact absurd hx (hn x)
  | runOk h _ _ _ _ =>
    obtain ⟨x, hx, -⟩ := Ninst.step_spawn_inv (hstep.symm.trans h)
    exact absurd hx (hn x)

/-- **`remove_liquidity_imbalance` `_A` call setup** (`0x3104` → `0xa9`): the eight words
`0x140 … 0x220` pushed, the resume pc formed (`PC + 6`, concretely `0x312c`), and the
jump into `_A` (entry 27). -/
theorem xa_rli_feeB {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {w140 w160 w180 w1a0 w1c0 w1e0 w200 w220 : B256}
    (hcode : sevm.code = code)
    (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (h140 : WordAt img 0x140 w140) (h160 : WordAt img 0x160 w160)
    (h180 : WordAt img 0x180 w180) (h1a0 : WordAt img 0x1a0 w1a0)
    (h1c0 : WordAt img 0x1c0 w1c0) (h1e0 : WordAt img 0x1e0 w1e0)
    (h200 : WordAt img 0x200 w200) (h220 : WordAt img 0x220 w220)
    (h : XAt sevm post 0x3104 (St b [] M G) L) :
    ∃ (M1 : Mem) (G1 : Nat),
      Mem.Reads M1 img ∧ Mem.Wf M1 ∧
      XAt sevm post 0xa9
        (St b (Nat.toB256 0x312c :: w220 :: w200 :: w1e0 :: w1c0 :: w1a0 :: w180 ::
          w160 :: w140 :: []) M1 G1) L := by
  xs 0x3107 (.push [0x01, 0x40] (by decide)) ri_push
  xmo 0x3108 (.reg .mload) (ri_mload_imgAt (o := 0x140) rfl)
  xs 0x310b (.push [0x01, 0x60] (by decide)) ri_push
  xmo 0x310c (.reg .mload) (ri_mload_imgAt (o := 0x160) rfl)
  xs 0x310f (.push [0x01, 0x80] (by decide)) ri_push
  xmo 0x3110 (.reg .mload) (ri_mload_imgAt (o := 0x180) rfl)
  xs 0x3113 (.push [0x01, 0xa0] (by decide)) ri_push
  xmo 0x3114 (.reg .mload) (ri_mload_imgAt (o := 0x1a0) rfl)
  xs 0x3117 (.push [0x01, 0xc0] (by decide)) ri_push
  xmo 0x3118 (.reg .mload) (ri_mload_imgAt (o := 0x1c0) rfl)
  xs 0x311b (.push [0x01, 0xe0] (by decide)) ri_push
  xmo 0x311c (.reg .mload) (ri_mload_imgAt (o := 0x1e0) rfl)
  xs 0x311f (.push [0x02, 0x00] (by decide)) ri_push
  xmo 0x3120 (.reg .mload) (ri_mload_imgAt (o := 0x200) rfl)
  xs 0x3123 (.push [0x02, 0x20] (by decide)) ri_push
  xmo 0x3124 (.reg .mload) (ri_mload_imgAt (o := 0x220) rfl)
  unfold WordAt at h140 h160 h180 h1a0 h1c0 h1e0 h200 h220
  simp only [h140, h160, h180, h1a0, h1c0, h1e0, h200, h220, B256.toB256_toBytes] at h
  xs 0x3126 (.push [0x06] (by decide)) ri_push
  obtain ⟨_, h⟩ := xa_rli_pc3126 hcode h
  xs 0x3128 (.reg .add) ri_add
  xs 0x312b (.push [0x00, 0xa9] (by decide)) ri_push
  xjmp 0xa9
  have hrw : Nat.toB256 0x3126 + Bytes.toB256 [0x06] = Nat.toB256 0x312c := by decide
  rw [hrw] at h
  exact ⟨_, _, hR, hW, h⟩

end Blanc.Lift.Curve3Pool
