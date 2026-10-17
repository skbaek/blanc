import Blanc.Lift.Curve3Pool.Walk.ViewsKit
import Blanc.Lift.Curve3Pool.Walk.ViewsGvp
import Blanc.Lift.Curve3Pool.Callee.GetYD

/-!
# `_calc_withdraw_one_coin(_token_amount, i)` on the derivation: the prologue

The private function (entry 36, pc `0x3cca`, return slot `0x180`, two return words) is walked on
the actual derivation (`XAt`), not as an exec-free specification: it makes the
`totalSupply()` `STATICCALL` (`0x3d78`). Its callees `_A`, `_xp`, `get_D` and `get_y_D` are
bridged. This file: the kit (`get_y_D` over the views' carrier) and the prologue up to the
supply at `0x280`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

section

variable {sevm : Sevm} {post b : Devm} {ρ : B256} {S : List B256} {M : Mem} {G : Nat}
  {L : List Exec.Frame} {LW : List (Nat × B256)} {s : State}

theorem cw_yd_entry :
    cert.entries[753]? = some ⟨0x3999, [.ret, .unk, .unk, .unk, .unk, .unk, .unk], 1⟩ := by
  have h : (cert.entries[753]?).map (fun e => (e.pc, e.frame, e.rets)) =
      some (0x3999, [.ret, .unk, .unk, .unk, .unk, .unk, .unk], 1) := by decide +kernel
  revert h
  generalize cert.entries[753]? = o
  rcases o with _ | ⟨pc, fr, r⟩
  · intro h; cases h
  · intro h
    cases h
    rfl
theorem cw_yd_prog : cert.prog[753]? = some t_3999_c753 := by decide +kernel
theorem cw_yd_mems : mems.getD 753 [] = [] := by decide +kernel

/-- **`get_y_D` crossed and read** over the carrier (memory covering `[0, 0x340)`): `y` with
`getYDChk A i xp D = some y`, the base unchanged, the words off its window kept and `y` at the
scratch word `0`. -/
theorem xa_vGetYD (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    {A i x0 x1 x2 D : B256} (hV : VW M LW) (hcov : 0x340 ≤ M.size)
    (h : XAt sevm post 0x3999 (St b (ρ :: A :: i :: x0 :: x1 :: x2 :: D :: S) M G) L) :
    ∃ v M' G', XAt sevm post ρ.toNat (St b (v :: S) M' G') L ∧
      ∃ hi : i.toNat < 3,
        getYDChk A.toNat ⟨i.toNat, hi⟩ (V3.mk x0.toNat x1.toNat x2.toNat).get D.toNat =
          some v.toNat ∧
      VW M' ((0, v) :: wordsOffW [(0, 32), (0x140, 0x340)] LW) := by
  rcases xa_calleeC hc cw_yd_entry cw_yd_prog cw_yd_mems yd_execFreeSet yd_free hcode hfork
      (S := [ρ, A, i, x0, x1, x2, D]) (base := S) rfl
      (.cons rfl (.cons trivial (.cons trivial (.cons trivial (.cons trivial (.cons trivial
        (.cons trivial .nil))))))) h with
    ⟨run, -⟩ | ⟨d', S', run, hx, -, -⟩
  · obtain ⟨d, he, -⟩ := getYD_spec hV.al hcov run
    cases he
  · obtain ⟨d, he, v, M', G', rfl, hi, hv, hsz, hw0, hk⟩ := getYD_spec hV.al hcov run
    cases he
    obtain ⟨hk, hwf⟩ := hk hV.wf
    have hV' := hV.keepsOff hk hwf (by rw [hsz]; exact hV.al)
    exact ⟨v, M', G', hx, hi, hv, ⟨Words.cons.mpr ⟨hw0 0 v List.mem_cons_self, hV'.words⟩,
      hwf, hV'.al⟩⟩

/-- `PRECISION_MUL`'s pushed words. -/
abbrev cwP1 : B256 := Bytes.toB256 [0x01]
abbrev cwPm : B256 := Bytes.toB256 [0xe8, 0xd4, 0xa5, 0x10, 0x00]

-- SEGMENT: cwA
/-- **The prologue** (`0x3cca` to `0x3d9a`): the arguments and return address stored, `amp =
_A()`, the adjusted fee, `PRECISION_MUL`, and `totalSupply()` read from the token (the next
child, static, a word back) into `0x280`. -/
theorem xa_cw_a (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) {a i : B256}
    (ha : Abstracts (b.getStor sevm.currentTarget) s) (hV : VW M [])
    (htok : ¬ sevm.benvStat.rules.isPrecomp ((b.getStor sevm.currentTarget).get tokenSlot).toAdr)
    (h : XAt sevm post 0x3cca (St b (ρ :: a :: i :: S) M G) L) :
    ∃ (A F : B256) (c : Exec.Frame) (d : Devm) (M' : Mem) (G' : Nat) (L' : List Exec.Frame),
      L = c :: L' ∧
      StaticWordChild ((b.getStor sevm.currentTarget).get tokenSlot).toAdr totalSupplyData c ∧
      aChk s sevm.benvStat.time.toNat = some A.toNat ∧ feeAdj s = some F.toNat ∧
      (∀ x, d.getStor x = b.getStor x) ∧ d.logs = b.logs ∧
      XAt sevm post 0x3d9a (St d S M' G') L' ∧
      VW M' [(0x280, vSupply c), (0x260, cwPm), (0x240, cwPm), (0x220, cwP1), (0x200, F),
        (0x1a0, A), (0x180, ρ), (0x160, i), (0x140, a)] := by
  xjd 0x3ccb  -- 3cca JUMPDEST
  xs 0x3cce (.push [0x01, 0x80] (by decide)) ri_push  -- 3ccb PUSH2 0x0180
  xsw 0x3ccf 0x180  -- 3cce MSTORE
  xs 0x3cd2 (.push [0x01, 0x40] (by decide)) ri_push  -- 3ccf PUSH2 0x0140
  xsw 0x3cd3 0x140  -- 3cd2 MSTORE
  xs 0x3cd6 (.push [0x01, 0x60] (by decide)) ri_push  -- 3cd3 PUSH2 0x0160
  xsw 0x3cd7 0x160  -- 3cd6 MSTORE
  xs 0x3cda (.push [0x01, 0x40] (by decide)) ri_push  -- 3cd7 PUSH2 0x0140
  xl 0x3cdb 0x140  -- 3cda MLOAD
  xs 0x3cde (.push [0x01, 0x60] (by decide)) ri_push  -- 3cdb PUSH2 0x0160
  xl 0x3cdf 0x160  -- 3cde MLOAD
  xs 0x3ce2 (.push [0x01, 0x80] (by decide)) ri_push  -- 3cdf PUSH2 0x0180
  xl 0x3ce3 0x180  -- 3ce2 MLOAD
  xs 0x3ce6 (.push [0x01, 0xa0] (by decide)) ri_push  -- 3ce3 PUSH2 0x01a0
  xlu 0x3ce7  -- 3ce6 MLOAD
  xs 0x3ce9 (.push [0x06] (by decide)) ri_push  -- 3ce7 PUSH1 0x06
  cvpc 0x3cea  -- 3ce9 PC
  xs 0x3ceb (.reg .add) ri_add  -- 3cea ADD
  xs 0x3cee (.push [0x00, 0xa9] (by decide)) ri_push  -- 3ceb PUSH2 0x00a9
  xjmp 0xa9  -- 3cee JUMP
  obtain ⟨A, b1, M1, _, hb1, h, hA, hV1⟩ := xa_vAV hc hcode hfork ha hV h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xjd 0x3cf0  -- 3cef JUMPDEST
  xs 0x3cf3 (.push [0x01, 0xe0] (by decide)) ri_push  -- 3cf0 PUSH2 0x01e0
  xsw 0x3cf4 0x1e0  -- 3cf3 MSTORE
  xs 0x3cf7 (.push [0x01, 0xa0] (by decide)) ri_push  -- 3cf4 PUSH2 0x01a0
  xsw 0x3cf8 0x1a0  -- 3cf7 MSTORE
  xs 0x3cfb (.push [0x01, 0x80] (by decide)) ri_push  -- 3cf8 PUSH2 0x0180
  xsw 0x3cfc 0x180  -- 3cfb MSTORE
  xs 0x3cff (.push [0x01, 0x60] (by decide)) ri_push  -- 3cfc PUSH2 0x0160
  xsw 0x3d00 0x160  -- 3cff MSTORE
  xs 0x3d03 (.push [0x01, 0x40] (by decide)) ri_push  -- 3d00 PUSH2 0x0140
  xsw 0x3d04 0x140  -- 3d03 MSTORE
  xs 0x3d07 (.push [0x01, 0xe0] (by decide)) ri_push  -- 3d04 PUSH2 0x01e0
  xl 0x3d08 0x1e0  -- 3d07 MLOAD
  xs 0x3d0b (.push [0x01, 0xa0] (by decide)) ri_push  -- 3d08 PUSH2 0x01a0
  xsw 0x3d0c 0x1a0  -- 3d0b MSTORE
  xs 0x3d0e (.push [0x02] (by decide)) ri_push  -- 3d0c PUSH1 0x02
  xw 0x3d0f (.reg .sload) ri_sload  -- 3d0e SLOAD
  xs 0x3d11 (.push [0x03] (by decide)) ri_push  -- 3d0f PUSH1 0x03
  xs 0x3d12 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3d11 DUP1
  xs 0x3d13 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3d12 DUP3
  xs 0x3d14 (.reg .mul) ri_mul  -- 3d13 MUL
  xs 0x3d15 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3d14 DUP3
  xs 0x3d16 (.reg .iszero) ri_iszero  -- 3d15 ISZERO
  xs 0x3d17 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3d16 DUP3
  xs 0x3d18 (.reg (.dup 4)) (ri_dup (by rfl))  -- 3d17 DUP5
  xs 0x3d19 (.reg (.dup 3)) (ri_dup (by rfl))  -- 3d18 DUP4
  xs 0x3d1a (.reg .div) ri_div  -- 3d19 DIV
  xs 0x3d1b (.reg .eq) ri_eq  -- 3d1a EQ
  xs 0x3d1c (.reg .or) ri_or  -- 3d1b OR
  xs 0x3d1f (.push [0x3d, 0x24] (by decide)) ri_push  -- 3d1c PUSH2 0x3d24
  xji 0x3d20 0x3d24 hw
  · xdead
  have hm3 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xjd 0x3d25  -- 3d24 JUMPDEST
  xs 0x3d26 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3d25 DUP1
  xs 0x3d27 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3d26 SWAP1
  xs 0x3d28 (.reg .pop) ri_pop  -- 3d27 POP
  xs 0x3d29 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3d28 SWAP1
  xs 0x3d2a (.reg .pop) ri_pop  -- 3d29 POP
  xs 0x3d2b (.reg (.swap 0)) (ri_swap (by rfl))  -- 3d2a SWAP1
  xs 0x3d2c (.reg .pop) ri_pop  -- 3d2b POP
  xs 0x3d2e (.push [0x08] (by decide)) ri_push  -- 3d2c PUSH1 0x08
  xs 0x3d2f (.reg (.dup 0)) (ri_dup (by rfl))  -- 3d2e DUP1
  xs 0x3d30 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3d2f DUP1
  xs 0x3d33 (.push [0x3d, 0x38] (by decide)) ri_push  -- 3d30 PUSH2 0x3d38
  xji 0x3d34 0x3d38 hw
  · xdead
  clear hw
  xjd 0x3d39  -- 3d38 JUMPDEST
  xs 0x3d3a (.reg (.dup 2)) (ri_dup (by rfl))  -- 3d39 DUP3
  xs 0x3d3b (.reg .div) ri_div  -- 3d3a DIV
  xs 0x3d3c (.reg (.swap 0)) (ri_swap (by rfl))  -- 3d3b SWAP1
  xs 0x3d3d (.reg .pop) ri_pop  -- 3d3c POP
  xs 0x3d3e (.reg (.swap 0)) (ri_swap (by rfl))  -- 3d3d SWAP1
  xs 0x3d3f (.reg .pop) ri_pop  -- 3d3e POP
  xs 0x3d42 (.push [0x02, 0x00] (by decide)) ri_push  -- 3d3f PUSH2 0x0200
  xsw 0x3d43 0x200  -- 3d42 MSTORE
  xs 0x3d46 (.push [0x02, 0x20] (by decide)) ri_push  -- 3d43 PUSH2 0x0220
  xs 0x3d48 (.push [0x01] (by decide)) ri_push  -- 3d46 PUSH1 0x01
  xs 0x3d49 (.reg (.dup 1)) (ri_dup (by rfl))  -- 3d48 DUP2
  xsw 0x3d4a 0x220  -- 3d49 MSTORE
  xs 0x3d50 (.push [0xe8, 0xd4, 0xa5, 0x10, 0x00] (by decide)) ri_push  -- 3d4a PUSH5 0xe8d4a51000
  xs 0x3d51 (.reg (.dup 1)) (ri_dup (by rfl))  -- 3d50 DUP2
  xs 0x3d53 (.push [0x20] (by decide)) ri_push  -- 3d51 PUSH1 0x20
  xs 0x3d54 (.reg .add) ri_add  -- 3d53 ADD
  xsw 0x3d55 0x240  -- 3d54 MSTORE
  xs 0x3d5b (.push [0xe8, 0xd4, 0xa5, 0x10, 0x00] (by decide)) ri_push  -- 3d55 PUSH5 0xe8d4a51000
  xs 0x3d5c (.reg (.dup 1)) (ri_dup (by rfl))  -- 3d5b DUP2
  xs 0x3d5e (.push [0x40] (by decide)) ri_push  -- 3d5c PUSH1 0x40
  xs 0x3d5f (.reg .add) ri_add  -- 3d5e ADD
  xsw 0x3d60 0x260  -- 3d5f MSTORE
  xs 0x3d61 (.reg .pop) ri_pop  -- 3d60 POP
  xs 0x3d63 (.push [0x20] (by decide)) ri_push  -- 3d61 PUSH1 0x20
  xs 0x3d66 (.push [0x03, 0x00] (by decide)) ri_push  -- 3d63 PUSH2 0x0300
  xs 0x3d68 (.push [0x04] (by decide)) ri_push  -- 3d66 PUSH1 0x04
  xs 0x3d6d (.push [0x18, 0x16, 0x0d, 0xdd] (by decide)) ri_push  -- 3d68 PUSH4 0x18160ddd
  xs 0x3d70 (.push [0x02, 0xa0] (by decide)) ri_push  -- 3d6d PUSH2 0x02a0
  have hW0 := hV.wf
  xsw 0x3d71 0x2a0  -- 3d70 MSTORE
  xs 0x3d74 (.push [0x02, 0xbc] (by decide)) ri_push  -- 3d71 PUSH2 0x02bc
  xs 0x3d76 (.push [0x05] (by decide)) ri_push  -- 3d74 PUSH1 0x05
  xw 0x3d77 (.reg .sload) ri_sload  -- 3d76 SLOAD
  xs 0x3d78 (.reg .gas) ri_gas_remaining  -- 3d77 GAS
  obtain ⟨d, flag, out, M', L1, h, hVo, hrd, hob, hstor, hlogs, hk⟩ :=
    xa_staticcallV (pc' := 0x3d79) (o := 0x300) hfork (atN hcode (by kernel_rfl)) rfl rfl rfl hV h
  clear hV
  xs 0x3d7c (.push [0x3d, 0x81] (by decide)) ri_push  -- 3d79 PUSH2 0x3d81
  xji 0x3d7d 0x3d81 hw
  · xdead
  xjd 0x3d82  -- 3d81 JUMPDEST
  xs 0x3d84 (.push [0x1f] (by decide)) ri_push  -- 3d82 PUSH1 0x1f
  xs 0x3d85 (.reg .returndatasize) ri_returndatasize  -- 3d84 RETURNDATASIZE
  xs 0x3d86 (.reg .gt) ri_gt  -- 3d85 GT
  xs 0x3d89 (.push [0x3d, 0x8e] (by decide)) ri_push  -- 3d86 PUSH2 0x3d8e
  have hwf := hw
  clear hw
  rcases hk hwf with ⟨hpre, -⟩ | ⟨c, hL, hdepth, hout, hacc, hcodeK, htgt, hdata, hstat, hcout,
    hclogs, hcpre, hcpost⟩
  · exact absurd hpre (by rw [getStorVal_eq, afterSload_getStor, hb1.getStor, tokenSlot_lit]; exact htok)
  clear hk
  subst hcout
  xji 0x3d8a 0x3d8e hw
  · xdead
  have hlen : 32 ≤ c.post.output.length := by
    have e := gtCheck_ne_zero hw
    rw [hrd, B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hob] at e
    exact e
  clear hw
  have hV := hVo hlen
  clear hVo
  vnorm
  xjd 0x3d8f  -- 3d8e JUMPDEST
  xs 0x3d91 (.push [0x00] (by decide)) ri_push  -- 3d8f PUSH1 0x00
  xs 0x3d92 (.reg .pop) ri_pop  -- 3d91 POP
  xs 0x3d95 (.push [0x03, 0x00] (by decide)) ri_push  -- 3d92 PUSH2 0x0300
  xl 0x3d96 0x300  -- 3d95 MLOAD
  xs 0x3d99 (.push [0x02, 0x80] (by decide)) ri_push  -- 3d96 PUSH2 0x0280
  xsw 0x3d9a 0x280  -- 3d99 MSTORE
  have hfee : (b1.getStorVal sevm.currentTarget (Bytes.toB256 [2])).toNat = s.fee := by
    rw [getStorVal_eq, hb1.getStor]; exact ha.fee
  refine ⟨A, b1.getStorVal sevm.currentTarget (Bytes.toB256 [2]) * Bytes.toB256 [3] /
    Bytes.toB256 [8], c, d, _, _, L1, hL, ?_, hA, ?_, ?_, ?_, h, hV.sub ?_⟩
  · refine ⟨?_, ?_, hstat, hlen, hclogs⟩
    · rw [htgt, getStorVal_eq, afterSload_getStor, hb1.getStor, tokenSlot_lit]
    · rw [hdata, show (Bytes.toB256 [2, 0xbc]).toNat = 700 from rfl,
        show (Bytes.toB256 [4]).toNat = 4 from rfl,
        Mem.read_write_word_inside hW0 672 _ (by decide) (by decide)]
      decide
  · unfold feeAdj
    rw [← hfee, show (3 : Nat) = (Bytes.toB256 [3]).toNat from rfl, chkMul_toNat_of_nofm hm3,
      Option.bind_eq_bind, Option.bind_some, show (8 : Nat) = (Bytes.toB256 [8]).toNat from rfl,
      chkDiv_toNat_of_ne (by decide)]
  · intro x
    rw [hstor, afterSload_getStor, afterSload_getStor, hb1.getStor]
  · rw [hlogs, afterSload_logs, afterSload_logs, hb1.logs]
  · simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self]

end

end Blanc.Lift.Curve3Pool
