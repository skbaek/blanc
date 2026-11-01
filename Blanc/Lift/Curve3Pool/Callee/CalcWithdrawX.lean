import Blanc.Lift.Curve3Pool.Walk.ViewsKit
import Blanc.Lift.Curve3Pool.Walk.ViewsGvp
import Blanc.Lift.Curve3Pool.Callee.GetYD
import Blanc.Lift.Curve3Pool.Walk.AutoStep

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
        (0x1a0, A), (0x180, ρ), (0x160, i), (0x140, a)] ∧
      d.output = b.output ∧ (∀ x, b.getCode x ≠ .empty → d.getCode x = b.getCode x) ∧
      (IdReady sevm b → c.post.getCode 4 = c.pre.getCode 4 → IdReady sevm d) := by
  xa 2
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
  xa 2
  xjmp 0xa9  -- 3cee JUMP
  obtain ⟨A, b1, M1, _, hb1, h, hA, hV1⟩ := xa_vAV hc hcode hfork ha hV h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xa 2
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
  xa 13
  xji 0x3d20 0x3d24 hw
  · xdead
  have hm3 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xa 12
  xji 0x3d34 0x3d38 hw
  · xdead
  clear hw
  xa 8
  xsw 0x3d43 0x200  -- 3d42 MSTORE
  xa 3
  xsw 0x3d4a 0x220  -- 3d49 MSTORE
  xa 4
  xsw 0x3d55 0x240  -- 3d54 MSTORE
  xa 4
  xsw 0x3d60 0x260  -- 3d5f MSTORE
  xa 6
  have hW0 := hV.wf
  xsw 0x3d71 0x2a0  -- 3d70 MSTORE
  xa 2
  xw 0x3d77 (.reg .sload) ri_sload  -- 3d76 SLOAD
  xs 0x3d78 (.reg .gas) ri_gas_remaining  -- 3d77 GAS
  obtain ⟨d, flag, out, M', L1, h, hVo, hrd, hob, hstor, hlogs, hk⟩ :=
    xa_staticcallV (pc' := 0x3d79) (o := 0x300) hfork (atN hcode (by kernel_rfl)) rfl rfl rfl hV h
  clear hV
  xs 0x3d7c (.push [0x3d, 0x81] (by decide)) ri_push  -- 3d79 PUSH2 0x3d81
  xji 0x3d7d 0x3d81 hw
  · xdead
  xa 5
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
    have e := B256.lt_of_gtCheck_ne_zero hw
    rw [hrd, B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hob] at e
    exact e
  clear hw
  have hV := hVo hlen
  clear hVo
  vnorm
  xa 4
  xl 0x3d96 0x300  -- 3d95 MLOAD
  xs 0x3d99 (.push [0x02, 0x80] (by decide)) ri_push  -- 3d96 PUSH2 0x0280
  xsw 0x3d9a 0x280  -- 3d99 MSTORE
  have hfee : (b1.getStorVal sevm.currentTarget (Bytes.toB256 [2])).toNat = s.fee := by
    rw [getStorVal_eq, hb1.getStor]; exact ha.fee
  refine ⟨A, b1.getStorVal sevm.currentTarget (Bytes.toB256 [2]) * Bytes.toB256 [3] /
    Bytes.toB256 [8], c, d, _, _, L1, hL, ?_, hA, ?_, ?_, ?_, h, hV.sub ?_, ?_, ?_, ?_⟩
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
  · rw [hout, afterSload_output, afterSload_output, hb1.output]
  · intro x hx
    rw [hcodeK x (by rw [afterSload_getCode, afterSload_getCode, hb1.getCode]; exact hx),
      afterSload_getCode, afterSload_getCode, hb1.getCode]
  · intro hid h4
    have hB := ((hb1.idReady hid).afterSload (Bytes.toB256 [2])).afterSload
      (Bytes.toB256 [5])
    exact ⟨by rw [hcpost, h4, hcpre]; exact hB.nodeleg, hacc _ hB.warm, hid.pre, hid.fork⟩

end

end Blanc.Lift.Curve3Pool
