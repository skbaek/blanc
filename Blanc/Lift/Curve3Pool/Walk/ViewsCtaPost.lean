import Blanc.Lift.Curve3Pool.Walk.ViewsCtaD1
import Blanc.Lift.Curve3Pool.Walk.ViewsGvp
import Blanc.Lift.Curve3Pool.Walk.AutoStep

/-! # `calc_token_amount`'s suffix: `totalSupply()`, the difference, `diff · supply / D0` -/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

section

variable {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}

-- SEGMENT: ctaFin
/-- **From the joined difference (`0xe03`) to the `RETURN`**: the checked `diff · supply`, the
nonzero `D0`, the output `diff · supply / D0`. -/
theorem xa_cta_fin {M : Mem} {df T D0 : B256}
    (hcode : sevm.code = code) (hV : VW M [(0x500, df), (0x460, T), (0x200, D0)])
    (h : XAt sevm post 0xe03 (St b [] M G) L) :
    L = [] ∧ B256.Nofm df T ∧ D0 ≠ 0 ∧ (∀ a, post.getStor a = b.getStor a) ∧
      post.logs = b.logs ∧ post.output = (df * T / D0).toBytes := by
  xa 2
  xl 0xe08 0x500  -- e07 MLOAD
  xs 0xe0b (.push [0x04, 0x60] (by decide)) ri_push  -- e08 PUSH2 0x0460
  xl 0xe0c 0x460  -- e0b MLOAD
  xa 12
  xji 0xe1b 0xe1f hw
  · xdead
  have hmul := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xa 9
  xl 0xe2b 0x200  -- e2a MLOAD
  xa 3
  xji 0xe31 0xe35 hw
  · xdead
  have hD0 := hw
  clear hw
  xa 8
  have hfinalwf := hV.wf
  xsw 0xe3f 0x0  -- e3e MSTORE
  xa 2
  obtain ⟨hrun, rfl⟩ := xa_halt (l := .return_) (atL hcode (by kernel_rfl)) h
  obtain ⟨hout, hstor, hlogs⟩ := ri_return hrun
  refine ⟨rfl, hmul, hD0, fun a => by rw [hstor], by rw [hlogs], ?_⟩
  rw [hout, show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [32]).toNat = 32 from rfl, Mem.read_write_word_of_wf hfinalwf]

-- SEGMENT: ctaTail
/-- **From `D1` at `0x340` (`0xd77`) to the `RETURN`**: `totalSupply()` from the token (the
frame's only child, static, a word back), the checked difference by the deposit flag, and the
output `diff · supply / D0`. -/
theorem xa_cta_tail {M : Mem} {D0 D1 : B256}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (htok : ¬ sevm.benvStat.rules.isPrecomp ((b.getStor sevm.currentTarget).get tokenSlot).toAdr)
    (hV : VW M [(0x340, D1), (0x200, D0)])
    (h : XAt sevm post 0xd77 (St b [] M G) L) :
    ∃ c df, L = [c] ∧
      StaticWordChild ((b.getStor sevm.currentTarget).get tokenSlot).toAdr totalSupplyData c ∧
      ((ctaDep sevm ≠ 0 ∧ D0.toNat ≤ D1.toNat ∧ df = D1 - D0) ∨
        (ctaDep sevm = 0 ∧ D1.toNat ≤ D0.toNat ∧ df = D0 - D1)) ∧
      B256.Nofm df (vSupply c) ∧ D0 ≠ 0 ∧ (∀ a, post.getStor a = b.getStor a) ∧
      post.logs = b.logs ∧ post.output = (df * vSupply c / D0).toBytes := by
  xa 5
  have hW0 := hV.wf
  xsw 0xd87 0x480  -- d86 MSTORE
  xa 2
  xw 0xd8d (.reg .sload) ri_sload  -- d8c SLOAD
  xs 0xd8e (.reg .gas) ri_gas_remaining  -- d8d GAS
  obtain ⟨d, flag, out, M', L1, h, hVo, hrd, hob, hstor, hlogs, hk⟩ :=
    xa_staticcallV (pc' := 0xd8f) (o := 0x4e0) hfork (atN hcode (by kernel_rfl)) rfl rfl rfl hV h
  clear hV
  xs 0xd92 (.push [0x0d, 0x97] (by decide)) ri_push  -- d8f PUSH2 0x0d97
  xji 0xd93 0xd97 hw
  · xdead
  xa 5
  have hwf := hw
  clear hw
  rcases hk hwf with ⟨hpre, -⟩ | ⟨c, hL, hdepth, hout, hacc, hcodeK, htgt, hdata, hstat, hcout,
    hclogs, hcpre, hcpost⟩
  · exact absurd hpre (by rw [getStorVal_eq, tokenSlot_lit]; exact htok)
  clear hk
  subst hcout
  xji 0xda0 0xda4 hw
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
  xl 0xdac 0x4e0  -- dab MLOAD
  xs 0xdaf (.push [0x04, 0x60] (by decide)) ri_push  -- dac PUSH2 0x0460
  xsw 0xdb0 0x460  -- daf MSTORE
  xa 2
  xsw 0xdb6 0x500  -- db5 MSTORE
  xa 4
  xji 0xdbe 0xde2 hw
  swap
  · have hd0 := B256.eq_of_eqCheck_ne_zero hw
    clear hw
    xa 2
    xl 0xde7 0x200  -- de6 MLOAD
    xs 0xdea (.push [0x03, 0x40] (by decide)) ri_push  -- de7 PUSH2 0x0340
    xl 0xdeb 0x340  -- dea MLOAD
    xa 5
    xji 0xdf3 0xdf7 hw
    · xdead
    have hle := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
    clear hw
    xa 9
    xsw 0xe03 0x500  -- e02 MSTORE
    obtain ⟨hL1, hm, hD0, hs, hl, ho⟩ := xa_cta_fin (df := D0 - D1) (T := vSupply c) (D0 := D0)
      hcode (hV.sub (by
      simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])) h
    refine ⟨c, _, by rw [hL, hL1], ⟨?_, ?_, hstat, hlen, hclogs⟩, .inr ⟨hd0, hle, rfl⟩, hm, hD0,
      fun a => by rw [hs, hstor, afterSload_getStor], by rw [hl, hlogs, afterSload_logs], ho⟩
    · rw [htgt, getStorVal_eq, tokenSlot_lit]
    · rw [hdata, show (Bytes.toB256 [4, 0x9c]).toNat = 1180 from rfl,
        show (Bytes.toB256 [4]).toNat = 4 from rfl,
        Mem.read_write_word_inside hW0 1152 _ (by decide) (by decide)]
      decide
  have hd1 := ne_of_eqCheck_eq_zero hw
  clear hw
  xs 0xdc1 (.push [0x03, 0x40] (by decide)) ri_push  -- dbe PUSH2 0x0340
  xl 0xdc2 0x340  -- dc1 MLOAD
  xs 0xdc5 (.push [0x02, 0x00] (by decide)) ri_push  -- dc2 PUSH2 0x0200
  xl 0xdc6 0x200  -- dc5 MLOAD
  xa 5
  xji 0xdce 0xdd2 hw
  · xdead
  have hle := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xa 9
  xsw 0xdde 0x500  -- ddd MSTORE
  xs 0xde1 (.push [0x0e, 0x03] (by decide)) ri_push  -- dde PUSH2 0x0e03
  xjmp 0xe03  -- de1 JUMP
  obtain ⟨hL1, hm, hD0, hs, hl, ho⟩ := xa_cta_fin (df := D1 - D0) (T := vSupply c) (D0 := D0)
    hcode (hV.sub (by
    simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])) h
  refine ⟨c, _, by rw [hL, hL1], ⟨?_, ?_, hstat, hlen, hclogs⟩, .inl ⟨hd1, hle, rfl⟩, hm, hD0,
    fun a => by rw [hs, hstor, afterSload_getStor], by rw [hl, hlogs, afterSload_logs], ho⟩
  · rw [htgt, getStorVal_eq, tokenSlot_lit]
  · rw [hdata, show (Bytes.toB256 [4, 0x9c]).toNat = 1180 from rfl,
      show (Bytes.toB256 [4]).toNat = 4 from rfl,
      Mem.read_write_word_inside hW0 1152 _ (by decide) (by decide)]
    decide

end

end Blanc.Lift.Curve3Pool
