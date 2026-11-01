import Blanc.Lift.Curve3Pool.Walk.RemoveImbalanceDispatch
import Blanc.Lift.Curve3Pool.Callee.CalcWithdrawXSpec
import Blanc.Lift.Curve3Pool.Walk.Exchange
import Blanc.Lift.Curve3Pool.Walk.AutoStep

/-!
# `remove_liquidity_imbalance` on the word carrier, part 1: guards, supply, `_A`, balances

`xa_rli_front` (`0x304f` → the first frame save's head `0x31b7`): `assert lock == 0; lock = 1`,
the non-payable guard, `assert not is_killed`, `token.totalSupply()` (the frame's next child,
static, at least a word back) with `total_supply != 0`, `_fee = fee * 3 / 8` and `admin_fee`,
the eight words `0x140 … 0x220` pushed around `_A` (crossed with `xa_vAV`) and written back,
`amp` at `0x220`, `old_balances` loaded from storage to `0x280` and copied to `new_balances` at
`0x2e0`. The walk runs over the views' word carrier `VW` (the dispatcher's memory is aligned),
with no premise on the token beyond its not being a precompile: the base's code at address 4 is
carried through the child by the caller's per-child premise.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

section

variable {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {s : State}

-- SEGMENT: rliFront
/-- **Guards, supply, `_A` and the balances** (`0x304f` → `0x31b7`). -/
theorem xa_rli_front (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (htok : ¬ sevm.benvStat.rules.isPrecomp ((b.getStor sevm.currentTarget).get tokenSlot).toAdr)
    (h : XAt sevm post 0x304f (St b [] (vdMem sevm) G) L) :
    (b.getStor sevm.currentTarget).get lockSlot = 0 ∧ sevm.value = 0 ∧
    (b.getStor sevm.currentTarget).get isKilledSlot = 0 ∧
    ∃ (c : Exec.Frame) (L' : List Exec.Frame) (A : B256) (b' : Devm) (M' : Mem) (G' : Nat),
      L = c :: L' ∧
      StaticWordChild ((b.getStor sevm.currentTarget).get tokenSlot).toAdr totalSupplyData c ∧
      vSupply c ≠ 0 ∧ ((b.getStor sevm.currentTarget).get feeSlot).Nofm (Bytes.toB256 [3]) ∧
      aChk s sevm.benvStat.time.toNat = some A.toNat ∧
      (∀ x, (b'.getStor sevm.currentTarget).get x =
        ((b.getStor sevm.currentTarget).set lockSlot 1).get x) ∧
      b'.logs = b.logs ∧ b'.output = b.output ∧
      (∀ x, b.getCode x ≠ .empty → b'.getCode x = b.getCode x) ∧
      (IdReady sevm b → c.post.getCode 4 = c.pre.getCode 4 → IdReady sevm b') ∧
      XAt sevm post 0x31b7 (St b' [] M' G') L' ∧
      VW M' [(0x360, Bytes.toB256 [1, 64]), (0x140, vSupply c),
        (0x1e0, (b.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8]),
        (0x200, (b.getStor sevm.currentTarget).get adminFeeSlot), (0x220, A),
        (0x280, balAt (b.getStor sevm.currentTarget) 0),
        (0x2a0, balAt (b.getStor sevm.currentTarget) 1),
        (0x2c0, balAt (b.getStor sevm.currentTarget) 2),
        (0x2e0, balAt (b.getStor sevm.currentTarget) 0),
        (0x300, balAt (b.getStor sevm.currentTarget) 1),
        (0x320, balAt (b.getStor sevm.currentTarget) 2)] := by
  have hV : VW (vdMem sevm) [] := ⟨Words.nil _, vyMem_wf Mem.wf_empty _,
    by rw [vyMem_empty_size]⟩
  xs 0x3053 (.push [0xff, 0xff, 0xff] (by decide)) ri_push  -- 304f PUSH3 0xffffff
  xw 0x3054 (.reg .sload) ri_sload  -- 3053 SLOAD
  xa 2
  xji 0x3059 0x305d hw
  · xdead
  have hlock : (b.getStor sevm.currentTarget).get lockSlot = 0 := by
    have e := B256.eq_of_eqCheck_ne_zero hw
    rw [lockSlot_lit] at e
    exact e
  clear hw
  xa 3
  xw 0x3065 (.reg .sstore) ri_sstore  -- 3064 SSTORE
  xa 3
  xji 0x306b 0x306f hw
  · xdead
  have hval : sevm.value = 0 := B256.eq_of_eqCheck_ne_zero hw
  clear hw
  xa 2
  xw 0x3073 (.reg .sload) ri_sload  -- 3072 SLOAD
  xa 2
  xji 0x3078 0x307c hw
  · xdead
  have hkill : (b.getStor sevm.currentTarget).get isKilledSlot = 0 := by
    have e := B256.eq_of_eqCheck_ne_zero hw
    rw [isKilledSlot_lit, getStorVal_afterSstore_ne (by decide), getStorVal_afterSload,
      getStorVal_eq] at e
    exact e
  clear hw
  xa 6
  xsw 0x308d 0x160  -- 308c MSTORE
  xa 2
  xw 0x3093 (.reg .sload) ri_sload  -- 3092 SLOAD
  xs 0x3094 (.reg .gas) ri_gas_remaining  -- 3093 GAS
  obtain ⟨d, flag, out, M', L1, h, hVo, hrd, hob, hstor, hlogs, hk⟩ :=
    xa_staticcallV (pc' := 0x3095) (o := 0x1c0) hfork (atN hcode (by kernel_rfl)) rfl rfl rfl hV h
  clear hV
  xs 0x3098 (.push [0x30, 0x9d] (by decide)) ri_push  -- 3095 PUSH2 0x309d
  xji 0x3099 0x309d hw
  · xdead
  have hwf := hw
  clear hw
  rcases hk hwf with ⟨hpre, -⟩ | ⟨c, hL, hdepth, hout, hacc, hcodeK, htgt, hdata, hstat, hcout,
    hclogs, hcpre, hcpost⟩
  · exact absurd hpre (by
      rw [getStorVal_eq, afterSload_getStor, afterSstore_getStor_self, afterSload_getStor,
        tokenSlot_lit, Stor.get_set_ne _ (show Bytes.toB256 [255, 255, 255] ≠ tokenSlot by decide)]
      exact htok)
  clear hk hwf
  subst hcout
  xa 5
  xji 0x30a6 0x30aa hw
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
  xl 0x30b2 0x1c0  -- 30b1 MLOAD
  xs 0x30b5 (.push [0x01, 0x40] (by decide)) ri_push  -- 30b2 PUSH2 0x0140
  xsw 0x30b6 0x140  -- 30b5 MSTORE
  xa 2
  xl 0x30bc 0x140  -- 30bb MLOAD
  xa 2
  xji 0x30c1 0x30c5 hw
  · xdead
  have hT0 : vSupply c ≠ 0 := by
    rw [zero_lit, B256.xor_zero] at hw
    exact hw
  clear hw
  xa 2
  xw 0x30c9 (.reg .sload) ri_sload  -- 30c8 SLOAD
  xa 13
  xji 0x30da 0x30de hw
  · xdead
  have hm3 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xa 12
  xji 0x30ee 0x30f2 hw
  · xdead
  clear hw
  xa 8
  xsw 0x30fd 0x1e0  -- 30fc MSTORE
  xs 0x30ff (.push [0x03] (by decide)) ri_push  -- 30fd PUSH1 0x03
  xw 0x3100 (.reg .sload) ri_sload  -- 30ff SLOAD
  xs 0x3103 (.push [0x02, 0x00] (by decide)) ri_push  -- 3100 PUSH2 0x0200
  xsw 0x3104 0x200  -- 3103 MSTORE
  xs 0x3107 (.push [0x01, 0x40] (by decide)) ri_push  -- 3104 PUSH2 0x0140
  xl 0x3108 0x140  -- 3107 MLOAD
  xs 0x310b (.push [0x01, 0x60] (by decide)) ri_push  -- 3108 PUSH2 0x0160
  xl 0x310c 0x160  -- 310b MLOAD
  xs 0x310f (.push [0x01, 0x80] (by decide)) ri_push  -- 310c PUSH2 0x0180
  xlu 0x3110  -- 310f MLOAD
  xs 0x3113 (.push [0x01, 0xa0] (by decide)) ri_push  -- 3110 PUSH2 0x01a0
  xlu 0x3114  -- 3113 MLOAD
  xs 0x3117 (.push [0x01, 0xc0] (by decide)) ri_push  -- 3114 PUSH2 0x01c0
  xl 0x3118 0x1c0  -- 3117 MLOAD
  xs 0x311b (.push [0x01, 0xe0] (by decide)) ri_push  -- 3118 PUSH2 0x01e0
  xl 0x311c 0x1e0  -- 311b MLOAD
  xs 0x311f (.push [0x02, 0x00] (by decide)) ri_push  -- 311c PUSH2 0x0200
  xl 0x3120 0x200  -- 311f MLOAD
  xs 0x3123 (.push [0x02, 0x20] (by decide)) ri_push  -- 3120 PUSH2 0x0220
  xlu 0x3124  -- 3123 MLOAD
  xs 0x3126 (.push [0x06] (by decide)) ri_push  -- 3124 PUSH1 0x06
  cvpc 0x3127  -- 3126 PC
  xa 2
  xjmp 0xa9  -- 312b JUMP
  have hs1 : ∀ x, ((afterSload sevm (afterSload sevm d (Bytes.toB256 [2])) (Bytes.toB256 [3])).getStor
      sevm.currentTarget).get x = ((b.getStor sevm.currentTarget).set lockSlot 1).get x := by
    intro x
    rw [afterSload_getStor, afterSload_getStor, hstor, afterSload_getStor, afterSload_getStor,
      afterSstore_getStor_self, afterSload_getStor, lockSlot_lit,
      show Bytes.toB256 [1] = (1 : B256) from by decide]
  have ha1 := ha.of_lock fun x hx => by rw [hs1, Stor.get_set_ne _ (Ne.symm hx)]
  obtain ⟨A, b2, M2, _, hb2, h, hA, hV1⟩ := xa_vAV hc hcode hfork ha1 hV h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  rw [show (Nat.toB256 12582 + Bytes.toB256 [6]).toNat = 0x312c from by decide] at h
  xa 2
  xsw 0x3131 0x260  -- 3130 MSTORE
  xs 0x3134 (.push [0x02, 0x20] (by decide)) ri_push  -- 3131 PUSH2 0x0220
  xsw 0x3135 0x220  -- 3134 MSTORE
  xs 0x3138 (.push [0x02, 0x00] (by decide)) ri_push  -- 3135 PUSH2 0x0200
  xsw 0x3139 0x200  -- 3138 MSTORE
  xs 0x313c (.push [0x01, 0xe0] (by decide)) ri_push  -- 3139 PUSH2 0x01e0
  xsw 0x313d 0x1e0  -- 313c MSTORE
  xs 0x3140 (.push [0x01, 0xc0] (by decide)) ri_push  -- 313d PUSH2 0x01c0
  xsw 0x3141 0x1c0  -- 3140 MSTORE
  xs 0x3144 (.push [0x01, 0xa0] (by decide)) ri_push  -- 3141 PUSH2 0x01a0
  xsw 0x3145 0x1a0  -- 3144 MSTORE
  xs 0x3148 (.push [0x01, 0x80] (by decide)) ri_push  -- 3145 PUSH2 0x0180
  xsw 0x3149 0x180  -- 3148 MSTORE
  xs 0x314c (.push [0x01, 0x60] (by decide)) ri_push  -- 3149 PUSH2 0x0160
  xsw 0x314d 0x160  -- 314c MSTORE
  xs 0x3150 (.push [0x01, 0x40] (by decide)) ri_push  -- 314d PUSH2 0x0140
  xsw 0x3151 0x140  -- 3150 MSTORE
  xs 0x3154 (.push [0x02, 0x60] (by decide)) ri_push  -- 3151 PUSH2 0x0260
  xl 0x3155 0x260  -- 3154 MLOAD
  xs 0x3158 (.push [0x02, 0x20] (by decide)) ri_push  -- 3155 PUSH2 0x0220
  xsw 0x3159 0x220  -- 3158 MSTORE
  xa 4
  xsw 0x3162 0xc0  -- 3161 MSTORE
  xa 2
  xk 0x3167 0xc0  -- 3166 SHA3
  xw 0x3168 (.reg .sload) ri_sload  -- 3167 SLOAD
  xs 0x3169 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3168 DUP3
  xsw 0x316a 0x280  -- 3169 MSTORE
  xa 3
  xsw 0x3170 0xc0  -- 316f MSTORE
  xa 2
  xk 0x3175 0xc0  -- 3174 SHA3
  xs 0x3176 (.reg .add) ri_add  -- 3175 ADD
  xw 0x3177 (.reg .sload) ri_sload  -- 3176 SLOAD
  xa 3
  xsw 0x317c 0x2a0  -- 317b MSTORE
  xa 3
  xsw 0x3182 0xc0  -- 3181 MSTORE
  xa 2
  xk 0x3187 0xc0  -- 3186 SHA3
  xs 0x3188 (.reg .add) ri_add  -- 3187 ADD
  xw 0x3189 (.reg .sload) ri_sload  -- 3188 SLOAD
  xa 3
  xsw 0x318e 0x2c0  -- 318d MSTORE
  xa 5
  xl 0x3198 0x280  -- 3197 MLOAD
  xs 0x3199 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3198 DUP3
  xsw 0x319a 0x2e0  -- 3199 MSTORE
  xa 3
  xl 0x319f 0x2a0  -- 319e MLOAD
  xa 3
  xsw 0x31a4 0x300  -- 31a3 MSTORE
  xa 3
  xl 0x31a9 0x2c0  -- 31a8 MLOAD
  xa 3
  xsw 0x31ae 0x320  -- 31ad MSTORE
  xa 4
  xsw 0x31b7 0x360  -- 31b6 MSTORE
  have hd : ∀ x, (d.getStor sevm.currentTarget).get x =
      ((b.getStor sevm.currentTarget).set lockSlot 1).get x := by
    intro x
    rw [← hs1, afterSload_getStor, afterSload_getStor]
  have hB2 : ∀ x, (b2.getStor sevm.currentTarget).get x =
      ((b.getStor sevm.currentTarget).set lockSlot 1).get x := by
    intro x
    rw [hb2.getStor, hs1]
  simp (config := {decide := true}) only [show Bytes.toB256 [1] = (1 : B256) from by decide,
    balancesBase_eq, getStorVal_eq, afterSload_getStor, hB2, hd, Stor.get_set_ite, ↓reduceIte]
    at h hV hm3
  rw [← feeSlot_lit, ← adminFeeSlot_lit]
  rw [show balancesBase = balancesBase + Nat.toB256 0 from by decide,
    show balancesBase + Nat.toB256 0 + 1 = balancesBase + Nat.toB256 1 from by decide,
    show balancesBase + Nat.toB256 0 + Bytes.toB256 [2] = balancesBase + Nat.toB256 2 from by decide]
    at hV
  have hB0 : IdReady sevm b → IdReady sevm (afterSload sevm (afterSload sevm (afterSstore sevm
      (afterSload sevm b (Bytes.toB256 [255, 255, 255])) (Bytes.toB256 [255, 255, 255])
      (Bytes.toB256 [1])) (Bytes.toB256 [15])) (Bytes.toB256 [5])) := fun hb =>
    (((hb.afterSload _).afterSstore _ _).afterSload _).afterSload _
  refine ⟨hlock, hval, hkill, c, L1, A, _, _, _, hL, ⟨?_, ?_, hstat, hlen, hclogs⟩, hT0, hm3, hA,
    fun x => ?_, ?_, ?_, fun x hx => ?_, fun hb h4 => ?_, h, hV.sub ?_⟩
  · rw [htgt, getStorVal_eq, afterSload_getStor, afterSstore_getStor_self, afterSload_getStor,
      tokenSlot_lit, Stor.get_set_ne _ (show Bytes.toB256 [255, 255, 255] ≠ tokenSlot by decide)]
  · rw [hdata, show (Bytes.toB256 [1, 124]).toNat = 380 from rfl,
      show (Bytes.toB256 [4]).toNat = 4 from rfl,
      Mem.read_write_word_inside (vyMem_wf Mem.wf_empty _) 352 _ (by decide) (by decide)]
    decide
  · rw [afterSload_getStor, afterSload_getStor, afterSload_getStor, hB2]
  · rw [afterSload_logs, afterSload_logs, afterSload_logs, hb2.logs, afterSload_logs,
      afterSload_logs, hlogs, afterSload_logs, afterSload_logs, afterSstore_logs, afterSload_logs]
  · rw [afterSload_output, afterSload_output, afterSload_output, hb2.output, afterSload_output,
      afterSload_output, hout, afterSload_output, afterSload_output, afterSstore_output,
      afterSload_output]
  · rw [afterSload_getCode, afterSload_getCode, afterSload_getCode, hb2.getCode,
      afterSload_getCode, afterSload_getCode, hcodeK x (by
        rwa [afterSload_getCode, afterSload_getCode, afterSstore_getCode, afterSload_getCode]),
      afterSload_getCode, afterSload_getCode, afterSstore_getCode, afterSload_getCode]
  · have hb0 := hB0 hb
    have hdI : IdReady sevm d :=
      ⟨by rw [hcpost, h4, hcpre]; exact hb0.nodeleg, hacc _ hb0.warm, hb.pre, hb.fork⟩
    exact ((hb2.idReady ((hdI.afterSload _).afterSload _)).afterSload _).afterSload _
      |>.afterSload _
  · simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self]

end

end Blanc.Lift.Curve3Pool
