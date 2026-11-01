import Blanc.Lift.Curve3Pool.Walk.ViewsDyu
import Blanc.Lift.Curve3Pool.Walk.AutoStep

/-! # The checked arithmetic and return suffix of `get_dy_underlying` -/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

abbrev dyuPj (sevm : Sevm) : B256 := pickWord3 (dyJ sevm).toNat dyuP1 dyuPm dyuPm
abbrev dyuAmount (sevm : Sevm) (x0 x1 x2 y : B256) : B256 :=
  (dyJxp sevm x0 x1 x2 - y - Bytes.toB256 [1]) / dyuPj sevm
abbrev dyuFee (sevm : Sevm) (b : Devm) (x0 x1 x2 y : B256) : B256 :=
  (b.getStorVal sevm.currentTarget (Bytes.toB256 [2])) * dyuAmount sevm x0 x1 x2 y /
    Bytes.toB256 [0x02, 0x54, 0x0b, 0xe4, 0x00]

/-- `get_dy_underlying`'s suffix reads every arithmetic guard and returns the exact net amount. -/
theorem xa_dyu_post {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    {M : Mem} {x0 x1 x2 y : B256}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hj : (dyJ sevm).toNat < 3)
    (hV : VW M [(0x3e0, y), (0x140, x0), (0x160, x1), (0x180, x2), (0x220, dyuP1),
      (0x240, dyuPm), (0x260, dyuPm)])
    (h : XAt sevm post 0x222c (St b [] M G) L) :
    L = [] ∧ y.toNat ≤ (dyJxp sevm x0 x1 x2).toNat ∧
      (Bytes.toB256 [1]).toNat ≤ (dyJxp sevm x0 x1 x2 - y).toNat ∧ dyuPj sevm ≠ 0 ∧
      B256.Nofm (b.getStorVal sevm.currentTarget (Bytes.toB256 [2]))
        (dyuAmount sevm x0 x1 x2 y) ∧
      (dyuFee sevm b x0 x1 x2 y).toNat ≤ (dyuAmount sevm x0 x1 x2 y).toNat ∧
      (∀ a, post.getStor a = b.getStor a) ∧ post.logs = b.logs ∧
      post.output = (dyuAmount sevm x0 x1 x2 y - dyuFee sevm b x0 x1 x2 y).toBytes := by
  xs 0x222f (.push [0x03, 0xe0] (by decide)) ri_push  -- 222c PUSH2 0x03e0
  xl 0x2230 0x3e0  -- 222f MLOAD
  xs 0x2233 (.push [0x02, 0xa0] (by decide)) ri_push  -- 2230 PUSH2 0x02a0
  xsw 0x2234 0x2a0  -- 2233 MSTORE
  xa 7
  xji 0x2242 0x2246 hw
  · xdead
  clear hw
  xa 4
  replace h := xa_nextAt (n := .reg .mload) (pc' := 0x224c) (atN hcode (by kernel_rfl)) (by nofun) (by rfl) h
  obtain ⟨_, sr, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_mloadWord3 (base := 0x140) hV.words hV.al
    (wlook_mem (by rfl)) (wlook_mem (by rfl)) (wlook_mem (by rfl)) hj
    (by rw [word3_indexAddr hj (by decide)]; rfl) sr
  clear sr
  xs 0x224f (.push [0x02, 0xa0] (by decide)) ri_push  -- 224c PUSH2 0x02a0
  xl 0x2250 0x2a0  -- 224f MLOAD
  xa 5
  xji 0x2258 0x225c hw
  · xdead
  have hsub0 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xa 14
  xji 0x226e 0x2272 hw
  · xdead
  have hsub1 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xa 15
  xji 0x2288 0x228c hw
  · xdead
  clear hw
  xa 4
  replace h := xa_nextAt (n := .reg .mload) (pc' := 0x2292) (atN hcode (by kernel_rfl)) (by nofun) (by rfl) h
  obtain ⟨_, sr, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_mloadWord3 (base := 0x220) hV.words hV.al
    (wlook_mem (by rfl)) (wlook_mem (by rfl)) (wlook_mem (by rfl)) hj
    (by rw [word3_indexAddr hj (by decide)]; rfl) sr
  clear sr
  xa 3
  xji 0x2298 0x229c hw
  · xdead
  have hrate := hw
  clear hw
  xa 8
  xsw 0x22a7 0x400  -- 22a6 MSTORE
  xs 0x22a9 (.push [0x02] (by decide)) ri_push  -- 22a7 PUSH1 0x02
  xw 0x22aa (.reg .sload) ri_sload  -- 22a9 SLOAD
  xs 0x22ad (.push [0x04, 0x00] (by decide)) ri_push  -- 22aa PUSH2 0x0400
  xl 0x22ae 0x400  -- 22ad MLOAD
  xa 12
  xji 0x22bd 0x22c1 hw
  · xdead
  have hmul1 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xa 12
  xji 0x22d5 0x22d9 hw
  · xdead
  clear hw
  xa 8
  xsw 0x22e4 0x420  -- 22e3 MSTORE
  xs 0x22e7 (.push [0x04, 0x00] (by decide)) ri_push  -- 22e4 PUSH2 0x0400
  xl 0x22e8 0x400  -- 22e7 MLOAD
  xs 0x22eb (.push [0x04, 0x20] (by decide)) ri_push  -- 22e8 PUSH2 0x0420
  xl 0x22ec 0x420  -- 22eb MLOAD
  xa 5
  xji 0x22f4 0x22f8 hw
  · xdead
  have hsub2 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xa 9
  have hfinalwf := hV.wf
  xsw 0x2303 0x0  -- 2302 MSTORE
  xa 2
  obtain ⟨hrun, rfl⟩ := xa_halt (l := .return_) (atL hcode (by kernel_rfl)) h
  obtain ⟨hout, hstor, hlogs⟩ := ri_return hrun
  refine ⟨rfl, hsub0, hsub1, hrate, hmul1, hsub2,
    fun a => by rw [hstor, afterSload_getStor], by rw [hlogs, afterSload_logs], ?_⟩
  rw [hout, show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [32]).toNat = 32 from rfl, Mem.read_write_word_of_wf hfinalwf]

end Blanc.Lift.Curve3Pool
