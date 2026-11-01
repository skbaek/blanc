import Blanc.Lift.Curve3Pool.Walk.ViewsDy
import Blanc.Lift.Curve3Pool.Walk.AutoStep

/-! # The checked arithmetic and return suffix of `get_dy` -/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

abbrev dyJxp (sevm : Sevm) (x0 x1 x2 : B256) : B256 := pickWord3 (dyJ sevm).toNat x0 x1 x2
abbrev dyRate (sevm : Sevm) : B256 := pickWord3 (dyJ sevm).toNat rP rQ rQ
abbrev dyAmount (sevm : Sevm) (x0 x1 x2 y : B256) : B256 :=
  (dyJxp sevm x0 x1 x2 - y - Bytes.toB256 [1]) * rP / dyRate sevm
abbrev dyFee (sevm : Sevm) (b : Devm) (x0 x1 x2 y : B256) : B256 :=
  (b.getStorVal sevm.currentTarget (Bytes.toB256 [2])) * dyAmount sevm x0 x1 x2 y /
    Bytes.toB256 [0x02, 0x54, 0x0b, 0xe4, 0x00]

/-- `get_dy`'s suffix reads every arithmetic guard and returns the exact net amount. -/
theorem xa_dy_post {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    {M : Mem} {x0 x1 x2 y : B256}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hj : (dyJ sevm).toNat < 3)
    (hV : VW M [(0x3e0, y), (0x140, rP), (0x160, rQ), (0x180, rQ),
      (0x1a0, x0), (0x1c0, x1), (0x1e0, x2)])
    (h : XAt sevm post 0x1f43 (St b [] M G) L) :
    L = [] ∧ y.toNat ≤ (dyJxp sevm x0 x1 x2).toNat ∧
      (Bytes.toB256 [1]).toNat ≤ (dyJxp sevm x0 x1 x2 - y).toNat ∧
      B256.Nofm (dyJxp sevm x0 x1 x2 - y - Bytes.toB256 [1]) rP ∧ dyRate sevm ≠ 0 ∧
      B256.Nofm (b.getStorVal sevm.currentTarget (Bytes.toB256 [2]))
        (dyAmount sevm x0 x1 x2 y) ∧
      (dyFee sevm b x0 x1 x2 y).toNat ≤ (dyAmount sevm x0 x1 x2 y).toNat ∧
      (∀ a, post.getStor a = b.getStor a) ∧ post.logs = b.logs ∧
      post.output = (dyAmount sevm x0 x1 x2 y - dyFee sevm b x0 x1 x2 y).toBytes := by
  xs 0x1f46 (.push [0x03, 0xe0] (by decide)) ri_push
  xl 0x1f47 0x3e0
  xs 0x1f4a (.push [0x02, 0xa0] (by decide)) ri_push
  xsw 0x1f4b 0x2a0
  xa 7
  xji 0x1f59 0x1f5d hw
  · xdead
  clear hw
  xa 4
  replace h := xa_nextAt (n := .reg .mload) (pc' := 0x1f63) (atN hcode (by kernel_rfl)) (by nofun) (by rfl) h
  obtain ⟨_, sr, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_mloadWord3 (base := 0x1a0) hV.words hV.al
    (wlook_mem (by rfl)) (wlook_mem (by rfl)) (wlook_mem (by rfl)) hj
    (by rw [word3_indexAddr hj (by decide)]; rfl) sr
  clear sr
  xs 0x1f66 (.push [0x02, 0xa0] (by decide)) ri_push
  xl 0x1f67 0x2a0
  xa 5
  xji 0x1f6f 0x1f73 hw
  · xdead
  have hsub0 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xa 14
  xji 0x1f85 0x1f89 hw
  · xdead
  have hsub1 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xa 21
  xji 0x1fa9 0x1fad hw
  · xdead
  have hmul0 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xa 15
  xji 0x1fc3 0x1fc7 hw
  · xdead
  clear hw
  xa 4
  replace h := xa_nextAt (n := .reg .mload) (pc' := 0x1fcd) (atN hcode (by kernel_rfl)) (by nofun) (by rfl) h
  obtain ⟨_, sr, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_mloadWord3 (base := 0x140) hV.words hV.al
    (wlook_mem (by rfl)) (wlook_mem (by rfl)) (wlook_mem (by rfl)) hj
    (by rw [word3_indexAddr hj (by decide)]; rfl) sr
  clear sr
  xa 3
  xji 0x1fd3 0x1fd7 hw
  · xdead
  have hrate := hw
  clear hw
  xa 8
  xsw 0x1fe2 0x400
  xs 0x1fe4 (.push [0x02] (by decide)) ri_push
  xw 0x1fe5 (.reg .sload) ri_sload
  xs 0x1fe8 (.push [0x04, 0x00] (by decide)) ri_push
  xl 0x1fe9 0x400
  xa 12
  xji 0x1ff8 0x1ffc hw
  · xdead
  have hmul1 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xa 12
  xji 0x2010 0x2014 hw
  · xdead
  clear hw
  xa 8
  xsw 0x201f 0x420
  xs 0x2022 (.push [0x04, 0x00] (by decide)) ri_push
  xl 0x2023 0x400
  xs 0x2026 (.push [0x04, 0x20] (by decide)) ri_push
  xl 0x2027 0x420
  xa 5
  xji 0x202f 0x2033 hw
  · xdead
  have hsub2 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xa 9
  have hfinalwf := hV.wf
  xsw 0x203e 0x0
  xa 2
  obtain ⟨hrun, rfl⟩ := xa_halt (l := .return_) (atL hcode (by kernel_rfl)) h
  obtain ⟨hout, hstor, hlogs⟩ := ri_return hrun
  refine ⟨rfl, hsub0, hsub1, hmul0, hrate, hmul1, hsub2,
    fun a => by rw [hstor, afterSload_getStor], by rw [hlogs, afterSload_logs], ?_⟩
  rw [hout, show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [32]).toNat = 32 from rfl, Mem.read_write_word_of_wf hfinalwf]

end Blanc.Lift.Curve3Pool
