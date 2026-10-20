import Blanc.Lift.Curve3Pool.Walk.ViewsDy

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
  xs 0x1f4e (.push [0x01, 0xa0] (by decide)) ri_push
  xs 0x1f50 (.push [0x24] (by decide)) ri_push
  xs 0x1f51 (.reg .calldataload) ri_calldataload
  xs 0x1f53 (.push [0x03] (by decide)) ri_push
  xs 0x1f54 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x1f55 (.reg .lt) ri_lt
  xs 0x1f58 (.push [0x1f, 0x5d] (by decide)) ri_push
  xji 0x1f59 0x1f5d hw
  · xdead
  clear hw
  xjd 0x1f5e
  xs 0x1f60 (.push [0x20] (by decide)) ri_push
  xs 0x1f61 (.reg .mul) ri_mul
  xs 0x1f62 (.reg .add) ri_add
  replace h := xa_nextAt (n := .reg .mload) (pc' := 0x1f63) (atN hcode (by kernel_rfl)) (by nofun) (by rfl) h
  obtain ⟨_, sr, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_mloadWord3 (base := 0x1a0) hV.words hV.al
    (wlook_mem (by rfl)) (wlook_mem (by rfl)) (wlook_mem (by rfl)) hj
    (by rw [word3_indexAddr hj (by decide)]; rfl) sr
  clear sr
  xs 0x1f66 (.push [0x02, 0xa0] (by decide)) ri_push
  xl 0x1f67 0x2a0
  xs 0x1f68 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x1f69 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x1f6a (.reg .lt) ri_lt
  xs 0x1f6b (.reg .iszero) ri_iszero
  xs 0x1f6e (.push [0x1f, 0x73] (by decide)) ri_push
  xji 0x1f6f 0x1f73 hw
  · xdead
  have hsub0 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xjd 0x1f74
  xs 0x1f75 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x1f76 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x1f77 (.reg .sub) ri_sub
  xs 0x1f78 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x1f79 (.reg .pop) ri_pop
  xs 0x1f7a (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x1f7b (.reg .pop) ri_pop
  xs 0x1f7d (.push [0x01] (by decide)) ri_push
  xs 0x1f7e (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x1f7f (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x1f80 (.reg .lt) ri_lt
  xs 0x1f81 (.reg .iszero) ri_iszero
  xs 0x1f84 (.push [0x1f, 0x89] (by decide)) ri_push
  xji 0x1f85 0x1f89 hw
  · xdead
  have hsub1 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xjd 0x1f8a
  xs 0x1f8b (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x1f8c (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x1f8d (.reg .sub) ri_sub
  xs 0x1f8e (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x1f8f (.reg .pop) ri_pop
  xs 0x1f90 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x1f91 (.reg .pop) ri_pop
  xs 0x1f9a (.push [0x0d, 0xe0, 0xb6, 0xb3, 0xa7, 0x64, 0x00, 0x00] (by decide)) ri_push
  xs 0x1f9b (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x1f9c (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x1f9d (.reg .mul) ri_mul
  xs 0x1f9e (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x1f9f (.reg .iszero) ri_iszero
  xs 0x1fa0 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x1fa1 (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0x1fa2 (.reg (.dup 3)) (ri_dup (by rfl))
  xs 0x1fa3 (.reg .div) ri_div
  xs 0x1fa4 (.reg .eq) ri_eq
  xs 0x1fa5 (.reg .or) ri_or
  xs 0x1fa8 (.push [0x1f, 0xad] (by decide)) ri_push
  xji 0x1fa9 0x1fad hw
  · xdead
  have hmul0 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xjd 0x1fae
  xs 0x1faf (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x1fb0 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x1fb1 (.reg .pop) ri_pop
  xs 0x1fb2 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x1fb3 (.reg .pop) ri_pop
  xs 0x1fb4 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x1fb5 (.reg .pop) ri_pop
  xs 0x1fb8 (.push [0x01, 0x40] (by decide)) ri_push
  xs 0x1fba (.push [0x24] (by decide)) ri_push
  xs 0x1fbb (.reg .calldataload) ri_calldataload
  xs 0x1fbd (.push [0x03] (by decide)) ri_push
  xs 0x1fbe (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x1fbf (.reg .lt) ri_lt
  xs 0x1fc2 (.push [0x1f, 0xc7] (by decide)) ri_push
  xji 0x1fc3 0x1fc7 hw
  · xdead
  clear hw
  xjd 0x1fc8
  xs 0x1fca (.push [0x20] (by decide)) ri_push
  xs 0x1fcb (.reg .mul) ri_mul
  xs 0x1fcc (.reg .add) ri_add
  replace h := xa_nextAt (n := .reg .mload) (pc' := 0x1fcd) (atN hcode (by kernel_rfl)) (by nofun) (by rfl) h
  obtain ⟨_, sr, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_mloadWord3 (base := 0x140) hV.words hV.al
    (wlook_mem (by rfl)) (wlook_mem (by rfl)) (wlook_mem (by rfl)) hj
    (by rw [word3_indexAddr hj (by decide)]; rfl) sr
  clear sr
  xs 0x1fce (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x1fcf (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x1fd2 (.push [0x1f, 0xd7] (by decide)) ri_push
  xji 0x1fd3 0x1fd7 hw
  · xdead
  have hrate := hw
  clear hw
  xjd 0x1fd8
  xs 0x1fd9 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x1fda (.reg .div) ri_div
  xs 0x1fdb (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x1fdc (.reg .pop) ri_pop
  xs 0x1fdd (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x1fde (.reg .pop) ri_pop
  xs 0x1fe1 (.push [0x04, 0x00] (by decide)) ri_push
  xsw 0x1fe2 0x400
  xs 0x1fe4 (.push [0x02] (by decide)) ri_push
  xw 0x1fe5 (.reg .sload) ri_sload
  xs 0x1fe8 (.push [0x04, 0x00] (by decide)) ri_push
  xl 0x1fe9 0x400
  xs 0x1fea (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x1feb (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x1fec (.reg .mul) ri_mul
  xs 0x1fed (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x1fee (.reg .iszero) ri_iszero
  xs 0x1fef (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x1ff0 (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0x1ff1 (.reg (.dup 3)) (ri_dup (by rfl))
  xs 0x1ff2 (.reg .div) ri_div
  xs 0x1ff3 (.reg .eq) ri_eq
  xs 0x1ff4 (.reg .or) ri_or
  xs 0x1ff7 (.push [0x1f, 0xfc] (by decide)) ri_push
  xji 0x1ff8 0x1ffc hw
  · xdead
  have hmul1 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xjd 0x1ffd
  xs 0x1ffe (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x1fff (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2000 (.reg .pop) ri_pop
  xs 0x2001 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2002 (.reg .pop) ri_pop
  xs 0x2003 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2004 (.reg .pop) ri_pop
  xs 0x200a (.push [0x02, 0x54, 0x0b, 0xe4, 0x00] (by decide)) ri_push
  xs 0x200b (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x200c (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x200f (.push [0x20, 0x14] (by decide)) ri_push
  xji 0x2010 0x2014 hw
  · xdead
  clear hw
  xjd 0x2015
  xs 0x2016 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2017 (.reg .div) ri_div
  xs 0x2018 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2019 (.reg .pop) ri_pop
  xs 0x201a (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x201b (.reg .pop) ri_pop
  xs 0x201e (.push [0x04, 0x20] (by decide)) ri_push
  xsw 0x201f 0x420
  xs 0x2022 (.push [0x04, 0x00] (by decide)) ri_push
  xl 0x2023 0x400
  xs 0x2026 (.push [0x04, 0x20] (by decide)) ri_push
  xl 0x2027 0x420
  xs 0x2028 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2029 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x202a (.reg .lt) ri_lt
  xs 0x202b (.reg .iszero) ri_iszero
  xs 0x202e (.push [0x20, 0x33] (by decide)) ri_push
  xji 0x202f 0x2033 hw
  · xdead
  have hsub2 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xjd 0x2034
  xs 0x2035 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x2036 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x2037 (.reg .sub) ri_sub
  xs 0x2038 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x2039 (.reg .pop) ri_pop
  xs 0x203a (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x203b (.reg .pop) ri_pop
  xs 0x203d (.push [0x00] (by decide)) ri_push
  have hfinalwf := hV.wf
  xsw 0x203e 0x0
  xs 0x2040 (.push [0x20] (by decide)) ri_push
  xs 0x2042 (.push [0x00] (by decide)) ri_push
  obtain ⟨hrun, rfl⟩ := xa_halt (l := .return_) (atL hcode (by kernel_rfl)) h
  obtain ⟨hout, hstor, hlogs⟩ := ri_return hrun
  refine ⟨rfl, hsub0, hsub1, hmul0, hrate, hmul1, hsub2,
    fun a => by rw [hstor, afterSload_getStor], by rw [hlogs, afterSload_logs], ?_⟩
  rw [hout, show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [32]).toNat = 32 from rfl, Mem.read_write_word_of_wf hfinalwf]

end Blanc.Lift.Curve3Pool
