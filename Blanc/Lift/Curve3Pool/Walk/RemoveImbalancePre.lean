import Blanc.Lift.Curve3Pool.Walk.Kit

/-!
# `remove_liquidity_imbalance`, part 1: lock, value, kill check and supply

From the arm's body (`0x304f`, after the dispatcher's test) to the supply check's
landing (`0x30c5`): `assert lock == 0; lock = 1`, the non-payable guard, the
`is_killed` assert, `total_supply = token.totalSupply()` (a `STATICCALL` whose reply
must be at least 32 bytes), the supply word stored at `0x140`, and the
`total_supply != 0` check.

`xa_rli_pre`: the lock was clear and the call carried no value; the frame's next
child is the `totalSupply()` call to the stored token (static, at least 32 bytes back,
no logs); the base after it holds the pool's storage with the lock set and every other
account's storage unchanged; the memory image has the supply word at `0x140`, and the
supply word is nonzero.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- **`remove_liquidity_imbalance` up to its supply check** (see the module note). -/
theorem xa_rli_pre {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (htok : ¬ sevm.benvStat.rules.isPrecomp ((b.getStor sevm.currentTarget).get tokenSlot).toAdr)
    (hSK : StaticKeeps sevm ((b.getStor sevm.currentTarget).get tokenSlot))
    (h : XAt sevm post 0x304f (St b [] M G) L) :
    (b.getStor sevm.currentTarget).get lockSlot = 0 ∧ sevm.value = 0 ∧
    ∃ (c : Exec.Frame) (L' : List Exec.Frame) (b1 : Devm) (M1 : Mem) (G1 : Nat) (img1 : Bytes),
      L = c :: L' ∧ 0 < sevm.depth ∧
      c.sevm.currentTarget = ((b.getStor sevm.currentTarget).get tokenSlot).toAdr ∧
      c.sevm.data = totalSupplyData ∧ c.sevm.isStatic = true ∧ 32 ≤ c.post.output.length ∧
      c.post.logs = [] ∧ (∀ a, c.pre.getCode a = b.getCode a) ∧
      (∀ a, b1.getCode a = c.post.getCode a) ∧
      (∀ x, (b1.getStor sevm.currentTarget).get x =
        ((b.getStor sevm.currentTarget).set lockSlot 1).get x) ∧
      (∀ a, a ≠ sevm.currentTarget → b1.getStor a = b.getStor a) ∧
      b1.logs = b.logs ∧ b1.output = b.output ∧ Devm.AccGrow b b1 ∧ b1.getCode 4 = b.getCode 4 ∧
      (∀ a, b.getCode a ≠ .empty → b1.getCode a = b.getCode a) ∧
      Mem.Reads M1 img1 ∧ Mem.Wf M1 ∧
      WordAt img1 0x140 (Bytes.toB256 (c.post.output.take 32)) ∧
      Bytes.toB256 (c.post.output.take 32) ≠ 0 ∧
      XAt sevm post 0x30c5 (St b1 [] M1 G1) L' := by
  xs 0x3053 (.push [0xff, 0xff, 0xff] (by decide)) ri_push
  xw 0x3054 (.reg .sload) ri_sload
  xs 0x3055 (.reg .iszero) ri_iszero
  xs 0x3058 (.push [0x30, 0x5d] (by decide)) ri_push
  xji 0x3059 0x305d hw
  · xdead
  have hlock : (b.getStor sevm.currentTarget).get lockSlot = 0 := by
    have e := eqCheck_ne_zero_eq hw
    rw [lockSlot_lit] at e
    exact e
  clear hw
  xjd 0x305e
  xs 0x3060 (.push [0x01] (by decide)) ri_push
  xs 0x3064 (.push [0xff, 0xff, 0xff] (by decide)) ri_push
  xw 0x3065 (.reg .sstore) ri_sstore
  xs 0x3066 (.reg .callvalue) ri_callvalue
  xs 0x3067 (.reg .iszero) ri_iszero
  xs 0x306a (.push [0x30, 0x6f] (by decide)) ri_push
  xji 0x306b 0x306f hw
  · xdead
  have hval : sevm.value = 0 := eqCheck_ne_zero_eq hw
  clear hw
  xjd 0x3070
  xs 0x3072 (.push [0x0f] (by decide)) ri_push
  xw 0x3073 (.reg .sload) ri_sload
  xs 0x3074 (.reg .iszero) ri_iszero
  xs 0x3077 (.push [0x30, 0x7c] (by decide)) ri_push
  xji 0x3078 0x307c hw
  · xdead
  have hkill : (b.getStor sevm.currentTarget).get isKilledSlot = 0 := by
    have e := eqCheck_ne_zero_eq hw
    have hne : lockSlot ≠ Bytes.toB256 [0x0f] := by decide
    rw [lockSlot_lit, getStorVal_afterSstore_ne hne, getStorVal_afterSload,
      show Bytes.toB256 [0x0f] = isKilledSlot by decide] at e
    exact e
  clear hw
  refine ⟨hlock, hval, ?_⟩
  xjd 0x307d
  xs 0x307f (.push [0x20] (by decide)) ri_push
  xs 0x3082 (.push [0x01, 0xc0] (by decide)) ri_push
  xs 0x3084 (.push [0x04] (by decide)) ri_push
  xs 0x3089 (.push [0x18, 0x16, 0x0d, 0xdd] (by decide)) ri_push
  xs 0x308c (.push [0x01, 0x60] (by decide)) ri_push
  xmo 0x308d (.reg .mstore) (ri_mstore_imgAt (o := 0x160) rfl)
  xs 0x3090 (.push [0x01, 0x7c] (by decide)) ri_push
  xs 0x3092 (.push [0x05] (by decide)) ri_push
  xw 0x3093 (.reg .sload) ri_sload
  xs 0x3094 (.reg .gas) ri_gas_remaining
  replace h := xa_staticcall_img (pc' := 0x3095) (i := 0x17c) (n := 4) (o := 0x1c0) (z := 0x20)
    hfork (atN hcode (by kernel_rfl)) rfl rfl rfl rfl rfl hR hW h
  clear hR hW
  obtain ⟨d1, flag, out, M, L1, h, ⟨d0, hrun0, hcd0⟩, hR, hW, hrd, hob, hstor, hlogs, hk⟩ := h
  xs 0x3098 (.push [0x30, 0x9d] (by decide)) ri_push
  xji 0x3099 0x309d hw
  · xdead
  have htok' : ((afterSload sevm (afterSstore sevm (afterSload sevm b (Bytes.toB256 [255, 255, 255]))
      (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1])) (Bytes.toB256 [0x0f])).getStorVal
      sevm.currentTarget (Bytes.toB256 [5])) =
      (b.getStor sevm.currentTarget).get tokenSlot := by
    rw [lockSlot_lit, tokenSlot_lit, getStorVal_afterSload,
      getStorVal_afterSstore_ne lock_ne_token, getStorVal_afterSload]
    rfl
  rw [htok'] at hk hrun0
  have stCode : ∀ {b : Devm} {S : List B256} {M : Mem} {G : Nat},
      (St b S M G).getCode = b.getCode := by
    intro b S M G
    rfl
  have h4 : d1.getCode 4 = b.getCode 4 := by
    rw [← congrFun hcd0 4, hSK _ _ _ _ _ _ _ _ rfl hrun0, stCode, afterSload_getCode,
      afterSload_getCode, afterSstore_getCode, afterSload_getCode]
  rcases hk hw with ⟨hpre, -⟩ | ⟨c, hL, hdepth, hout, hacc, hcodeK, htgt, hdata, hstat, hcout,
    hclogs, hcpre, hcpost⟩
  · exact absurd hpre htok
  clear hk
  xjd 0x309e
  xs 0x30a0 (.push [0x1f] (by decide)) ri_push
  xs 0x30a1 (.reg .returndatasize) ri_returndatasize
  xs 0x30a2 (.reg .gt) ri_gt
  xs 0x30a5 (.push [0x30, 0xaa] (by decide)) ri_push
  xji 0x30a6 0x30aa hw2
  · xdead
  have hlen : 32 ≤ out.length := by
    have e := gtCheck_ne_zero hw2
    rw [hrd, B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hob] at e
    exact e
  clear hw2
  xjd 0x30ab
  xs 0x30ad (.push [0x00] (by decide)) ri_push
  xs 0x30ae (.reg .pop) ri_pop
  xs 0x30b1 (.push [0x01, 0xc0] (by decide)) ri_push
  xmo 0x30b2 (.reg .mload) (ri_mload_imgAt (o := 0x1c0) rfl)
  xs 0x30b5 (.push [0x01, 0x40] (by decide)) ri_push
  xmo 0x30b6 (.reg .mstore) (ri_mstore_imgAt (o := 0x140) rfl)
  xs 0x30b8 (.push [0x00] (by decide)) ri_push
  xs 0x30bb (.push [0x01, 0x40] (by decide)) ri_push
  xmo 0x30bc (.reg .mload) (ri_mload_imgAt (o := 0x140) rfl)
  xs 0x30bd (.reg .xor) ri_xor
  xs 0x30c0 (.push [0x30, 0xc5] (by decide)) ri_push
  xji 0x30c1 0x30c5 hw
  · xdead
  have hTw : List.sliceD (Bytes.writeAt (Bytes.writeAt img 352 (Bytes.toB256 [24, 22, 13, 221]).toBytes)
      448 (List.take 32 out)) 448 32 0 = List.take 32 out := by
    rw [Bytes.sliceD_writeAt_inside _ _ _ _ _ (le_refl _)
      (by rw [List.length_take]; omega), Nat.sub_self]
    exact List.sliceD_zero_of_length (by rw [List.length_take]; omega)
  have himg : Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 352
      (Bytes.toB256 [24, 22, 13, 221]).toBytes) 448 (List.take 32 out)) 320
      (Bytes.toB256 (List.sliceD (Bytes.writeAt (Bytes.writeAt img 352
        (Bytes.toB256 [24, 22, 13, 221]).toBytes) 448 (List.take 32 out)) 448 32 0)).toBytes =
      Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 352
        (Bytes.toB256 [24, 22, 13, 221]).toBytes) 448 (List.take 32 out)) 320
        (Bytes.toB256 (c.post.output.take 32)).toBytes := by
    rw [hTw, hcout]
  refine ⟨c, L1, d1, M, _, Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 352
      (Bytes.toB256 [24, 22, 13, 221]).toBytes) 448 (List.take 32 out)) 320
      (Bytes.toB256 (c.post.output.take 32)).toBytes, hL, hdepth, htgt, ?_, hstat,
    by rw [hcout]; exact hlen, hclogs, ?_, hcpost, ?_, ?_, ?_, ?_, ?_, h4, ?_, ?_, ?_, ?_, ?_, h⟩
  · rw [hdata, Bytes.sliceD_writeAt_inside _ _ _ _ _ (by decide)
      (by rw [B256.length_toBytes])]
    decide
  · intro a
    rw [hcpre, afterSload_getCode, afterSload_getCode, afterSstore_getCode, afterSload_getCode]
  · intro x
    rw [hstor, afterSload_getStor, afterSload_getStor, afterSstore_getStor_self, afterSload_getStor,
      lockSlot_lit]
    rfl
  · intro a ha
    rw [hstor, afterSload_getStor, afterSload_getStor, afterSstore_getStor_ne _ _ _ _ _ (Ne.symm ha),
      afterSload_getStor]
  · rw [hlogs, afterSload_logs, afterSload_logs, afterSstore_logs, afterSload_logs]
  · rw [hout, afterSload_output, afterSload_output, afterSstore_output, afterSload_output]
  · refine Devm.AccGrow.trans (Devm.AccGrow.of_eq ?_) hacc
    rw [afterSload_accessedAddresses, afterSload_accessedAddresses, afterSstore_accessedAddresses,
      afterSload_accessedAddresses]
  · intro a ha
    have e := hcodeK a
      (by rwa [afterSload_getCode, afterSload_getCode, afterSstore_getCode, afterSload_getCode])
    rwa [afterSload_getCode, afterSload_getCode, afterSstore_getCode, afterSload_getCode] at e
  · rw [← himg]; exact hR
  · exact hW
  · exact WordAt.write_self _ _ _
  · rw [zero_lit, B256.xor_zero] at hw
    have hW320 : WordAt
        (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 352 (Bytes.toB256 [24, 22, 13, 221]).toBytes)
          448 (List.take 32 out)) 320 (Bytes.toB256 (List.sliceD (Bytes.writeAt (Bytes.writeAt img 352
            (Bytes.toB256 [24, 22, 13, 221]).toBytes) 448 (List.take 32 out)) 448 32 0)).toBytes) 320
        (Bytes.toB256 (List.sliceD (Bytes.writeAt (Bytes.writeAt img 352
          (Bytes.toB256 [24, 22, 13, 221]).toBytes) 448 (List.take 32 out)) 448 32 0)) :=
      WordAt.write_self _ _ _
    rw [hW320.read, hTw] at hw
    rw [hcout]
    exact hw

end Blanc.Lift.Curve3Pool
