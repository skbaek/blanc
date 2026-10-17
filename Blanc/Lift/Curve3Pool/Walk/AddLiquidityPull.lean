import Blanc.Lift.Curve3Pool.Walk.AddLiquidityD0

/-!
# `add_liquidity`, part 4: the pull loop

`new_balances = old_balances`, then for each coin `i`: `in_amount = amounts[i]` (asserted
positive on a first deposit), and for a positive amount the `transferFrom` `raw_call` (for coin
`2`, between two `balanceOf(self)` reads), then `new_balances[i] = old_balances[i] + in_amount`
(checked).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The pull loop's words: the words before the loop, the counter and `new_balances`. -/
structure AlPullImg (img : Bytes) (i : Nat) (F AF A T D0 : B256) (old nv : Nat → B256) : Prop where
  m0 : AlMem0 img F AF A T D0 old
  ctr : WordAt img 0x4c0 (Nat.toB256 i)
  n0 : WordAt img 0x460 (nv 0)
  n1 : WordAt img 0x480 (nv 1)
  n2 : WordAt img 0x4a0 (nv 2)

/-- `amounts[i]`, as the body reads it. -/
abbrev alAmt (sevm : Sevm) (i : Nat) : B256 :=
  Sevm.dataWord sevm (Bytes.toB256 [0x20] * Nat.toB256 i + Bytes.toB256 [4])

theorem AlMem0.keep {img : Bytes} {F AF A T D0 : B256} {old : Nat → B256} {o : Nat} {xs : Bytes}
    (h : AlMem0 img F AF A T D0 old) (ho : 0x360 ≤ o ∨ o + xs.length ≤ 0x140) :
    AlMem0 (Bytes.writeAt img o xs) F AF A T D0 old where
  f0 := h.f0.write_other (by omega)
  f1 := h.f1.write_other (by omega)
  f2 := h.f2.write_other (by omega)
  fee := h.fee.write_other (by omega)
  adm := h.adm.write_other (by omega)
  amp := h.amp.write_other (by omega)
  supply := h.supply.write_other (by omega)
  d0 := h.d0.write_other (by omega)
  o0 := h.o0.write_other (by omega)
  o1 := h.o1.write_other (by omega)
  o2 := h.o2.write_other (by omega)

/-- **Before the loop** (`0x1031` → `0x105d`): `new_balances = old_balances`, counter `0`. -/
theorem xa_al_p4 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {F AF A T D0 : B256} {old : Nat → B256} (hcode : sevm.code = code)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0)
    (hm : AlMem0 img F AF A T D0 old) (h : XAt sevm post 0x1031 (St b [] M G) L) :
    ∃ M' img' G', Mem.Reads M' img' ∧ Mem.Wf M' ∧ M'.size % 32 = 0 ∧
      AlPullImg img' 0 F AF A T D0 old old ∧ XAt sevm post 0x105d (St b [3, 0x4c0] M' G') L := by
  xjd 0x1032
  xs 0x1035 (.push [0x04, 0x60] (by decide)) ri_push
  xs 0x1038 (.push [0x03, 0x00] (by decide)) ri_push
  xs 0x1039 (.reg (.dup 0)) (ri_dup (by rfl))
  xml 0x103a 0x300 hm.o0
  xs 0x103b (.reg (.dup 2)) (ri_dup (by rfl))
  xma 0x103c (.reg .mstore) (ri_mstore_imgAtA (o := 0x460) rfl)
  xs 0x103d (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x103f (.push [0x20] (by decide)) ri_push
  xs 0x1040 (.reg .add) ri_add
  xml 0x1041 0x320 hm.o1
  xs 0x1042 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x1044 (.push [0x20] (by decide)) ri_push
  xs 0x1045 (.reg .add) ri_add
  xma 0x1046 (.reg .mstore) (ri_mstore_imgAtA (o := 0x480) rfl)
  xs 0x1047 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x1049 (.push [0x40] (by decide)) ri_push
  xs 0x104a (.reg .add) ri_add
  xml 0x104b 0x340 hm.o2
  xs 0x104c (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x104e (.push [0x40] (by decide)) ri_push
  xs 0x104f (.reg .add) ri_add
  xma 0x1050 (.reg .mstore) (ri_mstore_imgAtA (o := 0x4a0) rfl)
  xs 0x1051 (.reg .pop) ri_pop
  xs 0x1052 (.reg .pop) ri_pop
  xs 0x1055 (.push [0x04, 0xc0] (by decide)) ri_push
  xs 0x1057 (.push [0x00] (by decide)) ri_push
  xs 0x1059 (.push [0x03] (by decide)) ri_push
  xs 0x105a (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x105b (.reg (.dup 3)) (ri_dup (by rfl))
  xma 0x105c (.reg .mstore) (ri_mstore_imgAtA (o := 0x4c0) rfl)
  xs 0x105d (.reg .add) ri_add
  rw [show [Bytes.toB256 [3] + Bytes.toB256 [0], Bytes.toB256 [4, 192]] = ([3, 0x4c0] : List B256)
    by decide] at h
  refine ⟨_, _, _, hR, hW, hA, ⟨?_, ?_, ?_, ?_, ?_⟩, h⟩
  · exact (((hm.keep (by simp only [B256.length_toBytes]; omega)).keep
      (by simp only [B256.length_toBytes]; omega)).keep (by simp only [B256.length_toBytes]; omega)).keep
      (by simp only [B256.length_toBytes]; omega)
  · rw [show Nat.toB256 0 = Bytes.toB256 [0] by decide]; wchain
  all_goals wchain

end Blanc.Lift.Curve3Pool
