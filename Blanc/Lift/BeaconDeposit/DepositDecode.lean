import Blanc.Lift.BeaconDeposit.DepositArgs
import Blanc.Lift.BeaconDeposit.CountView
import Blanc.Lift.ExactWalkOps

namespace Blanc.Lift.BeaconDeposit

open Jaune
open Blanc.Lift

theorem dispatch_deposit {sevm : Sevm} {b : Devm} {g : Nat} {o : Outcome}
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = 0x22895118)
    (k : SFunc.RunExact prog sevm (St b [Sevm.selector sevm] mem0 g) t_00a4_c32 o) :
    SFunc.RunExact prog sevm (St b [] Mem.empty (g + 95)) t_0000_c0 o := by
  refine rx_push rfl (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
  refine rx_mstore (c := 12) (M' := mem0) ?_ (by rw [show (Bytes.toB256 [0x40]).toNat = 64 by decide]; rfl) ?_
  · rw [St.extCost_eq (n := 0) rfl]; decide
  refine rx_push rfl (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
  refine rx_calldatasize (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.one_lt_ofNat]) ?_
  refine rx_lt (v := 0) ?_ (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
  · rw [B256.ltCheck, ite_eq_right]
    intro h
    have h1 := B256.toNat_lt_toNat h
    rw [B256.toNat_toB256_of_lt h_len'] at h1
    have h4 : (Bytes.toB256 [0x04]).toNat = 4 := by decide
    omega
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
  refine rx_branch_zero ?_
  refine rx_push rfl (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
  refine rx_calldataload (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
  refine rx_shr (v := Sevm.selector sevm) ?_ (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
  · rw [show (Bytes.toB256 [0xe0]).toNat = 224 by decide,
      show Bytes.toB256 [0x00] = 0 by decide]
    rfl
  refine cmp_miss (by rw [hsel]; decide) ?_
  refine cmp_hit (j := 32) (by rw [hsel]; decide) rfl k

def depositDecodeGas : Nat := 560

lemma toNat_add_of_lt {x y : B256} (h : x.toNat + y.toNat < 2 ^ 256) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [B256.toNat_add]
  change (x.toNat + y.toNat) % 2 ^ 256 = _
  exact Nat.mod_eq_of_lt h

lemma gtCheck_eq_zero_of_toNat_le {x y : B256} (h : x.toNat ≤ y.toNat) :
    B256.gtCheck x y = 0 := by
  rw [B256.gtCheck, ite_eq_right]
  intro hxy
  have hxy' := B256.toNat_lt_toNat hxy
  omega

lemma ltCheck_eq_zero_of_toNat_le {x y : B256} (h : y.toNat ≤ x.toNat) :
    B256.ltCheck x y = 0 := by
  rw [B256.ltCheck, ite_eq_right]
  intro hxy
  have hxy' := B256.toNat_lt_toNat hxy
  omega

lemma toNat_sub_of_toNat_le {x y : B256} (h : y.toNat ≤ x.toNat) :
    (x - y).toNat = x.toNat - y.toNat := by
  rw [B256.toNat_sub]
  change (2^256 + x.toNat - y.toNat) % 2^256 = x.toNat - y.toNat
  have hp : 2^256 + x.toNat - y.toNat ≥ 2^256 := by omega
  rw [Nat.mod_eq_sub_mod hp]
  have he : 2^256 + x.toNat - y.toNat - 2^256 = x.toNat - y.toNat := by omega
  rw [he, Nat.mod_eq_of_lt]
  have hx := x.toNat_lt
  omega

lemma bsub_add_cancel {x y : B256} (h : y.toNat ≤ x.toNat) : (x - y) + y = x := by
  apply B256.toNat_inj
  rw [toNat_add_of_lt]
  · rw [toNat_sub_of_toNat_le h]
    omega
  · rw [toNat_sub_of_toNat_le h]
    have hy := y.toNat_lt
    have hx := x.toNat_lt
    omega

lemma mul_one_b256 (x : B256) : x * (1 : B256) = x := by
  apply B256.toNat_inj
  rw [B256.toNat_mul]
  have h1 : (1 : B256).toNat = 1 := by decide
  rw [h1, Nat.mul_one, Nat.lo_eq_of_lt x.toNat_lt]

theorem offset0 {sevm : Sevm} {b : Devm} {g : Nat} {o : Outcome} {sel : B256}
    (hcd : sevm.data.length < 2 ^ 256)
    (hlen4 : 4 ≤ sevm.data.length)
    (ho : (argOff sevm 0).toNat ≤ 2 ^ 32)
    (hh : (4 + argOff sevm 0 + 32).toNat ≤ sevm.data.length)
    (k : SFunc.RunExact prog sevm
      (St b [4 + argOff sevm 0, 36, 4, sevm.data.length.toB256, 0x01b8, sel] mem0 g)
      t_00e7_c32 o) :
    SFunc.RunExact prog sevm
      (St b [sevm.data.length.toB256 - 4, 4, 0x01b8, sel] mem0 (g + 88)) t_00ba_c32 o := by
  have h4 : (4 : B256).toNat = 4 := by decide
  have hlen : sevm.data.length.toB256.toNat = sevm.data.length :=
    B256.toNat_toB256_of_lt hcd
  have hsub : (sevm.data.length.toB256 - 4).toNat = sevm.data.length - 4 := by
    rw [B256.toNat_sub, hlen, h4]
    change (2^256 + sevm.data.length - 4) % 2^256 = sevm.data.length - 4
    have hp : 2^256 + sevm.data.length - 4 ≥ 2^256 := by omega
    rw [Nat.mod_eq_sub_mod hp]
    have he : 2^256 + sevm.data.length - 4 - 2^256 = sevm.data.length - 4 := by omega
    rw [he, Nat.mod_eq_of_lt]
    omega
  have hcancel : (sevm.data.length.toB256 - 4) + 4 = sevm.data.length.toB256 :=
    bsub_add_cancel (by rw [h4, hlen]; exact hlen4)
  have hcancel' : 4 + (sevm.data.length.toB256 - 4) = sevm.data.length.toB256 := by
    rw [B256.add_comm]
    exact hcancel
  have hmax : (Nat.toB256 (2 ^ 32)).toNat = 2 ^ 32 := by decide
  have hoff : B256.gtCheck (argOff sevm 0) (Nat.toB256 (2 ^ 32)) = 0 :=
    gtCheck_eq_zero_of_toNat_le (by rw [hmax]; exact ho)
  have hbound : B256.gtCheck ((4 + argOff sevm 0) + 32) sevm.data.length.toB256 = 0 :=
    gtCheck_eq_zero_of_toNat_le (by simpa only [hlen] using hh)
  refine rx_dest ?_
  refine rx_dup2 (S := [0x01b8, sel]) (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_add' (v := sevm.data.length.toB256) (by rw [hcancel']) (by simp only [List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_swap1 ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_dup2 (S := [sevm.data.length.toB256, 0x01b8, sel]) (by simp only [List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_add' (v := 36) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_dup2 (S := [sevm.data.length.toB256, 0x01b8, sel]) (by simp only [List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_calldataload (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_dup2 (S := [36, 4, sevm.data.length.toB256, 0x01b8, sel]) (by simp only [List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  have hmaxword : Bytes.toB256 [0x01, 0, 0, 0, 0] = Nat.toB256 (2 ^ 32) := by decide
  have harg : argOff sevm 0 = Sevm.dataWord sevm 4 := by
    unfold argOff
    rw [show Nat.toB256 0 = (0 : B256) by decide]
    congr 1
  have hoff' : B256.gtCheck (Sevm.dataWord sevm 4) (Bytes.toB256 [0x01, 0, 0, 0, 0]) = 0 := by
    simpa only [hmaxword, Nat.reducePow, harg] using hoff
  refine rx_gt (v := 0) hoff' (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_iszero (v := 1) (by simp only [B256.eqCheck, ↓reduceIte]) (by simp only [List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_branch_succ (d := Bytes.toB256 [0, 0xd5]) (w := 1)
    (S := [argOff sevm 0, 36, 4, sevm.data.length.toB256, 0x01b8, sel]) (by decide) ?_
  refine rx_dest ?_
  refine rx_dup3 (S := [sevm.data.length.toB256, 0x01b8, sel]) (by simp only [List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_add' (v := 4 + argOff sevm 0) (by simp only) (by simp only [List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_dup4 (S := [0x01b8, sel]) (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_dup3 (S := [36, 4, sevm.data.length.toB256, 0x01b8, sel])
    (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_add' (v := (4 + argOff sevm 0) + 32) rfl (by simp only [List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_gt (v := 0) (by simpa only using hbound) (by simp only [List.length_cons, List.length_nil,
    zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_iszero (v := 1) (by simp only [B256.eqCheck, ↓reduceIte]) (by simp only [List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  exact rx_branch_succ (d := Bytes.toB256 [0, 0xe7]) (w := 1)
    (S := [4 + argOff sevm 0, 36, 4, sevm.data.length.toB256, 0x01b8, sel]) (by decide) k

/-- The `deposit` wrapper's head guard: `CALLDATASIZE - 4 ≥ 0x80`. 40 gas. -/
theorem head_block {sevm : Sevm} {b : Devm} {g : Nat} {o : Outcome} {sel : B256}
    (hcd : sevm.data.length < 2 ^ 256)
    (hhead : 132 ≤ sevm.data.length)
    (k : SFunc.RunExact prog sevm
      (St b [sevm.data.length.toB256 - 4, 4, 0x01b8, sel] mem0 g) t_00ba_c32 o) :
    SFunc.RunExact prog sevm (St b [sel] mem0 (g + 40)) t_00a4_c32 o := by
  have hlen : sevm.data.length.toB256.toNat = sevm.data.length :=
    B256.toNat_toB256_of_lt hcd
  have h4 : (4 : B256).toNat = 4 := by decide
  have hsub : (sevm.data.length.toB256 - 4).toNat = sevm.data.length - 4 := by
    rw [B256.toNat_sub, hlen, h4]
    change (2 ^ 256 + sevm.data.length - 4) % 2 ^ 256 = sevm.data.length - 4
    have hp : 2 ^ 256 + sevm.data.length - 4 ≥ 2 ^ 256 := by omega
    rw [Nat.mod_eq_sub_mod hp]
    have he : 2 ^ 256 + sevm.data.length - 4 - 2 ^ 256 = sevm.data.length - 4 := by omega
    rw [he, Nat.mod_eq_of_lt]
    omega
  have h80 : (Bytes.toB256 [0x80] : B256).toNat = 128 := by decide
  have hlt : B256.ltCheck (sevm.data.length.toB256 - 4) (Bytes.toB256 [0x80]) = 0 :=
    ltCheck_eq_zero_of_toNat_le (by rw [h80, hsub]; omega)
  refine rx_dest ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_calldatasize (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_sub' (v := sevm.data.length.toB256 - 4) rfl (by simp only [List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_dup2 (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_lt (v := 0) hlt (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_iszero (v := 1) (by simp only [B256.eqCheck, ↓reduceIte]) (by simp only [List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  exact rx_branch_succ (d := Bytes.toB256 [0x00, 0xba]) (w := 1) (by decide) k

/-- The length guard for dynamic argument `0` (`pc 0x00e7`-`0x0109`): `argLen 0 ≤ 2^32` and
`argPtr 0 + argLen 0 ≤ CDS`, combined via `OR`. 70 gas. -/
theorem len_block0 {sevm : Sevm} {b : Devm} {g : Nat} {o : Outcome} {sel : B256}
    (hcd : sevm.data.length < 2 ^ 256) (ht : TailDecodable sevm 0)
    (k : SFunc.RunExact prog sevm
      (St b [36, argLen sevm 0, argPtr sevm 0, 4, sevm.data.length.toB256, 0x01b8, sel] mem0 g)
      t_0109_c32 o) :
    SFunc.RunExact prog sevm
      (St b [4 + argOff sevm 0, 36, 4, sevm.data.length.toB256, 0x01b8, sel] mem0 (g + 70))
      t_00e7_c32 o := by
  have hlen : sevm.data.length.toB256.toNat = sevm.data.length :=
    B256.toNat_toB256_of_lt hcd
  have hmax : (Nat.toB256 (2 ^ 32)).toNat = 2 ^ 32 := by decide
  have hguard1 : B256.gtCheck (argPtr sevm 0 + argLen sevm 0) sevm.data.length.toB256 = 0 :=
    gtCheck_eq_zero_of_toNat_le (by simpa only [hlen] using ht.2.2.2)
  have hguard2 : B256.gtCheck (argLen sevm 0) (Nat.toB256 (2 ^ 32)) = 0 :=
    gtCheck_eq_zero_of_toNat_le (by rw [hmax]; exact ht.2.2.1)
  refine rx_dest ?_
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_calldataload (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_swap1 ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_add' (v := argPtr sevm 0)
    (by rw [show Bytes.toB256 [0x20] = (32 : B256) by decide]; rfl) (by simp only [List.length_cons,
      List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_swap2 ?_
  refine rx_dup (n := 4) rfl (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_dup4 (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_mul (v := argLen sevm 0)
    (by rw [show Bytes.toB256 [0x01] = (1 : B256) by decide]; exact mul_one_b256 _) (by simp only [List.length_cons,
      List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_dup (n := 4) rfl (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_add' (v := argPtr sevm 0 + argLen sevm 0) rfl (by simp only [List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_gt (v := 0) hguard1 (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push (w := Nat.toB256 (2 ^ 32)) (by decide) (by simp only [List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_dup4 (by simp only [Nat.reducePow, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_gt (v := 0) hguard2 (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_or (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_iszero (v := 1) (by simp only [B256.eqCheck, ↓reduceIte]) (by simp only [List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  exact rx_branch_succ (d := Bytes.toB256 [0x01, 0x09]) (w := 1) (by decide) k

/-- The length guard for dynamic argument `1` (`pc 0x0139`-`0x015b`), argument `0`'s decoded
`len, ptr` carried underneath. 70 gas. -/
theorem len_block1 {sevm : Sevm} {b : Devm} {g : Nat} {o : Outcome} {sel : B256}
    (hcd : sevm.data.length < 2 ^ 256) (ht : TailDecodable sevm 1)
    (k : SFunc.RunExact prog sevm
      (St b [68, argLen sevm 1, argPtr sevm 1, 4, sevm.data.length.toB256,
        argLen sevm 0, argPtr sevm 0, 0x01b8, sel] mem0 g) t_015b_c32 o) :
    SFunc.RunExact prog sevm
      (St b [4 + argOff sevm 1, 68, 4, sevm.data.length.toB256,
        argLen sevm 0, argPtr sevm 0, 0x01b8, sel] mem0 (g + 70)) t_0139_c32 o := by
  have hlen : sevm.data.length.toB256.toNat = sevm.data.length :=
    B256.toNat_toB256_of_lt hcd
  have hmax : (Nat.toB256 (2 ^ 32)).toNat = 2 ^ 32 := by decide
  have hguard1 : B256.gtCheck (argPtr sevm 1 + argLen sevm 1) sevm.data.length.toB256 = 0 :=
    gtCheck_eq_zero_of_toNat_le (by simpa only [hlen] using ht.2.2.2)
  have hguard2 : B256.gtCheck (argLen sevm 1) (Nat.toB256 (2 ^ 32)) = 0 :=
    gtCheck_eq_zero_of_toNat_le (by rw [hmax]; exact ht.2.2.1)
  refine rx_dest ?_
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_calldataload (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_swap1 ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_add' (v := argPtr sevm 1)
    (by rw [show Bytes.toB256 [0x20] = (32 : B256) by decide]; rfl) (by simp only [List.length_cons,
      List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_swap2 ?_
  refine rx_dup (n := 4) rfl (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_dup4 (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_mul (v := argLen sevm 1)
    (by rw [show Bytes.toB256 [0x01] = (1 : B256) by decide]; exact mul_one_b256 _) (by simp only [List.length_cons,
      List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_dup (n := 4) rfl (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_add' (v := argPtr sevm 1 + argLen sevm 1) rfl (by simp only [List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_gt (v := 0) hguard1 (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push (w := Nat.toB256 (2 ^ 32)) (by decide) (by simp only [List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_dup4 (by simp only [Nat.reducePow, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_gt (v := 0) hguard2 (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_or (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_iszero (v := 1) (by simp only [B256.eqCheck, ↓reduceIte]) (by simp only [List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  exact rx_branch_succ (d := Bytes.toB256 [0x01, 0x5b]) (w := 1) (by decide) k

/-- The length guard for dynamic argument `2` (`pc 0x018b`-`0x01ad`), arguments `0` and `1`'s
decoded `len, ptr` carried underneath. 70 gas. -/
theorem len_block2 {sevm : Sevm} {b : Devm} {g : Nat} {o : Outcome} {sel : B256}
    (hcd : sevm.data.length < 2 ^ 256) (ht : TailDecodable sevm 2)
    (k : SFunc.RunExact prog sevm
      (St b [100, argLen sevm 2, argPtr sevm 2, 4, sevm.data.length.toB256,
        argLen sevm 1, argPtr sevm 1, argLen sevm 0, argPtr sevm 0, 0x01b8, sel] mem0 g)
      t_01ad_c32 o) :
    SFunc.RunExact prog sevm
      (St b [4 + argOff sevm 2, 100, 4, sevm.data.length.toB256,
        argLen sevm 1, argPtr sevm 1, argLen sevm 0, argPtr sevm 0, 0x01b8, sel] mem0 (g + 70))
      t_018b_c32 o := by
  have hlen : sevm.data.length.toB256.toNat = sevm.data.length :=
    B256.toNat_toB256_of_lt hcd
  have hmax : (Nat.toB256 (2 ^ 32)).toNat = 2 ^ 32 := by decide
  have hguard1 : B256.gtCheck (argPtr sevm 2 + argLen sevm 2) sevm.data.length.toB256 = 0 :=
    gtCheck_eq_zero_of_toNat_le (by simpa only [hlen] using ht.2.2.2)
  have hguard2 : B256.gtCheck (argLen sevm 2) (Nat.toB256 (2 ^ 32)) = 0 :=
    gtCheck_eq_zero_of_toNat_le (by rw [hmax]; exact ht.2.2.1)
  refine rx_dest ?_
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_calldataload (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_swap1 ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_add' (v := argPtr sevm 2)
    (by rw [show Bytes.toB256 [0x20] = (32 : B256) by decide]; rfl) (by simp only [List.length_cons,
      List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_swap2 ?_
  refine rx_dup (n := 4) rfl (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_dup4 (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_mul (v := argLen sevm 2)
    (by rw [show Bytes.toB256 [0x01] = (1 : B256) by decide]; exact mul_one_b256 _) (by simp only [List.length_cons,
      List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_dup (n := 4) rfl (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_add' (v := argPtr sevm 2 + argLen sevm 2) rfl (by simp only [List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_gt (v := 0) hguard1 (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push (w := Nat.toB256 (2 ^ 32)) (by decide) (by simp only [List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_dup4 (by simp only [Nat.reducePow, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_gt (v := 0) hguard2 (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_or (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_iszero (v := 1) (by simp only [B256.eqCheck, ↓reduceIte]) (by simp only [List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  exact rx_branch_succ (d := Bytes.toB256 [0x01, 0xad]) (w := 1) (by decide) k

/-- The swap dance restaging argument `0`'s `(len, ptr)` and recomputing `argOff 1` (`pc 0x0109`
through the two offset guards, ending `0x0139`). 97 gas. -/
theorem tail1 {sevm : Sevm} {b : Devm} {g : Nat} {o : Outcome} {sel : B256}
    (hcd : sevm.data.length < 2 ^ 256) (ht : TailDecodable sevm 1)
    (k : SFunc.RunExact prog sevm
      (St b [4 + argOff sevm 1, 68, 4, sevm.data.length.toB256, argLen sevm 0, argPtr sevm 0,
        0x01b8, sel] mem0 g) t_0139_c32 o) :
    SFunc.RunExact prog sevm
      (St b [36, argLen sevm 0, argPtr sevm 0, 4, sevm.data.length.toB256, 0x01b8, sel] mem0
        (g + 97)) t_0109_c32 o := by
  have hlen : sevm.data.length.toB256.toNat = sevm.data.length :=
    B256.toNat_toB256_of_lt hcd
  have hmax : (Nat.toB256 (2 ^ 32)).toNat = 2 ^ 32 := by decide
  have hpos1 : (4 : B256) + 32 * Nat.toB256 1 = 36 := by decide
  have hoff1 : argOff sevm 1 = Sevm.dataWord sevm 36 := by
    unfold argOff; rw [hpos1]
  have hguard1 : B256.gtCheck (argOff sevm 1) (Nat.toB256 (2 ^ 32)) = 0 :=
    gtCheck_eq_zero_of_toNat_le (by rw [hmax]; exact ht.1)
  have hguard2 : B256.gtCheck ((4 + argOff sevm 1) + 32) sevm.data.length.toB256 = 0 :=
    gtCheck_eq_zero_of_toNat_le (by simpa only [hlen] using ht.2.1)
  refine rx_dest ?_
  refine rx_swap2 ?_
  refine rx_swap (n := 3) rfl ?_
  refine rx_swap1 ?_
  refine rx_swap3 ?_
  refine rx_swap1 ?_
  refine rx_swap2 ?_
  refine rx_push rfl (by simp only [List.set_cons_zero, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_dup2 (by simp only [List.set_cons_zero, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_add' (v := 68) (by decide) (by simp only [List.set_cons_zero, List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_swap1 ?_
  refine rx_calldataload (by simp only [List.set_cons_zero, List.length_cons, List.length_nil,
    zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  rw [← hoff1]
  refine rx_push (w := Nat.toB256 (2 ^ 32)) (by decide) (by simp only [List.set_cons_zero,
    List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_dup2 (by simp only [Nat.reducePow, List.set_cons_zero, List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_gt (v := 0) hguard1 (by simp only [List.set_cons_zero, List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_iszero (v := 1) (by simp only [B256.eqCheck, ↓reduceIte]) (by simp only [List.set_cons_zero,
    List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push rfl (by simp only [List.set_cons_zero, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_branch_succ (d := Bytes.toB256 [0x01, 0x27]) (w := 1) (by decide) ?_
  refine rx_dest ?_
  refine rx_dup3 (by simp only [List.set_cons_zero, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_add' (v := 4 + argOff sevm 1) rfl (by simp only [List.set_cons_zero, List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_dup4 (by simp only [List.set_cons_zero, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push rfl (by simp only [List.set_cons_zero, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_dup3 (by simp only [List.set_cons_zero, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_add' (v := (4 + argOff sevm 1) + 32) rfl (by simp only [List.set_cons_zero,
    List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_gt (v := 0) hguard2 (by simp only [List.set_cons_zero, List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_iszero (v := 1) (by simp only [B256.eqCheck, ↓reduceIte]) (by simp only [List.set_cons_zero,
    List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push rfl (by simp only [List.set_cons_zero, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  exact rx_branch_succ (d := Bytes.toB256 [0x01, 0x39]) (w := 1) (by decide) k

/-- The swap dance restaging arguments `0,1`'s `(len, ptr)` and recomputing `argOff 2`
(`pc 0x015b` through the two offset guards, ending `0x018b`). 97 gas. -/
theorem tail2 {sevm : Sevm} {b : Devm} {g : Nat} {o : Outcome} {sel : B256}
    (hcd : sevm.data.length < 2 ^ 256) (ht : TailDecodable sevm 2)
    (k : SFunc.RunExact prog sevm
      (St b [4 + argOff sevm 2, 100, 4, sevm.data.length.toB256, argLen sevm 1, argPtr sevm 1,
        argLen sevm 0, argPtr sevm 0, 0x01b8, sel] mem0 g) t_018b_c32 o) :
    SFunc.RunExact prog sevm
      (St b [68, argLen sevm 1, argPtr sevm 1, 4, sevm.data.length.toB256,
        argLen sevm 0, argPtr sevm 0, 0x01b8, sel] mem0 (g + 97)) t_015b_c32 o := by
  have hlen : sevm.data.length.toB256.toNat = sevm.data.length :=
    B256.toNat_toB256_of_lt hcd
  have hmax : (Nat.toB256 (2 ^ 32)).toNat = 2 ^ 32 := by decide
  have hpos2 : (4 : B256) + 32 * Nat.toB256 2 = 68 := by decide
  have hoff2 : argOff sevm 2 = Sevm.dataWord sevm 68 := by
    unfold argOff; rw [hpos2]
  have hguard1 : B256.gtCheck (argOff sevm 2) (Nat.toB256 (2 ^ 32)) = 0 :=
    gtCheck_eq_zero_of_toNat_le (by rw [hmax]; exact ht.1)
  have hguard2 : B256.gtCheck ((4 + argOff sevm 2) + 32) sevm.data.length.toB256 = 0 :=
    gtCheck_eq_zero_of_toNat_le (by simpa only [hlen] using ht.2.1)
  refine rx_dest ?_
  refine rx_swap2 ?_
  refine rx_swap (n := 3) rfl ?_
  refine rx_swap1 ?_
  refine rx_swap3 ?_
  refine rx_swap1 ?_
  refine rx_swap2 ?_
  refine rx_push rfl (by simp only [List.set_cons_zero, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_dup2 (by simp only [List.set_cons_zero, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_add' (v := 100) (by decide) (by simp only [List.set_cons_zero, List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_swap1 ?_
  refine rx_calldataload (by simp only [List.set_cons_zero, List.length_cons, List.length_nil,
    zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  rw [← hoff2]
  refine rx_push (w := Nat.toB256 (2 ^ 32)) (by decide) (by simp only [List.set_cons_zero,
    List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_dup2 (by simp only [Nat.reducePow, List.set_cons_zero, List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_gt (v := 0) hguard1 (by simp only [List.set_cons_zero, List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_iszero (v := 1) (by simp only [B256.eqCheck, ↓reduceIte]) (by simp only [List.set_cons_zero,
    List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push rfl (by simp only [List.set_cons_zero, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_branch_succ (d := Bytes.toB256 [0x01, 0x79]) (w := 1) (by decide) ?_
  refine rx_dest ?_
  refine rx_dup3 (by simp only [List.set_cons_zero, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_add' (v := 4 + argOff sevm 2) rfl (by simp only [List.set_cons_zero, List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_dup4 (by simp only [List.set_cons_zero, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push rfl (by simp only [List.set_cons_zero, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_dup3 (by simp only [List.set_cons_zero, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_add' (v := (4 + argOff sevm 2) + 32) rfl (by simp only [List.set_cons_zero,
    List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_gt (v := 0) hguard2 (by simp only [List.set_cons_zero, List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_iszero (v := 1) (by simp only [B256.eqCheck, ↓reduceIte]) (by simp only [List.set_cons_zero,
    List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push rfl (by simp only [List.set_cons_zero, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  exact rx_branch_succ (d := Bytes.toB256 [0x01, 0x8b]) (w := 1) (by decide) k

theorem deposit_wrapper {sevm : Sevm} {b b' : Devm} {M' : Mem} {g g' : Nat} {sel : B256}
    (hdec : DepositDecodable sevm) (hcd : sevm.data.length < 2 ^ 256)
    (body : SFunc.RunExact prog sevm (St b (depositArgStack sevm [sel]) mem0 g) t_0304_c7
      (.returned (St b' [sel] M' (g' + 1)))) :
    ∃ post, SFunc.RunExact prog sevm (St b [sel] mem0 (g + depositDecodeGas)) t_00a4_c32
      (.halted post) ∧ post = St b' [sel] M' g' := by
  obtain ⟨hhead, ht0, ht1, ht2⟩ := hdec
  refine ⟨St b' [sel] M' g', ?_, rfl⟩
  unfold depositDecodeGas
  refine head_block hcd hhead ?_
  refine offset0 hcd (by omega) ht0.1 ht0.2.1 ?_
  refine len_block0 hcd ht0 ?_
  refine tail1 hcd ht1 ?_
  refine len_block1 hcd ht1 ?_
  refine tail2 hcd ht2 ?_
  refine len_block2 hcd ht2 ?_
  refine rx_dest ?_
  refine rx_swap2 ?_
  refine rx_swap (n := 3) rfl ?_
  refine rx_pop ?_
  refine rx_swap2 ?_
  refine rx_pop ?_
  refine rx_calldataload (by simp only [List.set_cons_zero, List.length_cons, List.length_nil,
    zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_push rfl (by simp only [List.set_cons_zero, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_callRet (j := 7) rfl body ?_
  refine rx_dest ?_
  exact .last rfl

end Blanc.Lift.BeaconDeposit
