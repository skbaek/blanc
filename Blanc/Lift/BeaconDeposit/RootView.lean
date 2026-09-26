import Blanc.Lift.BeaconDeposit.RootLoop
import Blanc.Lift.BeaconDeposit.CountView

/-!
# `get_deposit_root()` on the deployed beacon deposit contract: liveness with exact gas

The walk of the deployed runtime's `get_deposit_root` path over the lifted program `prog`:

* the dispatcher (entry 0): three selector misses and the hit on `0xc5f2892f`
  (`dispatch_root`, 139 gas);
* the wrapper (entry 34): the `nonpayable` guard, the call into the internal function, and the
  `RETURN` of the root word stored at the free pointer (`root_wrapper`, 82 gas);
* the internal function (entry 10, `root_fn`): the count read (warm or cold), the 32
  iterations of the Merkle loop at entry 24 (`root_loop`, `Blanc/Lift/BeaconDeposit/RootLoop.lean`),
  and the exit (`root_exit`, 1959 gas): the count re-read (warm by then),
  `to_little_endian_64` (`to_little_endian_64_run`), the packing of
  `node ‖ le64 count ‖ bytes24(0)` (with a partial-word copy of the eight count bytes) and its
  SHA-256 through `copy_sha` (`Blanc/Lift/PackedSha.lean`).

`get_deposit_root_runExact` is the counterpart of the Blanc port's
`getDepositRoot_zero_runCompiled_noRawSstore` over `SProg.RunExact prog`: the output is
`(Acc.root sha256 (solAcc stor)).toBytes` and the gas is `rootViewGas`, to be composed with
the certificate's `exec_of_runExact` once it is checked.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune
open Blanc.BeaconDeposit

/-- The mix-in's hash tail (entry 30's exit). -/
abbrev mixExit : SFunc :=
  mergeTree (shaCallTree 0x14 0x9c 0x14 0xb1 t_1493_c24 t_14ad_c24 t_14b1_c24)

theorem prog_30 : prog[30]? = some (mcpyTree 0x14 0x3f 0x14 0x02 30 mixExit) := rfl

theorem t_1402_eq : t_1402_c24 = mcpyTree 0x14 0x3f 0x14 0x02 30 mixExit := rfl

theorem t_10d1_c10_eq : t_10d1_c10 = t_10d1_c24 := rfl

/-! ## The loop's exit: the mix-in -/

theorem b256_zero_or (x : B256) : ((0 : B256) ||| x) = x := by
  rcases x with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  apply Prod.ext <;> apply Prod.ext <;> exact UInt64.zero_or

theorem mem_sloadAccessed {o : Adr} {keys : KeySet} {k : B256} {p : Adr × B256} (h : p ∈ keys) :
    p ∈ sloadAccessedStorageKeys o keys k := by
  unfold sloadAccessedStorageKeys
  split
  · exact h
  · exact Std.HashSet.mem_insert.mpr (Or.inr h)

theorem mem_rootKeys {o : Adr} {p : Adr × B256} :
    ∀ n h s keys, p ∈ keys → p ∈ rootKeys o n h s keys
  | 0, _, _, _, hp => hp
  | n + 1, h, s, _, hp => mem_rootKeys n (h + 1) (s / 2) _ (mem_sloadAccessed hp)

/-- The gas from the loop head at height 32 to the function's return: the exit test and the
count re-read (152, the slot warm), `to_little_endian_64` (821), the mix-in's packing and the
partial-word copy of the eight count bytes (345), the copy, merge and precompile call
(598), the return (26), and the memory expansion from 103 to 108 words (17). -/
def rootExitGas : Nat := 1959

section Exit

variable {sevm : Sevm} {G : Nat}

theorem root_exit {b : Devm} {M : Mem} {img : Bytes} {node rv ret : B256} {count : Nat}
    {R0 : List B256}
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = 3296)
    (hfp : img.sliceD 64 32 0 = (Nat.toB256 3200).toBytes) (hR : R0.length < 800)
    (hok : ShaOk sevm b) (hG : G + 5000 < 2 ^ 256) (hcd : sevm.data.length < 2 ^ 256)
    (hcount : b.getStorVal sevm.currentTarget solCountSlot = Nat.toB256 count)
    (hc32 : count < 2 ^ 32)
    (hwarm : (⟨sevm.currentTarget, solCountSlot⟩ : Adr × B256) ∈ b.accessedStorageKeys) :
    ∃ b' M', BaseRel b b' ∧ b'.accessedStorageKeys = b.accessedStorageKeys ∧ Mem.Wf M' ∧
      M'.size = 3456 ∧
      (∃ img', Mem.Reads M' img' ∧ img'.sliceD 64 32 0 = (Nat.toB256 3360).toBytes) ∧
      SFunc.RunExactCut prog sevm [24]
        (St b (Nat.toB256 32 :: Nat.toB256 0 :: node :: rv :: ret :: R0) M (G + rootExitGas))
        t_10d1_c24
        (.done (.returned (St b' (mixIn Bytes.sha256 node count :: R0) M' G))) := by
  set R := rv :: ret :: R0 with hRdef
  have hRl : R.length < 810 := by rw [hRdef]; simp; omega
  have hpB : (Nat.toB256 3200).toNat = 3200 := by decide
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := by decide
  have hcost : sloadCost sevm b (Bytes.toB256 [0x20]) = 100 := by
    rw [show Bytes.toB256 [0x20] = solCountSlot by decide]
    unfold sloadCost; rw [ite_eq_left_iff.mpr (fun h => absurd hwarm h)]; rfl
  have hafter : afterSload sevm b (Bytes.toB256 [0x20]) = b := by
    rw [show Bytes.toB256 [0x20] = solCountSlot by decide]
    unfold afterSload; exact ite_eq_left_iff.mpr (fun h => absurd hwarm h)
  have hcnt : b.getStorVal sevm.currentTarget (Bytes.toB256 [0x20]) = Nat.toB256 count := by
    rw [show Bytes.toB256 [0x20] = solCountSlot by decide, hcount]
  -- `to_little_endian_64`
  obtain ⟨M1, hwf1, hr1, hs1, hle⟩ := to_little_endian_64_run (sevm := sevm) (b := b)
    (G := G + 986) (v := Nat.toB256 count) (ret := Bytes.toB256 [0x12, 0xff])
    (rest := node :: Bytes.toB256 [0x02] :: Nat.toB256 0 :: node :: R) (by simp; omega) hwf hr (by simp [hs])
    (by simp [hs]) (by rw [hfp, B256.toB256_toBytes]) (by simp [hpB]) (by simp [hpB]) (by simp [hpB])
    hcd
  rw [hs, hpB, show leGas 3296 3200 = 821 by decide] at hle
  rw [hs, hpB, show max 3296 (3200 + 64) = 3296 by decide] at hs1
  set img1 := leImg img (Nat.toB256 3200) (Nat.toB256 count) with himg1
  have h1_64 : img1.sliceD 64 32 0 = (Nat.toB256 3264).toBytes := by
    rw [himg1, leImg, hpB, Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), sliceD_word_self]
    rfl
  have h1_len : img1.sliceD 3200 32 0 = (Nat.toB256 8).toBytes := by
    rw [himg1, leImg, hpB, Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; omega),
      sliceD_word_self]
    rfl
  set M2 := M1.write 3296 node.toBytes with hM2
  have hs2 : M2.size = 3328 := by
    rw [hM2, Mem.size_write_word_aligned (by rw [hs1]) (by decide), hs1]; decide
  have hwf2 : Mem.Wf M2 := hwf1.write _ _
  have hr2 := hr1.write hwf1 3296 node.toBytes
  have h2_len : (Bytes.writeAt img1 3296 node.toBytes).sliceD 3200 32 0 = (Nat.toB256 8).toBytes := by
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), h1_len]
  -- the partial last word: the eight count bytes
  set ws := Bytes.toB256 (M2.read 3232 32).1 with hws
  set M2' := (M2.read 3328 32).2 with hM2'
  have hs2' : M2'.size = 3360 := by rw [hM2', read_ext_size hs2 (by decide) (by decide)]; decide
  have hwd : Bytes.toB256 (M2.read 3328 32).1 = 0 := by
    rw [read_past_size hwf2 (by rw [hs2])]; decide
  set m := Bytes.toB256 (255 :: List.replicate 31 255) +
    B256.bexp (Bytes.toB256 [0x01, 0x00]) (Nat.toB256 24) with hm
  have hmask : (~~~ m) = maskTop8 := by rw [hm]; decide +kernel
  set M3 := M2'.write 3328 (ws &&& ~~~ m).toBytes with hM3
  set M4 := M3.write 3336 (0 : B256).toBytes with hM4
  have hs3 : M3.size = 3360 := by
    rw [hM3, Mem.size_write_word_aligned (by rw [hs2']) (by decide), hs2']; decide
  have hs4 : M4.size = 3392 := by rw [hM4, Mem.size_write_word_at, hs3]; decide
  have hwf3 : Mem.Wf M3 := (hwf2.extend _ _).write _ _
  have hwf4 : Mem.Wf M4 := hwf3.write _ _
  have hr3 := (hr2.extend 3328 32).write (hwf2.extend _ _) 3328 (ws &&& ~~~ m).toBytes
  have hr4 := hr3.write hwf3 3336 (0 : B256).toBytes
  set img4 := Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img1 3296 node.toBytes) 3328
    (ws &&& ~~~ m).toBytes) 3336 (0 : B256).toBytes with himg4
  have h4_64 : img4.sliceD 64 32 0 = (Nat.toB256 3264).toBytes := by
    rw [himg4, Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), h1_64]
  set M5 := M4.write 3264 (Nat.toB256 64).toBytes with hM5
  set M6 := M5.write 64 (Nat.toB256 3360).toBytes with hM6
  have hs5 : M5.size = 3392 := by
    rw [hM5, Mem.size_write_word_aligned (by rw [hs4]) (by decide), hs4]; decide
  have hs6 : M6.size = 3392 := by
    rw [hM6, Mem.size_write_word_aligned (by rw [hs5]) (by decide), hs5]; decide
  have hwf5 : Mem.Wf M5 := hwf4.write _ _
  have hwf6 : Mem.Wf M6 := hwf5.write _ _
  have hr5 := hr4.write hwf4 3264 (Nat.toB256 64).toBytes
  have hr6 := hr5.write hwf5 64 (Nat.toB256 3360).toBytes
  have h5_64 : (Bytes.writeAt img4 3264 (Nat.toB256 64).toBytes).sliceD 64 32 0 =
      (Nat.toB256 3264).toBytes := by
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), h4_64]
  have h5_len : (Bytes.writeAt img4 3264 (Nat.toB256 64).toBytes).sliceD 3264 32 0 =
      (Nat.toB256 64).toBytes := sliceD_word_self _ _ _
  set img6 := Bytes.writeAt (Bytes.writeAt img4 3264 (Nat.toB256 64).toBytes) 64
    (Nat.toB256 3360).toBytes with himg6
  have h6_64 : img6.sliceD 64 32 0 = (Nat.toB256 3360).toBytes := sliceD_word_self _ _ _
  have h6_len : img6.sliceD 3264 32 0 = (Nat.toB256 64).toBytes := by
    rw [himg6, Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; omega), h5_len]
  have hval : (ws &&& ~~~ m).toBytes = (ws.toBytes.take 8) ++ List.replicate 24 0 := by
    rw [hmask, B256.and_comm, maskTop8_and]
  have h6_node : img6.sliceD 3296 32 0 = node.toBytes := by
    rw [himg6, Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; omega),
      Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]), himg4,
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), sliceD_word_self]
  have h6_w2 : img6.sliceD (3296 + 32) 32 0 = (ws &&& ~~~ m).toBytes := by
    rw [himg6, Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; omega),
      Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; omega), himg4,
      show (32 : Nat) = 8 + 24 from rfl, List.sliceD_split,
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by rw [B256.length_toBytes]; omega),
      Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by rw [B256.length_toBytes]; omega), hval]
    have ht : (ws.toBytes.take 8).length = 8 := by simp [B256.length_toBytes]
    rw [show B256.toBytes 0 = List.replicate 32 0 by decide]
    simp only [List.sliceD, show 3296 + (8 + 24) - 3328 = 0 from rfl, List.drop_zero]
    rw [List.takeD_eq_take 0 (by simp [ht]), List.take_left' ht,
      List.takeD_eq_take 0 (by simp), List.take_replicate]
    rfl
  obtain ⟨b', M', img', hpost, hwf', hr', hs', hw', hh', hrun⟩ :=
    copy_sha (fs := prog) (sevm := sevm) (C := [24]) (b := b) (R := Nat.toB256 0 :: node :: R)
      (M := M6) (G := G + 26) (T := t_14b1_c24) (fail1 := t_1493_c24) (fail2 := t_14ad_c24)
      (n := 3392) (s := 3296) (d := 3360) (w1 := node) (w2 := ws &&& ~~~ m)
      (x1 := Nat.toB256 3296) (x3 := Nat.toB256 3360) (x4 := Nat.toB256 3264)
      prog_30 (by simp) hwf6 hr6 hs6 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by omega) h6_64 h6_node h6_w2 (by simp; omega) hok.nodeleg hok.warm hok.pre
      hok.fork hok.depth (by omega)
  have hle8 : (ws.toBytes).take 8 = Blanc.BeaconDeposit.le64 count := by
    have h8 : (Blanc.BeaconDeposit.le64 count).length = 8 := rfl
    rw [hws, toBytes_read, hr2.read, show (32 : Nat) = 8 + 24 from rfl, List.sliceD_split,
      List.take_left' (List.length_sliceD _ _ _ _), Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      himg1, leImg, hpB, show (3200 + 32 : Nat) = 3232 from rfl,
      B256.toNat_toB256_of_lt (show count < 2 ^ 256 by omega), ← h8, Bytes.sliceD_writeAt]
  have hroot : Bytes.sha256 (node.toBytes ++ (ws &&& ~~~ m).toBytes) =
      mixIn Bytes.sha256 node count := by
    rw [hval, hle8, mixIn, zeros, List.append_assoc]
  rw [hroot] at hh' hpost
  refine ⟨b', M', baseRel_sha hpost, hpost.keys, hwf', by rw [hs'], ⟨img', hr', hw'⟩, ?_⟩
  unfold t_10d1_c24 t_12f0_c24
  refine rxc_dest ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_lt (v := 0) (by decide) (by simp; omega) ?_
  refine rxc_iszero (v := 1) (by decide) (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_branch_succ (by decide) ?_
  refine rxc_dest ?_
  refine rxc_pop ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_dup (n := 2) rfl (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  rw [show G + 1918 = G + 986 + 821 + 8 + 3 + sloadCost sevm b (Bytes.toB256 [0x20]) by
    rw [hcost]]
  refine rxc_sload_sel hok.fork (by simp; omega) ?_
  rw [hafter, hcnt]
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_callRet rfl hle ?_
  unfold t_12ff_c24
  refine rxc_dest ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_shl (v := 0) (by decide) (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 3264) ?_ (by rw [h40]; exact read_word hr1 64 h1_64)
    ?_ (by simp; omega) ?_
  · rw [h40]; exact charge_covered hs1 (by decide) (by decide)
  · rw [h40]; exact read_covered hs1 (by decide) (by decide)
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_add' (v := Nat.toB256 3296) (by decide) (by simp; omega) ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_dup (n := 4) rfl (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_mstore (c := 7) (M' := M2) ?_ (by rw [show (Nat.toB256 3296).toNat = 3296 by decide]) ?_
  · rw [show (Nat.toB256 3296).toNat = 3296 by decide, St.extCost_eq hs1]; decide
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_add' (v := Nat.toB256 3328) (by decide) (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 8) ?_ (by rw [hpB]; exact read_word hr2 3200 h2_len)
    ?_ (by simp; omega) ?_
  · rw [hpB]; exact charge_covered hs2 (by decide) (by decide)
  · rw [hpB]; exact read_covered hs2 (by decide) (by decide)
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_add' (v := Nat.toB256 3232) (by decide) (by simp; omega) ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine mcpy_exit (s := 3232) (d := 3328) (l := 8) (by omega) (by simp; omega) ?_
  unfold t_135a_c24
  refine rxc_dest ?_
  refine rxc_mload (c := 3) (v := ws) ?_ rfl ?_ (by simp; omega) ?_
  · rw [show (Nat.toB256 3232).toNat = 3232 by decide]
    exact charge_covered hs2 (by decide) (by decide)
  · rw [show (Nat.toB256 3232).toNat = 3232 by decide]
    exact read_covered hs2 (by decide) (by decide)
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_mload_ext (c := 6) (v := 0) (M' := M2') ?_ ?_ ?_ (by simp; omega) ?_
  · rw [show (Nat.toB256 3328).toNat = 3328 by decide, St.extCost_eq hs2]; decide
  · rw [show (Nat.toB256 3328).toNat = 3328 by decide, hwd]
  · rw [show (Nat.toB256 3328).toNat = 3328 by decide]
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_swap (n := 3) rfl ?_
  refine rxc_dup (n := 4) rfl (by simp; omega) ?_
  refine rxc_sub' (v := Nat.toB256 24) (by decide) (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_exp' (c := 60) (by decide) (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_add' (v := m) rfl (by simp; omega) ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_not rfl (by simp; omega) ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_and rfl (by simp; omega) ?_
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_and (b256_and_zero m) (by simp; omega) ?_
  refine rxc_or (v := ws &&& ~~~ m) (b256_zero_or _) (by simp; omega) ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_mstore (c := 3) (M' := M3) ?_ (by rw [show (Nat.toB256 3328).toNat = 3328 by decide]) ?_
  · rw [show (Nat.toB256 3328).toNat = 3328 by decide]
    exact charge_covered hs2' (by decide) (by decide)
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_swap (n := 5) rfl ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_swap (n := 5) rfl ?_
  refine rxc_and (b256_and_zero _) (by simp; omega) ?_
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_add' (v := Nat.toB256 3336) (by decide) (by simp; omega) ?_
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_dup (n := 2) rfl (by simp; omega) ?_
  refine rxc_mstore (c := 6) (M' := M4) ?_ (by rw [show (Nat.toB256 3336).toNat = 3336 by decide]) ?_
  · rw [show (Nat.toB256 3336).toNat = 3336 by decide, St.extCost_eq hs3]; decide
  refine rxc_pop ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 3264) ?_ (by rw [h40]; exact read_word hr4 64 h4_64)
    ?_ (by simp; omega) ?_
  · rw [h40]; exact charge_covered hs4 (by decide) (by decide)
  · rw [h40]; exact read_covered hs4 (by decide) (by decide)
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_sub' (v := Nat.toB256 72) (by decide) (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_add' (v := Nat.toB256 64) (by decide) (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_mstore (c := 3) (M' := M5) ?_ (by rw [show (Nat.toB256 3264).toNat = 3264 by decide]) ?_
  · rw [show (Nat.toB256 3264).toNat = 3264 by decide]
    exact charge_covered hs4 (by decide) (by decide)
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_add' (v := Nat.toB256 3360) (by decide) (by simp; omega) ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_mstore (c := 3) (M' := M6) ?_ (by rw [h40]) ?_
  · rw [h40]; exact charge_covered hs5 (by decide) (by decide)
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 64) ?_
    (by rw [show (Nat.toB256 3264).toNat = 3264 by decide]; exact read_word hr6 3264 h6_len)
    ?_ (by simp; omega) ?_
  · rw [show (Nat.toB256 3264).toNat = 3264 by decide]
    exact charge_covered hs6 (by decide) (by decide)
  · rw [show (Nat.toB256 3264).toNat = 3264 by decide]
    exact read_covered hs6 (by decide) (by decide)
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_swap (n := 5) rfl ?_
  refine rxc_pop ?_
  refine rxc_swap (n := 3) rfl ?_
  refine rxc_pop ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_dup (n := 5) rfl (by simp; omega) ?_
  refine rxc_add' (v := Nat.toB256 3296) (by decide) (by simp; omega) ?_
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_pop ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  rw [t_1402_eq]
  refine hrun _ ?_
  unfold t_14b1_c24
  have h3360 : (Nat.toB256 3360).toNat = 3360 := by decide
  refine rxc_dest ?_
  refine rxc_pop ?_
  refine rxc_mload (c := 3) (v := mixIn Bytes.sha256 node count) ?_
    (by rw [h3360]; exact read_word hr' 3360 hh') ?_ (by simp; omega) ?_
  · rw [h3360]; exact charge_covered hs' (by decide) (by decide)
  · rw [h3360]; exact read_covered hs' (by decide) (by decide)
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_swap (n := 0) rfl ?_
  exact rxc_ret

end Exit

/-! ## The internal `get_deposit_root` (entry 10) -/

/-- The gas of the internal function from its entry: 19 and the count read before the loop,
the 32 iterations, and the exit. -/
def rootFnGas (sevm : Sevm) (base : Devm) (count : Nat) : Nat :=
  19 + sloadCost sevm base solCountSlot +
    rootGas sevm.currentTarget 32 0 count (afterSload sevm base solCountSlot).accessedStorageKeys +
    rootExitGas

theorem img0_word : img0.sliceD 64 32 0 = (Nat.toB256 128).toBytes := by
  rw [img0, sliceD_word_self]; rfl

theorem acc_root_eq {stor : Stor} {count : Nat} (hc : stor.get solCountSlot = Nat.toB256 count)
    (hc32 : count < 2 ^ 32) :
    mixIn Bytes.sha256 (climb Bytes.sha256 (solAcc stor).branch 32 0 count 0) count =
      Acc.root Bytes.sha256 (solAcc stor) := by
  have : (solAcc stor).count = count := by
    show (stor.get solCountSlot).toNat = count
    rw [hc, B256.toNat_toB256_of_lt (by omega)]
  rw [Acc.root, this]

theorem root_fn {sevm : Sevm} {base : Devm} {stor : Stor} {count : Nat} {ret : B256}
    {R0 : List B256} {G : Nat}
    (hstor : Devm.getStor base sevm.currentTarget = stor)
    (hcountValue : stor.get solCountSlot = Nat.toB256 count) (hc32 : count < 2 ^ 32)
    (hzero : SolZeroHashesCorrect stor) (hok : ShaOk sevm base) (hR : R0.length < 700)
    (hcd : sevm.data.length < 2 ^ 256) (hG : G + rootFnGas sevm base count + 5000 < 2 ^ 256) :
    ∃ bF MF, BaseRel base bF ∧
      bF.accessedStorageKeys = rootKeys sevm.currentTarget 32 0 count
        (afterSload sevm base solCountSlot).accessedStorageKeys ∧
      Mem.Wf MF ∧ MF.size = 3456 ∧
      (∃ img, Mem.Reads MF img ∧ img.sliceD 64 32 0 = (Nat.toB256 3360).toBytes) ∧
      SFunc.RunExact prog sevm (St base (ret :: R0) mem0 (G + rootFnGas sevm base count))
        t_10c7_c10
        (.returned (St bF (Acc.root Bytes.sha256 (solAcc stor) :: R0) MF G)) := by
  set b1 := afterSload sevm base solCountSlot with hb1
  have h20 : Bytes.toB256 [0x20] = solCountSlot := by decide
  have hrel1 := baseRel_afterSload sevm base solCountSlot
  have hstor1 : Devm.getStor b1 sevm.currentTarget = stor := by rw [hrel1.stor, hstor]
  have hcnt : base.getStorVal sevm.currentTarget solCountSlot = Nat.toB256 count := by
    show (Devm.getStor base sevm.currentTarget).get solCountSlot = _
    rw [hstor, hcountValue]
  have hin : (⟨sevm.currentTarget, solCountSlot⟩ : Adr × B256) ∈ b1.accessedStorageKeys := by
    rw [hb1, afterSload_accessedStorageKeys]
    unfold sloadAccessedStorageKeys
    split
    · assumption
    · exact Std.HashSet.mem_insert.mpr (Or.inl (by simp))
  have hexit : ∀ devm, RootInv sevm b1 stor count b1.accessedStorageKeys
      (Bytes.toB256 [0x00] :: ret :: R0) (G + rootExitGas) 32 devm →
      ∃ r, SFunc.RunExactCut prog sevm [24] devm t_10d1_c24 r ∧ (∀ d, r ≠ .at 24 d) ∧
        (fun r => ∃ bF MF, r = .done (.returned (St bF
        (mixIn Bytes.sha256 (climb Bytes.sha256 (solAcc stor).branch 32 0 count 0) count :: R0)
          MF G)) ∧ BaseRel b1 bF ∧
        bF.accessedStorageKeys = rootKeys sevm.currentTarget 32 0 count b1.accessedStorageKeys ∧
        Mem.Wf MF ∧ MF.size = 3456 ∧
        (∃ img, Mem.Reads MF img ∧ img.sliceD 64 32 0 = (Nat.toB256 3360).toBytes)) r := by
    intro devm ⟨b, M, hdevm, hrel, hkeys, hwf, hs, ⟨img, hr, hfp⟩, hGi⟩
    have hdiv : count / 2 ^ 32 = 0 := Nat.div_eq_of_lt hc32
    rw [hdiv] at hdevm
    simp only [Nat.sub_self, rootGas, Nat.add_zero] at hdevm
    subst hdevm
    have hs' : M.size = 3296 := by rw [hs]; rfl
    have hfp' : img.sliceD 64 32 0 = (Nat.toB256 3200).toBytes := by rw [hfp]; rfl
    have hcb : b.getStorVal sevm.currentTarget solCountSlot = Nat.toB256 count := by
      rw [hrel.getStorVal, hrel1.getStorVal, hcnt]
    have hwb : (⟨sevm.currentTarget, solCountSlot⟩ : Adr × B256) ∈ b.accessedStorageKeys := by
      rw [hkeys]; exact mem_rootKeys _ _ _ _ hin
    obtain ⟨bF, MF, hrelF, hkeysF, hwfF, hsF, hfpF, hrunF⟩ :=
      root_exit (sevm := sevm) (G := G) (b := b)
        (node := climb Bytes.sha256 (solAcc stor).branch 32 0 count 0)
        (rv := Bytes.toB256 [0x00]) (ret := ret) (R0 := R0) hwf hr hs' hfp' (by omega)
        ((hok.of_rel hrel1).of_rel hrel) (by unfold rootFnGas at hG; omega) hcd hcb hc32 hwb
    exact ⟨_, hrunF, by simp, bF, MF, rfl, hrel.trans hrelF, by rw [hkeysF, hkeys], hwfF, hsF,
      hfpF⟩
  obtain ⟨r, hrun, bF, MF, rfl, hrelF, hkeysF, hwfF, hsF, hfpF⟩ :=
    root_loop (sevm := sevm) (base := b1) (stor := stor) (count := count)
      (R := Bytes.toB256 [0x00] :: ret :: R0) (Gx := G + rootExitGas)
      (Q := fun r => ∃ bF MF, r = .done (.returned (St bF
        (mixIn Bytes.sha256 (climb Bytes.sha256 (solAcc stor).branch 32 0 count 0) count :: R0)
          MF G)) ∧ BaseRel b1 bF ∧
        bF.accessedStorageKeys = rootKeys sevm.currentTarget 32 0 count b1.accessedStorageKeys ∧
        Mem.Wf MF ∧ MF.size = 3456 ∧
        (∃ img, Mem.Reads MF img ∧ img.sliceD 64 32 0 = (Nat.toB256 3360).toBytes))
      hstor1 hzero hc32 (hok.of_rel hrel1) (by simp; omega) (by unfold rootFnGas at hG; rw [← hb1] at hG; omega)
      hexit wf_mem0 reads_mem0 mem0_size img0_word
  · refine ⟨bF, MF, hrel1.trans hrelF, hkeysF, hwfF, hsF, hfpF, ?_⟩
    rw [← acc_root_eq hcountValue hc32]
    unfold rootFnGas
    rw [show G + (19 + sloadCost sevm base solCountSlot + rootGas sevm.currentTarget 32 0 count
        (afterSload sevm base solCountSlot).accessedStorageKeys + rootExitGas) =
      G + rootExitGas + rootGas sevm.currentTarget 32 0 count
        (afterSload sevm base solCountSlot).accessedStorageKeys + 15
        + sloadCost sevm base solCountSlot + 4 by omega]
    unfold t_10c7_c10
    refine rx_dest ?_
    refine rx_push h20 (by simp; omega) ?_
    refine rx_sload_sel hok.fork (by simp; omega) ?_
    rw [hcnt]
    refine rx_push (w := 0) (by decide) (by simp; omega) ?_
    refine rx_swap (n := 0) rfl ?_
    refine rx_dup (n := 1) rfl (by simp; omega) ?_
    refine rx_swap (n := 0) rfl ?_
    refine rx_dup (n := 1) rfl (by simp; omega) ?_
    rw [t_10d1_c10_eq, SFunc.runExact_iff_runExactCut_nil]
    exact hrun

/-! ## The wrapper (entry 34) and the dispatcher -/

/-- The `get_deposit_root` wrapper: the `nonpayable` guard, the call into entry 10, and the
return of the root word stored at the free pointer.  82 gas of its own. -/
theorem root_wrapper {sevm : Sevm} {base : Devm} {stor : Stor} {count : Nat} {sel : B256}
    {G : Nat}
    (hval : sevm.value = 0)
    (hstor : Devm.getStor base sevm.currentTarget = stor)
    (hcountValue : stor.get solCountSlot = Nat.toB256 count) (hc32 : count < 2 ^ 32)
    (hzero : SolZeroHashesCorrect stor) (hok : ShaOk sevm base)
    (hcd : sevm.data.length < 2 ^ 256) (hG : G + rootFnGas sevm base count + 6000 < 2 ^ 256) :
    ∃ bF MF, BaseRel base bF ∧
      bF.accessedStorageKeys = rootKeys sevm.currentTarget 32 0 count
        (afterSload sevm base solCountSlot).accessedStorageKeys ∧
      SFunc.RunExact prog sevm (St base [sel] mem0 (G + (82 + rootFnGas sevm base count)))
        t_0244_c34
        (.halted ((St bF [sel] MF G).withOutput (Acc.root Bytes.sha256 (solAcc stor)).toBytes)) := by
  set root := Acc.root Bytes.sha256 (solAcc stor) with hroot
  obtain ⟨bF, MF, hrelF, hkeysF, hwfF, hsF, ⟨img, hr, hfp⟩, hfn⟩ :=
    root_fn (sevm := sevm) (base := base) (stor := stor) (count := count)
      (ret := Bytes.toB256 [0x02, 0x59]) (R0 := [sel]) (G := G + 43) hstor hcountValue hc32 hzero
      hok (by simp) hcd (by omega)
  set MF' := MF.write 3360 root.toBytes with hMF'
  have hsF' : MF'.size = 3456 := by
    rw [hMF', Mem.size_write_word_aligned (by rw [hsF]) (by decide), hsF]; decide
  have hr' := hr.write hwfF 3360 root.toBytes
  have hfp' : (Bytes.writeAt img 3360 root.toBytes).sliceD 64 32 0 =
      (Nat.toB256 3360).toBytes := by
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), hfp]
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := by decide
  have h3360 : (Nat.toB256 3360).toNat = 3360 := by decide
  refine ⟨bF, MF', hrelF, hkeysF, ?_⟩
  rw [show G + (82 + rootFnGas sevm base count) = G + 43 + rootFnGas sevm base count + 39 by
    omega]
  unfold t_0244_c34
  refine rx_dest ?_
  refine rx_callvalue (by simp) ?_
  refine rx_dup1 (by simp) ?_
  refine rx_iszero (v := 1) (by simp [B256.eqCheck, hval]) (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_0250_c34
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_push rfl (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_callRet (j := 10) rfl hfn ?_
  unfold t_0259_c34
  refine rx_dest ?_
  refine rx_push rfl (by simp) ?_
  refine rx_dup1 (by simp) ?_
  refine rx_mload (c := 3) (v := Nat.toB256 3360) ?_ (by rw [h40]; exact read_word hr 64 hfp) ?_
    (by simp) ?_
  · rw [h40]; exact charge_covered hsF (by decide) (by decide)
  · rw [h40]; exact read_covered hsF (by decide) (by decide)
  refine rx_swap2 ?_
  refine rx_dup3 (by simp) ?_
  refine rx_mstore (c := 3) (M' := MF') ?_ (by rw [h3360]) ?_
  · rw [h3360]; exact charge_covered hsF (by decide) (by decide)
  refine rx_mload (c := 3) (v := Nat.toB256 3360) ?_ (by rw [h40]; exact read_word hr' 64 hfp') ?_
    (by simp) ?_
  · rw [h40]; exact charge_covered hsF' (by decide) (by decide)
  · rw [h40]; exact read_covered hsF' (by decide) (by decide)
  refine rx_swap1 ?_
  refine rx_dup2 (by simp) ?_
  refine rx_swap1 ?_
  refine rx_sub' (v := 0) (by decide) (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_add' (v := 32) (by decide) (by simp) ?_
  refine rx_swap1 ?_
  have hret := rx_return (fs := prog) (sevm := sevm) (b := bF) (S := [sel]) (M := MF') (G := G)
    (i := Nat.toB256 3360) (sz := 32) (out := root.toBytes) ?_ ?_
  · have hpost : ((St bF [sel] MF' G).memRead (Nat.toB256 3360).toNat (32 : B256).toNat).2 =
        St bF [sel] MF' G := by
      show (St bF [sel] MF' G).withMemory (MF'.read _ _).2 = _
      rw [h3360, show (32 : B256).toNat = 32 by decide,
        read_covered hsF' (by decide) (by decide)]
      rfl
    rw [hpost] at hret
    exact hret
  · rw [St.extCost_eq hsF', h3360, show (32 : B256).toNat = 32 by decide]; decide
  · rw [h3360, show (32 : B256).toNat = 32 by decide, hr'.read, sliceD_word_self]

/-- The dispatcher path to `get_deposit_root()` (entry 34): `mstore(0x40, 0x80)`, the
`CALLDATASIZE < 4` test, the selector, three misses and the hit.  139 gas. -/
theorem dispatch_root {sevm : Sevm} {b : Devm} {g : Nat} {o : Outcome}
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = 0xc5f2892f)
    (k : SFunc.RunExact prog sevm (St b [Sevm.selector sevm] mem0 g) t_0244_c34 o) :
    SFunc.RunExact prog sevm (St b [] Mem.empty (g + 139)) t_0000_c0 o := by
  refine rx_push rfl (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_mstore (c := 12) (M' := mem0) ?_ (by rw [show (Bytes.toB256 [0x40]).toNat = 64 by decide]; rfl) ?_
  · rw [St.extCost_eq (n := 0) rfl]; decide
  refine rx_push rfl (by simp) ?_
  refine rx_calldatasize (by simp) ?_
  refine rx_lt (v := 0) ?_ (by simp) ?_
  · rw [B256.ltCheck, ite_eq_right_iff]
    intro h
    have h1 := B256.toNat_lt_toNat h
    rw [B256.toNat_toB256_of_lt h_len'] at h1
    have h4 : (Bytes.toB256 [0x04]).toNat = 4 := by decide
    omega
  refine rx_push rfl (by simp) ?_
  refine rx_branch_zero ?_
  refine rx_push rfl (by simp) ?_
  refine rx_calldataload (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_shr (v := Sevm.selector sevm) ?_ (by simp) ?_
  · rw [show (Bytes.toB256 [0xe0]).toNat = 224 by decide,
      show Bytes.toB256 [0x00] = 0 by decide]
    rfl
  refine cmp_miss (by rw [hsel]; decide) ?_
  refine cmp_miss (by rw [hsel]; decide) ?_
  refine cmp_miss (by rw [hsel]; decide) ?_
  exact cmp_hit (j := 34) (by rw [hsel]; decide) rfl k

/-! ## `get_deposit_root()` -/

/-- Gas of a `get_deposit_root()` call: the dispatcher (139), the wrapper (82) and the internal
function (`rootFnGas`: 19, the count read, the 32 iterations of `rootGas` and the exit
`rootExitGas`). -/
def rootViewGas (sevm : Sevm) (base : Devm) (count : Nat) : Nat :=
  139 + (82 + rootFnGas sevm base count)

/-- **`get_deposit_root()` on the deployed bytes: a gas-exact lifted run returning the model
root.**  The counterpart of the Blanc port's `getDepositRoot_zero_runCompiled_noRawSstore`:
the same premises (calldata at least a selector and `CALLDATASIZE` a word, zero value, the
selector, a covered fork, the count below `2^32`, the constructor's zero-hash table, the
undelegated and warm precompile 2, `isPrecomp 2`, a nonzero depth, a gas bound) with the
deployed layout's slots (`solCountSlot`, `SolZeroHashesCorrect`).  The output is
`(Acc.root sha256 (solAcc stor)).toBytes`; storage, code, warm accounts, logs and error are
unchanged, and the warm storage keys are the count slot and the 32 slots the loop reads
(`rootKeys`).  Compose with the certificate's `exec_of_runExact` for the `Exec` statement. -/
theorem get_deposit_root_runExact (sevm : Sevm) (base : Devm) (stor : Stor) (count G : Nat)
    (hdataLength : 4 ≤ sevm.data.length)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = Blanc.BeaconDeposit.getDepositRootSelector)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hstor : Devm.getStor base sevm.currentTarget = stor)
    (hcountValue : stor.get solCountSlot = Nat.toB256 count)
    (hcount : count < 2 ^ 32)
    (hzero : SolZeroHashesCorrect stor)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound : G + rootViewGas sevm base count + 6000 < 2 ^ 256) :
    ∃ post, SProg.RunExact prog sevm
        (base.setMach ⟨[], Mem.empty, G + rootViewGas sevm base count, base.stateGas⟩) post ∧
      post.stack = [Sevm.selector sevm] ∧
      post.gasLeft = G ∧
      post.output = (Acc.root Bytes.sha256 (solAcc stor)).toBytes ∧
      (∀ a, Devm.getStor post a = Devm.getStor base a) ∧
      (∀ a, post.getCode a = base.getCode a) ∧
      post.accessedAddresses = base.accessedAddresses ∧
      post.accessedStorageKeys = rootKeys sevm.currentTarget 32 0 count
        (afterSload sevm base solCountSlot).accessedStorageKeys ∧
      post.logs = base.logs ∧
      post.error = base.error := by
  have hsel : Sevm.selector sevm = 0xc5f2892f :=
    hselector.trans Blanc.BeaconDeposit.getDepositRootSelector_eq
  obtain ⟨bF, MF, hrel, hkeys, hrun⟩ := root_wrapper (sevm := sevm) (base := base) (stor := stor)
    (count := count) (sel := Sevm.selector sevm) (G := G) hvalue hstor hcountValue hcount hzero
    ⟨hnodeleg, hwarm, hpre, hfork, hdepth⟩ hdataBound (by unfold rootViewGas at hbound; omega)
  have hd := dispatch_root (b := base) hdataLength hdataBound hsel hrun
  rw [show G + (82 + rootFnGas sevm base count) + 139 = G + rootViewGas sevm base count by
    unfold rootViewGas; omega] at hd
  exact ⟨_, ⟨_, rfl, hd⟩, rfl, rfl, rfl, fun a => hrel.stor a, fun a => hrel.code a, hrel.addrs,
    hkeys, hrel.logs, hrel.error⟩

end Blanc.Lift.BeaconDeposit
