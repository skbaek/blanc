import Blanc.Lift.BeaconDeposit.LittleEndian
import Blanc.BeaconDepositEncoding

/-!
# `get_deposit_count()` on the deployed beacon deposit contract: liveness with exact gas

The walk of the deployed runtime's `get_deposit_count` path over the lifted program `prog`:

* the dispatcher (entry 0): free pointer `0x80`, the `CALLDATASIZE < 4` test, the selector
  (`calldataload(0) >> 224`), two misses and the hit on `0x621fd130` (117 gas);
* the wrapper (entry 33): the `nonpayable` guard and the call into the getter (39 gas);
* the getter (entry 8): `SLOAD 0x20` and the call into `to_little_endian_64` (entry 25,
  `to_little_endian_64_run`), 38 gas and the `SLOAD` charge around the callee's 830;
* the ABI encoding back in the wrapper: head word `0x20`, length `8`, the payload copied by the
  solc copy loop (first pass inlined in entry 33, `copy_step`; loop entry 9, `copy_loop` with the
  `SFunc.RunExactCut.iterate` construction), the padding clean-up and `RETURN` (390 gas).

In all 1514 gas with the count slot warm and 3514 cold, and the output is
`abiDynamicBytesReturn (le64 word.toNat)`, the counterpart of the Blanc port's
`getDepositCount_warm_runCompiled_noRawSstore`.  The statements are over `SProg.RunExact prog`,
to be composed with the certificate's `exec_of_runExact` once it is checked.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

/-! ## Memory images -/

/-- After the dispatcher's `mstore(0x40, 0x80)`. -/
def mem0 : Mem := Mem.empty.write 64 (Bytes.toB256 [0x80]).toBytes

/-- Its image. -/
def img0 : Bytes := Bytes.writeAt [] 64 (Bytes.toB256 [0x80]).toBytes

theorem mem0_size : mem0.size = 96 := by
  rw [mem0, Mem.size_write_word_at]; rfl

theorem wf_mem0 : Mem.Wf mem0 := Mem.wf_empty.write _ _

theorem reads_mem0 : Mem.Reads mem0 img0 := Mem.reads_empty.write Mem.wf_empty 64 _

theorem img0_fp : Bytes.toB256 (img0.sliceD 64 32 0) = Bytes.toB256 [0x80] := by
  have := Bytes.sliceD_writeAt [] (Bytes.toB256 [0x80]).toBytes 64
  rw [B256.length_toBytes] at this
  rw [img0, this, B256.toB256_toBytes]

theorem p80 : (Bytes.toB256 [0x80]).toNat = 128 := by decide

/-- The image after `to_little_endian_64`. -/
abbrev img1 (w : B256) : Bytes := leImg img0 (Bytes.toB256 [0x80]) w

/-- The image after the ABI head (`0x20`) and length (`8`) words at `0xc0` and `0xe0`. -/
def img5 (w : B256) : Bytes :=
  Bytes.writeAt (Bytes.writeAt (img1 w) 192 (Bytes.toB256 [0x20]).toBytes) 224 (8 : B256).toBytes

/-- The memory image a `get_deposit_count` call leaves: the ABI return window at `0xc0..0x120`
holds `0x20`, `8` and `le64 word` padded with zeros. -/
def countImg (w : B256) : Bytes :=
  Bytes.writeAt (img5 w) 256 (Blanc.BeaconDeposit.le64 w.toNat ++ List.replicate 24 0)

theorem sliceD_word_self (bs : Bytes) (n : Nat) (x : B256) :
    (Bytes.writeAt bs n x.toBytes).sliceD n 32 0 = x.toBytes := by
  have := Bytes.sliceD_writeAt bs x.toBytes n
  rwa [B256.length_toBytes] at this

theorem img1_fp (w : B256) : (img1 w).sliceD 64 32 0 = (Bytes.toB256 [0x80] + 64).toBytes := by
  rw [img1, leImg, p80, Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), sliceD_word_self]

theorem img1_len (w : B256) : (img1 w).sliceD 128 32 0 = (8 : B256).toBytes := by
  rw [img1, leImg, p80, Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; omega), sliceD_word_self]

theorem img5_len (w : B256) : (img5 w).sliceD 128 32 0 = (8 : B256).toBytes := by
  rw [img5, Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), img1_len]

/-- The payload word the copy loop reads: `le64 w` and the 24 bytes after it. -/
theorem img5_payload (w : B256) :
    ((img5 w).sliceD 160 32 0).take 8 = Blanc.BeaconDeposit.le64 w.toNat := by
  rw [img5, Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), img1, leImg, p80,
    show (32 : Nat) = 8 + 24 by rfl, List.sliceD_split,
    show (128 + 32 : Nat) = 160 by rfl]
  have h8 : (Blanc.BeaconDeposit.le64 w.toNat).length = 8 := rfl
  have := Bytes.sliceD_writeAt
    (Bytes.writeAt (Bytes.writeAt img0 128 (8 : B256).toBytes) 64 (Bytes.toB256 [0x80] + 64).toBytes)
    (Blanc.BeaconDeposit.le64 w.toNat) 160
  rw [h8] at this
  rw [this, List.take_left' h8]

/-- The padding clean-up's mask `not(256^(32 - 8) - 1)`: the top eight bytes. -/
def maskTop8 : B256 := ~~~(B256.bexp (Bytes.toB256 [0x01, 0x00]) 24 - Bytes.toB256 [0x01])

theorem maskTop8_eq : maskTop8 =
    ((((0xffffffffffffffff : UInt64), (0 : UInt64)) : B128), (((0 : UInt64), (0 : UInt64)) : B128)) := by
  apply B256.toNat_inj
  decide +kernel

theorem maskTop8_and (W : B256) :
    (maskTop8 &&& W).toBytes = W.toBytes.take 8 ++ List.replicate 24 0 := by
  rw [maskTop8_eq]
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := W
  have hmax : (0xffffffffffffffff : UInt64) &&& a = a := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_and, show (0xffffffffffffffff : UInt64).toNat = 2 ^ 64 - 1 from rfl,
      Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (UInt64.toNat_lt a)]
  have hz : (0 : UInt64).toBytes = List.replicate 8 0 := by decide
  change B256.toBytes (B256.and _ _) = _
  simp only [B256.and, B256.toBytes, B128.toBytes]
  change (B128.and _ _).1.toBytes ++ (B128.and _ _).2.toBytes ++
    ((B128.and _ _).1.toBytes ++ (B128.and _ _).2.toBytes) = _
  simp only [B128.and, hmax, UInt64.zero_and, hz, List.append_assoc]
  rw [List.take_left' (UInt64.length_toBytes a)]
  rfl

/-! ## The dispatcher -/

/-- The dispatcher path to `get_deposit_count()` (entry 33): `mstore(0x40, 0x80)`, the
`CALLDATASIZE < 4` test, the selector `calldataload(0) >> 224`, two misses and the hit.
117 gas. -/
theorem dispatch_count {sevm : Sevm} {b : Devm} {g : Nat} {o : Outcome}
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = 0x621fd130)
    (k : SFunc.RunExact prog sevm (St b [Sevm.selector sevm] mem0 g) t_01ba_c33 o) :
    SFunc.RunExact prog sevm (St b [] Mem.empty (g + 117)) t_0000_c0 o := by
  refine rx_push rfl (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_mstore (c := 12) (M' := mem0) ?_ (by rw [show (Bytes.toB256 [0x40]).toNat = 64 by decide]; rfl) ?_
  · rw [St.extCost_eq (n := 0) rfl]; decide
  refine rx_push rfl (by simp) ?_
  refine rx_calldatasize (by simp) ?_
  refine rx_lt (v := 0) ?_ (by simp) ?_
  · rw [B256.ltCheck, ite_eq_right]
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
  exact cmp_hit (j := 33) (by rw [hsel]; decide) rfl k

/-! ## The getter (entry 8) around `to_little_endian_64` -/

/-- The deployed layout's `deposit_count` slot. -/
abbrev countSlot : B256 := 0x20

theorem slot20 : Bytes.toB256 [0x20] = countSlot := by decide

/-- The getter with the slot's value `w` read at charge `sl`: 38 gas, the read, and
`to_little_endian_64`'s 830 (868 and the read), over `mem0`; it returns the payload pointer `0x80` over a memory
of six words reading as `img1 w`. -/
theorem count_getter {sevm : Sevm} {b b' : Devm} {g : Nat} {sel : B256} {sl : Nat} {w : B256}
    (hcd : sevm.data.length < 2 ^ 256)
    (hsload : ∀ S : List B256, ∀ M : Mem, ∀ G : Nat, ∀ f : SFunc, ∀ o : Outcome,
      S.length < 1000 →
      SFunc.RunExact prog sevm (St b' (w :: S) M G) f o →
      SFunc.RunExact prog sevm (St b (countSlot :: S) M (G + sl)) (.next (.reg .sload) f) o) :
    ∃ M', Mem.Wf M' ∧ Mem.Reads M' (img1 w) ∧ M'.size = 192 ∧
      SFunc.RunExact prog sevm (St b [Bytes.toB256 [0x01, 0xcf], sel] mem0 (g + (868 + sl)))
        t_10b5_c8 (.returned (St b' [Bytes.toB256 [0x80], sel] M' g)) := by
  obtain ⟨M', hwf', hr', hs', hrun⟩ := to_little_endian_64_run (sevm := sevm) (b := b')
    (G := g + 17) (v := w) (ret := Bytes.toB256 [0x10, 0xc2])
    (rest := [Bytes.toB256 [0x60], Bytes.toB256 [0x01, 0xcf], sel]) (by simp) wf_mem0 reads_mem0
    (by rw [mem0_size]) (by rw [mem0_size]) img0_fp (by rw [p80]) (by rw [p80]; omega)
    (by rw [p80]; decide) hcd
  rw [mem0_size, p80] at hs'
  refine ⟨M', hwf', hr', by rw [hs']; decide, ?_⟩
  rw [show g + (868 + sl) = ((g + 17 + 830) + 11) + sl + 10 by omega]
  have hgas : leGas mem0.size (Bytes.toB256 [0x80]).toNat = 830 := by
    rw [mem0_size, p80]; decide
  rw [hgas] at hrun
  refine rx_dest ?_
  refine rx_push rfl (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_push slot20 (by simp) ?_
  refine hsload _ _ _ _ _ (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_callRet (j := 25) rfl hrun ?_
  refine rx_dest ?_
  refine rx_swap1 ?_
  refine rx_pop ?_
  refine rx_swap1 ?_
  exact rx_ret

/-! ## The ABI encoding -/

/-- The exit of the copy loop at entry 9 (`N = 1` word copied from `0xa0` to `0x100`), the
padding clean-up and `RETURN`: 197 gas. -/
theorem count_exit {sevm : Sevm} {b : Devm} {g : Nat} {sel w : B256} {M : Mem}
    (hwf : Mem.Wf M) (hr : Mem.Reads M (copyImg (img5 w) 160 256 1)) (hs : M.size = 288) :
    ∃ Mf, Mem.Wf Mf ∧ Mem.Reads Mf (countImg w) ∧ Mf.size = 288 ∧
      SFunc.RunExact prog sevm
        (St b [(32 * 1).toB256, 160, 256, 8, 8, 160, 256, Bytes.toB256 [0x80] + 64,
          Bytes.toB256 [0x80] + 64, Bytes.toB256 [0x80], sel] M (g + 197)) t_0209_c9
        (.halted ((St b [sel] Mf g).withOutput
          (Blanc.BeaconDeposit.abiDynamicBytesReturn (Blanc.BeaconDeposit.le64 w.toNat)))) := by
  set V := (img5 w).sliceD 160 32 0 with hV
  have hVlen : V.length = 32 := List.length_sliceD _ _ _ _
  set W := Bytes.toB256 V with hW
  have hWb : W.toBytes = V := Bytes.toBytes_toB256_of_length hVlen
  set W' := maskTop8 &&& W with hW'
  have hW'b : W'.toBytes = Blanc.BeaconDeposit.le64 w.toNat ++ List.replicate 24 0 := by
    rw [hW', maskTop8_and, hWb, hV, img5_payload]
  have hW'len : W'.toBytes.length = 32 := B256.length_toBytes _
  set Mf := M.write 256 W'.toBytes with hMf
  have hXf : Bytes.writeAt (copyImg (img5 w) 160 256 1) 256 W'.toBytes = countImg w := by
    rw [copyImg, show 32 * 1 = 32 from rfl, ← hV, Bytes.writeAt_writeAt_same _ _ _ _
      (by rw [hVlen, hW'len]), countImg, hW'b]
  have hrf : Mem.Reads Mf (countImg w) := by rw [← hXf]; exact hr.write hwf _ _
  have hsf : Mf.size = 288 := by
    rw [hMf, Mem.size_write_word_aligned (by rw [hs]) (by decide), hs]; decide
  refine ⟨Mf, hwf.write _ _, hrf, hsf, ?_⟩
  have hsl : ∀ S : List B256, S.length ≤ 12 → S.length < 1024 := fun _ h => by omega
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_swap1 ?_
  refine rx_pop ?_
  refine rx_swap1 ?_
  refine rx_dup2 (by simp) ?_
  refine rx_add' (v := 264) (by decide) (by simp) ?_
  refine rx_swap1 ?_
  refine rx_push rfl (by simp) ?_
  refine rx_and (v := 8) (by decide) (by simp) ?_
  refine rx_dup1 (by simp) ?_
  refine rx_iszero (v := 0) (by decide) (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_branchTo_zero ?_
  -- t_021d: the padding clean-up
  refine rx_dup1 (by simp) ?_
  refine rx_dup3 (by simp) ?_
  refine rx_sub' (v := 256) (by decide) (by simp) ?_
  refine rx_dup1 (by simp) ?_
  refine rx_mload (c := 3) (v := W) ?_ ?_ ?_ (by simp) ?_
  · rw [St.extCost_eq hs, show (256 : B256).toNat = 256 by decide]; decide
  · rw [show (256 : B256).toNat = 256 by decide, hr.read, copyImg, show 32 * 1 = 32 from rfl]
    have := Bytes.sliceD_writeAt (img5 w) ((img5 w).sliceD 160 32 0) 256
    rw [List.length_sliceD] at this
    rw [this]
  · rw [show (256 : B256).toNat = 256 by decide]
    exact Mem.read_snd_eq_self (memExtSize_of_le (by rw [hs]) (by rw [hs]))
  refine rx_push rfl (by simp) ?_
  refine rx_dup (n := 3) rfl (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_sub' (v := 24) (by decide) (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_exp' (c := 60) (by decide) (by simp) ?_
  refine rx_sub (by simp) ?_
  refine rx_not (v := maskTop8) rfl (by simp) ?_
  refine rx_and rfl (by simp) ?_
  refine rx_dup2 (by simp) ?_
  refine rx_mstore (c := 3) (M' := Mf) ?_ (by rw [show (256 : B256).toNat = 256 by decide]) ?_
  · rw [St.extCost_eq hs, show (256 : B256).toNat = 256 by decide]; decide
  refine rx_push rfl (by simp) ?_
  refine rx_add' (v := 288) (by decide) (by simp) ?_
  refine rx_swap2 ?_
  refine rx_pop ?_
  -- t_0236: the return
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_swap3 ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_push rfl (by simp) ?_
  refine rx_mload (c := 3) (v := 192) ?_ ?_ ?_ (by simp) ?_
  · rw [St.extCost_eq hsf, show (Bytes.toB256 [0x40]).toNat = 64 by decide]; decide
  · rw [show (Bytes.toB256 [0x40]).toNat = 64 by decide, hrf.read, countImg,
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), img5,
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), img1_fp, B256.toB256_toBytes]
    decide
  · rw [show (Bytes.toB256 [0x40]).toNat = 64 by decide]
    exact Mem.read_snd_eq_self (memExtSize_of_le (by rw [hsf]) (by rw [hsf]; omega))
  refine rx_dup1 (by simp) ?_
  refine rx_swap2 ?_
  refine rx_sub' (v := 96) (by decide) ?_ ?_
  · simp
  refine rx_swap1 ?_
  have hret := rx_return (fs := prog) (sevm := sevm) (b := b) (S := [sel]) (M := Mf) (G := g)
    (i := 192) (sz := 96) (out := Blanc.BeaconDeposit.abiDynamicBytesReturn (Blanc.BeaconDeposit.le64 w.toNat)) ?_ ?_
  · have hread : (Mf.read (192 : B256).toNat (96 : B256).toNat).2 = Mf := by
      rw [show (192 : B256).toNat = 192 by decide, show (96 : B256).toNat = 96 by decide]
      exact Mem.read_snd_eq_self (memExtSize_of_le (by rw [hsf]) (by rw [hsf]))
    have hpost : ((St b [sel] Mf g).memRead (192 : B256).toNat (96 : B256).toNat).2 =
        St b [sel] Mf g := by
      show (St b [sel] Mf g).withMemory (Mf.read _ _).2 = _
      rw [hread]; rfl
    rw [hpost] at hret
    exact hret
  · rw [St.extCost_eq hsf, show (192 : B256).toNat = 192 by decide,
      show (96 : B256).toNat = 96 by decide]; decide
  · rw [show (192 : B256).toNat = 192 by decide, show (96 : B256).toNat = 96 by decide, hrf.read,
      show (96 : Nat) = 32 + (32 + 32) from rfl, List.sliceD_split, List.sliceD_split, countImg,
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), img5,
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), sliceD_word_self, sliceD_word_self]
    rw [show (192 + 32 + 32 : Nat) = 256 from rfl]
    have hl : (Blanc.BeaconDeposit.le64 w.toNat ++ List.replicate 24 (0 : UInt8)).length = 32 := rfl
    have key : ∀ bs : Bytes, (Bytes.writeAt bs 256
        (Blanc.BeaconDeposit.le64 w.toNat ++ List.replicate 24 0)).sliceD 256 32 0 =
        Blanc.BeaconDeposit.le64 w.toNat ++ List.replicate 24 0 := fun bs => by
      have := Bytes.sliceD_writeAt bs (Blanc.BeaconDeposit.le64 w.toNat ++ List.replicate 24 0) 256
      rwa [hl] at this
    rw [key, BeaconDeposit.abiDynamicBytesReturn_le64_eq, show Bytes.toB256 [0x20] = (32 : B256) by decide]
    simp only [List.append_assoc]

theorem t_01f1_c33_eq : t_01f1_c33 = copyLoopTree 0x02 0x09 0x01 0xf1 9 t_0209_c33 := rfl

theorem prog_9 : prog[9]? = some (copyLoopTree 0x02 0x09 0x01 0xf1 9 t_0209_c9) := rfl

/-- The copy loop's exit path only jumps to entry 1 (the shared return tail), never back to
the loop head at entry 9. -/
theorem exit_avoids : t_0209_c9.avoids [9] [1] = true := by decide

theorem exit_avoids_closed :
    ∀ j t, j ∈ [1] → prog[j]? = some t → t.avoids [9] [1] = true := by
  intro j t hj ht
  simp only [List.mem_singleton] at hj
  subst hj
  have h1 : prog[1]? = some t_0236_c1 := rfl
  rw [h1] at ht
  cases ht
  decide

/-- The wrapper after the getter returns (pc `0x01cf`): the ABI head `0x20` at the free pointer
`0xc0`, the length at `0xe0`, the one-word copy of the payload to `0x100` (its first pass
inlined here, `copy_step`; the loop at entry 9 exits at once, `copy_loop`), the padding clean-up
and `RETURN` of `0xc0..0x120`.  390 gas. -/
theorem count_tail {sevm : Sevm} {b : Devm} {g : Nat} {sel w : B256} {M : Mem}
    (hwf : Mem.Wf M) (hr : Mem.Reads M (img1 w)) (hs : M.size = 192) :
    ∃ Mf, Mem.Wf Mf ∧ Mem.Reads Mf (countImg w) ∧ Mf.size = 288 ∧
      SFunc.RunExact prog sevm (St b [Bytes.toB256 [0x80], sel] M (g + 390)) t_01cf_c33
        (.halted ((St b [sel] Mf g).withOutput
          (Blanc.BeaconDeposit.abiDynamicBytesReturn (Blanc.BeaconDeposit.le64 w.toNat)))) := by
  have hq : (Bytes.toB256 [0x80] + 64).toNat = 192 := by decide
  set M4 := M.write 192 (Bytes.toB256 [0x20]).toBytes with hM4
  set M5 := M4.write 224 (8 : B256).toBytes with hM5
  have hs4 : M4.size = 224 := by
    rw [hM4, Mem.size_write_word_aligned (by rw [hs]) (by decide), hs]; decide
  have hs5 : M5.size = 256 := by
    rw [hM5, Mem.size_write_word_aligned (by rw [hs4]) (by decide), hs4]; decide
  have hwf5 : Mem.Wf M5 := (hwf.write _ _).write _ _
  have hr4 : Mem.Reads M4 (Bytes.writeAt (img1 w) 192 (Bytes.toB256 [0x20]).toBytes) :=
    hr.write hwf _ _
  have hr5 : Mem.Reads M5 (img5 w) := hr4.write (hwf.write _ _) _ _
  -- the copy
  set R : List B256 := [8, 160, 256, Bytes.toB256 [0x80] + 64, Bytes.toB256 [0x80] + 64,
    Bytes.toB256 [0x80], sel] with hR
  have hwfC : CopyWf (160 : B256) (256 : B256) (8 : B256) R 256 1 :=
    { iter := fun j => by rw [show (8 : B256).toNat = 8 by decide]; omega
      n32 := by decide
      dst32 := by decide
      src_le := by decide
      disj := by decide
      src_lt := by decide
      dst_lt := by decide
      room := by simp [hR] }
  obtain ⟨M6, hwf6, hr6, hs6, seg⟩ := copy_step (fs := prog) (sevm := sevm) (b := b) (C := [9])
    (e0 := 0x02) (e1 := 0x09) (r0 := 0x01) (r1 := 0xf1) (k := 9) (exitT := t_0209_c33)
    (img := img5 w) (List.mem_singleton_self 9) hwfC (j := 0) (by decide) hwf5
    (hr5.writeAt_nil _) (by rw [hs5]; decide) (g + 223)
  obtain ⟨r, hrest, Mf, hwff, hrf, hsf, rfl⟩ := copy_loop (fs := prog) (sevm := sevm) (b := b)
    (C := []) prog_9 (by simp) hwfC (j0 := 1) le_rfl hwf6 hr6 hs6 (Gx := g + 197)
    (fun r => ∃ Mf, Mem.Wf Mf ∧ Mem.Reads Mf (countImg w) ∧ Mf.size = 288 ∧
      r = .done (.halted ((St b [sel] Mf g).withOutput
        (Blanc.BeaconDeposit.abiDynamicBytesReturn (Blanc.BeaconDeposit.le64 w.toNat)))))
    (fun M'' h1 h2 h3 => by
      have h2' : Mem.Reads M'' (copyImg (img5 w) 160 256 1) := h2
      obtain ⟨Mf, hwff, hrf, hsf, hrun⟩ := count_exit (sevm := sevm) (b := b) (g := g) (sel := sel)
        h1 h2' (by rw [h3]; decide)
      exact ⟨_, hrun.toCut exit_avoids_closed exit_avoids, by simp, Mf, hwff, hrf, hsf, rfl⟩)
  refine ⟨Mf, hwff, hrf, hsf, ?_⟩
  have e1 : calculateMemoryGasCost (copySize 256 (256 : B256).toNat (0 + 1)) -
      calculateMemoryGasCost (copySize 256 (256 : B256).toNat 0) = 3 := by decide
  have e2 : copyGas 256 (256 : B256).toNat 1 1 = 26 := by decide
  rw [e1] at seg
  rw [e2] at hrest
  have hall := SFunc.RunExactCut.resume prog_9 (by simp) seg hrest
  -- the head and length words, and the copy's operands
  refine rx_dest ?_
  refine rx_push rfl (by simp) ?_
  refine rx_dup1 (by simp) ?_
  refine rx_mload (c := 3) (v := Bytes.toB256 [0x80] + 64) ?_ ?_ ?_ (by simp) ?_
  · rw [St.extCost_eq hs, show (Bytes.toB256 [0x40]).toNat = 64 by decide]; decide
  · rw [show (Bytes.toB256 [0x40]).toNat = 64 by decide, hr.read, img1_fp, B256.toB256_toBytes]
  · rw [show (Bytes.toB256 [0x40]).toNat = 64 by decide]
    exact Mem.read_snd_eq_self (memExtSize_of_le (by rw [hs]) (by rw [hs]; omega))
  refine rx_push rfl (by simp) ?_
  refine rx_dup1 (by simp) ?_
  refine rx_dup3 (by simp) ?_
  refine rx_mstore (c := 6) (M' := M4) ?_ (by rw [hq]) ?_
  · rw [St.extCost_eq hs, hq]; decide
  refine rx_dup4 (by simp) ?_
  refine rx_mload (c := 3) (v := 8) ?_ ?_ ?_ (by simp) ?_
  · rw [St.extCost_eq hs4, p80]; decide
  · rw [p80, hr4.read, Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), img1_len,
      B256.toB256_toBytes]
  · rw [p80]; exact Mem.read_snd_eq_self (memExtSize_of_le (by rw [hs4]) (by rw [hs4]; omega))
  refine rx_dup2 (by simp) ?_
  refine rx_dup4 (by simp) ?_
  refine rx_add' (v := 224) (by decide) (by simp) ?_
  refine rx_mstore (c := 6) (M' := M5) ?_ (by rw [show (224 : B256).toNat = 224 by decide]) ?_
  · rw [St.extCost_eq hs4, show (224 : B256).toNat = 224 by decide]; decide
  refine rx_dup4 (by simp) ?_
  refine rx_mload (c := 3) (v := 8) ?_ ?_ ?_ (by simp) ?_
  · rw [St.extCost_eq hs5, p80]; decide
  · rw [p80, hr5.read, img5_len, B256.toB256_toBytes]
  · rw [p80]; exact Mem.read_snd_eq_self (memExtSize_of_le (by rw [hs5]) (by rw [hs5]; omega))
  refine rx_swap2 ?_
  refine rx_swap3 ?_
  refine rx_dup4 (by simp) ?_
  refine rx_swap3 ?_
  refine rx_swap1 ?_
  refine rx_dup4 (by simp) ?_
  refine rx_add' (v := 256) (by decide) (by simp) ?_
  refine rx_swap2 ?_
  refine rx_dup (n := 5) rfl (by simp) ?_
  refine rx_add' (v := 160) (by decide) (by simp) ?_
  refine rx_swap1 ?_
  refine rx_dup1 (by simp) ?_
  refine rx_dup4 (by simp) ?_
  refine rx_dup4 (by simp) ?_
  refine rx_push (w := (32 * 0).toB256) (by decide) (by simp) ?_
  rw [t_01f1_c33_eq, SFunc.runExact_iff_runExactCut_nil]
  exact hall

/-! ## The wrapper (entry 33) -/

/-- The `get_deposit_count` wrapper: the `nonpayable` guard, the call into the getter, and the
encoding.  39 gas of its own, the getter's `868 + sl`, and the encoding's 390. -/
theorem count_wrapper {sevm : Sevm} {b b' : Devm} {g : Nat} {sel : B256} {sl : Nat} {w : B256}
    (hval : sevm.value = 0) (hcd : sevm.data.length < 2 ^ 256)
    (hsload : ∀ S : List B256, ∀ M : Mem, ∀ G : Nat, ∀ f : SFunc, ∀ o : Outcome,
      S.length < 1000 →
      SFunc.RunExact prog sevm (St b' (w :: S) M G) f o →
      SFunc.RunExact prog sevm (St b (countSlot :: S) M (G + sl)) (.next (.reg .sload) f) o) :
    ∃ Mf, Mem.Wf Mf ∧ Mem.Reads Mf (countImg w) ∧ Mf.size = 288 ∧
      SFunc.RunExact prog sevm (St b [sel] mem0 (g + (1297 + sl))) t_01ba_c33
        (.halted ((St b' [sel] Mf g).withOutput
          (Blanc.BeaconDeposit.abiDynamicBytesReturn (Blanc.BeaconDeposit.le64 w.toNat)))) := by
  obtain ⟨M', hwf', hr', hs', hcall⟩ := count_getter (g := g + 390) (sel := sel) hcd hsload
  obtain ⟨Mf, hwff, hrf, hsf, htail⟩ := count_tail (sevm := sevm) (b := b') (g := g) (sel := sel)
    hwf' hr' hs'
  refine ⟨Mf, hwff, hrf, hsf, ?_⟩
  rw [show g + (1297 + sl) = ((g + 390) + (868 + sl)) + 39 by omega]
  refine rx_dest ?_
  refine rx_callvalue (by simp) ?_
  refine rx_dup1 (by simp) ?_
  refine rx_iszero (v := 1) (by simp [B256.eqCheck, hval]) (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_branch_succ (by decide) ?_
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_push rfl (by simp) ?_
  refine rx_push rfl (by simp) ?_
  exact rx_callRet (j := 8) rfl hcall htail

/-! ## `get_deposit_count()` -/

/-- Gas of a `get_deposit_count()` call with the count slot warm: dispatcher 117, wrapper 39,
getter 38 + `SLOAD` 100, `to_little_endian_64` 830 (821 and the expansion from three words to
six), encoding 390 (97 for the head and length words and the operands, 70 for the one copied
word, 26 for the loop's exit test, 197 for the clean-up and `RETURN`). -/
def countGasWarm : Nat := 1514

/-- With the slot cold: the `SLOAD` costs 2100 instead of 100. -/
def countGasCold : Nat := 3514

/-- **`get_deposit_count()` on the deployed bytes, slot warm: a gas-exact lifted run returning
`abiDynamicBytesReturn (le64 word)`.**  The counterpart of the Blanc port's
`getDepositCount_warm_runCompiled_noRawSstore`: same premises (calldata at least a selector,
`CALLDATASIZE` a word, zero value, the selector, a covered fork, the count slot warm and holding
`word`), the deployed layout's slot `0x20` in place of the port's `0x200`.  The post-state is
the pre-state with only the machine changed (world and metadata are `base`'s: no storage
write, no log) and the output set; its memory reads as `countImg word`.  Compose with the
certificate's `exec_of_runExact` for the `Exec` statement. -/
theorem get_deposit_count_warm_runExact (sevm : Sevm) (base : Devm) (word : B256) (G : Nat)
    (hdataLength : 4 ≤ sevm.data.length)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = Blanc.BeaconDeposit.getDepositCountSelector)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hwarm : (⟨sevm.currentTarget, countSlot⟩ : Adr × B256) ∈ base.accessedStorageKeys)
    (hstorage : base.getStorVal sevm.currentTarget countSlot = word) :
    ∃ Mf, Mem.Wf Mf ∧ Mem.Reads Mf (countImg word) ∧ Mf.size = 288 ∧
      SProg.RunExact prog sevm
        (base.setMach ⟨[], Mem.empty, G + countGasWarm, base.stateGas⟩)
        ((base.setMach ⟨[Sevm.selector sevm], Mf, G, base.stateGas⟩).withOutput
          (Blanc.BeaconDeposit.abiDynamicBytesReturn (Blanc.BeaconDeposit.le64 word.toNat))) := by
  have hleg : sevm.benvStat.rules.stateGas = none := hfork.rules_stateGas_none
  have hsel : Sevm.selector sevm = 0x621fd130 :=
    hselector.trans Blanc.BeaconDeposit.getDepositCountSelector_eq
  obtain ⟨Mf, hwff, hrf, hsf, hrun⟩ := count_wrapper (sevm := sevm) (b := base) (b' := base)
    (g := G) (sel := Sevm.selector sevm) (sl := 100) (w := word) hvalue hdataBound
    (fun S M G' f o hS k => by
      rw [← hstorage] at k
      exact rx_sload_warm hleg hwarm (by omega) k)
  refine ⟨Mf, hwff, hrf, hsf, _, rfl, ?_⟩
  exact dispatch_count (b := base) hdataLength hdataBound hsel hrun

/-- **`get_deposit_count()`, slot cold**: 3514 gas, and the slot's key joins the accessed set. -/
theorem get_deposit_count_cold_runExact (sevm : Sevm) (base : Devm) (word : B256) (G : Nat)
    (hdataLength : 4 ≤ sevm.data.length)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = Blanc.BeaconDeposit.getDepositCountSelector)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hcold : (⟨sevm.currentTarget, countSlot⟩ : Adr × B256) ∉ base.accessedStorageKeys)
    (hstorage : base.getStorVal sevm.currentTarget countSlot = word) :
    ∃ Mf, Mem.Wf Mf ∧ Mem.Reads Mf (countImg word) ∧ Mf.size = 288 ∧
      SProg.RunExact prog sevm
        (base.setMach ⟨[], Mem.empty, G + countGasCold, base.stateGas⟩)
        (((addAccessedStorageKey base sevm.currentTarget countSlot).setMach
          ⟨[Sevm.selector sevm], Mf, G, base.stateGas⟩).withOutput
          (Blanc.BeaconDeposit.abiDynamicBytesReturn (Blanc.BeaconDeposit.le64 word.toNat))) := by
  have hleg : sevm.benvStat.rules.stateGas = none := hfork.rules_stateGas_none
  have hsel : Sevm.selector sevm = 0x621fd130 :=
    hselector.trans Blanc.BeaconDeposit.getDepositCountSelector_eq
  obtain ⟨Mf, hwff, hrf, hsf, hrun⟩ := count_wrapper (sevm := sevm) (b := base)
    (b' := addAccessedStorageKey base sevm.currentTarget countSlot)
    (g := G) (sel := Sevm.selector sevm) (sl := 2100) (w := word) hvalue hdataBound
    (fun S M G' f o hS k => by
      rw [← hstorage] at k
      exact rx_sload_cold hleg hcold (by omega) k)
  refine ⟨Mf, hwff, hrf, hsf, _, rfl, ?_⟩
  exact dispatch_count (b := base) hdataLength hdataBound hsel hrun

end Blanc.Lift.BeaconDeposit
