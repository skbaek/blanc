import Blanc.Lift.Weth9.Jumps
import Blanc.Lift.ExactWalk
import Blanc.WethGas
import Blanc.Lift.Weth9.Words
import Blanc.Lift.Weth9.Spec

namespace Blanc.Lift.Weth9

open Jaune

theorem toNat_div' {x y : B256} (h : y ≠ 0) : (x / y).toNat = x.toNat / y.toNat := by
  show (B256.divMod x y).fst.toNat = _
  rw [B256.divMod, ite_eq_right_iff.mpr (fun h0 => absurd h0 h)]
  exact B256.toNat_toB256_of_lt
    (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (B256.toNat_lt x))

/-- solc 0.4's selector extraction, `div(calldataload(0), 2^224) & 0xffffffff`,
is `Sevm.selector`'s `>>> 224`. -/
theorem sel_extract (x : B256) :
    (Bytes.toB256 [0xff, 0xff, 0xff, 0xff] &&&
      x / Bytes.toB256 [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00]) = x >>> 224 := by
  have hP : (Bytes.toB256 [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00]).toNat = 2 ^ 224 := by decide
  have hm : (Bytes.toB256 [0xff, 0xff, 0xff, 0xff]).toNat = 2 ^ 32 - 1 := by decide
  have hP0 : Bytes.toB256 [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00] ≠ 0 := by decide
  apply B256.toNat_inj
  rw [B256.toNat_and, toNat_div' hP0, hP, hm, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]
  rcases x with ⟨⟨x3, x2⟩, lo⟩
  have h1 : B256.shiftRight ((x3, x2), lo) 224 = ((0 : B128), B128.shiftRight (x3, x2) 96) := by
    simp [B256.shiftRight]; rfl
  have h2 : B128.shiftRight (x3, x2) 96 = ((0 : UInt64), x3 >>> (32 : UInt64)) := by
    simp only [B128.shiftRight]; rfl
  change B256.toNat ((x3, x2), lo) / 2 ^ 224 % 2 ^ 32 = B256.toNat (B256.shiftRight ((x3, x2), lo) 224)
  rw [h1, h2]
  have e1 : B256.toNat ((x3, x2), lo) = B128.toNat (x3, x2) * 2 ^ 128 + lo.toNat :=
    B256.toNat_eq _
  have e2 : B128.toNat (x3, x2) = x3.toNat * 2 ^ 64 + x2.toNat := B128.toNat_eq _
  have e3 : B256.toNat ((0 : B128), ((0 : UInt64), x3 >>> (32 : UInt64))) =
      B128.toNat (0 : B128) * 2 ^ 128 + B128.toNat ((0 : UInt64), x3 >>> (32 : UInt64)) :=
    B256.toNat_eq _
  have e4 : B128.toNat ((0 : UInt64), x3 >>> (32 : UInt64)) =
      (0 : UInt64).toNat * 2 ^ 64 + (x3 >>> (32 : UInt64)).toNat := B128.toNat_eq _
  have e5 : (x3 >>> (32 : UInt64)).toNat = x3.toNat / 2 ^ 32 := by
    rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl
  have h3 := UInt64.toNat_lt x3
  have h2' := UInt64.toNat_lt x2
  have hlo := B128.toNat_lt (x := lo)
  simp only [B128.toNat_zero, UInt64.toNat_zero] at h3 h2' e3 e4
  omega

/-! ## Memory images -/

/-- After the dispatcher's `mstore(0x40, 0x60)`. -/
def memFp : Mem := Mem.empty.write 64 (0x60 : B256).toBytes

theorem memFp_size : memFp.size = 96 := by
  rw [memFp, Mem.size_write_word_at]; rfl

theorem wf_memFp : Mem.Wf memFp := Mem.wf_empty.write _ _

theorem reads_memFp : Mem.Reads memFp (Bytes.writeAt [] 64 (0x60 : B256).toBytes) :=
  Mem.reads_empty.write Mem.wf_empty 64 _

theorem sliceD_word_same (bs : Bytes) (n : Nat) (w : B256) :
    (Bytes.writeAt bs n w.toBytes).sliceD n 32 0 = w.toBytes := by
  have h := Bytes.sliceD_writeAt bs w.toBytes n
  rwa [B256.length_toBytes] at h

theorem read_snd_self {μ : Mem} {n i : Nat} (hs : μ.size = n) (h32 : n % 32 = 0)
    (hw : i + 32 ≤ n) : (μ.read i 32).2 = μ :=
  Mem.read_snd_eq_self (by rw [hs]; exact memExtSize_of_le h32 hw)

theorem read_snd_self64 {μ : Mem} {n : Nat} (hs : μ.size = n) (h32 : n % 32 = 0)
    (hw : 64 ≤ n) : (μ.read 0 64).2 = μ :=
  Mem.read_snd_eq_self (by rw [hs]; exact memExtSize_of_le h32 (by omega))

theorem size_write_in {μ : Mem} {n i : Nat} {w : B256} (hs : μ.size = n) (hw : i + 32 ≤ n) :
    (μ.write i w.toBytes).size = n := by
  rw [Mem.size_write_word_at, hs, ite_eq_left_iff.mpr (fun h => absurd hw h)]

/-- The balance-slot scratch image: `mstore(0x20, 3); mstore(0, a)` over `memFp`. -/
def memBal (a : B256) : Mem := (memFp.write 32 (3 : B256).toBytes).write 0 a.toBytes

theorem memBal_size (a : B256) : (memBal a).size = 96 :=
  size_write_in (size_write_in memFp_size (by omega)) (by omega)

theorem memBal_keccak (a : B256) :
    ((memBal a).read 0 64).1 = a.toBytes ++ (3 : B256).toBytes := by
  simpa [memBal] using Mem.read_two_word_writes_at_raw_right_first memFp 0 a 3

theorem reads_memBal (a : B256) : Mem.Reads (memBal a)
    (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt [] 64 (0x60 : B256).toBytes) 32
      (3 : B256).toBytes) 0 a.toBytes) :=
  (reads_memFp.write wf_memFp 32 _).write (wf_memFp.write _ _) 0 _

theorem wf_memBal (a : B256) : Mem.Wf (memBal a) := (wf_memFp.write _ _).write _ _

theorem memBal_fp (a : B256) : ((memBal a).read 64 32).1 = (0x60 : B256).toBytes := by
  rw [(reads_memBal a).read, Bytes.readWord_writeAt_of_disjoint _ _ _ _ (.inr (by omega)),
    Bytes.readWord_writeAt_of_disjoint _ _ _ _ (.inr (by omega)), sliceD_word_same]

theorem memFp_fp : (memFp.read 64 32).1 = (0x60 : B256).toBytes := by
  rw [reads_memFp.read, sliceD_word_same]

/-- The return image: the answer word at the free-memory pointer `0x60`. -/
def memOut (μ : Mem) (v : B256) : Mem := μ.write 96 v.toBytes

theorem memOut_size {μ : Mem} (hs : μ.size = 96) (v : B256) : (memOut μ v).size = 128 := by
  rw [memOut, Mem.size_write_word_at, hs]; rfl

theorem memOut_fp {μ : Mem} {bs : Bytes} (hwf : Mem.Wf μ) (hr : Mem.Reads μ bs)
    (hfp : (μ.read 64 32).1 = (0x60 : B256).toBytes) (v : B256) :
    ((memOut μ v).read 64 32).1 = (0x60 : B256).toBytes := by
  rw [memOut, (hr.write hwf 96 v.toBytes).read, Bytes.readWord_writeAt_of_disjoint _ _ _ _
    (.inl (by omega)), ← hr.read, hfp]

theorem memOut_val {μ : Mem} {bs : Bytes} (hwf : Mem.Wf μ) (hr : Mem.Reads μ bs) (v : B256) :
    ((memOut μ v).read 96 32).1 = v.toBytes := by
  rw [memOut, (hr.write hwf 96 v.toBytes).read, sliceD_word_same]

open Blanc.Lift in
/-- One solc dispatcher comparison that does not match: `DUP1 PUSH4 c EQ PUSH2 d
JUMPI`, 22 gas. -/
theorem cmp_miss {sevm : Sevm} {b : Devm} {M : Mem} {g : Nat} {o : Outcome} {sel : B256}
    {c0 c1 c2 c3 d0 d1 : UInt8} {l1 l2} {nxt : SFunc} {j : Nat}
    (hne : Bytes.toB256 [c0, c1, c2, c3] ≠ sel)
    (k : SFunc.RunExact prog sevm (St b [sel] M g) nxt o) :
    SFunc.RunExact prog sevm (St b [sel] M (g + 22))
      (.next (.reg (.dup 0)) (.next (.push [c0, c1, c2, c3] l1) (.next (.reg .eq)
        (.next (.push [d0, d1] l2) (.branchTo nxt j))))) o := by
  refine rx_dup1 (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_eq (v := 0) ?_ (by simp) ?_
  · simp [B256.eqCheck, hne]
  refine rx_push rfl (by simp) ?_
  exact rx_branchTo_zero k

open Blanc.Lift in
/-- One solc dispatcher comparison that matches, jumping to entry `j`. -/
theorem cmp_hit {sevm : Sevm} {b : Devm} {M : Mem} {g : Nat} {o : Outcome} {sel : B256}
    {c0 c1 c2 c3 d0 d1 : UInt8} {l1 l2} {nxt tgt : SFunc} {j : Nat}
    (heq : Bytes.toB256 [c0, c1, c2, c3] = sel) (hj : prog[j]? = some tgt)
    (k : SFunc.RunExact prog sevm (St b [sel] M g) tgt o) :
    SFunc.RunExact prog sevm (St b [sel] M (g + 22))
      (.next (.reg (.dup 0)) (.next (.push [c0, c1, c2, c3] l1) (.next (.reg .eq)
        (.next (.push [d0, d1] l2) (.branchTo nxt j))))) o := by
  refine rx_dup1 (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_eq (v := 1) ?_ (by simp) ?_
  · simp [B256.eqCheck, heq]
  refine rx_push rfl (by simp) ?_
  exact rx_branchTo_succ (by decide) hj k

open Blanc.Lift in
/-- The dispatcher up to its first selector comparison (`name()`): the
free-memory pointer, the `CALLDATASIZE < 4` fallback test, and the selector
extraction.  84 gas. -/
theorem dispatch_head {sevm : Sevm} {b : Devm} {g : Nat} {o : Outcome}
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (hname : Bytes.toB256 [0x06, 0xfd, 0xde, 0x03] ≠ Sevm.selector sevm)
    (k : SFunc.RunExact prog sevm (St b [Sevm.selector sevm] memFp g) t_0041_c0 o) :
    SFunc.RunExact prog sevm (St b [] Mem.empty (g + 84)) t_0000_c0 o := by
  refine rx_push (w := 0x60) (by decide) (by simp) ?_
  refine rx_push (w := 0x40) (by decide) (by simp) ?_
  refine rx_mstore (c := 12) (M' := memFp) ?_ rfl ?_
  · rw [St.extCost_eq (n := 0) rfl]; decide
  refine rx_push (w := 4) (by decide) (by simp) ?_
  refine rx_calldatasize (by simp) ?_
  refine rx_lt (v := 0) ?_ (by simp) ?_
  · rw [B256.ltCheck, if_neg]
    intro h
    have h1 := B256.toNat_lt_toNat h
    rw [B256.toNat_toB256_of_lt h_len'] at h1
    have h4 : (4 : B256).toNat = 4 := rfl
    omega
  refine rx_push rfl (by simp) ?_
  refine rx_branch_zero ?_
  refine rx_push (w := 0) (by decide) (by simp) ?_
  refine rx_calldataload (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_swap1 ?_
  refine rx_div rfl (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_and (sel_extract _) (by simp) ?_
  exact cmp_miss hname k

/-! ## `balanceOf(address)` -/

open Blanc.Lift in
/-- The mapping getter at 0xb18 up to its `SLOAD`: `keccak(a ‖ 3)`. 80 gas. -/
theorem bal_callee_pre {sevm : Sevm} {b : Devm} {g : Nat} {o : Outcome} {a r : B256}
    {S : List B256} (hroom : S.length < 1000)
    (k : SFunc.RunExact prog sevm (St b (mapSlot a 3 :: r :: S) (memBal a) g)
      (.next (.reg .sload) (.next (.reg (.dup 1)) .ret)) o) :
    SFunc.RunExact prog sevm (St b (a :: r :: S) memFp (g + 80)) t_0b18_c6 o := by
  refine rx_dest ?_
  refine rx_push (w := 3) (by decide) (by simp; omega) ?_
  refine rx_push (w := 32) (by decide) (by simp; omega) ?_
  refine rx_mstore (c := 3) (M' := memFp.write 32 (3 : B256).toBytes) ?_ rfl ?_
  · rw [St.extCost_eq memFp_size]; decide
  refine rx_dup1 (by simp; omega) ?_
  refine rx_push (w := 0) (by decide) (by simp; omega) ?_
  refine rx_mstore (c := 3) (M' := memBal a) ?_ rfl ?_
  · rw [St.extCost_eq (size_write_in memFp_size (by omega))]; decide
  refine rx_push (w := 64) (by decide) (by simp; omega) ?_
  refine rx_push (w := 0) (by decide) (by simp; omega) ?_
  refine rx_keccak (c := 42) (v := mapSlot a 3) ?_ ?_ ?_ (by simp; omega) ?_
  · rw [St.extCost_eq (memBal_size a)]; decide
  · show Bytes.keccak ((memBal a).read 0 64).1 = _
    rw [memBal_keccak]; rfl
  · exact read_snd_self64 (memBal_size a) (by decide) (by decide)
  refine rx_push (w := 0) (by decide) (by simp; omega) ?_
  refine rx_swap2 ?_
  refine rx_pop ?_
  refine rx_swap1 ?_
  exact rx_pop k

open Blanc.Lift in
theorem bal_callee_cold {sevm : Sevm} {b : Devm} {g : Nat} {a r : B256} {S : List B256}
    (hroom : S.length < 1000) (hlegacy : sevm.benvStat.rules.stateGas = none)
    (hcold : (⟨sevm.currentTarget, mapSlot a 3⟩ : Adr × B256) ∉ b.accessedStorageKeys) :
    SFunc.RunExact prog sevm (St b (a :: r :: S) memFp (g + 2191)) t_0b18_c6
      (.returned (St (addAccessedStorageKey b sevm.currentTarget (mapSlot a 3))
        (b.getStorVal sevm.currentTarget (mapSlot a 3) :: r :: S) (memBal a) g)) :=
  bal_callee_pre hroom (rx_sload_cold hlegacy hcold (by simp; omega)
    (rx_dup2 (by simp; omega) rx_ret))

open Blanc.Lift in
theorem bal_callee_warm {sevm : Sevm} {b : Devm} {g : Nat} {a r : B256} {S : List B256}
    (hroom : S.length < 1000) (hlegacy : sevm.benvStat.rules.stateGas = none)
    (hwarm : (⟨sevm.currentTarget, mapSlot a 3⟩ : Adr × B256) ∈ b.accessedStorageKeys) :
    SFunc.RunExact prog sevm (St b (a :: r :: S) memFp (g + 191)) t_0b18_c6
      (.returned (St b (b.getStorVal sevm.currentTarget (mapSlot a 3) :: r :: S) (memBal a) g)) :=
  bal_callee_pre hroom (rx_sload_warm hlegacy hwarm (by simp; omega)
    (rx_dup2 (by simp; omega) rx_ret))

open Blanc.Lift in
/-- The ABI-encoding tail shared by the one-word views: write the answer at the
free-memory pointer (`0x60`, one word of expansion) and return it.  53 gas. -/
theorem word_tail {sevm : Sevm} {b : Devm} {g : Nat} {v r sel : B256} {μ : Mem} {bs : Bytes}
    (hs : μ.size = 96) (hwf : Mem.Wf μ) (hr : Mem.Reads μ bs)
    (hfp : (μ.read 64 32).1 = (0x60 : B256).toBytes) :
    ∃ post, SFunc.RunExact prog sevm (St b [v, r, sel] μ (g + 53)) t_02cc_c22 (.halted post) ∧
      post.gasLeft = g ∧ post.output = v.toBytes := by
  refine ⟨?post, ?run, ?gas, ?out⟩
  case run =>
    refine rx_dest ?_
    refine rx_push (w := 64) (by decide) (by simp) ?_
    refine rx_mload (c := 3) (v := 0x60) ?_ ?_ (read_snd_self hs (by decide) (by decide))
      (by simp) ?_
    · rw [St.extCost_eq hs]; decide
    · show Bytes.toB256 (μ.read 64 32).1 = _
      rw [hfp, B256.toB256_toBytes]
    refine rx_dup1 (by simp) ?_
    refine rx_dup3 (by simp) ?_
    refine rx_dup2 (by simp) ?_
    refine rx_mstore (c := 6) (M' := memOut μ v) ?_ rfl ?_
    · rw [St.extCost_eq hs]; decide
    refine rx_push (w := 32) (by decide) (by simp) ?_
    refine rx_add (by simp) ?_
    refine rx_swap2 ?_
    refine rx_pop ?_
    refine rx_pop ?_
    refine rx_push (w := 64) (by decide) (by simp) ?_
    refine rx_mload (c := 3) (v := 0x60) ?_ ?_
      (read_snd_self (memOut_size hs v) (by decide) (by decide)) (by simp) ?_
    · rw [St.extCost_eq (memOut_size hs v)]; decide
    · show Bytes.toB256 ((memOut μ v).read 64 32).1 = _
      rw [memOut_fp hwf hr hfp, B256.toB256_toBytes]
    refine rx_dup1 (by simp) ?_
    refine rx_swap2 ?_
    refine rx_sub (by simp) ?_
    refine rx_swap1 ?_
    refine rx_return (out := v.toBytes) ?_ ?_
    · rw [St.extCost_eq (memOut_size hs v)]; decide
    · have h32 : ((32 : B256) + 0x60 - 0x60).toNat = 32 := by decide
      rw [h32]
      exact memOut_val hwf hr v
  case gas => rfl
  case out => rfl

open Blanc.Lift in
/-- The `balanceOf` wrapper at 0x295: the `nonpayable` guard, the argument decode
(`calldataload(4) & (2^160 - 1)`) and the call into the getter; 74 gas before the
callee, and `word_tail`'s 53 after it. -/
theorem bal_entry {sevm : Sevm} {b b' : Devm} {g G : Nat} {sel v : B256} {μ : Mem} {bs : Bytes}
    (hval : sevm.value = 0)
    (hcall : SFunc.RunExact prog sevm
      (St b [(Sevm.dataWord sevm 4).toAdr.toB256, Bytes.toB256 [0x02, 0xcc], sel] memFp G)
      t_0b18_c6 (.returned (St b' [v, Bytes.toB256 [0x02, 0xcc], sel] μ (g + 53))))
    (hs : μ.size = 96) (hwf : Mem.Wf μ) (hr : Mem.Reads μ bs)
    (hfp : (μ.read 64 32).1 = (0x60 : B256).toBytes) :
    ∃ post, SFunc.RunExact prog sevm (St b [sel] memFp (G + 74)) t_0295_c22 (.halted post) ∧
      post.gasLeft = g ∧ post.output = v.toBytes := by
  obtain ⟨post, hrun, hg, ho⟩ :=
    word_tail (sevm := sevm) (b := b') (g := g) (v := v) (r := Bytes.toB256 [0x02, 0xcc])
      (sel := sel) hs hwf hr hfp
  refine ⟨post, ?_, hg, ho⟩
  refine rx_dest ?_
  refine rx_callvalue (by simp) ?_
  refine rx_iszero (v := 1) (by simp [B256.eqCheck, hval]) (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_branch_succ (by decide) ?_
  refine rx_dest ?_
  refine rx_push rfl (by simp) ?_
  refine rx_push (w := 4) (by decide) (by simp) ?_
  refine rx_dup1 (by simp) ?_
  refine rx_dup1 (by simp) ?_
  refine rx_calldataload (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_and (ff20_and_word _) (by simp) ?_
  refine rx_swap1 ?_
  refine rx_push (w := 32) (by decide) (by simp) ?_
  refine rx_add (by simp) ?_
  refine rx_swap1 ?_
  refine rx_swap2 ?_
  refine rx_swap1 ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_push rfl (by simp) ?_
  exact rx_callRet (j := 6) rfl hcall hrun

set_option maxRecDepth 1000 in
theorem boSel_eq : Blanc.boSel = 0x70a08231 := by decide

set_option maxRecDepth 1000 in
theorem dcSel_eq : Blanc.dcSel = 0x313ce567 := by decide

open Blanc.Lift in
/-- The dispatcher path to `balanceOf(address)`: five non-matching comparisons,
then the match that jumps to entry 22.  216 gas in all. -/
theorem dispatch_balanceOf {sevm : Sevm} {b : Devm} {g : Nat} {o : Outcome}
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = 0x70a08231)
    (k : SFunc.RunExact prog sevm (St b [Sevm.selector sevm] memFp g) t_0295_c22 o) :
    SFunc.RunExact prog sevm (St b [] Mem.empty (g + 216)) t_0000_c0 o := by
  refine dispatch_head h_len h_len' (by rw [hsel]; decide) ?_
  refine cmp_miss (by rw [hsel]; decide) ?_
  refine cmp_miss (by rw [hsel]; decide) ?_
  refine cmp_miss (by rw [hsel]; decide) ?_
  refine cmp_miss (by rw [hsel]; decide) ?_
  refine cmp_miss (by rw [hsel]; decide) ?_
  exact cmp_hit (j := 22) (by rw [hsel]; decide) rfl k

open Blanc.Lift in
/-- `pre` as an `St` state. -/
theorem pre_eq_St {pre : Devm} {g c : Nat} (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty) (hg : g + c = pre.gasLeft) :
    St pre [] Mem.empty (g + c) = pre := by
  rw [hg]; exact (St.self h_stack h_mem).symm

/-! ## `decimals()`

WETH9 stores `decimals` as a `uint8` packed at the bottom of slot 2, so unlike
Blanc-WETH (which returns the constant `0x12`) the call reads storage:
`sload(2) / 256^0 & 0xff`. -/

theorem bexp_256_0 : B256.bexp (Bytes.toB256 [0x01, 0x00]) 0 = 1 := by
  unfold B256.bexp
  rw [show (0 : B256).toNat = 0 from rfl]
  simp [Nat.powMod, Nat.powMod.go]
  rfl

theorem div_one' (s : B256) : s / 1 = s := by
  apply B256.toNat_inj
  rw [toNat_div' (by decide), show (1 : B256).toNat = 1 from rfl, Nat.div_one]

open Blanc.Lift in
/-- The `decimals` getter at 0xb05 up to its `SLOAD` of slot 2: 7 gas. -/
theorem dec_callee_pre {sevm : Sevm} {b : Devm} {g : Nat} {o : Outcome} {r : B256}
    {S : List B256} {M : Mem} (hroom : S.length < 1000)
    (k : SFunc.RunExact prog sevm (St b (2 :: 0 :: r :: S) M g)
      (.next (.reg .sload) (.next (.reg (.swap 0)) (.next (.push [0x01, 0x00] (by decide))
        (.next (.reg .exp) (.next (.reg (.swap 0)) (.next (.reg .div)
          (.next (.push [0xff] (by decide)) (.next (.reg .and) (.next (.reg (.dup 1))
            .ret))))))))) o) :
    SFunc.RunExact prog sevm (St b (r :: S) M (g + 10)) t_0b05_c7 o := by
  refine rx_dest ?_
  refine rx_push (w := 2) (by decide) (by simp; omega) ?_
  refine rx_push (w := 0) (by decide) (by simp; omega) ?_
  exact rx_swap1 k

open Blanc.Lift in
/-- The getter after its `SLOAD`: `x / 256^0 & 0xff` and the return jump; 41 gas. -/
theorem dec_callee_post {sevm : Sevm} {b : Devm} {g : Nat} {r x : B256}
    {S : List B256} {M : Mem} (hroom : S.length < 1000) :
    SFunc.RunExact prog sevm (St b (x :: 0 :: r :: S) M (g + 41))
      (.next (.reg (.swap 0)) (.next (.push [0x01, 0x00] (by decide))
        (.next (.reg .exp) (.next (.reg (.swap 0)) (.next (.reg .div)
          (.next (.push [0xff] (by decide)) (.next (.reg .and) (.next (.reg (.dup 1))
            .ret))))))))
      (.returned (St b ((Bytes.toB256 [0xff] &&& x) :: r :: S) M g)) := by
  refine rx_swap1 ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_exp (by decide) (by simp; omega) ?_
  refine rx_swap1 ?_
  refine rx_div (v := x) (by rw [bexp_256_0, div_one']) (by simp; omega) ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_and rfl (by simp; omega) ?_
  exact rx_dup2 (by simp; omega) rx_ret

open Blanc.Lift in
theorem dec_callee_cold {sevm : Sevm} {b : Devm} {g : Nat} {r : B256} {S : List B256} {M : Mem}
    (hroom : S.length < 1000) (hlegacy : sevm.benvStat.rules.stateGas = none)
    (hcold : (⟨sevm.currentTarget, 2⟩ : Adr × B256) ∉ b.accessedStorageKeys) :
    SFunc.RunExact prog sevm (St b (r :: S) M (g + 2151)) t_0b05_c7
      (.returned (St (addAccessedStorageKey b sevm.currentTarget 2)
        ((Bytes.toB256 [0xff] &&& b.getStorVal sevm.currentTarget 2) :: r :: S) M g)) :=
  dec_callee_pre hroom (rx_sload_cold hlegacy hcold (by simp; omega) (dec_callee_post hroom))

open Blanc.Lift in
theorem dec_callee_warm {sevm : Sevm} {b : Devm} {g : Nat} {r : B256} {S : List B256} {M : Mem}
    (hroom : S.length < 1000) (hlegacy : sevm.benvStat.rules.stateGas = none)
    (hwarm : (⟨sevm.currentTarget, 2⟩ : Adr × B256) ∈ b.accessedStorageKeys) :
    SFunc.RunExact prog sevm (St b (r :: S) M (g + 151)) t_0b05_c7
      (.returned (St b ((Bytes.toB256 [0xff] &&& b.getStorVal sevm.currentTarget 2) :: r :: S)
        M g)) :=
  dec_callee_pre hroom (rx_sload_warm hlegacy hwarm (by simp; omega) (dec_callee_post hroom))

open Blanc.Lift in
/-- The `decimals` ABI tail at 0x279: mask to `uint8` twice, write at the
free-memory pointer, return one word.  65 gas. -/
theorem dec_tail {sevm : Sevm} {b : Devm} {g : Nat} {d r sel : B256} :
    ∃ post, SFunc.RunExact prog sevm (St b [d, r, sel] memFp (g + 65)) t_0279_c23
        (.halted post) ∧ post.gasLeft = g ∧
      post.output = (Bytes.toB256 [0xff] &&& (Bytes.toB256 [0xff] &&& d)).toBytes := by
  refine ⟨?post, ?run, ?gas, ?out⟩
  case run =>
    refine rx_dest ?_
    refine rx_push (w := 64) (by decide) (by simp) ?_
    refine rx_mload (c := 3) (v := 0x60) ?_ ?_ (read_snd_self memFp_size (by decide) (by decide))
      (by simp) ?_
    · rw [St.extCost_eq memFp_size]; decide
    · show Bytes.toB256 (memFp.read 64 32).1 = _
      rw [memFp_fp, B256.toB256_toBytes]
    refine rx_dup1 (by simp) ?_
    refine rx_dup3 (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_and rfl (by simp) ?_
    refine rx_push rfl (by simp) ?_
    refine rx_and rfl (by simp) ?_
    refine rx_dup2 (by simp) ?_
    refine rx_mstore (c := 6) (M' := memOut memFp _) ?_ rfl ?_
    · rw [St.extCost_eq memFp_size]; decide
    refine rx_push (w := 32) (by decide) (by simp) ?_
    refine rx_add (by simp) ?_
    refine rx_swap2 ?_
    refine rx_pop ?_
    refine rx_pop ?_
    refine rx_push (w := 64) (by decide) (by simp) ?_
    refine rx_mload (c := 3) (v := 0x60) ?_ ?_
      (read_snd_self (memOut_size memFp_size _) (by decide) (by decide)) (by simp) ?_
    · rw [St.extCost_eq (memOut_size memFp_size _)]; decide
    · show Bytes.toB256 ((memOut memFp _).read 64 32).1 = _
      rw [memOut_fp wf_memFp reads_memFp memFp_fp, B256.toB256_toBytes]
    refine rx_dup1 (by simp) ?_
    refine rx_swap2 ?_
    refine rx_sub (by simp) ?_
    refine rx_swap1 ?_
    refine rx_return (out := (Bytes.toB256 [0xff] &&& (Bytes.toB256 [0xff] &&& d)).toBytes) ?_ ?_
    · rw [St.extCost_eq (memOut_size memFp_size _)]; decide
    · have h32 : ((32 : B256) + 0x60 - 0x60).toNat = 32 := by decide
      rw [h32]
      exact memOut_val wf_memFp reads_memFp _
  case gas => rfl
  case out => rfl

open Blanc.Lift in
/-- The `decimals` wrapper at 0x266: the `nonpayable` guard and the call; 34 gas
before the callee and `dec_tail`'s 65 after it. -/
theorem dec_entry {sevm : Sevm} {b b' : Devm} {g G : Nat} {sel d : B256}
    (hval : sevm.value = 0)
    (hcall : SFunc.RunExact prog sevm (St b [Bytes.toB256 [0x02, 0x79], sel] memFp G)
      t_0b05_c7 (.returned (St b' [d, Bytes.toB256 [0x02, 0x79], sel] memFp (g + 65)))) :
    ∃ post, SFunc.RunExact prog sevm (St b [sel] memFp (G + 34)) t_0266_c23 (.halted post) ∧
      post.gasLeft = g ∧
      post.output = (Bytes.toB256 [0xff] &&& (Bytes.toB256 [0xff] &&& d)).toBytes := by
  obtain ⟨post, hrun, hg, ho⟩ :=
    dec_tail (sevm := sevm) (b := b') (g := g) (d := d) (r := Bytes.toB256 [0x02, 0x79])
      (sel := sel)
  refine ⟨post, ?_, hg, ho⟩
  refine rx_dest ?_
  refine rx_callvalue (by simp) ?_
  refine rx_iszero (v := 1) (by simp [B256.eqCheck, hval]) (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_branch_succ (by decide) ?_
  refine rx_dest ?_
  refine rx_push rfl (by simp) ?_
  refine rx_push rfl (by simp) ?_
  exact rx_callRet (j := 7) rfl hcall hrun

open Blanc.Lift in
/-- The dispatcher path to `decimals()`: four non-matching comparisons, then the
match that jumps to entry 23.  194 gas. -/
theorem dispatch_decimals {sevm : Sevm} {b : Devm} {g : Nat} {o : Outcome}
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = 0x313ce567)
    (k : SFunc.RunExact prog sevm (St b [Sevm.selector sevm] memFp g) t_0266_c23 o) :
    SFunc.RunExact prog sevm (St b [] Mem.empty (g + 194)) t_0000_c0 o := by
  refine dispatch_head h_len h_len' (by rw [hsel]; decide) ?_
  refine cmp_miss (by rw [hsel]; decide) ?_
  refine cmp_miss (by rw [hsel]; decide) ?_
  refine cmp_miss (by rw [hsel]; decide) ?_
  refine cmp_miss (by rw [hsel]; decide) ?_
  exact cmp_hit (j := 23) (by rw [hsel]; decide) rfl k

/-! ## The closed-form cost

In the style of Blanc-WETH's `wethGasWith` (`Blanc/WethGas.lean`): the fee
schedule abstracted, one parenthesised group per segment of the walk, in the
order the walk charges them.  `mem` is the linear memory coefficient: the
dispatcher's `mstore(0x40, 0x60)` expands empty memory to three words
(`3 * mem`, the quadratic term `9 / 512` being `0`) and the answer's `mstore`
at `0x60` adds a fourth (`mem`, `16 / 512 = 0`).  `EXP`'s byte charge is absent
because its exponent is `0`. -/

/-- The dispatcher's head: free-memory pointer, `CALLDATASIZE < 4` test,
selector extraction, and the first (`name()`) comparison. -/
def headGasWith (base vl lo hi mem : Nat) : Nat :=
  (vl + vl + (vl + 3 * mem))
    + (vl + base + vl + vl + hi)
    + (vl + vl + vl + vl + lo + vl + vl)
    + (vl + vl + vl + vl + hi)

/-- One dispatcher comparison, `DUP1 PUSH4 EQ PUSH2 JUMPI`. -/
def cmpGasWith (vl hi : Nat) : Nat := vl + vl + vl + vl + hi

/-- The one-word ABI tail after the getter returns (`word_tail`). -/
def wordTailGasWith (jd base vl mem : Nat) : Nat :=
  jd + (vl + vl + vl + vl + vl + (vl + mem) + vl + vl + vl + base + base)
    + (vl + vl + vl + vl + vl + vl)

/-- `balanceOf(address)` on the deployed WETH9, `sload` its storage charge. -/
def balanceOfGas9With (jd base vl lo hi mid mem kec kecw sload : Nat) : Nat :=
  headGasWith base vl lo hi mem
    + 5 * cmpGasWith vl hi + cmpGasWith vl hi
    + (jd + (base + vl + vl + hi))
    + (jd + (vl + vl + vl + vl + vl + vl + vl + vl + vl + vl + vl + vl + vl + base + base + vl)
      + mid)
    + (jd + (vl + vl + vl + vl + vl + vl + vl + vl + (kec + 2 * kecw) + vl + vl + base + vl + base)
      + sload + vl + mid)
    + wordTailGasWith jd base vl mem

/-- `decimals()` on the deployed WETH9: it reads slot 2. -/
def decimalsGas9With (jd base vl lo hi mid ex mem sload : Nat) : Nat :=
  headGasWith base vl lo hi mem
    + 4 * cmpGasWith vl hi + cmpGasWith vl hi
    + (jd + (base + vl + vl + hi))
    + (jd + vl + vl + mid)
    + (jd + vl + vl + vl + sload + vl + vl + ex + vl + lo + vl + vl + vl + mid)
    + (jd + (vl + vl + vl + vl + vl + vl + vl + vl + vl + (vl + mem) + vl + vl + vl + base + base)
      + (vl + vl + vl + vl + vl + vl))

def balanceOfGas9 : Nat :=
  balanceOfGas9With gJumpdest gBase gVerylow gLow gHigh gMid gMemory gKeccak256 gasKeccak256Word
    gasColdSload

def balanceOfGas9Warm : Nat :=
  balanceOfGas9With gJumpdest gBase gVerylow gLow gHigh gMid gMemory gKeccak256 gasKeccak256Word
    gasWarmAccess

def decimalsGas9 : Nat :=
  decimalsGas9With gJumpdest gBase gVerylow gLow gHigh gMid gExp gMemory gasColdSload

def decimalsGas9Warm : Nat :=
  decimalsGas9With gJumpdest gBase gVerylow gLow gHigh gMid gExp gMemory gasWarmAccess

theorem balanceOfGas9_eq : balanceOfGas9 = 2534 := by decide
theorem balanceOfGas9Warm_eq : balanceOfGas9Warm = 534 := by decide
theorem decimalsGas9_eq : decimalsGas9 = 2444 := by decide
theorem decimalsGas9Warm_eq : decimalsGas9Warm = 444 := by decide

/-- The storage key `balanceOf` reads. -/
def boKey (sevm : Sevm) : Adr × B256 :=
  ⟨sevm.currentTarget, balSlot (Sevm.dataWord sevm 4).toAdr⟩

/-- The storage key `decimals` reads. -/
def dcKey (sevm : Sevm) : Adr × B256 := ⟨sevm.currentTarget, 2⟩

/-- **What a call to the deployed WETH9 costs, by selector and pre-state, under
an arbitrary fee schedule.**  `none` where this module has not priced the
selector.  Both priced selectors read storage, so both carry the cold/warm
`if`. -/
def weth9GasWith (jd base vl lo hi mid ex mem kec kecw cold warm : Nat) :
    B256 → Sevm → Devm → Option Nat := fun sel sevm pre =>
  if sel = Blanc.boSel then
    some (balanceOfGas9With jd base vl lo hi mid mem kec kecw
      (if boKey sevm ∈ pre.accessedStorageKeys then warm else cold))
  else if sel = Blanc.dcSel then
    some (decimalsGas9With jd base vl lo hi mid ex mem
      (if dcKey sevm ∈ pre.accessedStorageKeys then warm else cold))
  else none

/-- `weth9GasWith` at Jaune's fee schedule. -/
def weth9Gas : B256 → Sevm → Devm → Option Nat :=
  weth9GasWith gJumpdest gBase gVerylow gLow gHigh gMid gExp gMemory gKeccak256 gasKeccak256Word
    gasColdSload gasWarmAccess

theorem weth9Gas_eq_with :
    weth9Gas = weth9GasWith gJumpdest gBase gVerylow gLow gHigh gMid gExp gMemory gKeccak256
      gasKeccak256Word gasColdSload gasWarmAccess := rfl

theorem weth9Gas_boSel {sevm : Sevm} {pre : Devm} :
    weth9Gas Blanc.boSel sevm pre =
      some (if boKey sevm ∈ pre.accessedStorageKeys then balanceOfGas9Warm else balanceOfGas9) := by
  by_cases h : boKey sevm ∈ pre.accessedStorageKeys
  · rw [if_pos h]
    simp only [weth9Gas, weth9GasWith, if_pos h]
    rfl
  · rw [if_neg h]
    simp only [weth9Gas, weth9GasWith, if_neg h]
    rfl

theorem weth9Gas_dcSel {sevm : Sevm} {pre : Devm} :
    weth9Gas Blanc.dcSel sevm pre =
      some (if dcKey sevm ∈ pre.accessedStorageKeys then decimalsGas9Warm else decimalsGas9) := by
  by_cases h : dcKey sevm ∈ pre.accessedStorageKeys
  · rw [if_pos h]
    simp only [weth9Gas, weth9GasWith, if_neg Blanc.dcSel_ne_boSel, if_pos h]
    rfl
  · rw [if_neg h]
    simp only [weth9Gas, weth9GasWith, if_neg Blanc.dcSel_ne_boSel, if_neg h]
    rfl

/-- The most a priced WETH9 entrypoint can cost: the storage read cold. -/
def weth9GasMaxWith (jd base vl lo hi mid ex mem kec kecw cold : Nat) : B256 → Option Nat :=
  fun sel =>
    if sel = Blanc.boSel then some (balanceOfGas9With jd base vl lo hi mid mem kec kecw cold)
    else if sel = Blanc.dcSel then some (decimalsGas9With jd base vl lo hi mid ex mem cold)
    else none

def weth9GasMax : B256 → Option Nat :=
  weth9GasMaxWith gJumpdest gBase gVerylow gLow gHigh gMid gExp gMemory gKeccak256
    gasKeccak256Word gasColdSload

/-- **No calldata and no accessed-key state can make a priced WETH9 entrypoint
cost more than `weth9GasMax`** — `wethGas_le_max`'s statement for the deployed
bytecode. -/
theorem weth9Gas_le_max {sel : B256} {sevm : Sevm} {pre : Devm} {cost : Nat}
    (h_cost : weth9Gas sel sevm pre = some cost) :
    ∃ bound, weth9GasMax sel = some bound ∧ cost ≤ bound := by
  simp only [weth9Gas, weth9GasWith] at h_cost
  simp only [weth9GasMax, weth9GasMaxWith]
  by_cases hb : sel = Blanc.boSel
  · subst hb
    rw [if_pos rfl] at h_cost ⊢
    refine ⟨_, rfl, ?_⟩
    injection h_cost with h_cost
    subst h_cost
    split <;> decide
  · rw [if_neg hb] at h_cost ⊢
    by_cases hd : sel = Blanc.dcSel
    · subst hd
      rw [if_pos rfl] at h_cost ⊢
      refine ⟨_, rfl, ?_⟩
      injection h_cost with h_cost
      subst h_cost
      split <;> decide
    · rw [if_neg hd] at h_cost
      exact absurd h_cost (by simp)

/-! ## The deployed WETH9 against Blanc-WETH (a measurement)

| call | Blanc-WETH `wethGas` | WETH9 `weth9Gas` |
|---|---|---|
| `balanceOf`, cold key | 2260 | 2534 (+274) |
| `balanceOf`, warm key | 260 | 534 (+274) |
| `decimals()` | 158 (constant, no storage) | 2444 cold / 444 warm |

The +274 on `balanceOf` is solc 0.4's code shape, not the storage read: the
free-memory-pointer store (12), the `CALLDATASIZE < 4` fallback test (21), a
`DIV`/`AND` selector extraction instead of `SHR` (23), a linear comparison
chain (6 × 22 before the wrapper, against Blanc-WETH's four-level tree), the
`calldataload(4) & mask` decode and internal call/return (≈70), `keccak`-based
mapping addressing (42 + its two `mstore`s), and ABI encoding through the
free-memory pointer (one more word of memory).  `decimals()` differs in kind:
WETH9 keeps it in storage slot 2, so it pays an `SLOAD`. -/

theorem balanceOf_weth9_vs_weth :
    balanceOfGas9 = Blanc.balanceOfGas + 274 ∧ balanceOfGas9Warm = Blanc.balanceOfGasWarm + 274 := by
  decide

theorem decimals_weth9_vs_weth :
    decimalsGas9 = Blanc.decimalsGas + 2286 ∧ decimalsGas9Warm = Blanc.decimalsGas + 286 := by
  decide

/-! ## The runs -/

theorem and_ff3 (x : B256) :
    (Bytes.toB256 [0xff] &&& (Bytes.toB256 [0xff] &&& (Bytes.toB256 [0xff] &&& x))) =
      x &&& 0xff := by
  rw [show Bytes.toB256 [0xff] = 0xff by decide, B256.and_comm 0xff x,
    B256.and_comm 0xff (x &&& 0xff), B256.and_idem_right,
    B256.and_comm 0xff (x &&& 0xff), B256.and_idem_right]

open Blanc.Lift in
/-- A `balanceOf(address)` call on the deployed WETH9 has a gas-exact synthetic
run costing exactly `weth9Gas`, and it returns the balance slot of the
argument's address. -/
theorem weth9_balanceOf_runExact {sevm : Sevm} {pre : Devm} {cost : Nat}
    (hfork : CoveredFork sevm.benvStat.fork)
    (h_value : sevm.value = 0)
    (h_sel : Sevm.selector sevm = Blanc.boSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_cost : weth9Gas (Sevm.selector sevm) sevm pre = some cost)
    (h_gas : cost ≤ pre.gasLeft) :
    ∃ post, SProg.RunExact prog sevm pre post ∧ post.gasLeft + cost = pre.gasLeft ∧
      post.output = (Devm.getStorVal pre sevm.currentTarget
        (balSlot (Sevm.dataWord sevm 4).toAdr)).toBytes := by
  have hsel : Sevm.selector sevm = 0x70a08231 := h_sel.trans boSel_eq
  have hleg : sevm.benvStat.rules.stateGas = none := hfork.rules_stateGas_none
  rw [h_sel, weth9Gas_boSel] at h_cost
  injection h_cost with h_cost
  by_cases hw : boKey sevm ∈ pre.accessedStorageKeys
  · rw [if_pos hw, balanceOfGas9Warm_eq] at h_cost
    subst h_cost
    obtain ⟨post, hrun, hg, ho⟩ := bal_entry (b := pre) (g := pre.gasLeft - 534)
      (G := pre.gasLeft - 534 + 53 + 191) h_value
      (bal_callee_warm (b := pre) (g := pre.gasLeft - 534 + 53) (S := [Sevm.selector sevm])
        (by simp) hleg hw)
      (memBal_size _) (wf_memBal _) (reads_memBal _) (memBal_fp _)
    have h0 := dispatch_balanceOf (b := pre) h_len h_len' hsel hrun
    rw [pre_eq_St h_stack h_mem (by omega)] at h0
    exact ⟨post, ⟨_, rfl, h0⟩, by omega, ho⟩
  · rw [if_neg hw, balanceOfGas9_eq] at h_cost
    subst h_cost
    obtain ⟨post, hrun, hg, ho⟩ := bal_entry (b := pre) (g := pre.gasLeft - 2534)
      (G := pre.gasLeft - 2534 + 53 + 2191) h_value
      (bal_callee_cold (b := pre) (g := pre.gasLeft - 2534 + 53) (S := [Sevm.selector sevm])
        (by simp) hleg hw)
      (memBal_size _) (wf_memBal _) (reads_memBal _) (memBal_fp _)
    have h0 := dispatch_balanceOf (b := pre) h_len h_len' hsel hrun
    rw [pre_eq_St h_stack h_mem (by omega)] at h0
    exact ⟨post, ⟨_, rfl, h0⟩, by omega, ho⟩

open Blanc.Lift in
/-- A `decimals()` call on the deployed WETH9 has a gas-exact synthetic run
costing exactly `weth9Gas`, and it returns the low byte of storage slot 2. -/
theorem weth9_decimals_runExact {sevm : Sevm} {pre : Devm} {cost : Nat}
    (hfork : CoveredFork sevm.benvStat.fork)
    (h_value : sevm.value = 0)
    (h_sel : Sevm.selector sevm = Blanc.dcSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_cost : weth9Gas (Sevm.selector sevm) sevm pre = some cost)
    (h_gas : cost ≤ pre.gasLeft) :
    ∃ post, SProg.RunExact prog sevm pre post ∧ post.gasLeft + cost = pre.gasLeft ∧
      post.output = (Devm.getStorVal pre sevm.currentTarget 2 &&& 0xff).toBytes := by
  have hsel : Sevm.selector sevm = 0x313ce567 := h_sel.trans dcSel_eq
  have hleg : sevm.benvStat.rules.stateGas = none := hfork.rules_stateGas_none
  rw [h_sel, weth9Gas_dcSel] at h_cost
  injection h_cost with h_cost
  by_cases hw : dcKey sevm ∈ pre.accessedStorageKeys
  · rw [if_pos hw, decimalsGas9Warm_eq] at h_cost
    subst h_cost
    obtain ⟨post, hrun, hg, ho⟩ := dec_entry (b := pre) (g := pre.gasLeft - 444)
      (G := pre.gasLeft - 444 + 65 + 151) h_value
      (dec_callee_warm (b := pre) (g := pre.gasLeft - 444 + 65) (S := [Sevm.selector sevm])
        (by simp) hleg hw)
    have h0 := dispatch_decimals (b := pre) h_len h_len' hsel hrun
    rw [pre_eq_St h_stack h_mem (by omega)] at h0
    refine ⟨post, ⟨_, rfl, h0⟩, by omega, ?_⟩
    rw [ho, and_ff3]
  · rw [if_neg hw, decimalsGas9_eq] at h_cost
    subst h_cost
    obtain ⟨post, hrun, hg, ho⟩ := dec_entry (b := pre) (g := pre.gasLeft - 2444)
      (G := pre.gasLeft - 2444 + 65 + 2151) h_value
      (dec_callee_cold (b := pre) (g := pre.gasLeft - 2444 + 65) (S := [Sevm.selector sevm])
        (by simp) hleg hw)
    have h0 := dispatch_decimals (b := pre) h_len h_len' hsel hrun
    rw [pre_eq_St h_stack h_mem (by omega)] at h0
    refine ⟨post, ⟨_, rfl, h0⟩, by omega, ?_⟩
    rw [ho, and_ff3]

/-! ## Parity rows P3 (exact gas) and P2 (liveness), at the `exec` altitude -/

/-- **P3, `balanceOf(address)`: the deployed WETH9 costs exactly what `weth9Gas`
says, with no coldness assumption** (the counterpart of Blanc-WETH's
`weth_balanceOf_gas_exact_wethGas`).  Two hypotheses Blanc-WETH does not carry:
`h_len` — solc 0.4's dispatcher sends calldata shorter than four bytes to the
fallback (`deposit`) before looking at the selector — and `h_len'`, because
`CALLDATASIZE` pushes the length modulo `2^256`. -/
theorem weth9_balanceOf_gas_exact {sevm : Sevm} {pre : Devm} {cost : Nat}
    (h_code : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork)
    (h_value : sevm.value = 0)
    (h_sel : Sevm.selector sevm = Blanc.boSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_cost : weth9Gas (Sevm.selector sevm) sevm pre = some cost)
    (h_gas : cost ≤ pre.gasLeft) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧ post.gasLeft + cost = pre.gasLeft ∧
      post.output = (Devm.getStorVal pre sevm.currentTarget
        (balSlot (Sevm.dataWord sevm 4).toAdr)).toBytes := by
  obtain ⟨post, hrun, hg, ho⟩ :=
    weth9_balanceOf_runExact hfork h_value h_sel h_len h_len' h_stack h_mem h_cost h_gas
  exact ⟨post, (exec_iff_exec_eq 0 sevm pre (.ok post)).mp (exec_of_runExact h_code hfork hrun),
    hg, ho⟩

/-- **P3, `decimals()`** (the counterpart of `weth_decimals_gas_exact_wethGas`).
WETH9 reads `decimals` from storage slot 2, so unlike Blanc-WETH the cost
depends on the pre-state and the answer is the slot's low byte. -/
theorem weth9_decimals_gas_exact {sevm : Sevm} {pre : Devm} {cost : Nat}
    (h_code : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork)
    (h_value : sevm.value = 0)
    (h_sel : Sevm.selector sevm = Blanc.dcSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_cost : weth9Gas (Sevm.selector sevm) sevm pre = some cost)
    (h_gas : cost ≤ pre.gasLeft) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧ post.gasLeft + cost = pre.gasLeft ∧
      post.output = (Devm.getStorVal pre sevm.currentTarget 2 &&& 0xff).toBytes := by
  obtain ⟨post, hrun, hg, ho⟩ :=
    weth9_decimals_runExact hfork h_value h_sel h_len h_len' h_stack h_mem h_cost h_gas
  exact ⟨post, (exec_iff_exec_eq 0 sevm pre (.ok post)).mp (exec_of_runExact h_code hfork hrun),
    hg, ho⟩

/-- **P2: the deployed WETH9's `balanceOf(address)` call succeeds** and returns
the argument's balance slot (the counterpart of `weth_balanceOf_succeeds`, with
the same cold-key premise).  Unlike Blanc-WETH, whose `balanceOf` indexes by the
raw calldata word, WETH9 masks the argument to an address first, so the slot is
`balSlot` of that address. -/
theorem weth9_balanceOf_succeeds {sevm : Sevm} {pre : Devm}
    (h_code : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork)
    (h_value : sevm.value = 0)
    (h_sel : Sevm.selector sevm = Blanc.boSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_cold : (⟨sevm.currentTarget, balSlot (Sevm.dataWord sevm 4).toAdr⟩ : Adr × B256)
      ∉ pre.accessedStorageKeys)
    (h_gas : balanceOfGas9 ≤ pre.gasLeft) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧
      post.output = (Devm.getStorVal pre sevm.currentTarget
        (balSlot (Sevm.dataWord sevm 4).toAdr)).toBytes := by
  have h_cost : weth9Gas (Sevm.selector sevm) sevm pre = some balanceOfGas9 := by
    rw [h_sel, weth9Gas_boSel, if_neg (show boKey sevm ∉ pre.accessedStorageKeys from h_cold)]
  obtain ⟨post, hexec, _, ho⟩ :=
    weth9_balanceOf_gas_exact h_code hfork h_value h_sel h_len h_len' h_stack h_mem h_cost h_gas
  exact ⟨post, hexec, ho⟩

/-- **P2, `decimals()`: the call succeeds** and returns the low byte of slot 2,
with the slot's key cold. -/
theorem weth9_decimals_succeeds {sevm : Sevm} {pre : Devm}
    (h_code : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork)
    (h_value : sevm.value = 0)
    (h_sel : Sevm.selector sevm = Blanc.dcSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_cold : (⟨sevm.currentTarget, 2⟩ : Adr × B256) ∉ pre.accessedStorageKeys)
    (h_gas : decimalsGas9 ≤ pre.gasLeft) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧
      post.output = (Devm.getStorVal pre sevm.currentTarget 2 &&& 0xff).toBytes := by
  have h_cost : weth9Gas (Sevm.selector sevm) sevm pre = some decimalsGas9 := by
    rw [h_sel, weth9Gas_dcSel, if_neg (show dcKey sevm ∉ pre.accessedStorageKeys from h_cold)]
  obtain ⟨post, hexec, _, ho⟩ :=
    weth9_decimals_gas_exact h_code hfork h_value h_sel h_len h_len' h_stack h_mem h_cost h_gas
  exact ⟨post, hexec, ho⟩

end Blanc.Lift.Weth9
