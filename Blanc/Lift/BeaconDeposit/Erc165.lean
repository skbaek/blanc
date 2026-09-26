import Blanc.Lift.BeaconDeposit.Prog
import Blanc.Lift.ExactWalk
import Blanc.BeaconDepositCore

namespace Blanc.Lift.BeaconDeposit

open Jaune

def erc165Gas (sevm : Sevm) : Nat :=
  if Sevm.argWord sevm 0 >>> 224 = Blanc.BeaconDeposit.erc165InterfaceId then 269 else 286

theorem supportsInterfaceSelector_eq :
    Blanc.BeaconDeposit.supportsInterfaceSelector = 0x01ffc9a7 := by decide +kernel

def memFp : Mem := Mem.empty.write 64 (0x80 : B256).toBytes

theorem memFp_size : memFp.size = 96 := by
  rw [memFp, Mem.size_write_word_at]
  rfl

theorem wf_memFp : Mem.Wf memFp := Mem.wf_empty.write _ _

theorem reads_memFp : Mem.Reads memFp (Bytes.writeAt [] 64 (0x80 : B256).toBytes) :=
  Mem.reads_empty.write Mem.wf_empty 64 _

theorem memFp_fp : (memFp.read 64 32).1 = (0x80 : B256).toBytes := by
  rw [reads_memFp.read]
  exact sliceD_word_same _ _ _

def memOut (μ : Mem) (v : B256) : Mem := μ.write 128 v.toBytes

theorem memOut_size {μ : Mem} (hs : μ.size = 96) (v : B256) : (memOut μ v).size = 160 := by
  rw [memOut, Mem.size_write_word_at, hs]
  rfl

theorem memOut_fp {μ : Mem} {bs : Bytes} (hwf : Mem.Wf μ) (hr : Mem.Reads μ bs)
    (hfp : (μ.read 64 32).1 = (0x80 : B256).toBytes) (v : B256) :
    ((memOut μ v).read 64 32).1 = (0x80 : B256).toBytes := by
  rw [memOut, (hr.write hwf 128 v.toBytes).read,
    Bytes.readWord_writeAt_of_disjoint _ _ _ _ (.inl (by omega)), ← hr.read, hfp]

theorem memOut_val {μ : Mem} {bs : Bytes} (hwf : Mem.Wf μ) (hr : Mem.Reads μ bs) (v : B256) :
    ((memOut μ v).read 128 32).1 = v.toBytes := by
  rw [memOut, (hr.write hwf 128 v.toBytes).read]
  exact sliceD_word_same _ _ _

open Blanc.Lift in
theorem bool_tail {sevm : Sevm} {b : Devm} {g : Nat} {v sel : B256} :
    ∃ post, SFunc.RunExact prog sevm (St b [v, sel] memFp (g + 55)) t_0090_c31
      (.halted post) ∧ post.gasLeft = g ∧
      post.output = (B256.eqCheck (B256.eqCheck v 0) 0).toBytes ∧
      post.state = b.state ∧ post.logs = b.logs := by
  refine ⟨?post, ?run, ?gas, ?out, ?state, ?logs⟩
  case run =>
    refine rx_dest ?_
    refine rx_push (w := 64) (by decide) (by simp) ?_
    refine rx_dup1 (by simp) ?_
    refine rx_mload (c := 3) (v := 0x80) ?_ ?_
      (read_covered memFp_size (by decide) (by decide)) (by simp) ?_
    · rw [St.extCost_eq memFp_size]
      decide
    · show Bytes.toB256 (memFp.read 64 32).1 = _
      rw [memFp_fp, B256.toB256_toBytes]
    refine rx_swap2 ?_
    refine rx_iszero (v := B256.eqCheck v 0) rfl (by simp) ?_
    refine rx_iszero (v := B256.eqCheck (B256.eqCheck v 0) 0) rfl (by simp) ?_
    refine rx_dup3 (by simp) ?_
    refine rx_mstore (c := 9) (M' := memOut memFp _) ?_ rfl ?_
    · rw [St.extCost_eq memFp_size]
      decide
    refine rx_mload (c := 3) (v := 0x80) ?_ ?_
      (read_covered (memOut_size memFp_size _) (by decide) (by decide)) (by simp) ?_
    · rw [St.extCost_eq (memOut_size memFp_size _)]
      decide
    · show Bytes.toB256 ((memOut memFp _).read 64 32).1 = _
      rw [memOut, (reads_memFp.write wf_memFp 128 _).read,
        Bytes.readWord_writeAt_of_disjoint _ _ _ _ (.inl (by omega)),
        ← reads_memFp.read, memFp_fp, B256.toB256_toBytes]
    refine rx_swap1 ?_
    refine rx_dup2 (by simp) ?_
    refine rx_swap1 ?_
    refine rx_sub (by simp) ?_
    refine rx_push (w := 32) (by decide) (by simp) ?_
    refine rx_add (by simp) ?_
    refine rx_swap1 ?_
    refine rx_return (out := (B256.eqCheck (B256.eqCheck v 0) 0).toBytes) ?_ ?_
    · rw [St.extCost_eq (memOut_size memFp_size _)]
      decide
    · change ((memOut memFp _).read 128 32).1 = _
      exact memOut_val wf_memFp reads_memFp _
  case gas => rfl
  case out => rfl
  case state => rfl
  case logs => rfl

def mask4 : B256 := Bytes.toB256
  [0xff, 0xff, 0xff, 0xff, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def ercWord : B256 := Bytes.toB256
  [0x01, 0xff, 0xc9, 0xa7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

open Blanc.Lift in
theorem callee_true {sevm : Sevm} {b : Devm} {g : Nat} {arg r sel : B256} {M : Mem}
    (harg : arg &&& mask4 = ercWord) :
    SFunc.RunExact prog sevm (St b [arg, r, sel] M (g + 54)) t_026b_c6
      (.returned (St b [1, sel] M g)) := by
  refine rx_dest ?_
  refine rx_push (w := 0) (by decide) (by simp) ?_
  refine rx_push (w := mask4) (by rfl) (by simp) ?_
  refine rx_dup3 (by simp) ?_
  refine rx_and (v := arg &&& mask4) (by rfl) (by simp) ?_
  refine rx_push (w := ercWord) (by rfl) (by simp) ?_
  refine rx_eq (v := 1) (by simp [B256.eqCheck, harg]) (by simp) ?_
  refine rx_dup1 (by simp) ?_
  refine rx_push (w := 0x02fe) (by decide) (by simp) ?_
  refine rx_branchTo_succ (by decide) rfl ?_
  refine rx_dest ?_
  refine rx_swap (n := 2) (S := [1, 0, arg, r, sel])
    (S' := [r, 0, arg, 1, sel]) (by rfl) ?_
  refine rx_swap2 ?_
  refine rx_pop ?_
  refine rx_pop ?_
  exact rx_ret

def depositWord : B256 := Bytes.toB256
  [0x85, 0x64, 0x09, 0x07, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private lemma nat_mask_shift_iff (x c : Nat) (hx : x < 2^64) (hc : c < 2^32) :
    x &&& (0xffffffff00000000 : Nat) = c <<< 32 ↔ x >>> 32 = c := by
  have hm : (0xffffffff00000000 : Nat) = (2^32 - 1) <<< 32 := by
    norm_num [Nat.shiftLeft_eq]
  rw [hm]
  have hmask_bit (i : Nat) (hi32 : 32 ≤ i) (hi64 : i < 64) :
      ((2^32 - 1) <<< 32).testBit i = true := by
    rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
    have heq : i - 32 < 32 := by
      have := Nat.add_sub_of_le hi32
      omega
    simp [hi32, heq]
  have hc_bit (i : Nat) (hi32 : 32 ≤ i) :
      (c <<< 32 : Nat).testBit i = c.testBit (i - 32) := by
    rw [Nat.testBit_shiftLeft]
    simp [hi32]
  have hm_bit_low (i : Nat) (hi : i < 32) :
      ((2^32 - 1) <<< 32 : Nat).testBit i = false := by
    rw [Nat.testBit_shiftLeft]
    simp [hi]
  have hc_bit_low (i : Nat) (hi : i < 32) :
      (c <<< 32 : Nat).testBit i = false := by
    rw [Nat.testBit_shiftLeft]
    simp [hi]
  have hc_bit_high (i : Nat) (hi : ¬ i < 32) :
      c.testBit i = false := by
    apply Nat.testBit_lt_two_pow
    exact lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hcs_lt : (c <<< 32 : Nat) < 2^64 := by
    rw [Nat.shiftLeft_eq]
    calc
      c * 2^32 < 2^32 * 2^32 := Nat.mul_lt_mul_of_pos_right hc (by norm_num)
      _ = 2^64 := by norm_num
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 32
    · have hbits := congrArg (fun z : Nat => z.testBit (32 + i)) h
      rw [Nat.testBit_and] at hbits
      rw [hmask_bit (32+i) (by omega) (by omega), hc_bit (32+i) (by omega)] at hbits
      simpa [Nat.testBit_shiftRight] using hbits
    · rw [Nat.testBit_shiftRight]
      have hx0 : x.testBit (32 + i) = false := by
        apply Nat.testBit_lt_two_pow
        have he : 64 ≤ 32+i := by omega
        exact lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) he)
      rw [hx0, hc_bit_high i hi]
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 32
    · rw [Nat.testBit_and, hm_bit_low i hi, hc_bit_low i hi]
      simp
    · by_cases hi64 : i < 64
      · have hbits := congrArg (fun z : Nat => z.testBit (i - 32)) h
        rw [Nat.testBit_shiftRight] at hbits
        have hxi : 32 + (i - 32) = i := by
          exact Nat.add_sub_of_le (by omega)
        rw [hxi] at hbits
        rw [Nat.testBit_and, hmask_bit i (by omega) hi64, hc_bit i (by omega)]
        simpa using hbits
      · have hi64' : 64 ≤ i := by omega
        rw [Nat.testBit_and]
        have hx0 : x.testBit i = false := by
          apply Nat.testBit_lt_two_pow
          exact lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hi64')
        have hm0 : ((2^32 - 1) <<< 32 : Nat).testBit i = false := by
          apply Nat.testBit_lt_two_pow
          have hm_lt : ((2^32 - 1) <<< 32 : Nat) < 2^64 := by
            rw [Nat.shiftLeft_eq]
            norm_num
          exact lt_of_lt_of_le hm_lt (Nat.pow_le_pow_right (by norm_num) hi64')
        have hc0 : (c <<< 32 : Nat).testBit i = false := by
          apply Nat.testBit_lt_two_pow
          exact lt_of_lt_of_le hcs_lt (Nat.pow_le_pow_right (by norm_num) hi64')
        rw [hx0, hm0, hc0]
        simp

private lemma u64_mask_shift_iff (x c : UInt64) (hc : c.toNat < 2^32) :
    x &&& 0xffffffff00000000 = c <<< (32 : UInt64) ↔
      x >>> (32 : UInt64) = c := by
  have hshift : (c <<< (32 : UInt64)).toNat = c.toNat <<< 32 := by
    simp only [UInt64.toNat_shiftLeft]
    norm_num
    have hlt : c.toNat <<< 32 < 2^64 := by
      rw [Nat.shiftLeft_eq]
      calc
        c.toNat * 2^32 < 2^32 * 2^32 :=
          Nat.mul_lt_mul_of_pos_right hc (by norm_num)
        _ = 2^64 := by norm_num
    exact hlt
  constructor
  · intro h
    apply UInt64.toNat_inj.mp
    change x.toNat >>> 32 = c.toNat
    have hn := congrArg UInt64.toNat h
    rw [UInt64.toNat_and, hshift] at hn
    exact (nat_mask_shift_iff x.toNat c.toNat (UInt64.toNat_lt x) hc).mp hn
  · intro h
    apply UInt64.toNat_inj.mp
    have hn := congrArg UInt64.toNat h
    change x.toNat >>> 32 = c.toNat at hn
    have hn' := (nat_mask_shift_iff x.toNat c.toNat (UInt64.toNat_lt x) hc).mpr hn
    rw [UInt64.toNat_and, hshift]
    exact hn'

private lemma mask_word_iff (x : B256) (c : UInt64) (hc : c.toNat < 2^32) :
    x &&& mask4 = ((c <<< (32 : UInt64), 0), (0, 0)) ↔
      x >>> 224 = ((0, 0), (0, c)) := by
  rcases x with ⟨⟨a,b⟩,⟨c',d⟩⟩
  change
    ((a &&& 0xffffffff00000000, b &&& 0), (c' &&& 0, d &&& 0)) =
        ((c <<< (32 : UInt64), 0), (0, 0)) ↔
      ((0, 0), (0, a >>> (32 : UInt64))) = ((0, 0), (0, c))
  simp only [UInt64.and_zero, UInt64.zero_and]
  constructor
  · intro h
    have ha := congrArg (fun z : B256 => z.1.1) h
    simpa using (u64_mask_shift_iff a c hc).mp ha
  · intro h
    have ha : a &&& 0xffffffff00000000 = c <<< (32 : UInt64) :=
      (u64_mask_shift_iff a c hc).mpr (congrArg (fun z : B256 => z.2.2) h)
    simpa [ha]

private lemma b256_and_comm (x y : B256) : x &&& y = y &&& x := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  rcases y with ⟨⟨e,f⟩,⟨g,h⟩⟩
  change ((a &&& e, b &&& f), (c &&& g, d &&& h)) =
    ((e &&& a, f &&& b), (g &&& c, h &&& d))
  simp [UInt64.and_comm]

private lemma b256_and_self_left (x y : B256) : x &&& (x &&& y) = x &&& y := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  rcases y with ⟨⟨e,f⟩,⟨g,h⟩⟩
  change ((a &&& (a &&& e), b &&& (b &&& f)),
      (c &&& (c &&& g), d &&& (d &&& h))) =
    ((a &&& e, b &&& f), (c &&& g, d &&& h))
  simp only [← UInt64.and_assoc, UInt64.and_self]

theorem mask_erc_iff (x : B256) :
    x &&& mask4 = ercWord ↔ x >>> 224 = Blanc.BeaconDeposit.erc165InterfaceId := by
  change x &&& mask4 = ((0x01ffc9a700000000, 0), (0, 0)) ↔
    x >>> 224 = ((0, 0), (0, 0x01ffc9a7))
  exact mask_word_iff x 0x01ffc9a7 (by norm_num)

theorem mask_deposit_iff (x : B256) :
    x &&& mask4 = depositWord ↔ x >>> 224 = Blanc.BeaconDeposit.depositInterfaceId := by
  change x &&& mask4 = ((0x8564090700000000, 0), (0, 0)) ↔
    x >>> 224 = ((0, 0), (0, 0x85640907))
  exact mask_word_iff x 0x85640907 (by norm_num)

open Blanc.Lift in
theorem callee_false {sevm : Sevm} {b : Devm} {g : Nat} {arg r sel : B256} {M : Mem}
    (harg : arg &&& mask4 ≠ ercWord) (hdep : arg &&& mask4 = depositWord) :
    SFunc.RunExact prog sevm (St b [arg, r, sel] M (g + 71)) t_026b_c6
      (.returned (St b [1, sel] M g)) := by
  refine rx_dest ?_
  refine rx_push (w := 0) (by decide) (by simp) ?_
  refine rx_push (w := mask4) (by rfl) (by simp) ?_
  refine rx_dup3 (by simp) ?_
  refine rx_and (v := arg &&& mask4) (by rfl) (by simp) ?_
  refine rx_push (w := ercWord) (by rfl) (by simp) ?_
  refine rx_eq (v := 0) (by simp [B256.eqCheck]; intro h; exact (harg h.symm).elim)
    (by simp) ?_
  refine rx_dup1 (by simp) ?_
  refine rx_push (w := 0x02fe) (by decide) (by simp) ?_
  refine rx_branchTo_zero ?_
  refine rx_pop ?_
  refine rx_push (w := mask4) (by rfl) (by simp) ?_
  refine rx_dup3 (by simp) ?_
  refine rx_and (v := arg &&& mask4) (by rfl) (by simp) ?_
  refine rx_push (w := depositWord) (by decide +kernel) (by simp) ?_
  refine rx_eq (v := 1) (by simp [B256.eqCheck, hdep]) (by simp) ?_
  refine rx_dest ?_
  refine rx_swap (n := 2) (S := [1, 0, arg, r, sel])
    (S' := [r, 0, arg, 1, sel]) (by rfl) ?_
  refine rx_swap2 ?_
  refine rx_pop ?_
  refine rx_pop ?_
  exact rx_ret

open Blanc.Lift in
theorem callee_neither {sevm : Sevm} {b : Devm} {g : Nat} {arg r sel : B256} {M : Mem}
    (harg : arg &&& mask4 ≠ ercWord) (hdep : arg &&& mask4 ≠ depositWord) :
    SFunc.RunExact prog sevm (St b [arg, r, sel] M (g + 71)) t_026b_c6
      (.returned (St b [0, sel] M g)) := by
  refine rx_dest ?_
  refine rx_push (w := 0) (by decide) (by simp) ?_
  refine rx_push (w := mask4) (by rfl) (by simp) ?_
  refine rx_dup3 (by simp) ?_
  refine rx_and (v := arg &&& mask4) (by rfl) (by simp) ?_
  refine rx_push (w := ercWord) (by rfl) (by simp) ?_
  refine rx_eq (v := 0) (by simp [B256.eqCheck]; intro h; exact (harg h.symm).elim)
    (by simp) ?_
  refine rx_dup1 (by simp) ?_
  refine rx_push (w := 0x02fe) (by decide) (by simp) ?_
  refine rx_branchTo_zero ?_
  refine rx_pop ?_
  refine rx_push (w := mask4) (by rfl) (by simp) ?_
  refine rx_dup3 (by simp) ?_
  refine rx_and (v := arg &&& mask4) (by rfl) (by simp) ?_
  refine rx_push (w := depositWord) (by decide +kernel) (by simp) ?_
  refine rx_eq (v := 0) (by simp [B256.eqCheck]; intro h; exact (hdep h.symm).elim)
    (by simp) ?_
  refine rx_dest ?_
  refine rx_swap (n := 2) (S := [0, 0, arg, r, sel])
    (S' := [r, 0, arg, 0, sel]) (by rfl) ?_
  refine rx_swap2 ?_
  refine rx_pop ?_
  refine rx_pop ?_
  exact rx_ret

open Blanc.Lift in
theorem wrapper_true {sevm : Sevm} {b b' : Devm} {g : Nat} {sel v : B256}
    (hval : sevm.value = 0)
    (h_len : 36 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (hcall : SFunc.RunExact prog sevm
      (St b [mask4 &&& Sevm.dataWord sevm 4, 0x90, sel] memFp (g + 109)) t_026b_c6
      (.returned (St b' [v, sel] memFp (g + 55)))) :
    ∃ post, SFunc.RunExact prog sevm (St b [sel] memFp (g + 196)) t_0044_c31
      (.halted post) ∧ post.gasLeft = g ∧
      post.output = (B256.eqCheck (B256.eqCheck v 0) 0).toBytes ∧
      post.state = b'.state ∧ post.logs = b'.logs := by
  obtain ⟨post, hrun, hg, ho, hs, hl⟩ :=
    bool_tail (sevm := sevm) (b := b') (g := g) (v := v) (sel := sel)
  refine ⟨post, ?_, hg, ho, hs, hl⟩
  refine rx_dest ?_
  refine rx_callvalue (by simp) ?_
  refine rx_dup1 (by simp) ?_
  refine rx_iszero (S := [sevm.value, sel]) (x := sevm.value) (v := 1)
    (by simp [B256.eqCheck, hval])
    (by simp) ?_
  refine rx_push (w := 0x50) (by decide) (by simp) ?_
  refine rx_branch_succ (by decide) ?_
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_push (w := 0x90) (by decide) (by simp) ?_
  refine rx_push (w := 4) (by decide) (by simp) ?_
  refine rx_dup1 (by simp) ?_
  refine rx_calldatasize (by simp) ?_
  refine rx_sub (by simp) ?_
  refine rx_push (w := 32) (by decide) (by simp) ?_
  refine rx_dup2 (by simp) ?_
  refine rx_lt (v := 0) (by
    rw [B256.ltCheck, if_neg]
    intro h
    have h1 := B256.toNat_lt_toNat h
    have h4 : (4 : B256).toNat = 4 := by decide
    have h32 : (32 : B256).toNat = 32 := by decide
    have hle : (4 : B256) ≤ Nat.toB256 sevm.data.length := by
      rw [B256.le_iff_toNat_le_toNat, B256.toNat_toB256_of_lt h_len']
      rw [h4]
      omega
    have hsub : (Nat.toB256 sevm.data.length - 4).toNat =
        sevm.data.length - 4 := by
      rw [B256.toNat_sub_eq_of_le _ _ hle,
        B256.toNat_toB256_of_lt h_len', h4]
    rw [hsub, h32] at h1
    omega) (by simp) ?_
  refine rx_iszero (v := 1) (by simp [B256.eqCheck]) (by simp) ?_
  refine rx_push (w := 0x67) (by decide) (by simp) ?_
  refine rx_branch_succ (by decide) ?_
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_calldataload (by simp) ?_
  refine rx_push (w := mask4) (by rfl) (by simp) ?_
  refine rx_and (v := mask4 &&& Sevm.dataWord sevm 4) (by rfl) (by simp) ?_
  refine rx_push (w := 0x026b) (by decide) (by simp) ?_
  exact rx_callRet (j := 6) rfl hcall hrun

open Blanc.Lift in
theorem wrapper_false {sevm : Sevm} {b b' : Devm} {g : Nat} {sel v : B256}
    (hval : sevm.value = 0)
    (h_len : 36 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (hcall : SFunc.RunExact prog sevm
      (St b [mask4 &&& Sevm.dataWord sevm 4, 0x90, sel] memFp (g + 126)) t_026b_c6
      (.returned (St b' [v, sel] memFp (g + 55)))) :
    ∃ post, SFunc.RunExact prog sevm (St b [sel] memFp (g + 213)) t_0044_c31
      (.halted post) ∧ post.gasLeft = g ∧
      post.output = (B256.eqCheck (B256.eqCheck v 0) 0).toBytes ∧
      post.state = b'.state ∧ post.logs = b'.logs := by
  obtain ⟨post, hrun, hg, ho, hs, hl⟩ :=
    bool_tail (sevm := sevm) (b := b') (g := g) (v := v) (sel := sel)
  refine ⟨post, ?_, hg, ho, hs, hl⟩
  refine rx_dest ?_
  refine rx_callvalue (by simp) ?_
  refine rx_dup1 (by simp) ?_
  refine rx_iszero (S := [sevm.value, sel]) (x := sevm.value) (v := 1)
    (by simp [B256.eqCheck, hval]) (by simp) ?_
  refine rx_push (w := 0x50) (by decide) (by simp) ?_
  refine rx_branch_succ (by decide) ?_
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_push (w := 0x90) (by decide) (by simp) ?_
  refine rx_push (w := 4) (by decide) (by simp) ?_
  refine rx_dup1 (by simp) ?_
  refine rx_calldatasize (by simp) ?_
  refine rx_sub (by simp) ?_
  refine rx_push (w := 32) (by decide) (by simp) ?_
  refine rx_dup2 (by simp) ?_
  refine rx_lt (v := 0) (by
    rw [B256.ltCheck, if_neg]
    intro h
    have h1 := B256.toNat_lt_toNat h
    have h4 : (4 : B256).toNat = 4 := by decide
    have h32 : (32 : B256).toNat = 32 := by decide
    have hle : (4 : B256) ≤ Nat.toB256 sevm.data.length := by
      rw [B256.le_iff_toNat_le_toNat, B256.toNat_toB256_of_lt h_len', h4]
      omega
    have hsub : (Nat.toB256 sevm.data.length - 4).toNat =
        sevm.data.length - 4 := by
      rw [B256.toNat_sub_eq_of_le _ _ hle,
        B256.toNat_toB256_of_lt h_len', h4]
    rw [hsub, h32] at h1
    omega) (by simp) ?_
  refine rx_iszero (v := 1) (by simp [B256.eqCheck]) (by simp) ?_
  refine rx_push (w := 0x67) (by decide) (by simp) ?_
  refine rx_branch_succ (by decide) ?_
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_calldataload (by simp) ?_
  refine rx_push (w := mask4) (by rfl) (by simp) ?_
  refine rx_and (v := mask4 &&& Sevm.dataWord sevm 4) (by rfl) (by simp) ?_
  refine rx_push (w := 0x026b) (by decide) (by simp) ?_
  exact rx_callRet (j := 6) rfl hcall hrun

open Blanc.Lift in
theorem dispatch_supports {sevm : Sevm} {b : Devm} {g : Nat} {o : Outcome}
    (h_len : 36 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = 0x01ffc9a7)
    (k : SFunc.RunExact prog sevm (St b [Sevm.selector sevm] memFp g)
      t_0044_c31 o) :
    SFunc.RunExact prog sevm (St b [] Mem.empty (g + 73)) t_0000_c0 o := by
  refine rx_push (w := 0x80) (by decide) (by simp) ?_
  refine rx_push (w := 0x40) (by decide) (by simp) ?_
  refine rx_mstore (c := 12) (M' := memFp) ?_ rfl ?_
  · rw [St.extCost_eq (n := 0) rfl]
    decide
  refine rx_push (w := 4) (by decide) (by simp) ?_
  refine rx_calldatasize (by simp) ?_
  refine rx_lt (v := 0) (by
    rw [B256.ltCheck, if_neg]
    intro h
    have h1 := B256.toNat_lt_toNat h
    rw [B256.toNat_toB256_of_lt h_len'] at h1
    have h4 : (4 : B256).toNat = 4 := rfl
    omega) (by simp) ?_
  refine rx_push (w := 0x003f) (by decide) (by simp) ?_
  refine rx_branch_zero ?_
  refine rx_push (w := 0) (by decide) (by simp) ?_
  refine rx_calldataload (by simp) ?_
  refine rx_push (w := 0xe0) (by decide) (by simp) ?_
  refine rx_binary (fn := fun x y => y >>> x.toNat) (c := gVerylow)
    (by rintro ⟨⟩) (fun _ => rfl) rfl (by simp) ?_
  refine rx_dup1 (by simp) ?_
  refine rx_push (w := 0x01ffc9a7) (by decide) (by simp) ?_
  refine rx_eq (v := 1) (by
    rw [B256.eqCheck, if_pos]
    exact hsel.symm) (by simp) ?_
  refine rx_push (w := 0x44) (by decide) (by simp) ?_
  exact rx_branchTo_succ (by decide) rfl k

open Blanc.Lift in
theorem supportsInterface_runExact {sevm : Sevm} {pre : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    (h_value : sevm.value = 0)
    (h_sel : Sevm.selector sevm = Blanc.BeaconDeposit.supportsInterfaceSelector)
    (h_len : 36 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_gas : erc165Gas sevm ≤ pre.gasLeft) :
    ∃ post, SProg.RunExact prog sevm pre post ∧
      post.gasLeft + erc165Gas sevm = pre.gasLeft ∧
      post.output = Blanc.BeaconDeposit.abiBoolReturn (decide
        (Sevm.argWord sevm 0 >>> 224 = Blanc.BeaconDeposit.erc165InterfaceId ∨
          Sevm.argWord sevm 0 >>> 224 = Blanc.BeaconDeposit.depositInterfaceId)) ∧
      post.state = pre.state ∧ post.logs = pre.logs := by
  have _ := hfork
  have hsel : Sevm.selector sevm = 0x01ffc9a7 :=
    h_sel.trans supportsInterfaceSelector_eq
  let arg : B256 := mask4 &&& Sevm.dataWord sevm 4
  have harg_erc : arg &&& mask4 = ercWord ↔
      Sevm.argWord sevm 0 >>> 224 = Blanc.BeaconDeposit.erc165InterfaceId := by
    change mask4 &&& Sevm.dataWord sevm 4 &&& mask4 = ercWord ↔
      Sevm.dataWord sevm 4 >>> 224 = Blanc.BeaconDeposit.erc165InterfaceId
    rw [b256_and_comm, b256_and_self_left, b256_and_comm mask4, mask_erc_iff]
  have harg_dep : arg &&& mask4 = depositWord ↔
      Sevm.argWord sevm 0 >>> 224 = Blanc.BeaconDeposit.depositInterfaceId := by
    change mask4 &&& Sevm.dataWord sevm 4 &&& mask4 = depositWord ↔
      Sevm.dataWord sevm 4 >>> 224 = Blanc.BeaconDeposit.depositInterfaceId
    rw [b256_and_comm, b256_and_self_left, b256_and_comm mask4, mask_deposit_iff]
  by_cases he : Sevm.argWord sevm 0 >>> 224 = Blanc.BeaconDeposit.erc165InterfaceId
  · have hroom : 269 ≤ pre.gasLeft := by
      simpa [erc165Gas, he] using h_gas
    let g := pre.gasLeft - 269
    have hcall := callee_true (sevm := sevm) (b := pre) (g := g + 55)
      (arg := arg) (r := 0x90) (sel := Sevm.selector sevm) (M := memFp)
      (harg_erc.mpr he)
    have hwrap := wrapper_true (sevm := sevm) (b := pre) (b' := pre) (g := g)
      h_value h_len h_len' (by simpa [arg] using hcall)
    obtain ⟨post, hrun, hg, ho, hs, hl⟩ := hwrap
    have hdispatch := dispatch_supports (sevm := sevm) (b := pre) (g := g + 196)
      h_len h_len' hsel hrun
    rw [pre_eq_St h_stack h_mem (by omega)] at hdispatch
    refine ⟨post, ⟨_, rfl, hdispatch⟩, ?_, ?_, hs, hl⟩
    · simp [erc165Gas, he]
      omega
    · rw [ho]
      simp [B256.eqCheck, Blanc.BeaconDeposit.abiBoolReturn, he]
  · have hne : arg &&& mask4 ≠ ercWord := fun h => he (harg_erc.mp h)
    by_cases hd : Sevm.argWord sevm 0 >>> 224 = Blanc.BeaconDeposit.depositInterfaceId
    · have hroom : 286 ≤ pre.gasLeft := by
        simpa [erc165Gas, he] using h_gas
      let g := pre.gasLeft - 286
      have hcall := callee_false (sevm := sevm) (b := pre) (g := g + 55)
        (arg := arg) (r := 0x90) (sel := Sevm.selector sevm) (M := memFp)
        hne (harg_dep.mpr hd)
      have hwrap := wrapper_false (sevm := sevm) (b := pre) (b' := pre) (g := g)
        h_value h_len h_len' (by simpa [arg] using hcall)
      obtain ⟨post, hrun, hg, ho, hs, hl⟩ := hwrap
      have hdispatch := dispatch_supports (sevm := sevm) (b := pre) (g := g + 213)
        h_len h_len' hsel hrun
      rw [pre_eq_St h_stack h_mem (by omega)] at hdispatch
      refine ⟨post, ⟨_, rfl, hdispatch⟩, ?_, ?_, hs, hl⟩
      · simp [erc165Gas, he]
        omega
      · rw [ho]
        simp [B256.eqCheck, Blanc.BeaconDeposit.abiBoolReturn, he, hd]
    · have hroom : 286 ≤ pre.gasLeft := by
        simpa [erc165Gas, he] using h_gas
      let g := pre.gasLeft - 286
      have hcall := callee_neither (sevm := sevm) (b := pre) (g := g + 55)
        (arg := arg) (r := 0x90) (sel := Sevm.selector sevm) (M := memFp)
        hne (fun h => hd (harg_dep.mp h))
      have hwrap := wrapper_false (sevm := sevm) (b := pre) (b' := pre) (g := g)
        h_value h_len h_len' (by simpa [arg] using hcall)
      obtain ⟨post, hrun, hg, ho, hs, hl⟩ := hwrap
      have hdispatch := dispatch_supports (sevm := sevm) (b := pre) (g := g + 213)
        h_len h_len' hsel hrun
      rw [pre_eq_St h_stack h_mem (by omega)] at hdispatch
      refine ⟨post, ⟨_, rfl, hdispatch⟩, ?_, ?_, hs, hl⟩
      · simp [erc165Gas, he]
        omega
      · rw [ho]
        simp [B256.eqCheck, Blanc.BeaconDeposit.abiBoolReturn, he, hd]
        decide +kernel

end Blanc.Lift.BeaconDeposit
