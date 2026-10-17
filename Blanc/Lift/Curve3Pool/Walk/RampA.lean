import Blanc.Lift.Curve3Pool.Walk.RampKit
import Blanc.Lift.WordWindowMemory

/-!
# `ramp_A(_future_A, _future_time)` on the derivation, with `_A` bridged

The body (`0x4777`): the non-payable guard, `assert msg.sender == self.owner`, the checked
`initial_A_time + MIN_RAMP_TIME ≤ block.timestamp` and `block.timestamp + MIN_RAMP_TIME ≤
_future_time`, `_A()` (inline save of `0x140`), `0 < _future_A < MAX_A`, the change bound (the
checked `_initial_A * MAX_A_CHANGE` or `_future_A * MAX_A_CHANGE`), the four ramp slots written,
and `RampA(_initial_A, _future_A, block.timestamp, _future_time)` logged from `0x1a0`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- The decoded arguments `_future_A`, `_future_time`. -/
abbrev rampFA (sevm : Sevm) : B256 := Sevm.dataWord sevm (Bytes.toB256 [4])
abbrev rampFT (sevm : Sevm) : B256 := Sevm.dataWord sevm (Bytes.toB256 [0x24])

/-- `MIN_RAMP_TIME`, as pushed. -/
abbrev rampMin : B256 := Bytes.toB256 [0x01, 0x51, 0x80]

section

variable {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {s : State}

-- SEGMENT: rampAPre
/-- **`ramp_A` up to the bound checks**: the guards and `_A`. -/
theorem xa_rampA_pre (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (h : XAt sevm post 0x4777 (St b [] (vdMem sevm) G) L) :
    sevm.value = 0 ∧ sevm.caller.toB256 = (b.getStor sevm.currentTarget).get ownerSlot ∧
      ((b.getStor sevm.currentTarget).get initialATimeSlot).toNat + rampMin.toNat < 2 ^ 256 ∧
      ¬ sevm.benvStat.time < (b.getStor sevm.currentTarget).get initialATimeSlot + rampMin ∧
      sevm.benvStat.time.toNat + rampMin.toNat < 2 ^ 256 ∧
      ¬ rampFT sevm < sevm.benvStat.time + rampMin ∧
      ∃ (A : B256) (b2 : Devm) (M : Mem) (G2 : Nat), SloadsOnly sevm b b2 ∧
        aChk s sevm.benvStat.time.toNat = some A.toNat ∧
        XAt sevm post 0x47ff (St b2 [] M G2) L ∧ VW M [(0x140, A)] := by
  have hV : VW (vdMem sevm) [] := ⟨Words.nil _, vyMem_wf Mem.wf_empty _,
    by rw [vyMem_empty_size]⟩
  xs 0x4778 (.reg .callvalue) ri_callvalue  -- 4777 CALLVALUE
  xs 0x4779 (.reg .iszero) ri_iszero  -- 4778 ISZERO
  xs 0x477c (.push [0x47, 0x81] (by decide)) ri_push  -- 4779 PUSH2 0x4781
  xji 0x477d 0x4781 hw
  · xdead  -- 477c JUMPI
  have hval : sevm.value = 0 := eqCheck_ne_zero_eq hw
  clear hw
  xjd 0x4782  -- 4781 JUMPDEST
  xs 0x4784 (.push [0x04] (by decide)) ri_push  -- 4782 PUSH1 0x04
  xw 0x4785 (.reg .sload) ri_sload  -- 4784 SLOAD
  xs 0x4786 (.reg .caller) ri_caller  -- 4785 CALLER
  xs 0x4787 (.reg .eq) ri_eq  -- 4786 EQ
  xs 0x478a (.push [0x47, 0x8f] (by decide)) ri_push  -- 4787 PUSH2 0x478f
  xji 0x478b 0x478f hw
  · xdead  -- 478a JUMPI
  have hown := eqCheck_ne_zero_eq hw
  clear hw
  xjd 0x4790  -- 478f JUMPDEST
  xs 0x4792 (.push [0x08] (by decide)) ri_push  -- 4790 PUSH1 0x08
  xw 0x4793 (.reg .sload) ri_sload  -- 4792 SLOAD
  xs 0x4797 (.push [0x01, 0x51, 0x80] (by decide)) ri_push  -- 4793 PUSH3 0x015180
  xs 0x4798 (.reg (.dup 1)) (ri_dup (by rfl))  -- 4797 DUP2
  xs 0x4799 (.reg (.dup 1)) (ri_dup (by rfl))  -- 4798 DUP2
  xs 0x479a (.reg (.dup 3)) (ri_dup (by rfl))  -- 4799 DUP4
  xs 0x479b (.reg .add) ri_add  -- 479a ADD
  xs 0x479c (.reg .lt) ri_lt  -- 479b LT
  xs 0x479d (.reg .iszero) ri_iszero  -- 479c ISZERO
  xs 0x47a0 (.push [0x47, 0xa5] (by decide)) ri_push  -- 479d PUSH2 0x47a5
  xji 0x47a1 0x47a5 hw
  · xdead  -- 47a0 JUMPI
  have hn0 := (B256.nof_iff_not_add_lt _ _).mpr
    (ltCheck_eq_zero_not_lt (eq_zero_of_iszero_ne_zero hw))
  clear hw
  xjd 0x47a6  -- 47a5 JUMPDEST
  xs 0x47a7 (.reg (.dup 0)) (ri_dup (by rfl))  -- 47a6 DUP1
  xs 0x47a8 (.reg (.dup 2)) (ri_dup (by rfl))  -- 47a7 DUP3
  xs 0x47a9 (.reg .add) ri_add  -- 47a8 ADD
  xs 0x47aa (.reg (.swap 0)) (ri_swap (by rfl))  -- 47a9 SWAP1
  xs 0x47ab (.reg .pop) ri_pop  -- 47aa POP
  xs 0x47ac (.reg (.swap 0)) (ri_swap (by rfl))  -- 47ab SWAP1
  xs 0x47ad (.reg .pop) ri_pop  -- 47ac POP
  xs 0x47ae (.reg .timestamp) ri_timestamp  -- 47ad TIMESTAMP
  xs 0x47af (.reg .lt) ri_lt  -- 47ae LT
  xs 0x47b0 (.reg .iszero) ri_iszero  -- 47af ISZERO
  xs 0x47b3 (.push [0x47, 0xb8] (by decide)) ri_push  -- 47b0 PUSH2 0x47b8
  xji 0x47b4 0x47b8 hw
  · xdead  -- 47b3 JUMPI
  have ht0 := ltCheck_eq_zero_not_lt (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xjd 0x47b9  -- 47b8 JUMPDEST
  xs 0x47ba (.reg .timestamp) ri_timestamp  -- 47b9 TIMESTAMP
  xs 0x47be (.push [0x01, 0x51, 0x80] (by decide)) ri_push  -- 47ba PUSH3 0x015180
  xs 0x47bf (.reg (.dup 1)) (ri_dup (by rfl))  -- 47be DUP2
  xs 0x47c0 (.reg (.dup 1)) (ri_dup (by rfl))  -- 47bf DUP2
  xs 0x47c1 (.reg (.dup 3)) (ri_dup (by rfl))  -- 47c0 DUP4
  xs 0x47c2 (.reg .add) ri_add  -- 47c1 ADD
  xs 0x47c3 (.reg .lt) ri_lt  -- 47c2 LT
  xs 0x47c4 (.reg .iszero) ri_iszero  -- 47c3 ISZERO
  xs 0x47c7 (.push [0x47, 0xcc] (by decide)) ri_push  -- 47c4 PUSH2 0x47cc
  xji 0x47c8 0x47cc hw
  · xdead  -- 47c7 JUMPI
  have hn1 := (B256.nof_iff_not_add_lt _ _).mpr
    (ltCheck_eq_zero_not_lt (eq_zero_of_iszero_ne_zero hw))
  clear hw
  xjd 0x47cd  -- 47cc JUMPDEST
  xs 0x47ce (.reg (.dup 0)) (ri_dup (by rfl))  -- 47cd DUP1
  xs 0x47cf (.reg (.dup 2)) (ri_dup (by rfl))  -- 47ce DUP3
  xs 0x47d0 (.reg .add) ri_add  -- 47cf ADD
  xs 0x47d1 (.reg (.swap 0)) (ri_swap (by rfl))  -- 47d0 SWAP1
  xs 0x47d2 (.reg .pop) ri_pop  -- 47d1 POP
  xs 0x47d3 (.reg (.swap 0)) (ri_swap (by rfl))  -- 47d2 SWAP1
  xs 0x47d4 (.reg .pop) ri_pop  -- 47d3 POP
  xs 0x47d6 (.push [0x24] (by decide)) ri_push  -- 47d4 PUSH1 0x24
  xs 0x47d7 (.reg .calldataload) ri_calldataload  -- 47d6 CALLDATALOAD
  xs 0x47d8 (.reg .lt) ri_lt  -- 47d7 LT
  xs 0x47d9 (.reg .iszero) ri_iszero  -- 47d8 ISZERO
  xs 0x47dc (.push [0x47, 0xe1] (by decide)) ri_push  -- 47d9 PUSH2 0x47e1
  xji 0x47dd 0x47e1 hw
  · xdead  -- 47dc JUMPI
  have ht1 := ltCheck_eq_zero_not_lt (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xjd 0x47e2  -- 47e1 JUMPDEST
  xs 0x47e5 (.push [0x01, 0x40] (by decide)) ri_push  -- 47e2 PUSH2 0x0140
  xlu 0x47e6  -- 47e5 MLOAD
  xs 0x47e8 (.push [0x06] (by decide)) ri_push  -- 47e6 PUSH1 0x06
  cvpc 0x47e9  -- 47e8 PC
  xs 0x47ea (.reg .add) ri_add  -- 47e9 ADD
  xs 0x47ed (.push [0x00, 0xa9] (by decide)) ri_push  -- 47ea PUSH2 0x00a9
  xjmp 0xa9  -- 47ed JUMP
  have ha1 : Abstracts ((afterSload sevm (afterSload sevm b (Bytes.toB256 [4]))
      (Bytes.toB256 [8])).getStor sevm.currentTarget) s := by
    rw [afterSload_getStor, afterSload_getStor]; exact ha
  obtain ⟨A, b2, M, _, hb2, h, hA, hV1⟩ := xa_vAV hc hcode hfork ha1 hV h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xjd 0x47ef  -- 47ee JUMPDEST
  xs 0x47f2 (.push [0x01, 0x80] (by decide)) ri_push  -- 47ef PUSH2 0x0180
  xsw 0x47f3 0x180  -- 47f2 MSTORE
  xs 0x47f6 (.push [0x01, 0x40] (by decide)) ri_push  -- 47f3 PUSH2 0x0140
  xsw 0x47f7 0x140  -- 47f6 MSTORE
  xs 0x47fa (.push [0x01, 0x80] (by decide)) ri_push  -- 47f7 PUSH2 0x0180
  xl 0x47fb 0x180  -- 47fa MLOAD
  xs 0x47fe (.push [0x01, 0x40] (by decide)) ri_push  -- 47fb PUSH2 0x0140
  xsw 0x47ff 0x140  -- 47fe MSTORE
  simp only [getStorVal_eq, afterSload_getStor] at hown hn0 ht0
  refine ⟨hval, by rw [hown]; rfl, hn0, ht0, hn1, ht1, A, b2, _, _,
    (((SloadsOnly.refl).sload _).sload _).trans hb2, hA, h, hV.sub ?_⟩
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
  exact .inl hx

-- SEGMENT: rampAOr
/-- **The change bound's second disjunct** (from `0x485e`, the first disjunct's flag `c` on the
stack): the assertion passes when `c ≠ 0` or `_future_A < _initial_A` with the checked
`_future_A * MAX_A_CHANGE ≥ _initial_A`. -/
theorem xa_rampA_or {b2 : Devm} {M : Mem} {A c : B256}
    (hcode : sevm.code = code) (hV : VW M [(0x140, A)])
    (h : XAt sevm post 0x485e (St b2 [c] M G) L) :
    (c ≠ 0 ∨ ((rampFA sevm).toNat < A.toNat ∧ B256.Nofm (rampFA sevm) (Bytes.toB256 [10]) ∧
      ¬ rampFA sevm * Bytes.toB256 [10] < A)) ∧ ∃ G2, XAt sevm post 0x48b0 (St b2 [] M G2) L := by
  xjd 0x485f  -- 485e JUMPDEST
  xs 0x4860 (.reg .iszero) ri_iszero  -- 485f ISZERO
  xs 0x4863 (.push [0x48, 0x6a] (by decide)) ri_push  -- 4860 PUSH2 0x486a
  xji 0x4864 0x486a hw
  · xs 0x4866 (.push [0x01] (by decide)) ri_push  -- 4864 PUSH1 0x01
    xs 0x4869 (.push [0x48, 0xa6] (by decide)) ri_push  -- 4866 PUSH2 0x48a6
    xjmp 0x48a6  -- 4869 JUMP
    xjd 0x48a7  -- 48a6 JUMPDEST
    xjd 0x48a8  -- 48a7 JUMPDEST
    xs 0x48ab (.push [0x48, 0xb0] (by decide)) ri_push  -- 48a8 PUSH2 0x48b0
    xji 0x48ac 0x48b0 hw2
    · exact absurd hw2 (by decide)
    · exact ⟨.inl (eqCheck_eq_zero hw), _, h⟩
  clear hw
  xjd 0x486b  -- 486a JUMPDEST
  xs 0x486e (.push [0x01, 0x40] (by decide)) ri_push  -- 486b PUSH2 0x0140
  xl 0x486f 0x140  -- 486e MLOAD
  xs 0x4871 (.push [0x04] (by decide)) ri_push  -- 486f PUSH1 0x04
  xs 0x4872 (.reg .calldataload) ri_calldataload  -- 4871 CALLDATALOAD
  xs 0x4873 (.reg .lt) ri_lt  -- 4872 LT
  xs 0x4874 (.reg .iszero) ri_iszero  -- 4873 ISZERO
  xs 0x4877 (.push [0x48, 0xa2] (by decide)) ri_push  -- 4874 PUSH2 0x48a2
  xji 0x4878 0x48a2 hw
  · have hlt := ltCheck_ne_zero (eqCheck_eq_zero hw)
    clear hw
    xs 0x487b (.push [0x01, 0x40] (by decide)) ri_push  -- 4878 PUSH2 0x0140
    xl 0x487c 0x140  -- 487b MLOAD
    xs 0x487e (.push [0x04] (by decide)) ri_push  -- 487c PUSH1 0x04
    xs 0x487f (.reg .calldataload) ri_calldataload  -- 487e CALLDATALOAD
    xs 0x4881 (.push [0x0a] (by decide)) ri_push  -- 487f PUSH1 0x0a
    xs 0x4882 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4881 DUP1
    xs 0x4883 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4882 DUP3
    xs 0x4884 (.reg .mul) ri_mul  -- 4883 MUL
    xs 0x4885 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4884 DUP3
    xs 0x4886 (.reg .iszero) ri_iszero  -- 4885 ISZERO
    xs 0x4887 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4886 DUP3
    xs 0x4888 (.reg (.dup 4)) (ri_dup (by rfl))  -- 4887 DUP5
    xs 0x4889 (.reg (.dup 3)) (ri_dup (by rfl))  -- 4888 DUP4
    xs 0x488a (.reg .div) ri_div  -- 4889 DIV
    xs 0x488b (.reg .eq) ri_eq  -- 488a EQ
    xs 0x488c (.reg .or) ri_or  -- 488b OR
    xs 0x488f (.push [0x48, 0x94] (by decide)) ri_push  -- 488c PUSH2 0x4894
    xji 0x4890 0x4894 hw
    · xdead  -- 488f JUMPI
    have hm := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
    clear hw
    xjd 0x4895  -- 4894 JUMPDEST
    xs 0x4896 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4895 DUP1
    xs 0x4897 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4896 SWAP1
    xs 0x4898 (.reg .pop) ri_pop  -- 4897 POP
    xs 0x4899 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4898 SWAP1
    xs 0x489a (.reg .pop) ri_pop  -- 4899 POP
    xs 0x489b (.reg (.swap 0)) (ri_swap (by rfl))  -- 489a SWAP1
    xs 0x489c (.reg .pop) ri_pop  -- 489b POP
    xs 0x489d (.reg .lt) ri_lt  -- 489c LT
    xs 0x489e (.reg .iszero) ri_iszero  -- 489d ISZERO
    xs 0x48a1 (.push [0x48, 0xa5] (by decide)) ri_push  -- 489e PUSH2 0x48a5
    xjmp 0x48a5  -- 48a1 JUMP
    xjd 0x48a6  -- 48a5 JUMPDEST
    xjd 0x48a7  -- 48a6 JUMPDEST
    xjd 0x48a8  -- 48a7 JUMPDEST
    xs 0x48ab (.push [0x48, 0xb0] (by decide)) ri_push  -- 48a8 PUSH2 0x48b0
    xji 0x48ac 0x48b0 hw
    · xdead  -- 48ab JUMPI
    exact ⟨.inr ⟨hlt, hm, ltCheck_eq_zero_not_lt (eq_zero_of_iszero_ne_zero hw)⟩, _, h⟩
  · xjd 0x48a3  -- 48a2 JUMPDEST
    xs 0x48a5 (.push [0x00] (by decide)) ri_push  -- 48a3 PUSH1 0x00
    xjd 0x48a6  -- 48a5 JUMPDEST
    xjd 0x48a7  -- 48a6 JUMPDEST
    xjd 0x48a8  -- 48a7 JUMPDEST
    xs 0x48ab (.push [0x48, 0xb0] (by decide)) ri_push  -- 48a8 PUSH2 0x48b0
    xji 0x48ac 0x48b0 hw2
    · xdead  -- 48ab JUMPI
    · exact absurd rfl hw2

-- SEGMENT: rampACheck
/-- **The bound checks** (`0x47ff` to `0x48b0`): `0 < _future_A < MAX_A` and the change bound. -/
theorem xa_rampA_check {b2 : Devm} {M : Mem} {A : B256}
    (hcode : sevm.code = code) (hV : VW M [(0x140, A)])
    (h : XAt sevm post 0x47ff (St b2 [] M G) L) :
    0 < (rampFA sevm).toNat ∧ (rampFA sevm).toNat < maxA ∧
      ((A.toNat ≤ (rampFA sevm).toNat ∧ (rampFA sevm).toNat ≤ A.toNat * maxAChange) ∨
        ((rampFA sevm).toNat < A.toNat ∧ A.toNat ≤ (rampFA sevm).toNat * maxAChange)) ∧
      ∃ G2, XAt sevm post 0x48b0 (St b2 [] M G2) L := by
  have h10 : (Bytes.toB256 [10]).toNat = maxAChange := by decide
  xs 0x4801 (.push [0x00] (by decide)) ri_push  -- 47ff PUSH1 0x00
  xs 0x4803 (.push [0x04] (by decide)) ri_push  -- 4801 PUSH1 0x04
  xs 0x4804 (.reg .calldataload) ri_calldataload  -- 4803 CALLDATALOAD
  xs 0x4805 (.reg .gt) ri_gt  -- 4804 GT
  xs 0x4806 (.reg .iszero) ri_iszero  -- 4805 ISZERO
  xs 0x4809 (.push [0x48, 0x16] (by decide)) ri_push  -- 4806 PUSH2 0x4816
  xji 0x480a 0x4816 hw
  swap
  · xjd 0x4817  -- 4816 JUMPDEST
    xs 0x4819 (.push [0x00] (by decide)) ri_push  -- 4817 PUSH1 0x00
    xjd 0x481a  -- 4819 JUMPDEST
    xs 0x481d (.push [0x48, 0x22] (by decide)) ri_push  -- 481a PUSH2 0x4822
    xji 0x481e 0x4822 hw2
    · xdead  -- 481d JUMPI
    · exact absurd rfl hw2
  have hpos := hw
  clear hw
  xs 0x480e (.push [0x0f, 0x42, 0x40] (by decide)) ri_push  -- 480a PUSH3 0x0f4240
  xs 0x4810 (.push [0x04] (by decide)) ri_push  -- 480e PUSH1 0x04
  xs 0x4811 (.reg .calldataload) ri_calldataload  -- 4810 CALLDATALOAD
  xs 0x4812 (.reg .lt) ri_lt  -- 4811 LT
  xs 0x4815 (.push [0x48, 0x19] (by decide)) ri_push  -- 4812 PUSH2 0x4819
  xjmp 0x4819  -- 4815 JUMP
  xjd 0x481a  -- 4819 JUMPDEST
  xs 0x481d (.push [0x48, 0x22] (by decide)) ri_push  -- 481a PUSH2 0x4822
  xji 0x481e 0x4822 hw
  · xdead  -- 481d JUMPI
  have hmax := ltCheck_ne_zero hw
  clear hw
  xjd 0x4823  -- 4822 JUMPDEST
  xs 0x4826 (.push [0x01, 0x40] (by decide)) ri_push  -- 4823 PUSH2 0x0140
  xl 0x4827 0x140  -- 4826 MLOAD
  xs 0x4829 (.push [0x04] (by decide)) ri_push  -- 4827 PUSH1 0x04
  xs 0x482a (.reg .calldataload) ri_calldataload  -- 4829 CALLDATALOAD
  xs 0x482b (.reg .lt) ri_lt  -- 482a LT
  xs 0x482c (.reg .iszero) ri_iszero  -- 482b ISZERO
  xs 0x482d (.reg .iszero) ri_iszero  -- 482c ISZERO
  xs 0x4830 (.push [0x48, 0x5b] (by decide)) ri_push  -- 482d PUSH2 0x485b
  xji 0x4831 0x485b hw
  · have hge := hw
    clear hw
    xs 0x4834 (.push [0x01, 0x40] (by decide)) ri_push  -- 4831 PUSH2 0x0140
    xl 0x4835 0x140  -- 4834 MLOAD
    xs 0x4837 (.push [0x0a] (by decide)) ri_push  -- 4835 PUSH1 0x0a
    xs 0x4838 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4837 DUP1
    xs 0x4839 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4838 DUP3
    xs 0x483a (.reg .mul) ri_mul  -- 4839 MUL
    xs 0x483b (.reg (.dup 2)) (ri_dup (by rfl))  -- 483a DUP3
    xs 0x483c (.reg .iszero) ri_iszero  -- 483b ISZERO
    xs 0x483d (.reg (.dup 2)) (ri_dup (by rfl))  -- 483c DUP3
    xs 0x483e (.reg (.dup 4)) (ri_dup (by rfl))  -- 483d DUP5
    xs 0x483f (.reg (.dup 3)) (ri_dup (by rfl))  -- 483e DUP4
    xs 0x4840 (.reg .div) ri_div  -- 483f DIV
    xs 0x4841 (.reg .eq) ri_eq  -- 4840 EQ
    xs 0x4842 (.reg .or) ri_or  -- 4841 OR
    xs 0x4845 (.push [0x48, 0x4a] (by decide)) ri_push  -- 4842 PUSH2 0x484a
    xji 0x4846 0x484a hw
    · xdead  -- 4845 JUMPI
    have hm := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
    clear hw
    xjd 0x484b  -- 484a JUMPDEST
    xs 0x484c (.reg (.dup 0)) (ri_dup (by rfl))  -- 484b DUP1
    xs 0x484d (.reg (.swap 0)) (ri_swap (by rfl))  -- 484c SWAP1
    xs 0x484e (.reg .pop) ri_pop  -- 484d POP
    xs 0x484f (.reg (.swap 0)) (ri_swap (by rfl))  -- 484e SWAP1
    xs 0x4850 (.reg .pop) ri_pop  -- 484f POP
    xs 0x4851 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4850 SWAP1
    xs 0x4852 (.reg .pop) ri_pop  -- 4851 POP
    xs 0x4854 (.push [0x04] (by decide)) ri_push  -- 4852 PUSH1 0x04
    xs 0x4855 (.reg .calldataload) ri_calldataload  -- 4854 CALLDATALOAD
    xs 0x4856 (.reg .gt) ri_gt  -- 4855 GT
    xs 0x4857 (.reg .iszero) ri_iszero  -- 4856 ISZERO
    xs 0x485a (.push [0x48, 0x5e] (by decide)) ri_push  -- 4857 PUSH2 0x485e
    xjmp 0x485e  -- 485a JUMP
    obtain ⟨hor, _, h⟩ := xa_rampA_or hcode hV h
    refine ⟨toNat_lt_of_iszero_gt_eq_zero hpos, hmax, ?_, _, h⟩
    rcases hor with hor | ⟨hl, hm', hn⟩
    · refine .inl ⟨?_, ?_⟩
      · have e := ltCheck_eq_zero_not_lt (eq_zero_of_iszero2_eq_zero hge)
        rw [B256.lt_iff_toNat_lt_toNat] at e
        exact Nat.le_of_not_lt e
      · have e := toNat_le_of_iszero_gt_ne_zero hor
        rwa [B256.toNat_mul_eq_of_nofm hm, h10] at e
    · rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_mul_eq_of_nofm hm', h10] at hn
      exact .inr ⟨hl, Nat.le_of_not_lt hn⟩
  · have hlt := hw
    clear hw
    xjd 0x485c  -- 485b JUMPDEST
    xs 0x485e (.push [0x00] (by decide)) ri_push  -- 485c PUSH1 0x00
    obtain ⟨hor, _, h⟩ := xa_rampA_or hcode hV h
    refine ⟨toNat_lt_of_iszero_gt_eq_zero hpos, hmax, ?_, _, h⟩
    rcases hor with hor | ⟨hl, hm', hn⟩
    · exact absurd rfl hor
    · rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_mul_eq_of_nofm hm', h10] at hn
      exact .inr ⟨hl, Nat.le_of_not_lt hn⟩

/-- The `RampA` topic as pushed. -/
theorem rampA_topic : Bytes.toB256 [0xa2, 0xb7, 0x1e, 0xc6, 0xdf, 0x94, 0x93, 0x00, 0xb5, 0x9a,
    0xab, 0x36, 0xb5, 0x5e, 0x18, 0x96, 0x97, 0xb7, 0x50, 0x11, 0x9d, 0xd3, 0x49, 0xfc, 0xfa, 0x8c,
    0x0f, 0x77, 0x9e, 0x83, 0xc2, 0x54] = topicRampA := by decide

-- SEGMENT: rampATail
/-- **The writes and the log** (`0x48b0` to the `STOP`). -/
theorem xa_rampA_tail {b2 : Devm} {M : Mem} {A : B256}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hV : VW M [(0x140, A)]) (h : XAt sevm post 0x48b0 (St b2 [] M G) L) :
    L = [] ∧
      (∀ x, (post.getStor sevm.currentTarget).get x =
        (((((b2.getStor sevm.currentTarget).set initialASlot A).set futureASlot (rampFA sevm)).set
          initialATimeSlot sevm.benvStat.time).set futureATimeSlot (rampFT sevm)).get x) ∧
      post.logs = b2.logs ++ [⟨sevm.currentTarget, [topicRampA], A.toBytes ++
        (rampFA sevm).toBytes ++ sevm.benvStat.time.toBytes ++ (rampFT sevm).toBytes⟩] ∧
      post.output = b2.output := by
  xjd 0x48b1  -- 48b0 JUMPDEST
  xs 0x48b4 (.push [0x01, 0x40] (by decide)) ri_push  -- 48b1 PUSH2 0x0140
  xl 0x48b5 0x140  -- 48b4 MLOAD
  xs 0x48b7 (.push [0x06] (by decide)) ri_push  -- 48b5 PUSH1 0x06
  xw 0x48b8 (.reg .sstore) ri_sstore  -- 48b7 SSTORE
  xs 0x48ba (.push [0x04] (by decide)) ri_push  -- 48b8 PUSH1 0x04
  xs 0x48bb (.reg .calldataload) ri_calldataload  -- 48ba CALLDATALOAD
  xs 0x48bd (.push [0x07] (by decide)) ri_push  -- 48bb PUSH1 0x07
  xw 0x48be (.reg .sstore) ri_sstore  -- 48bd SSTORE
  xs 0x48bf (.reg .timestamp) ri_timestamp  -- 48be TIMESTAMP
  xs 0x48c1 (.push [0x08] (by decide)) ri_push  -- 48bf PUSH1 0x08
  xw 0x48c2 (.reg .sstore) ri_sstore  -- 48c1 SSTORE
  xs 0x48c4 (.push [0x24] (by decide)) ri_push  -- 48c2 PUSH1 0x24
  xs 0x48c5 (.reg .calldataload) ri_calldataload  -- 48c4 CALLDATALOAD
  xs 0x48c7 (.push [0x09] (by decide)) ri_push  -- 48c5 PUSH1 0x09
  xw 0x48c8 (.reg .sstore) ri_sstore  -- 48c7 SSTORE
  xs 0x48cb (.push [0x01, 0x40] (by decide)) ri_push  -- 48c8 PUSH2 0x0140
  xl 0x48cc 0x140  -- 48cb MLOAD
  xs 0x48cf (.push [0x01, 0xa0] (by decide)) ri_push  -- 48cc PUSH2 0x01a0
  have hlogwf := hV.wf
  xsw 0x48d0 0x1a0  -- 48cf MSTORE
  xs 0x48d2 (.push [0x04] (by decide)) ri_push  -- 48d0 PUSH1 0x04
  xs 0x48d3 (.reg .calldataload) ri_calldataload  -- 48d2 CALLDATALOAD
  xs 0x48d6 (.push [0x01, 0xc0] (by decide)) ri_push  -- 48d3 PUSH2 0x01c0
  xsw 0x48d7 0x1c0  -- 48d6 MSTORE
  xs 0x48d8 (.reg .timestamp) ri_timestamp  -- 48d7 TIMESTAMP
  xs 0x48db (.push [0x01, 0xe0] (by decide)) ri_push  -- 48d8 PUSH2 0x01e0
  xsw 0x48dc 0x1e0  -- 48db MSTORE
  xs 0x48de (.push [0x24] (by decide)) ri_push  -- 48dc PUSH1 0x24
  xs 0x48df (.reg .calldataload) ri_calldataload  -- 48de CALLDATALOAD
  xs 0x48e2 (.push [0x02, 0x00] (by decide)) ri_push  -- 48df PUSH2 0x0200
  xsw 0x48e3 0x200  -- 48e2 MSTORE
  xs 0x4904 (.push [0xa2, 0xb7, 0x1e, 0xc6, 0xdf, 0x94, 0x93, 0x00, 0xb5, 0x9a, 0xab, 0x36, 0xb5, 0x5e, 0x18, 0x96, 0x97, 0xb7, 0x50, 0x11, 0x9d, 0xd3, 0x49, 0xfc, 0xfa, 0x8c, 0x0f, 0x77, 0x9e, 0x83, 0xc2, 0x54] (by decide)) ri_push  -- 48e3 PUSH32
  xs 0x4906 (.push [0x80] (by decide)) ri_push  -- 4904 PUSH1 0x80
  xs 0x4909 (.push [0x01, 0xa0] (by decide)) ri_push  -- 4906 PUSH2 0x01a0
  have hdata := Mem.read_four_word_writes hlogwf 0x1a0 A (rampFA sevm) sevm.benvStat.time
    (rampFT sevm)
  replace h := xa_nextAt (n := .reg (.log 1)) (pc' := 0x490a) (atN hcode (by kernel_rfl))
    (by nofun) (by rfl) h
  obtain ⟨_, s, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_log1 s
  clear s
  obtain ⟨hrun, hL⟩ := xa_halt (l := .stop) (atL hcode (by kernel_rfl)) h
  have hp := (Except.ok.inj hrun).symm
  subst hp hL
  refine ⟨rfl, fun x => ?_, ?_, ?_⟩
  · simp only [St]
    rw [← getStorVal_eq, Devm.getStorVal_setMach, getStorVal_eq, getStor_addLog,
      afterSstore_getStor_self, afterSstore_getStor_self, afterSstore_getStor_self,
      afterSstore_getStor_self, slot_06, slot_07, slot_08, slot_09]
  · simp only [St, Devm.setMach_logs]
    rw [logs_addLog, afterSstore_logs, afterSstore_logs, afterSstore_logs, afterSstore_logs,
      rampA_topic, show (Bytes.toB256 [1, 160]).toNat = 0x1a0 from rfl,
      show (Bytes.toB256 [128]).toNat = 128 from rfl]
    exact congrArg (fun z => b2.logs ++ [⟨sevm.currentTarget, [topicRampA], z⟩]) hdata
  · simp only [St, Devm.setMach_output]
    rw [output_addLog, afterSstore_output, afterSstore_output, afterSstore_output,
      afterSstore_output]

/-- **`ramp_A`'s raw effect**, given the certificate's checkedness. -/
theorem rampA_raw_of (hc : Cert.CheckedM code cert mems true) {pre : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRampA)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨_, hx⟩ := xa_vd_rampA hcode hlen hcd hsel hx
  obtain ⟨hval, hown, hn0, ht0, hn1, ht1, A, b2, M, G2, hb2, hA, hx, hV⟩ :=
    xa_rampA_pre hc hcode hfork hck.abs hx
  obtain ⟨hpos, hmax, hbd, _, hx⟩ := xa_rampA_check hcode hV hx
  obtain ⟨hL, hstor, hlogs, hout⟩ := xa_rampA_tail hcode hfork hV hx
  have hdec : decodeCall sevm = .rampA (rampFA sevm).toNat (rampFT sevm).toNat :=
    decodeCall_at (k := 11) rfl hsel hlen
  have hmin : rampMin.toNat = minRampTime := by decide
  have hown' : (quietEnv sevm).caller = s.owner := by
    show sevm.caller.toB256.toNat = _
    rw [hown, hck.abs.owner]
  have ht : (quietEnv sevm).time = sevm.benvStat.time.toNat := rfl
  have hiat : ((pre.getStor sevm.currentTarget).get initialATimeSlot).toNat = s.initialATime :=
    hck.abs.initialATime
  rw [B256.lt_iff_toNat_lt_toNat] at ht0 ht1
  have hst : rampA s (quietEnv sevm) (rampFA sevm).toNat (rampFT sevm).toNat =
      some ⟨{ s with initialA := A.toNat, futureA := (rampFA sevm).toNat,
                     initialATime := sevm.benvStat.time.toNat,
                     futureATime := (rampFT sevm).toNat }, none,
        [.rampA A.toNat (rampFA sevm).toNat sevm.benvStat.time.toNat (rampFT sevm).toNat], []⟩ := by
    unfold rampA
    simp only [Option.bind_eq_bind]
    rw [req, ite_eq_left hown', Option.bind_some, ← hiat, ← hmin, chkAdd_toNat_of_lt hn0,
      Option.bind_some, req, ite_eq_left (show (quietEnv sevm).time ≥ _ from Nat.le_of_not_lt ht0), Option.bind_some, ht,
      chkAdd_toNat_of_lt hn1, Option.bind_some, req, ite_eq_left (Nat.le_of_not_lt ht1),
      Option.bind_some, hA, Option.bind_some, req, ite_eq_left ⟨hpos, hmax⟩, Option.bind_some, req,
      ite_eq_left hbd, Option.bind_some]
  have hstep : step s (quietEnv sevm) (decodeCall sevm) =
      rampA s (quietEnv sevm) (rampFA sevm).toNat (rampFT sevm).toNat := by
    rw [hdec]
    show (if (quietEnv sevm).value = 0 then rampA s (quietEnv sevm) _ _ else none) = _
    rw [show (quietEnv sevm).value = 0 by show sevm.value.toNat = 0; rw [hval]; rfl,
      ite_eq_left rfl]
  rw [hst] at hstep
  refine ⟨quietEnv sevm, _, hstep, ?_⟩
  · refine rawEffect_noChild hL (ramp_storEffect (by rw [hdec]; rfl)
      (fun x => by rw [hstor, hb2.getStor]; rfl) rfl rfl rfl rfl) ?_
      (by rw [hout, hb2.output]; rfl) ?_
    · rw [hlogs, hb2.logs]
      simp only [List.map_cons, List.map_nil, eventLog, word, toB256_toNat]
    · rfl

end

end Blanc.Lift.Curve3Pool
