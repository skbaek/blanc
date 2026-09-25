import Blanc.Lift.Weth9.Booked
import Blanc.Lift.Silent
import Blanc.AddressSlotProofs

namespace Blanc.Lift

open Jaune
open Blanc
open Weth9

private def chain : List Ninst → SFunc → SFunc
  | [], f => f
  | n :: ns, f => .next n (chain ns f)

private theorem run_chain_prefix {fs : List SFunc} {sevm : Sevm}
    (xs ys : List Ninst) {devm : Devm} {f : SFunc} {o : Outcome}
    (run : SFunc.Run fs sevm devm (chain (xs ++ ys) f) o) :
    ∃ mid, Line.Run sevm devm xs mid ∧
      SFunc.Run fs sevm mid (chain ys f) o := by
  induction xs generalizing devm with
  | nil => exact ⟨devm, .nil, run⟩
  | cons n ns ih =>
      change SFunc.Run fs sevm devm (.next n (chain (ns ++ ys) f)) o at run
      cases run with
      | next hstep hrest =>
          rcases ih hrest with ⟨mid, hline, hrun⟩
          exact ⟨mid, .cons hstep hline, hrun⟩

private def depositPre : List Ninst :=
  [.reg .callvalue, .push [0x03] (by decide), .push [0x00] (by decide),
   .reg .caller,
   .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
     0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
   .reg .and,
   .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
     0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
   .reg .and, .reg (.dup 1), .reg .mstore,
   .push [0x20] (by decide), .reg .add, .reg (.swap 0), .reg (.dup 1),
   .reg .mstore, .push [0x20] (by decide), .reg .add,
   .push [0x00] (by decide), .reg .keccak256, .push [0x00] (by decide),
   .reg (.dup 2), .reg (.dup 2), .reg .sload, .reg .add,
   .reg (.swap 2), .reg .pop, .reg .pop, .reg (.dup 1), .reg (.swap 0)]

private def depositPost : List Ninst :=
  [.reg .pop, .reg .caller,
   .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
     0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
   .reg .and,
   .push [0xe1, 0xff, 0xfc, 0xc4, 0x92, 0x3d, 0x04, 0xb5, 0x59, 0xf4,
     0xd2, 0x9a, 0x8b, 0xfc, 0x6c, 0xda, 0x04, 0xeb, 0x5b, 0x0d, 0x3c,
     0x46, 0x07, 0x51, 0xc2, 0x40, 0x2c, 0x5c, 0x5c, 0xc9, 0x10, 0x9c] (by decide),
   .reg .callvalue, .push [0x40] (by decide), .reg .mload,
   .reg (.dup 0), .reg (.dup 2), .reg (.dup 1), .reg .mstore,
   .push [0x20] (by decide), .reg .add, .reg (.swap 1), .reg .pop, .reg .pop,
   .push [0x40] (by decide), .reg .mload, .reg (.dup 0), .reg (.swap 1),
   .reg .sub, .reg (.swap 0), .reg (.log 2)]

private theorem deposit_tree_eq :
    t_0440_c1 = .dest (chain (depositPre ++ [Ninst.sstore] ++ depositPost) .ret) := by
  simp [t_0440_c1, depositPre, depositPost, chain]

private theorem split_deposit_run {fs : List SFunc} {sevm : Sevm}
    {devm : Devm} {o : Outcome}
    (run : SFunc.Run fs sevm devm t_0440_c1 o) :
    ∃ d0 d1 d2 d3 dret,
      Devm.Burn devm d0 ∧
      Line.Run sevm d0 depositPre d1 ∧
      Ninst.Run sevm d1 Ninst.sstore d2 ∧
      Line.Run sevm d2 depositPost d3 ∧
      Devm.PopBurn [dret] d3 (Outcome.devm o) := by
  rw [deposit_tree_eq] at run
  cases run with
  | dest burn rest =>
      rcases run_chain_prefix depositPre ([Ninst.sstore] ++ depositPost) rest with
        ⟨d1, hpre, rest⟩
      rcases run_chain_prefix [Ninst.sstore] depositPost rest with
        ⟨d2, hsstore, rest⟩
      rcases run_chain_prefix depositPost [] rest with
        ⟨d3, hpost, rest⟩
      cases rest with
      | ret d hret =>
          exact ⟨_, d1, d2, d3, d, burn, hpre, of_run_singleton hsstore, hpost, hret⟩

/-
private def depositA : List Ninst :=
  [.reg .callvalue, .push [0x03] (by decide), .push [0x00] (by decide),
   .reg .caller,
   .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
     0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
   .reg .and,
   .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
     0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
   .reg .and]
private def depositB : List Ninst := [.reg (.dup 1), .reg .mstore]
private def depositC : List Ninst :=
  [.push [0x20] (by decide), .reg .add, .reg (.swap 0), .reg (.dup 1), .reg .mstore]
private def depositD : List Ninst :=
  [.push [0x20] (by decide), .reg .add, .push [0x00] (by decide), .reg .keccak256]
private def depositE : List Ninst :=
  [.push [0x00] (by decide), .reg (.dup 2), .reg (.dup 2), .reg .sload, .reg .add,
   .reg (.swap 2), .reg .pop, .reg .pop, .reg (.dup 1), .reg (.swap 0)]

private theorem depositPre_split :
    depositPre = depositA ++ depositB ++ depositC ++ depositD ++ depositE := by
  simp [depositA, depositB, depositC, depositD, depositE, depositPre]

private def depositA1 : List Ninst :=
  [.reg .callvalue, .push [0x03] (by decide), .push [0x00] (by decide), .reg .caller]
private def depositA2 : List Ninst :=
  [.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
     0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
   .reg .and,
   .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
     0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
   .reg .and]

private theorem depositA_split : depositA = depositA1 ++ depositA2 := by
  simp [depositA, depositA1, depositA2]

private def depositA2a : List Ninst :=
  [.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
     0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
   .reg .and]
private def depositA2b : List Ninst :=
  [.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
     0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
   .reg .and]

private theorem depositA2_split : depositA2 = depositA2a ++ depositA2b := by
  simp [depositA2, depositA2a, depositA2b]

private theorem caller_mask (a : Adr) :
    (a.toB256 &&& Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) =
      a.toB256 := by
  have hmask : Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]
      = (~~~ addressMask) := by decide
  rw [hmask, B256.and_comm]
  exact addressSlotReadWord_toB256 a

private theorem deposit_segment_A2a {sevm : Sevm} {s s' : Devm} {xs : Stack}
    (hxs : sevm.caller.toB256 :: 0 :: (3 : B256) :: sevm.value :: xs <<+ s.stack)
    (run : Line.Run sevm s depositA2a s') :
    sevm.caller.toB256 :: 0 :: (3 : B256) :: sevm.value :: xs <<+ s'.stack ∧
      s'.memory = s.memory := by
  revert run
  line_execute 1
  have r₁ := of_run_singleton h₁
  have hp1 := prefix_of_push (of_run_pushB256 r₁) hxs
  line_execute 1
  have r₂ := of_run_singleton h₂
  intro hrest
  cases hrest
  have hp2 : sevm.caller.toB256 :: 0 :: (3 : B256) :: sevm.value :: xs <<+ s'.stack := by
    simpa [caller_mask] using prefix_of_and r₂ hp1
  exact ⟨hp2, (Line.of_inv Devm.memory (by line_inv) h₂).symm⟩

private theorem deposit_segment_A2b {sevm : Sevm} {s s' : Devm} {xs : Stack}
    (hxs : sevm.caller.toB256 :: 0 :: (3 : B256) :: sevm.value :: xs <<+ s.stack)
    (run : Line.Run sevm s depositA2b s') :
    sevm.caller.toB256 :: 0 :: (3 : B256) :: sevm.value :: xs <<+ s'.stack ∧
      s'.memory = s.memory := by
  revert run
  line_execute 1
  have r₁ := of_run_singleton h₁
  have hp1 := prefix_of_push (of_run_pushB256 r₁) hxs
  line_execute 1
  have r₂ := of_run_singleton h₂
  intro hrest
  cases hrest
  have hp2 : sevm.caller.toB256 :: 0 :: (3 : B256) :: sevm.value :: xs <<+ s'.stack := by
    simpa [caller_mask] using prefix_of_and r₂ hp1
  exact ⟨hp2, (Line.of_inv Devm.memory (by line_inv) h₂).symm⟩

private theorem deposit_segment_A1 {sevm : Sevm} {s s' : Devm} {xs : Stack}
    (hxs : xs <<+ s.stack) (run : Line.Run sevm s depositA1 s') :
    sevm.caller.toB256 :: 0 :: (3 : B256) :: sevm.value :: xs <<+ s'.stack ∧
      s'.memory = s.memory := by
  revert run
  line_execute 4
  intro hrest
  cases hrest
  have hp : sevm.caller.toB256 :: 0 :: (3 : B256) :: sevm.value :: xs <<+ s'.stack := by
    generalize_line_prefix
  exact ⟨hp, (Line.of_inv Devm.memory (by line_inv) h₁).symm⟩

private theorem deposit_segment_A2 {sevm : Sevm} {s s' : Devm} {xs : Stack}
    (hxs : sevm.caller.toB256 :: 0 :: (3 : B256) :: sevm.value :: xs <<+ s.stack)
    (run : Line.Run sevm s depositA2 s') :
    sevm.caller.toB256 :: 0 :: (3 : B256) :: sevm.value :: xs <<+ s'.stack ∧
      s'.memory = s.memory := by
  rw [depositA2_split] at run
  rcases of_run_append depositA2a run with ⟨sm, h1, h2⟩
  rcases deposit_segment_A2a hxs h1 with ⟨hp, hm⟩
  rcases deposit_segment_A2b hp h2 with ⟨hp', hm'⟩
  exact ⟨hp', hm'.trans hm⟩

private theorem deposit_segment_A {sevm : Sevm} {s s' : Devm} {xs : Stack}
    (hxs : xs <<+ s.stack) (run : Line.Run sevm s depositA s') :
    sevm.caller.toB256 :: 0 :: (3 : B256) :: sevm.value :: xs <<+ s'.stack ∧
      s'.memory = s.memory := by
  rw [depositA_split] at run
  rcases of_run_append depositA1 run with ⟨sm, h1, h2⟩
  rcases deposit_segment_A1 hxs h1 with ⟨hp, hm⟩
  rcases deposit_segment_A2 hp h2 with ⟨hp', hm'⟩
  exact ⟨hp', hm'.trans hm⟩
-/

private theorem deposit_pre_stack {sevm : Sevm} {s s' : Devm}
    (run : Line.Run sevm s depositPre s') :
    ∃ xs : Stack,
      xs <<+ s.stack ∧
      balSlot sevm.caller ::
          (s.getStorVal sevm.currentTarget (balSlot sevm.caller) + sevm.value) :: xs <<+ s'.stack ∧
      (((s.memory.write 0 sevm.caller.toB256.toBytes).write 32 (3 : B256).toBytes).read 0 64).1 =
        sevm.caller.toB256.toBytes ++ (3 : B256).toBytes := by
  revert run
  sorry
/-
  have hp5raw :
      [((sevm.caller.toB256 &&& Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff]) &&& Bytes.toB256 [0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]), 0, 3, sevm.value]
        <<+ s₂.stack := by sorry
  have hmask : Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]
      = (~~~ addressMask) := by decide
  have hcaller_mask :
      (sevm.caller.toB256 &&& Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff]) = sevm.caller.toB256 := by
    rw [hmask, B256.and_comm]
    exact addressSlotReadWord_toB256 sevm.caller
  have hp5 : sevm.caller.toB256 :: 0 :: (3 : B256) :: sevm.value :: s.stack <<+ s₂.stack := by
    simpa [hcaller_mask] using hp5raw
  line_execute 1
  have hp6 : 0 :: sevm.caller.toB256 :: 0 :: (3 : B256) :: sevm.value :: s.stack <<+ s₃.stack := by
    generalize_line_prefix
  line_execute 1
  have hm1 := prefix_of_mstore_val (of_run_singleton h₄) hp6
  have hp7 : 0 :: (3 : B256) :: sevm.value :: s.stack <<+ s₄.stack := hm1.1
  line_execute 4
  have hp8 : (32 : B256) :: (3 : B256) :: (32 : B256) :: sevm.value :: s.stack <<+ s₅.stack := by
    generalize_line_prefix
  line_execute 1
  have hm2 := prefix_of_mstore_val (of_run_singleton h₆) hp8
  have hp9 : (32 : B256) :: sevm.value :: s.stack <<+ s₆.stack := hm2.1
  line_execute 3
  have hp10 : 0 :: (64 : B256) :: sevm.value :: s.stack <<+ s₇.stack := by
    generalize_line_prefix
  line_execute 1
  have hm3 := prefix_of_keccak256_val (of_run_singleton h₈) hp10
  have hp11 := hm3.1
 -/
/-
  have hmask : Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]
      = (~~~ addressMask) := by decide
  have hcaller_mask :
      (sevm.caller.toB256 &&& Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff]) = sevm.caller.toB256 := by
    rw [hmask, B256.and_comm]
    exact addressSlotReadWord_toB256 sevm.caller
  have hp6 : sevm.caller.toB256 :: 0 :: (3 : B256) :: sevm.value :: s.stack <<+ s₃.stack := by
    simpa [hcaller_mask] using prefix_of_and r5 hp5
  line_execute 1
  have r6 := of_run_singleton h₄
  have hp7 := prefix_of_push (of_run_pushB256 r6) hp6
  line_execute 1
  have r7 := of_run_singleton h₅
  have hp8 : sevm.caller.toB256 :: 0 :: (3 : B256) :: sevm.value :: s.stack <<+ s₅.stack := by
    simpa [hcaller_mask] using prefix_of_and r7 hp7
  line_execute 1
  have r8 := of_run_singleton h₆
  have hp9 : 0 :: sevm.caller.toB256 :: 0 :: (3 : B256) :: sevm.value :: s.stack <<+ s₆.stack :=
    prefix_of_dup_val r8 (by decide) hp8
  line_execute 1
  have r9 := of_run_singleton h₇
  have hm1 := prefix_of_mstore_val r9 hp9
  have hp10 : 0 :: (3 : B256) :: sevm.value :: s.stack <<+ s₇.stack := hm1.1
  line_execute 3
  have hp11 : (3 : B256) :: (32 : B256) :: sevm.value :: s.stack <<+ s₈.stack := by
    generalize_line_prefix
  line_execute 1
  have r10 := of_run_singleton h₉
  have hp12 : (32 : B256) :: (3 : B256) :: (32 : B256) :: sevm.value :: s.stack <<+ s₉.stack :=
    prefix_of_dup_val r10 (by decide) hp11
  line_execute 1
  have r11 := of_run_singleton h₁₀
  have hm2 := prefix_of_mstore_val r11 hp12
  have hp13 : (32 : B256) :: sevm.value :: s.stack <<+ s₁₀.stack := hm2.1
  line_execute 3
  have hp14 : 0 :: (32 : B256) :: sevm.value :: s.stack <<+ s₁₁.stack := by
    generalize_line_prefix
  line_execute 1
  have r12 := of_run_singleton h₁₂
  have hm3 := prefix_of_keccak256_val r12 hp14
  have hp15 := hm3.1
  line_execute 1
  have hp16 : (0 : B256) :: (balSlot sevm.caller) :: sevm.value :: s.stack <<+ s₁₃.stack := by
    simpa [balSlot, mapSlot] using
      (prefix_of_push (of_run_pushB256 (of_run_singleton h₁₃)) hp15)
  line_execute 2
  have hp17 : (balSlot sevm.caller) :: 0 :: 0 :: (balSlot sevm.caller) ::
      sevm.value :: s.stack <<+ s₁₄.stack := by
    generalize_line_prefix
  line_execute 1
  rcases prefix_of_sload (of_run_singleton h₁₅) hp17 with ⟨old, hp18, hold⟩
  line_execute 1
  have hp19 : (old + sevm.value) :: 0 :: (balSlot sevm.caller) ::
      sevm.value :: s.stack <<+ s₁₆.stack := by
    simpa using prefix_of_add (of_run_singleton h₁₆) hp18
  line_execute 1
  have hp20 : (balSlot sevm.caller) :: 0 :: (old + sevm.value) ::
      sevm.value :: s.stack <<+ s₁₇.stack := by
    generalize_line_prefix
  line_execute 2
  have hp21 : (old + sevm.value) :: sevm.value :: s.stack <<+ s₁₈.stack := by
    generalize_line_prefix
  line_execute 1
  have hp22 : sevm.value :: (old + sevm.value) :: sevm.value :: s.stack <<+ s₁₉.stack := by
    generalize_line_prefix
  line_execute 1
  have hp23 : (old + sevm.value) :: sevm.value :: sevm.value :: s.stack <<+ s₂₀.stack := by
    generalize_line_prefix
  intro hlast
  cases hlast
  sorry
 -/
/-
  revert run
  line_execute 1
  line_execute 1
  line_execute 1
  line_execute 1
  line_execute 1
  line_execute 1
  line_execute 1
  line_execute 1
  line_execute 1
  line_execute 1
  line_execute 1
  line_execute 1
  line_execute 1
  line_execute 1
  line_execute 1
  line_execute 1
  line_execute 1
  line_execute 1
  line_execute 1
  line_execute 1
  line_execute 1
  line_execute 1
  line_execute 1
  line_execute 1
  line_execute 1
  line_execute 1
  line_execute 1
  line_execute 1
  line_execute 1
  intro hlast
  cases hlast
  have r0 := of_run_singleton h₁
  have r1 := of_run_singleton h₂
  have r2 := of_run_singleton h₃
  have r3 := of_run_singleton h₄
  have r4 := of_run_singleton h₅
  have r5 := of_run_singleton h₆
  have r6 := of_run_singleton h₇
  have r7 := of_run_singleton h₈
  have r8 := of_run_singleton h₉
  have r9 := of_run_singleton h₁₀
  have r10 := of_run_singleton h₁₁
  have r11 := of_run_singleton h₁₂
  have r12 := of_run_singleton h₁₃
  have r13 := of_run_singleton h₁₄
  have r14 := of_run_singleton h₁₅
  have r15 := of_run_singleton h₁₆
  have r16 := of_run_singleton h₁₇
  have r17 := of_run_singleton h₁₈
  have r18 := of_run_singleton h₁₉
  have r19 := of_run_singleton h₂₀
  have r20 := of_run_singleton h₂₁
  have r21 := of_run_singleton h₂₂
  have r22 := of_run_singleton h₂₃
  have r23 := of_run_singleton h₂₄
  have r24 := of_run_singleton h₂₅
  have r25 := of_run_singleton h₂₆
  have r26 := of_run_singleton h₂₇
  have r27 := of_run_singleton h₂₈
  have r28 := of_run_singleton h₂₉
  have hmask : Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]
      = (~~~ addressMask) := by decide
  have hcaller_mask :
      (sevm.caller.toB256 &&& Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff]) = sevm.caller.toB256 := by
    rw [hmask, B256.and_comm]
    exact addressSlotReadWord_toB256 sevm.caller
  have hp0 : s.stack <<+ s.stack := ⟨[], by simp⟩
  have hp1 : sevm.value :: s.stack <<+ s₁.stack :=
    prefix_of_push (of_run_callvalue r0) hp0
  have hp2 : (3 : B256) :: sevm.value :: s.stack <<+ s₂.stack :=
    prefix_of_push (of_run_pushB256 r1) hp1
  have hp3 : 0 :: (3 : B256) :: sevm.value :: s.stack <<+ s₃.stack :=
    prefix_of_push (of_run_pushB256 r2) hp2
  have hp4 : sevm.caller.toB256 :: 0 :: (3 : B256) :: sevm.value :: s.stack <<+ s₄.stack :=
    prefix_of_push (of_run_caller r3) hp3
  have hp5 : Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] ::
      sevm.caller.toB256 :: 0 :: (3 : B256) :: sevm.value :: s.stack <<+ s₅.stack :=
    prefix_of_push (of_run_pushB256 r4) hp4
  have hp6 : sevm.caller.toB256 :: 0 :: (3 : B256) :: sevm.value :: s.stack <<+ s₆.stack := by
    simpa [hcaller_mask] using prefix_of_and r5 hp5
  have hp7 : Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] ::
      sevm.caller.toB256 :: 0 :: (3 : B256) :: sevm.value :: s.stack <<+ s₇.stack :=
    prefix_of_push (of_run_pushB256 r6) hp6
  have hp8 : sevm.caller.toB256 :: 0 :: (3 : B256) :: sevm.value :: s.stack <<+ s₈.stack := by
    simpa [hcaller_mask] using prefix_of_and r7 hp7
  have hp9 : 0 :: sevm.caller.toB256 :: 0 :: (3 : B256) :: sevm.value :: s.stack <<+ s₉.stack :=
    prefix_of_dup_val r8 (by decide) hp8
  have hm1 := prefix_of_mstore_val r9 hp9
  have hp10 : 0 :: (3 : B256) :: sevm.value :: s.stack <<+ s₁₀.stack := hm1.1
  have hp11 : 32 :: 0 :: (3 : B256) :: sevm.value :: s.stack <<+ s₁₁.stack :=
    prefix_of_push (of_run_pushB256 r10) hp10
  have hp12 : (32 : B256) :: (3 : B256) :: sevm.value :: s.stack <<+ s₁₂.stack :=
    prefix_of_add r11 hp11
  have hp13 : 3 :: (32 : B256) :: sevm.value :: s.stack <<+ s₁₃.stack := by
    apply Stack.prefix_of_swap (n := 0) (xs := [32, 3, sevm.value] ++ s.stack)
      (xs' := [3, 32, sevm.value] ++ s.stack)
    · simp [Stack.Swap, Stack.SwapCore]
    · exact of_run_swap r12
    · exact hp12
  -- blocked value-level walk omitted in this checkpoint
-/

theorem Weth9.deposit_effect {sevm : Sevm} {devm : Devm} {o : Outcome} {g : SFunc}
    (hg : prog[1]? = some g) (hfork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run prog sevm devm g o) :
    Devm.getStor (Outcome.devm o) sevm.currentTarget =
        (Devm.getStor devm sevm.currentTarget).set (balSlot sevm.caller)
          ((Devm.getStor devm sevm.currentTarget).get (balSlot sevm.caller) + sevm.value) ∧
      (Outcome.devm o).getBal = devm.getBal := by
  have hg' : g = t_0440_c1 := by
    simpa [prog, Cert.prog, cert] using hg.symm
  subst g
  rcases split_deposit_run run with
    ⟨d0, d1, d2, d3, dret, hburn, hpre, hsstore, hpost, hret⟩
  rcases deposit_pre_stack hpre with ⟨xs, hxs, hstack, hmem⟩
  have hset := sstore_getStor_set hsstore hstack
  have hpostStor : Devm.getStor d3 sevm.currentTarget = Devm.getStor d2 sevm.currentTarget :=
    congrFun (Line.of_inv Devm.getStor (by line_inv) hpost).symm sevm.currentTarget
  have hpostBal : d3.getBal = d2.getBal :=
    (Line.of_inv Devm.getBal (by line_inv) hpost).symm
  have hretStor : Devm.getStor (Outcome.devm o) sevm.currentTarget =
      Devm.getStor d3 sevm.currentTarget := Devm.PopBurn.getStor hret _
  have hretBal : (Outcome.devm o).getBal = d3.getBal := by
    funext a
    exact Devm.PopBurn.getBal hret a
  have hpreStor : Devm.getStor d1 sevm.currentTarget = Devm.getStor d0 sevm.currentTarget :=
    congrFun (Line.of_inv Devm.getStor (by line_inv) hpre).symm sevm.currentTarget
  have hsbal0 : d1.getBal = d2.getBal := Ninst.Hinv.inv hsstore
  have hsbal : d2.getBal = d1.getBal := hsbal0.symm
  have hburnStor : Devm.getStor d0 sevm.currentTarget = Devm.getStor devm sevm.currentTarget := by
    exact Devm.Burn.getStor hburn sevm.currentTarget
  have hburnBal : d0.getBal = devm.getBal := by
    funext a
    exact Devm.Burn.getBal hburn a
  have hpreVal : d0.getStorVal sevm.currentTarget (balSlot sevm.caller) =
      (Devm.getStor devm sevm.currentTarget).get (balSlot sevm.caller) := by
    change (Devm.getStor d0 sevm.currentTarget).get (balSlot sevm.caller) = _
    rw [hburnStor]
  have hpreBal : d1.getBal = d0.getBal :=
    (Line.of_inv Devm.getBal (by line_inv) hpre).symm
  constructor
  · rw [hretStor, hpostStor, hset, hpreStor, hburnStor, hpreVal]
  · rw [hretBal, hpostBal, hsbal, hpreBal, hburnBal]

theorem Weth9.deposit_solvent {sevm : Sevm} {devm : Devm} {o : Outcome} {g : SFunc}
    (hg : prog[1]? = some g) (hfork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run prog sevm devm g o)
    (h : Solvent (Devm.getStor devm sevm.currentTarget) sevm.value
      (devm.getBal sevm.currentTarget)) :
    Solvent (Devm.getStor (Outcome.devm o) sevm.currentTarget) 0
      ((Outcome.devm o).getBal sevm.currentTarget) := by
  rcases Weth9.deposit_effect hg hfork run with ⟨hstor, hbal⟩
  have hbal_ca : (Outcome.devm o).getBal sevm.currentTarget =
      devm.getBal sevm.currentTarget := congrFun hbal sevm.currentTarget
  rw [hstor, hbal_ca]
  unfold Solvent at h ⊢
  have hbound : bookedSum (Devm.getStor devm sevm.currentTarget) + sevm.value.toNat < 2 ^ 256 :=
    Nat.lt_of_le_of_lt h (B256.toNat_lt _)
  have hdeposit := bookedSum_deposit (s := Devm.getStor devm sevm.currentTarget)
    (a := sevm.caller) (v := sevm.value) hbound
  rw [hdeposit]
  rw [B256.toNat_zero, Nat.add_zero]
  exact h

end Blanc.Lift
