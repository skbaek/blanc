import Blanc.Lift.Weth9.Booked
import Blanc.Lift.Weth9.Words
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

private theorem deposit_pre_stack {sevm : Sevm} {s s' : Devm}
    (run : Line.Run sevm s depositPre s') :
    ∃ xs : Stack,
      xs <<+ s.stack ∧
      balSlot sevm.caller ::
          (s.getStorVal sevm.currentTarget (balSlot sevm.caller) + sevm.value) :: xs <<+ s'.stack ∧
      (((s.memory.write 0 sevm.caller.toB256.toBytes).write 32 (3 : B256).toBytes).read 0 64).1 =
        sevm.caller.toB256.toBytes ++ (3 : B256).toBytes := by
  have hmem2 : ∀ μ : Mem,
      (((μ.write 0 sevm.caller.toB256.toBytes).write 32 (3 : B256).toBytes).read 0 64).1 =
        sevm.caller.toB256.toBytes ++ (3 : B256).toBytes := fun μ =>
    Mem.read_two_word_writes_at_raw μ 0 sevm.caller.toB256 3
  unfold depositPre at run
  -- Segment A: CALLVALUE .. second AND
  obtain ⟨s1, h1, run⟩ := Line.of_run_cons run
  obtain ⟨s2, h2, run⟩ := Line.of_run_cons run
  obtain ⟨s3, h3, run⟩ := Line.of_run_cons run
  obtain ⟨s4, h4, run⟩ := Line.of_run_cons run
  obtain ⟨s5, h5, run⟩ := Line.of_run_cons run
  obtain ⟨s6, h6, run⟩ := Line.of_run_cons run
  obtain ⟨s7, h7, run⟩ := Line.of_run_cons run
  obtain ⟨s8, h8, run⟩ := Line.of_run_cons run
  have hp0 : s.stack <<+ s.stack := ⟨[], (List.append_nil _).symm⟩
  have hp1 : sevm.value :: s.stack <<+ s1.stack := prefix_of_push (of_run_callvalue h1) hp0
  have hp2 : (3 : B256) :: sevm.value :: s.stack <<+ s2.stack := by
    have := prefix_of_push (of_run_push h2) hp1
    rwa [w03_eq] at this
  have hp3 : (0 : B256) :: (3 : B256) :: sevm.value :: s.stack <<+ s3.stack := by
    have := prefix_of_push (of_run_push h3) hp2
    rwa [w00_eq] at this
  have hp4 : sevm.caller.toB256 :: (0 : B256) :: (3 : B256) :: sevm.value :: s.stack
      <<+ s4.stack := prefix_of_push (of_run_caller h4) hp3
  have hp6 : sevm.caller.toB256 :: (0 : B256) :: (3 : B256) :: sevm.value :: s.stack
      <<+ s6.stack := by
    have := prefix_of_and h6 (prefix_of_push (of_run_push h5) hp4)
    rwa [ff20_and_adr] at this
  have hp8 : sevm.caller.toB256 :: (0 : B256) :: (3 : B256) :: sevm.value :: s.stack
      <<+ s8.stack := by
    have := prefix_of_and h8 (prefix_of_push (of_run_push h7) hp6)
    rwa [ff20_and_adr] at this
  have hm8 : s.memory = s8.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (.cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 (.cons h6 (.cons h7
        (.cons h8 .nil))))))))
  have hst8 : Devm.getStor s = Devm.getStor s8 :=
    Line.of_inv Devm.getStor (by line_inv)
      (.cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 (.cons h6 (.cons h7
        (.cons h8 .nil))))))))
  -- Segment B: DUP2; MSTORE
  obtain ⟨s9, h9, run⟩ := Line.of_run_cons run
  obtain ⟨s10, h10, run⟩ := Line.of_run_cons run
  have hp9 : (0 : B256) :: sevm.caller.toB256 :: (0 : B256) :: (3 : B256) :: sevm.value ::
      s.stack <<+ s9.stack := prefix_of_dup_val h9 (by show_nth) hp8
  have hm9 : s8.memory = s9.memory := Ninst.Hinv.inv h9
  have hB := prefix_of_mstore_val h10 hp9
  have hp10 : (0 : B256) :: (3 : B256) :: sevm.value :: s.stack <<+ s10.stack := hB.1
  have hm10 : s10.memory = s.memory.write 0 sevm.caller.toB256.toBytes := by
    rw [hB.2, ← hm9, ← hm8, w0_toNat]
  have hst10 : Devm.getStor s8 = Devm.getStor s10 :=
    Line.of_inv Devm.getStor (by line_inv) (.cons h9 (.cons h10 .nil))
  -- Segment C: PUSH 0x20; ADD; SWAP1; DUP2; MSTORE
  obtain ⟨s11, h11, run⟩ := Line.of_run_cons run
  obtain ⟨s12, h12, run⟩ := Line.of_run_cons run
  obtain ⟨s13, h13, run⟩ := Line.of_run_cons run
  obtain ⟨s14, h14, run⟩ := Line.of_run_cons run
  obtain ⟨s15, h15, run⟩ := Line.of_run_cons run
  have hp11 : (32 : B256) :: (0 : B256) :: (3 : B256) :: sevm.value :: s.stack
      <<+ s11.stack := by
    have := prefix_of_push (of_run_push h11) hp10
    rwa [w20_eq] at this
  have hp12 : (32 : B256) :: (3 : B256) :: sevm.value :: s.stack <<+ s12.stack := by
    have := prefix_of_add h12 hp11
    rwa [w32_add_0] at this
  have hp13 : (3 : B256) :: (32 : B256) :: sevm.value :: s.stack <<+ s13.stack :=
    Stack.prefix_of_swap (n := 0) (by simp [Stack.Swap, Stack.SwapCore])
      (of_run_swap h13) hp12
  have hp14 : (32 : B256) :: (3 : B256) :: (32 : B256) :: sevm.value :: s.stack
      <<+ s14.stack := prefix_of_dup_val h14 (by show_nth) hp13
  have hm14 : s10.memory = s14.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (.cons h11 (.cons h12 (.cons h13 (.cons h14 .nil))))
  have hC := prefix_of_mstore_val h15 hp14
  have hp15 : (32 : B256) :: sevm.value :: s.stack <<+ s15.stack := hC.1
  have hm15 : s15.memory =
      (s.memory.write 0 sevm.caller.toB256.toBytes).write 32 (3 : B256).toBytes := by
    rw [hC.2, ← hm14, hm10, w32_toNat]
  have hst15 : Devm.getStor s10 = Devm.getStor s15 :=
    Line.of_inv Devm.getStor (by line_inv)
      (.cons h11 (.cons h12 (.cons h13 (.cons h14 (.cons h15 .nil)))))
  -- Segment D: PUSH 0x20; ADD; PUSH 0; SHA3
  obtain ⟨s16, h16, run⟩ := Line.of_run_cons run
  obtain ⟨s17, h17, run⟩ := Line.of_run_cons run
  obtain ⟨s18, h18, run⟩ := Line.of_run_cons run
  obtain ⟨s19, h19, run⟩ := Line.of_run_cons run
  have hp16 : (32 : B256) :: (32 : B256) :: sevm.value :: s.stack <<+ s16.stack := by
    have := prefix_of_push (of_run_push h16) hp15
    rwa [w20_eq] at this
  have hp17 : (64 : B256) :: sevm.value :: s.stack <<+ s17.stack := by
    have := prefix_of_add h17 hp16
    rwa [w32_add_32] at this
  have hp18 : (0 : B256) :: (64 : B256) :: sevm.value :: s.stack <<+ s18.stack := by
    have := prefix_of_push (of_run_push h18) hp17
    rwa [w00_eq] at this
  have hm18 : s15.memory = s18.memory :=
    Line.of_inv Devm.memory (by line_inv) (.cons h16 (.cons h17 (.cons h18 .nil)))
  have hp19 : balSlot sevm.caller :: sevm.value :: s.stack <<+ s19.stack := by
    have := (prefix_of_keccak256_val h19 hp18).1
    rwa [← hm18, hm15, w0_toNat, w64_toNat, hmem2] at this
  have hst19 : Devm.getStor s15 = Devm.getStor s19 :=
    Line.of_inv Devm.getStor (by line_inv)
      (.cons h16 (.cons h17 (.cons h18 (.cons h19 .nil))))
  -- Segment E: PUSH 0; DUP3; DUP3; SLOAD; ADD; SWAP3; POP; POP; DUP2; SWAP1
  obtain ⟨s20, h20, run⟩ := Line.of_run_cons run
  obtain ⟨s21, h21, run⟩ := Line.of_run_cons run
  obtain ⟨s22, h22, run⟩ := Line.of_run_cons run
  obtain ⟨s23, h23, run⟩ := Line.of_run_cons run
  obtain ⟨s24, h24, run⟩ := Line.of_run_cons run
  obtain ⟨s25, h25, run⟩ := Line.of_run_cons run
  obtain ⟨s26, h26, run⟩ := Line.of_run_cons run
  obtain ⟨s27, h27, run⟩ := Line.of_run_cons run
  obtain ⟨s28, h28, run⟩ := Line.of_run_cons run
  obtain ⟨s29, h29, run⟩ := Line.of_run_cons run
  cases run
  have hst22 : Devm.getStor s19 = Devm.getStor s22 :=
    Line.of_inv Devm.getStor (by line_inv) (.cons h20 (.cons h21 (.cons h22 .nil)))
  have hold : s22.getStorVal sevm.currentTarget (balSlot sevm.caller) =
      s.getStorVal sevm.currentTarget (balSlot sevm.caller) := by
    show (Devm.getStor s22 sevm.currentTarget).get (balSlot sevm.caller) =
      (Devm.getStor s sevm.currentTarget).get (balSlot sevm.caller)
    rw [← hst22, ← hst19, ← hst15, ← hst10, ← hst8]
  have hp20 : (0 : B256) :: balSlot sevm.caller :: sevm.value :: s.stack <<+ s20.stack := by
    have := prefix_of_push (of_run_push h20) hp19
    rwa [w00_eq] at this
  have hp21 : sevm.value :: (0 : B256) :: balSlot sevm.caller :: sevm.value :: s.stack
      <<+ s21.stack := prefix_of_dup_val h21 (by show_nth) hp20
  have hp22 : balSlot sevm.caller :: sevm.value :: (0 : B256) :: balSlot sevm.caller ::
      sevm.value :: s.stack <<+ s22.stack := prefix_of_dup_val h22 (by show_nth) hp21
  obtain ⟨old, hp23, hold'⟩ := prefix_of_sload h23 hp22
  rw [hold] at hold'
  subst hold'
  have hp24 := prefix_of_add h24 hp23
  have hp25 : sevm.value :: (0 : B256) :: balSlot sevm.caller ::
      (s.getStorVal sevm.currentTarget (balSlot sevm.caller) + sevm.value) :: s.stack
      <<+ s25.stack :=
    Stack.prefix_of_swap (n := 2) (by simp [Stack.Swap, Stack.SwapCore])
      (of_run_swap h25) hp24
  have hp27 := prefix_of_pop (of_run_pop h27) (prefix_of_pop (of_run_pop h26) hp25)
  have hp28 := prefix_of_dup_val h28 (by show_nth) hp27
  have hp29 : balSlot sevm.caller ::
      (s.getStorVal sevm.currentTarget (balSlot sevm.caller) + sevm.value) ::
      (s.getStorVal sevm.currentTarget (balSlot sevm.caller) + sevm.value) :: s.stack
      <<+ s'.stack :=
    Stack.prefix_of_swap (n := 0) (by simp [Stack.Swap, Stack.SwapCore])
      (of_run_swap h29) hp28
  exact ⟨[], nil_pref, pref_trans ⟨_ :: s.stack, rfl⟩ hp29, hmem2 s.memory⟩


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
