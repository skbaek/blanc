import Blanc.Lift.Weth9.Booked
import Blanc.Lift.Weth9.Words
import Blanc.Lift.Silent
import Blanc.Lift.CallFrame

/-!
# WETH9 `withdraw(wad)` preserves solvency

Entry 8 of the lifted WETH9 (`t_09d9_c8`, pc `0x9d9`, frame `[wad, ret]`):

```
require(balanceOf[msg.sender] >= wad);
balanceOf[msg.sender] -= wad;
msg.sender.transfer(wad);
Withdrawal(msg.sender, wad);
```

The walk is explicit, one instruction at a time, as in `Deposit.lean`.  The
`CALL` is discharged by the contract-generic `ContractSpecSem.post_of_call_self`
(`Blanc/Lift/CallFrame.lean`), whose deeper-frame hypothesis is exactly the one
`ContractSpecSem.Sound` supplies.  Everything after the `CALL` (the failure
check, the event, the return) is state-silent.
-/

namespace Blanc.Lift

open Jaune
open Blanc
open Weth9

private def wchain : List Ninst → SFunc → SFunc
  | [], f => f
  | n :: ns, f => .next n (wchain ns f)

private theorem run_wchain_prefix {fs : List SFunc} {sevm : Sevm}
    (xs ys : List Ninst) {devm : Devm} {f : SFunc} {o : Outcome}
    (run : SFunc.Run fs sevm devm (wchain (xs ++ ys) f) o) :
    ∃ mid, Line.Run sevm devm xs mid ∧
      SFunc.Run fs sevm mid (wchain ys f) o := by
  induction xs generalizing devm with
  | nil => exact ⟨devm, .nil, run⟩
  | cons n ns ih =>
      change SFunc.Run fs sevm devm (.next n (wchain (ns ++ ys) f)) o at run
      cases run with
      | next hstep hrest =>
          rcases ih hrest with ⟨mid, hline, hrun⟩
          exact ⟨mid, .cons hstep hline, hrun⟩

/-- `mstore(0, caller); mstore(32, 3); keccak256(0, 64)`: the balance slot of
the caller, pushed above the current stack. -/
private def slotLine : List Ninst :=
  [.push [0x03] (by decide), .push [0x00] (by decide),
   .reg .caller,
   .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
     0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
   .reg .and,
   .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
     0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
   .reg .and, .reg (.dup 1), .reg .mstore,
   .push [0x20] (by decide), .reg .add, .reg (.swap 0), .reg (.dup 1),
   .reg .mstore, .push [0x20] (by decide), .reg .add,
   .push [0x00] (by decide), .reg .keccak256]

/-- The `require` test: `iszero(iszero(iszero(lt(bal, wad))))`, then the jump
destination. -/
private def checkTail : List Ninst :=
  [.reg .sload, .reg .lt, .reg .iszero, .reg .iszero, .reg .iszero,
   .push [0x0a, 0x27] (by decide)]

/-- The debit up to the `SSTORE`: `balanceOf[caller] = bal - wad`. -/
private def debitTail : List Ninst :=
  [.push [0x00] (by decide), .reg (.dup 2), .reg (.dup 2), .reg .sload, .reg .sub,
   .reg (.swap 2), .reg .pop, .reg .pop, .reg (.dup 1), .reg (.swap 0)]

/-- From the `SSTORE` to the `CALL`: gas `2300 * (wad = 0)`, callee `caller`,
value `wad`, and the memory windows. -/
private def sendLine : List Ninst :=
  [.reg .pop, .reg .caller,
   .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
     0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
   .reg .and, .push [0x08, 0xfc] (by decide), .reg (.dup 2), .reg (.swap 0),
   .reg (.dup 1), .reg .iszero, .reg .mul, .reg (.swap 0),
   .push [0x40] (by decide), .reg .mload, .push [0x00] (by decide),
   .push [0x40] (by decide), .reg .mload, .reg (.dup 0), .reg (.dup 3),
   .reg .sub, .reg (.dup 1), .reg (.dup 5), .reg (.dup 8), .reg (.dup 8)]

/-- After the `CALL`: the success check, the `Withdrawal` event, the return. -/
private def afterCall : SFunc :=
  wchain [.reg (.swap 3), .reg .pop, .reg .pop, .reg .pop, .reg .pop, .reg .iszero,
    .reg .iszero, .push [0x0a, 0xb4] (by decide)] (.branch t_0ab0_c8 t_0ab4_c8)

private theorem withdraw_tree_eq :
    t_09d9_c8 = .dest (wchain ([.reg (.dup 0)] ++ slotLine ++ checkTail)
      (.branch t_0a23_c8 t_0a27_c8)) := by
  simp [t_09d9_c8, slotLine, checkTail, wchain]

private theorem debit_tree_eq :
    t_0a27_c8 = .dest (wchain ([.reg (.dup 0)] ++ slotLine ++ debitTail ++
      [Ninst.sstore] ++ sendLine ++ [.exec .call]) afterCall) := by
  simp [t_0a27_c8, slotLine, debitTail, sendLine, afterCall, wchain]

private theorem afterCall_silent : afterCall.silent = true := by decide

private theorem afterCall_refs : afterCall.refs.all (· ∈ ([] : List Nat)) = true := by
  decide

private theorem silentSet_nil : SilentSet prog [] = true := rfl

private theorem not_run_revert_tail {fs : List SFunc} {sevm : Sevm} {devm : Devm}
    {o : Outcome} :
    ¬ SFunc.Run fs sevm devm
      (.next (.push [0x00] (by decide)) (.next (.reg (.dup 0)) (.last .revert))) o := by
  intro run
  rcases run with _ | _ | _ | _ | _ | ⟨_, run⟩
  rcases run with _ | _ | _ | _ | _ | ⟨_, run⟩
  rcases run with _ | _ | _ | _ | ⟨h_run⟩
  dsimp [Linst.Run, Linst.run] at h_run
  rcases Except.bind_eq_ok h_run with ⟨_, _, h2⟩
  rcases Except.bind_eq_ok h2 with ⟨_, _, h4⟩
  rcases Except.bind_eq_ok h4 with ⟨_, _, h6⟩
  contradiction

/-- The slot walk: pushes `balSlot caller` and leaves the persistent state alone. -/
private theorem slot_walk {sevm : Sevm} {s s' : Devm} {ys : Stack}
    (hp0 : ys <<+ s.stack) (run : Line.Run sevm s slotLine s') :
    balSlot sevm.caller :: ys <<+ s'.stack ∧
      Devm.getStor s' = Devm.getStor s ∧ s'.getBal = s.getBal ∧
      s'.getCode = s.getCode := by
  have hstor : Devm.getStor s = Devm.getStor s' :=
    Line.of_inv Devm.getStor (by line_inv) run
  have hbal : s.getBal = s'.getBal := Line.of_inv Devm.getBal (by line_inv) run
  have hcode : s.getCode = s'.getCode := Line.of_inv Devm.getCode (by line_inv) run
  refine ⟨?_, hstor.symm, hbal.symm, hcode.symm⟩
  have hmem2 : ∀ μ : Mem,
      (((μ.write 0 sevm.caller.toB256.toBytes).write 32 (3 : B256).toBytes).read 0 64).1 =
        sevm.caller.toB256.toBytes ++ (3 : B256).toBytes := fun μ =>
    Mem.read_two_word_writes_at_raw μ 0 sevm.caller.toB256 3
  unfold slotLine at run
  obtain ⟨s2, h2, run⟩ := Line.of_run_cons run
  obtain ⟨s3, h3, run⟩ := Line.of_run_cons run
  obtain ⟨s4, h4, run⟩ := Line.of_run_cons run
  obtain ⟨s5, h5, run⟩ := Line.of_run_cons run
  obtain ⟨s6, h6, run⟩ := Line.of_run_cons run
  obtain ⟨s7, h7, run⟩ := Line.of_run_cons run
  obtain ⟨s8, h8, run⟩ := Line.of_run_cons run
  obtain ⟨s9, h9, run⟩ := Line.of_run_cons run
  obtain ⟨s10, h10, run⟩ := Line.of_run_cons run
  obtain ⟨s11, h11, run⟩ := Line.of_run_cons run
  obtain ⟨s12, h12, run⟩ := Line.of_run_cons run
  obtain ⟨s13, h13, run⟩ := Line.of_run_cons run
  obtain ⟨s14, h14, run⟩ := Line.of_run_cons run
  obtain ⟨s15, h15, run⟩ := Line.of_run_cons run
  obtain ⟨s16, h16, run⟩ := Line.of_run_cons run
  obtain ⟨s17, h17, run⟩ := Line.of_run_cons run
  obtain ⟨s18, h18, run⟩ := Line.of_run_cons run
  obtain ⟨s19, h19, run⟩ := Line.of_run_cons run
  cases run
  have hp2 : (3 : B256) :: ys <<+ s2.stack := by
    have := prefix_of_push (of_run_push h2) hp0
    rwa [w03_eq] at this
  have hp3 : (0 : B256) :: (3 : B256) :: ys <<+ s3.stack := by
    have := prefix_of_push (of_run_push h3) hp2
    rwa [w00_eq] at this
  have hp4 : sevm.caller.toB256 :: (0 : B256) :: (3 : B256) :: ys <<+ s4.stack :=
    prefix_of_push (of_run_caller h4) hp3
  have hp6 : sevm.caller.toB256 :: (0 : B256) :: (3 : B256) :: ys <<+ s6.stack := by
    have := prefix_of_and h6 (prefix_of_push (of_run_push h5) hp4)
    rwa [ff20_and_adr] at this
  have hp8 : sevm.caller.toB256 :: (0 : B256) :: (3 : B256) :: ys <<+ s8.stack := by
    have := prefix_of_and h8 (prefix_of_push (of_run_push h7) hp6)
    rwa [ff20_and_adr] at this
  have hm8 : s.memory = s8.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (.cons h2 (.cons h3 (.cons h4 (.cons h5 (.cons h6 (.cons h7
        (.cons h8 .nil)))))))
  -- DUP2; MSTORE
  have hp9 : (0 : B256) :: sevm.caller.toB256 :: (0 : B256) :: (3 : B256) :: ys
      <<+ s9.stack := prefix_of_dup_val h9 (by show_nth) hp8
  have hm9 : s8.memory = s9.memory := Ninst.Hinv.inv h9
  have hB := prefix_of_mstore_val h10 hp9
  have hp10 : (0 : B256) :: (3 : B256) :: ys <<+ s10.stack := hB.1
  have hm10 : s10.memory = s.memory.write 0 sevm.caller.toB256.toBytes := by
    rw [hB.2, ← hm9, ← hm8, w0_toNat]
  -- PUSH 0x20; ADD; SWAP1; DUP2; MSTORE
  have hp11 : (32 : B256) :: (0 : B256) :: (3 : B256) :: ys <<+ s11.stack := by
    have := prefix_of_push (of_run_push h11) hp10
    rwa [w20_eq] at this
  have hp12 : (32 : B256) :: (3 : B256) :: ys <<+ s12.stack := by
    have := prefix_of_add h12 hp11
    rwa [w32_add_0] at this
  have hp13 : (3 : B256) :: (32 : B256) :: ys <<+ s13.stack :=
    Stack.prefix_of_swap (n := 0) (by simp [Stack.Swap, Stack.SwapCore])
      (of_run_swap h13) hp12
  have hp14 : (32 : B256) :: (3 : B256) :: (32 : B256) :: ys <<+ s14.stack :=
    prefix_of_dup_val h14 (by show_nth) hp13
  have hm14 : s10.memory = s14.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (.cons h11 (.cons h12 (.cons h13 (.cons h14 .nil))))
  have hC := prefix_of_mstore_val h15 hp14
  have hp15 : (32 : B256) :: ys <<+ s15.stack := hC.1
  have hm15 : s15.memory =
      (s.memory.write 0 sevm.caller.toB256.toBytes).write 32 (3 : B256).toBytes := by
    rw [hC.2, ← hm14, hm10, w32_toNat]
  -- PUSH 0x20; ADD; PUSH 0; SHA3
  have hp16 : (32 : B256) :: (32 : B256) :: ys <<+ s16.stack := by
    have := prefix_of_push (of_run_push h16) hp15
    rwa [w20_eq] at this
  have hp17 : (64 : B256) :: ys <<+ s17.stack := by
    have := prefix_of_add h17 hp16
    rwa [w32_add_32] at this
  have hp18 : (0 : B256) :: (64 : B256) :: ys <<+ s18.stack := by
    have := prefix_of_push (of_run_push h18) hp17
    rwa [w00_eq] at this
  have hm18 : s15.memory = s18.memory :=
    Line.of_inv Devm.memory (by line_inv) (.cons h16 (.cons h17 (.cons h18 .nil)))
  have := (prefix_of_keccak256_val h19 hp18).1
  rwa [← hm18, hm15, w0_toNat, w64_toNat, hmem2] at this

/-- Two words popped by a `JUMPI`: they are the top two words of any known
prefix, and the rest of the prefix survives. -/
private theorem prefix_of_popBurn2 {s s' : Devm} {a b d w : B256} {xs : Stack}
    (hp : a :: b :: xs <<+ s.stack) (h : Devm.PopBurn [d, w] s s') :
    a = d ∧ b = w ∧ xs <<+ s'.stack := by
  have hs : s.stack = d :: w :: s'.stack := h.stack
  rcases hp with ⟨t, ht⟩
  have ht' : s.stack = a :: b :: (xs ++ t) := ht
  rw [hs] at ht'
  injection ht' with h1 ht'
  injection ht' with h2 ht'
  exact ⟨h1.symm, h2.symm, t, ht'⟩

/-- The `require` test. -/
private theorem check_walk {sevm : Sevm} {s s' : Devm} {slot wad : B256} {xs : Stack}
    (hp : slot :: wad :: wad :: xs <<+ s.stack) (run : Line.Run sevm s checkTail s') :
    ∃ d, d :: ((((s.getStorVal sevm.currentTarget slot <? wad) =? 0) =? 0) =? 0) ::
      wad :: xs <<+ s'.stack := by
  unfold checkTail at run
  obtain ⟨s1, h1, run⟩ := Line.of_run_cons run
  obtain ⟨s2, h2, run⟩ := Line.of_run_cons run
  obtain ⟨s3, h3, run⟩ := Line.of_run_cons run
  obtain ⟨s4, h4, run⟩ := Line.of_run_cons run
  obtain ⟨s5, h5, run⟩ := Line.of_run_cons run
  obtain ⟨s6, h6, run⟩ := Line.of_run_cons run
  cases run
  obtain ⟨bal, hp1, hbal⟩ := prefix_of_sload h1 hp
  subst hbal
  exact ⟨_, prefix_of_push (of_run_push h6) (prefix_of_iszero h5 (prefix_of_iszero h4
    (prefix_of_iszero h3 (prefix_of_lt h2 hp1))))⟩

/-- The debit up to the `SSTORE`. -/
private theorem debit_walk {sevm : Sevm} {s s' : Devm} {slot wad : B256} {xs : Stack}
    (hp : slot :: wad :: wad :: xs <<+ s.stack) (run : Line.Run sevm s debitTail s') :
    slot :: (s.getStorVal sevm.currentTarget slot - wad) ::
      (s.getStorVal sevm.currentTarget slot - wad) :: wad :: xs <<+ s'.stack := by
  unfold debitTail at run
  obtain ⟨s1, h1, run⟩ := Line.of_run_cons run
  obtain ⟨s2, h2, run⟩ := Line.of_run_cons run
  obtain ⟨s3, h3, run⟩ := Line.of_run_cons run
  obtain ⟨s4, h4, run⟩ := Line.of_run_cons run
  obtain ⟨s5, h5, run⟩ := Line.of_run_cons run
  obtain ⟨s6, h6, run⟩ := Line.of_run_cons run
  obtain ⟨s7, h7, run⟩ := Line.of_run_cons run
  obtain ⟨s8, h8, run⟩ := Line.of_run_cons run
  obtain ⟨s9, h9, run⟩ := Line.of_run_cons run
  obtain ⟨s10, h10, run⟩ := Line.of_run_cons run
  cases run
  have hst3 : Devm.getStor s = Devm.getStor s3 :=
    Line.of_inv Devm.getStor (by line_inv) (.cons h1 (.cons h2 (.cons h3 .nil)))
  have hold : s3.getStorVal sevm.currentTarget slot = s.getStorVal sevm.currentTarget slot := by
    show (Devm.getStor s3 sevm.currentTarget).get slot =
      (Devm.getStor s sevm.currentTarget).get slot
    rw [← hst3]
  have hp1 : (0 : B256) :: slot :: wad :: wad :: xs <<+ s1.stack := by
    have := prefix_of_push (of_run_push h1) hp
    rwa [w00_eq] at this
  have hp2 : wad :: (0 : B256) :: slot :: wad :: wad :: xs <<+ s2.stack :=
    prefix_of_dup_val h2 (by show_nth) hp1
  have hp3 : slot :: wad :: (0 : B256) :: slot :: wad :: wad :: xs <<+ s3.stack :=
    prefix_of_dup_val h3 (by show_nth) hp2
  obtain ⟨bal, hp4, hbal⟩ := prefix_of_sload h4 hp3
  rw [hold] at hbal
  subst hbal
  have hp5 := prefix_of_sub h5 hp4
  have hp6 : wad :: (0 : B256) :: slot ::
      (s.getStorVal sevm.currentTarget slot - wad) :: wad :: xs <<+ s6.stack :=
    Stack.prefix_of_swap (n := 2) (by simp [Stack.Swap, Stack.SwapCore])
      (of_run_swap h6) hp5
  have hp8 := prefix_of_pop (of_run_pop h8) (prefix_of_pop (of_run_pop h7) hp6)
  have hp9 := prefix_of_dup_val h9 (by show_nth) hp8
  exact Stack.prefix_of_swap (n := 0) (by simp [Stack.Swap, Stack.SwapCore])
    (of_run_swap h10) hp9

/-- From the `SSTORE` to the `CALL`: the value word is `wad`. -/
private theorem send_walk {sevm : Sevm} {s s' : Devm} {y wad : B256} {xs : Stack}
    (hp : y :: wad :: xs <<+ s.stack) (run : Line.Run sevm s sendLine s') :
    ∃ g c ys, g :: c :: wad :: ys <<+ s'.stack := by
  unfold sendLine at run
  obtain ⟨s1, h1, run⟩ := Line.of_run_cons run
  obtain ⟨s2, h2, run⟩ := Line.of_run_cons run
  obtain ⟨s3, h3, run⟩ := Line.of_run_cons run
  obtain ⟨s4, h4, run⟩ := Line.of_run_cons run
  obtain ⟨s5, h5, run⟩ := Line.of_run_cons run
  obtain ⟨s6, h6, run⟩ := Line.of_run_cons run
  obtain ⟨s7, h7, run⟩ := Line.of_run_cons run
  obtain ⟨s8, h8, run⟩ := Line.of_run_cons run
  obtain ⟨s9, h9, run⟩ := Line.of_run_cons run
  obtain ⟨s10, h10, run⟩ := Line.of_run_cons run
  obtain ⟨s11, h11, run⟩ := Line.of_run_cons run
  obtain ⟨s12, h12, run⟩ := Line.of_run_cons run
  obtain ⟨s13, h13, run⟩ := Line.of_run_cons run
  obtain ⟨s14, h14, run⟩ := Line.of_run_cons run
  obtain ⟨s15, h15, run⟩ := Line.of_run_cons run
  obtain ⟨s16, h16, run⟩ := Line.of_run_cons run
  obtain ⟨s17, h17, run⟩ := Line.of_run_cons run
  obtain ⟨s18, h18, run⟩ := Line.of_run_cons run
  obtain ⟨s19, h19, run⟩ := Line.of_run_cons run
  obtain ⟨s20, h20, run⟩ := Line.of_run_cons run
  obtain ⟨s21, h21, run⟩ := Line.of_run_cons run
  obtain ⟨s22, h22, run⟩ := Line.of_run_cons run
  obtain ⟨s23, h23, run⟩ := Line.of_run_cons run
  cases run
  -- POP; CALLER; mask; PUSH2 0x08fc
  have hp1 : wad :: xs <<+ s1.stack := prefix_of_pop (of_run_pop h1) hp
  have hp2 : sevm.caller.toB256 :: wad :: xs <<+ s2.stack :=
    prefix_of_push (of_run_caller h2) hp1
  obtain ⟨c, hp4⟩ : ∃ c : B256, c :: wad :: xs <<+ s4.stack :=
    ⟨_, prefix_of_and h4 (prefix_of_push (of_run_push h3) hp2)⟩
  obtain ⟨K, hp5⟩ : ∃ K : B256, K :: c :: wad :: xs <<+ s5.stack :=
    ⟨_, prefix_of_push (of_run_push h5) hp4⟩
  -- DUP3; SWAP1; DUP2; ISZERO; MUL; SWAP1
  have hp6 : wad :: K :: c :: wad :: xs <<+ s6.stack :=
    prefix_of_dup_val h6 (by show_nth) hp5
  have hp7 : K :: wad :: c :: wad :: xs <<+ s7.stack :=
    Stack.prefix_of_swap (n := 0) (by simp [Stack.Swap, Stack.SwapCore])
      (of_run_swap h7) hp6
  have hp8 : wad :: K :: wad :: c :: wad :: xs <<+ s8.stack :=
    prefix_of_dup_val h8 (by show_nth) hp7
  obtain ⟨z, hp9⟩ : ∃ z : B256, z :: K :: wad :: c :: wad :: xs <<+ s9.stack :=
    ⟨_, prefix_of_iszero h9 hp8⟩
  obtain ⟨g, hp10⟩ : ∃ g : B256, g :: wad :: c :: wad :: xs <<+ s10.stack :=
    ⟨_, prefix_of_mul h10 hp9⟩
  have hp11 : wad :: g :: c :: wad :: xs <<+ s11.stack :=
    Stack.prefix_of_swap (n := 0) (by simp [Stack.Swap, Stack.SwapCore])
      (of_run_swap h11) hp10
  -- PUSH1 0x40; MLOAD; PUSH1 0; PUSH1 0x40; MLOAD
  obtain ⟨p, hp12⟩ : ∃ p : B256, p :: wad :: g :: c :: wad :: xs <<+ s12.stack :=
    ⟨_, prefix_of_push (of_run_push h12) hp11⟩
  obtain ⟨m, hp13⟩ := prefix_of_mload h13 hp12
  obtain ⟨q, hp14⟩ : ∃ q : B256, q :: m :: wad :: g :: c :: wad :: xs <<+ s14.stack :=
    ⟨_, prefix_of_push (of_run_push h14) hp13⟩
  obtain ⟨p', hp15⟩ : ∃ p' : B256,
      p' :: q :: m :: wad :: g :: c :: wad :: xs <<+ s15.stack :=
    ⟨_, prefix_of_push (of_run_push h15) hp14⟩
  obtain ⟨m', hp16⟩ := prefix_of_mload h16 hp15
  -- DUP1; DUP4; SUB; DUP2; DUP6; DUP9; DUP9
  have hp17 := prefix_of_dup_val h17 (by show_nth) hp16
  have hp18 := prefix_of_dup_val h18 (by show_nth) hp17
  obtain ⟨r, hp19⟩ : ∃ r : B256,
      r :: m' :: q :: m :: wad :: g :: c :: wad :: xs <<+ s19.stack :=
    ⟨_, prefix_of_sub h19 hp18⟩
  have hp20 := prefix_of_dup_val h20 (by show_nth) hp19
  have hp21 := prefix_of_dup_val h21 (by show_nth) hp20
  have hp22 := prefix_of_dup_val h22 (by show_nth) hp21
  have hp23 := prefix_of_dup_val h23 (by show_nth) hp22
  exact ⟨_, _, _, hp23⟩

/-- `iszero(iszero(iszero(lt(bal, wad))))` is nonzero only when `wad ≤ bal`. -/
private theorem le_of_check {bal wad : B256}
    (h : ((((bal <? wad) =? 0) =? 0) =? 0) ≠ 0) : wad ≤ bal := by
  rw [← B256.not_lt]
  intro hlt
  apply h
  rw [B256.ltCheck, ite_eq_left_of_eq_true _ _ (eq_true hlt)]
  decide

/-- Persistent-state observations shared by two machine states. -/
private structure Same (a b : Devm) : Prop where
  stor : Devm.getStor a = Devm.getStor b
  bal : a.getBal = b.getBal
  code : a.getCode = b.getCode

private theorem Same.of_state {a b : Devm} (h : a.state = b.state) : Same a b :=
  ⟨funext (getStor_eq_of_state_eq h), funext (getBal_eq_of_state_eq h),
    funext (getCode_eq_of_state_eq h)⟩

private theorem Same.trans {a b c : Devm} (h : Same a b) (h' : Same b c) : Same a c :=
  ⟨h.stor.trans h'.stor, h.bal.trans h'.bal, h.code.trans h'.code⟩

section Withdraw

variable {c : ContractSpecSem}

/-- **WETH9 `withdraw(wad)` (entry 8) establishes the frame postcondition.**

Stated over any `ContractSpecSem` whose invariant admits the debit
(`hstep`: from `Inv s v b` and `wad ≤ balanceOf[a]`, the ether covers `wad`
and the invariant holds at the debited storage and balance).  `ih` is the
deeper-frame hypothesis of `ContractSpecSem.Sound`, verbatim; `hpre` is the
frame precondition at the entry's pre-state. -/
theorem Weth9.withdraw_post {ca : Adr}
    (hstep : ∀ {s : Stor} {v b : B256} {a : Adr} {wad : B256},
      c.Inv s v b → wad ≤ s.get (balSlot a) →
      wad ≤ b ∧ c.Inv (s.set (balSlot a) (s.get (balSlot a) - wad)) 0 (b - wad))
    {sevm : Sevm} {devm : Devm} {o : Outcome} {g : SFunc}
    (hfork : CoveredFork sevm.benvStat.fork) (hca : sevm.currentTarget = ca)
    (ih : ∀ pc' sevm' pre' post',
        Exec pc' sevm' pre' (.ok post') →
        sevm'.depth < sevm.depth →
        CodeSem.At c.sem ca pc' sevm' pre' →
        CoveredFork sevm'.benvStat.fork →
        c.PreWf ca sevm' pre' →
        c.Post ca sevm' post')
    (hg : prog[8]? = some g) (run : SFunc.Run prog sevm devm g o)
    (hpre : c.Pre ca sevm devm) :
    c.Post ca sevm (Outcome.devm o) := by
  have hg' : g = t_09d9_c8 := by
    simpa [prog, Cert.prog, cert] using hg.symm
  subst g
  rw [withdraw_tree_eq] at run
  cases run with
  | dest burn0 run =>
  rename_i d0
  obtain ⟨d1, hdup, run⟩ := run_wchain_prefix [.reg (.dup 0)] (slotLine ++ checkTail) run
  obtain ⟨d2, hslot, run⟩ := run_wchain_prefix slotLine checkTail run
  obtain ⟨d3, hcheck, run⟩ := run_wchain_prefix checkTail [] run
  have hdup1 := of_run_singleton hdup
  obtain ⟨wad, hw, hpush⟩ := of_run_dup hdup1
  obtain ⟨rest, hrest⟩ : ∃ rest, d0.stack = wad :: rest := by
    cases h : d0.stack with
    | nil => simp [h] at hw
    | cons x r =>
        simp [h] at hw
        exact ⟨r, by rw [hw]⟩
  have hp0 : wad :: rest <<+ d0.stack := ⟨[], by simp [Split, hrest]⟩
  have hp1 : wad :: wad :: rest <<+ d1.stack := prefix_of_push hpush hp0
  obtain ⟨hp2, hs2stor, hs2bal, hs2code⟩ := slot_walk hp1 hslot
  obtain ⟨dd, hp3⟩ := check_walk hp2 hcheck
  have same01 : Same devm d0 := Same.of_state burn0.state
  have same12 : Same d0 d2 :=
    Same.trans ⟨Line.of_inv Devm.getStor (by line_inv) hdup,
      Line.of_inv Devm.getBal (by line_inv) hdup,
      Line.of_inv Devm.getCode (by line_inv) hdup⟩ ⟨hs2stor.symm, hs2bal.symm, hs2code.symm⟩
  have same23 : Same d2 d3 := ⟨Line.of_inv Devm.getStor (by line_inv) hcheck,
      Line.of_inv Devm.getBal (by line_inv) hcheck,
      Line.of_inv Devm.getCode (by line_inv) hcheck⟩
  change SFunc.Run prog sevm d3 (.branch t_0a23_c8 t_0a27_c8) o at run
  cases run with
  | zero _ _ run => exact absurd run not_run_revert_tail
  | succ dw w hwnz pop run =>
  rename_i d4
  obtain ⟨-, hcond, hp4⟩ := prefix_of_popBurn2 hp3 pop
  subst hcond
  have hle := le_of_check hwnz
  have same34 : Same d3 d4 := Same.of_state pop.state
  rw [debit_tree_eq] at run
  cases run with
  | dest burn1 run =>
  rename_i d5
  obtain ⟨d6, hdup', run⟩ := run_wchain_prefix [.reg (.dup 0)]
    (slotLine ++ debitTail ++ [Ninst.sstore] ++ sendLine ++ [.exec .call]) run
  obtain ⟨d7, hslot', run⟩ := run_wchain_prefix slotLine
    (debitTail ++ [Ninst.sstore] ++ sendLine ++ [.exec .call]) run
  obtain ⟨d8, hdebit, run⟩ := run_wchain_prefix debitTail
    ([Ninst.sstore] ++ sendLine ++ [.exec .call]) run
  obtain ⟨d9, hsstore, run⟩ := run_wchain_prefix [Ninst.sstore]
    (sendLine ++ [.exec .call]) run
  obtain ⟨d10, hsend, run⟩ := run_wchain_prefix sendLine [.exec .call] run
  obtain ⟨d11, hcall, run⟩ := run_wchain_prefix [.exec .call] [] run
  change SFunc.Run prog sevm d11 afterCall o at run
  -- the debit walk
  have same45 : Same d4 d5 := Same.of_state burn1.state
  have hdup'1 := of_run_singleton hdup'
  have hp5 : wad :: rest <<+ d5.stack := by
    have h := burn1.stack
    rw [← h]
    exact hp4
  have hp6 : wad :: wad :: rest <<+ d6.stack := prefix_of_dup_val hdup'1 (by show_nth) hp5
  obtain ⟨hp7, hs7stor, hs7bal, hs7code⟩ := slot_walk hp6 hslot'
  have hp8 := debit_walk hp7 hdebit
  have hsstore1 := of_run_singleton hsstore
  have hset := sstore_getStor_set hsstore1 hp8
  have hp9 := prefix_of_sstore hsstore1 hp8
  obtain ⟨gw, cw, ys, hp10⟩ := send_walk hp9 hsend
  have same56 : Same d5 d7 :=
    Same.trans ⟨Line.of_inv Devm.getStor (by line_inv) hdup',
      Line.of_inv Devm.getBal (by line_inv) hdup',
      Line.of_inv Devm.getCode (by line_inv) hdup'⟩ ⟨hs7stor.symm, hs7bal.symm, hs7code.symm⟩
  have same78 : Same d7 d8 := ⟨Line.of_inv Devm.getStor (by line_inv) hdebit,
      Line.of_inv Devm.getBal (by line_inv) hdebit,
      Line.of_inv Devm.getCode (by line_inv) hdebit⟩
  have hbal89 : d8.getBal = d9.getBal := Ninst.Hinv.inv hsstore1
  have hcode89 : d8.getCode = d9.getCode := Ninst.Hinv.inv hsstore1
  have same910 : Same d9 d10 := ⟨Line.of_inv Devm.getStor (by line_inv) hsend,
      Line.of_inv Devm.getBal (by line_inv) hsend,
      Line.of_inv Devm.getCode (by line_inv) hsend⟩
  have same02 : Same devm d2 := same01.trans same12
  have same07 : Same devm d7 :=
    same02.trans (same23.trans (same34.trans (same45.trans same56)))
  have same08 : Same devm d8 := same07.trans same78
  -- the debit, in terms of the entry state
  subst hca
  have hold2 : d2.getStorVal sevm.currentTarget (balSlot sevm.caller) =
      (Devm.getStor devm sevm.currentTarget).get (balSlot sevm.caller) := by
    show (Devm.getStor d2 sevm.currentTarget).get (balSlot sevm.caller) = _
    rw [← same02.stor]
  have hold7 : d7.getStorVal sevm.currentTarget (balSlot sevm.caller) =
      (Devm.getStor devm sevm.currentTarget).get (balSlot sevm.caller) := by
    show (Devm.getStor d7 sevm.currentTarget).get (balSlot sevm.caller) = _
    rw [← same07.stor]
  rw [hold2] at hle
  rw [hold7] at hset
  obtain ⟨hleb, hinv⟩ := hstep (hpre.inv.left rfl) hle
  have hstor10 : Devm.getStor d10 sevm.currentTarget =
      (Devm.getStor devm sevm.currentTarget).set (balSlot sevm.caller)
        ((Devm.getStor devm sevm.currentTarget).get (balSlot sevm.caller) - wad) := by
    rw [← same910.stor, hset, ← same08.stor]
  have hbal10 : d10.getBal = devm.getBal := by
    rw [← same910.bal, ← hbal89, ← same08.bal]
  have hcode10 : d10.getCode = devm.getCode := by
    rw [← same910.code, ← hcode89, ← same08.code]
  have hpost : c.Post sevm.currentTarget sevm d11 := by
    refine ContractSpecSem.post_of_call_self hfork rfl ih hp10 ?_ ?_ ?_ ?_
      (of_run_singleton hcall)
    · rw [hcode10]; exact hpre.code
    · rw [hbal10]; exact hpre.side
    · rw [hbal10]; exact hleb
    · rw [hstor10, hbal10]; exact hinv
  exact ContractSpecSem.Post.of_state_eq hpost
    (SFunc.Run.state_of_silent silentSet_nil afterCall_silent afterCall_refs run)

/-- The debit step for the solvency invariant itself: the `hstep` premise of
`Weth9.withdraw_post` when the contract invariant is `Solvent`. -/
theorem Weth9.solvent_withdraw_step {s : Stor} {v b : B256} {a : Adr} {wad : B256}
    (h : Solvent s v b) (hle : wad ≤ s.get (balSlot a)) :
    wad ≤ b ∧ Solvent (s.set (balSlot a) (s.get (balSlot a) - wad)) 0 (b - wad) := by
  have hw := bookedSum_withdraw (a := a) hle
  unfold Solvent at h ⊢
  have hwb : wad.toNat ≤ b.toNat := by omega
  have hle' : wad ≤ b := B256.le_of_toNat_le_toNat hwb
  refine ⟨hle', ?_⟩
  rw [B256.toNat_sub_eq_of_le _ _ hle', B256.toNat_zero]
  omega

/-- **WETH9 `withdraw(wad)` preserves solvency**, for a `ContractSpecSem` whose
invariant is WETH9 solvency. -/
theorem Weth9.withdraw_solvent {ca : Adr}
    (hInv : ∀ s v b, c.Inv s v b ↔ Solvent s v b)
    {sevm : Sevm} {devm : Devm} {o : Outcome} {g : SFunc}
    (hfork : CoveredFork sevm.benvStat.fork) (hca : sevm.currentTarget = ca)
    (ih : ∀ pc' sevm' pre' post',
        Exec pc' sevm' pre' (.ok post') →
        sevm'.depth < sevm.depth →
        CodeSem.At c.sem ca pc' sevm' pre' →
        CoveredFork sevm'.benvStat.fork →
        c.PreWf ca sevm' pre' →
        c.Post ca sevm' post')
    (hg : prog[8]? = some g) (run : SFunc.Run prog sevm devm g o)
    (hpre : c.Pre ca sevm devm) :
    Solvent (Devm.getStor (Outcome.devm o) ca) 0 ((Outcome.devm o).getBal ca) := by
  have hstep : ∀ {s : Stor} {v b : B256} {a : Adr} {wad : B256},
      c.Inv s v b → wad ≤ s.get (balSlot a) →
      wad ≤ b ∧ c.Inv (s.set (balSlot a) (s.get (balSlot a) - wad)) 0 (b - wad) := by
    intro s v b a wad h hle
    obtain ⟨h1, h2⟩ := Weth9.solvent_withdraw_step ((hInv _ _ _).mp h) hle
    exact ⟨h1, (hInv _ _ _).mpr h2⟩
  exact (hInv _ _ _).mp (Weth9.withdraw_post hstep hfork hca ih hg run hpre).inv

end Withdraw

end Blanc.Lift
