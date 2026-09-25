import Blanc.Lift.Weth9.Spec
import Blanc.Lift.Weth9.Words
import Blanc.Lift.Weth9.Step

/-!
# Shared straight-line walks of the lifted WETH9 entries

The function proofs (`Deposit`, `Withdraw`, `Approve`, `TransferFrom`) walk
the same instruction lines: the Solidity mapping-slot computation
(`hashBlock`, and `hashLine` with its two address masks), the
read-modify-write before an `SSTORE` (`updLine`), the two words a `JUMPI`
pops, and the `revert` tail of a failed `require`.  They and the
persistent-state transports (`Same`, `SameCode`) live here once.
-/

namespace Blanc.Lift.Weth9

open Jaune
open Blanc
open Blanc.Lift

/-- `mapSlot a b` from stack `a :: 0 :: b`: two MSTOREs and a SHA3. -/
def hashBlock : List Ninst :=
  [.reg (.dup 1), .reg .mstore, .push [0x20] (by decide), .reg .add,
   .reg (.swap 0), .reg (.dup 1), .reg .mstore, .push [0x20] (by decide),
   .reg .add, .push [0x00] (by decide), .reg .keccak256]

theorem hash_block {sevm : Sevm} {s s' : Devm} {a b : B256} {xs : Stack}
    (run : Line.Run sevm s hashBlock s') (hp : a :: 0 :: b :: xs <<+ s.stack) :
    mapSlot a b :: xs <<+ s'.stack := by
  unfold hashBlock at run
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
  cases run
  have hp1 : (0 : B256) :: a :: 0 :: b :: xs <<+ s1.stack :=
    prefix_of_dup_val h1 (by show_nth) hp
  have hm1 : s.memory = s1.memory := Ninst.Hinv.inv h1
  have hA := prefix_of_mstore_val h2 hp1
  have hm2 : s2.memory = s.memory.write 0 a.toBytes := by
    rw [hA.2, ← hm1, w0_toNat]
  have hp3 : (32 : B256) :: (0 : B256) :: b :: xs <<+ s3.stack := by
    have := prefix_of_push (of_run_push h3) hA.1
    rwa [w20_eq] at this
  have hp4 : (32 : B256) :: b :: xs <<+ s4.stack := by
    have := prefix_of_add h4 hp3
    rwa [w32_add_0] at this
  have hp5 : b :: (32 : B256) :: xs <<+ s5.stack :=
    Stack.prefix_of_swap (n := 0) (by simp [Stack.Swap, Stack.SwapCore])
      (of_run_swap h5) hp4
  have hp6 : (32 : B256) :: b :: (32 : B256) :: xs <<+ s6.stack :=
    prefix_of_dup_val h6 (by show_nth) hp5
  have hm6 : s2.memory = s6.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (.cons h3 (.cons h4 (.cons h5 (.cons h6 .nil))))
  have hB := prefix_of_mstore_val h7 hp6
  have hm7 : s7.memory = (s.memory.write 0 a.toBytes).write 32 b.toBytes := by
    rw [hB.2, ← hm6, hm2, w32_toNat]
  have hp8 : (32 : B256) :: (32 : B256) :: xs <<+ s8.stack := by
    have := prefix_of_push (of_run_push h8) hB.1
    rwa [w20_eq] at this
  have hp9 : (64 : B256) :: xs <<+ s9.stack := by
    have := prefix_of_add h9 hp8
    rwa [w32_add_32] at this
  have hp10 : (0 : B256) :: (64 : B256) :: xs <<+ s10.stack := by
    have := prefix_of_push (of_run_push h10) hp9
    rwa [w00_eq] at this
  have hm10 : s7.memory = s10.memory :=
    Line.of_inv Devm.memory (by line_inv) (.cons h8 (.cons h9 (.cons h10 .nil)))
  have hmem : (((s.memory.write 0 a.toBytes).write 32 b.toBytes).read 0 64).1 =
      a.toBytes ++ b.toBytes := Mem.read_two_word_writes_at_raw s.memory 0 a b
  have := (prefix_of_keccak256_val h11 hp10).1
  rwa [← hm10, hm7, w0_toNat, w64_toNat, hmem] at this

/-- The 20-byte address mask `PUSH20 0xff..ff`. -/
abbrev pF : Ninst :=
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)

/-- `mstore(0, addr(x)); mstore(32, base); keccak256(0, 64)`, entered with the
word `x` above `0 :: base`: two address masks, then `hashBlock`. -/
def hashLine : List Ninst := [pF, .reg .and, pF, .reg .and] ++ hashBlock

theorem hash_walk {sevm : Sevm} {s s' : Devm} {x base : B256} {ys : Stack}
    (hp : x :: (0 : B256) :: base :: ys <<+ s.stack) (run : Line.Run sevm s hashLine s') :
    mapSlot x.toAdr.toB256 base :: ys <<+ s'.stack ∧
      Devm.getStor s' = Devm.getStor s ∧ s'.getBal = s.getBal := by
  have hstor : Devm.getStor s = Devm.getStor s' :=
    Line.of_inv Devm.getStor (by line_inv) run
  have hbal : s.getBal = s'.getBal := Line.of_inv Devm.getBal (by line_inv) run
  refine ⟨?_, hstor.symm, hbal.symm⟩
  obtain ⟨s4, run4, run⟩ := of_run_append [pF, .reg .and, pF, .reg .and] run
  obtain ⟨s1, h1, run4⟩ := Line.of_run_cons run4
  obtain ⟨s2, h2, run4⟩ := Line.of_run_cons run4
  obtain ⟨s3, h3, run4⟩ := Line.of_run_cons run4
  obtain ⟨s4', h4, run4⟩ := Line.of_run_cons run4
  cases run4
  have hp2 : x.toAdr.toB256 :: (0 : B256) :: base :: ys <<+ s2.stack := by
    have := prefix_of_and h2 (prefix_of_push (of_run_push h1) hp)
    rwa [ff20_and_word] at this
  have hp4 : x.toAdr.toB256 :: (0 : B256) :: base :: ys <<+ s4.stack := by
    have := prefix_of_and h4 (prefix_of_push (of_run_push h3) hp2)
    rwa [ff20_and_word, toAdr_toB256] at this
  exact hash_block run hp4

/-- `slot, w, y` ↦ `slot, f(sload slot, w), f(sload slot, w), y`: the part of a
read-modify-write before its `SSTORE`. -/
def updLine (op : Ninst) : List Ninst :=
  [.push [0x00] (by decide), .reg (.dup 2), .reg (.dup 2), .reg .sload, op,
   .reg (.swap 2), .reg .pop, .reg .pop, .reg (.dup 1), .reg (.swap 0)]

/-- The read-modify-write line, for an operation `op` computing `f`. -/
theorem upd_walk {sevm : Sevm} {s s' : Devm} {op : Ninst} {f : B256 → B256 → B256}
    {slot w y : B256} {xs : Stack}
    (hop : ∀ {a b : B256} {zs : Stack} {t t' : Devm}, Ninst.Run sevm t op t' →
      a :: b :: zs <<+ t.stack → f a b :: zs <<+ t'.stack)
    (hopStor : ∀ {t t' : Devm}, Ninst.Run sevm t op t' →
      Devm.getStor t = Devm.getStor t' ∧ t.getBal = t'.getBal)
    (hp : slot :: w :: y :: xs <<+ s.stack) (run : Line.Run sevm s (updLine op) s') :
    slot :: f (s.getStorVal sevm.currentTarget slot) w ::
        f (s.getStorVal sevm.currentTarget slot) w :: y :: xs <<+ s'.stack ∧
      Devm.getStor s' = Devm.getStor s ∧ s'.getBal = s.getBal := by
  unfold updLine at run
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
  have hst4 : Devm.getStor s = Devm.getStor s4 :=
    Line.of_inv Devm.getStor (by line_inv)
      (.cons h1 (.cons h2 (.cons h3 (.cons h4 .nil))))
  have hbal4 : s.getBal = s4.getBal :=
    Line.of_inv Devm.getBal (by line_inv)
      (.cons h1 (.cons h2 (.cons h3 (.cons h4 .nil))))
  have hst10 : Devm.getStor s5 = Devm.getStor s' :=
    Line.of_inv Devm.getStor (by line_inv)
      (.cons h6 (.cons h7 (.cons h8 (.cons h9 (.cons h10 .nil)))))
  have hbal10 : s5.getBal = s'.getBal :=
    Line.of_inv Devm.getBal (by line_inv)
      (.cons h6 (.cons h7 (.cons h8 (.cons h9 (.cons h10 .nil)))))
  have hold : s3.getStorVal sevm.currentTarget slot =
      s.getStorVal sevm.currentTarget slot := by
    have hst3 : Devm.getStor s = Devm.getStor s3 :=
      Line.of_inv Devm.getStor (by line_inv) (.cons h1 (.cons h2 (.cons h3 .nil)))
    show (Devm.getStor s3 sevm.currentTarget).get slot =
      (Devm.getStor s sevm.currentTarget).get slot
    rw [← hst3]
  refine ⟨?_, ?_, ?_⟩
  · have hp1 : (0 : B256) :: slot :: w :: y :: xs <<+ s1.stack := by
      have := prefix_of_push (of_run_push h1) hp
      rwa [w00_eq] at this
    have hp2 : w :: (0 : B256) :: slot :: w :: y :: xs <<+ s2.stack :=
      prefix_of_dup_val h2 (by show_nth) hp1
    have hp3 : slot :: w :: (0 : B256) :: slot :: w :: y :: xs <<+ s3.stack :=
      prefix_of_dup_val h3 (by show_nth) hp2
    obtain ⟨bal, hp4, hbal⟩ := prefix_of_sload h4 hp3
    rw [hold] at hbal
    subst hbal
    have hp5 := hop h5 hp4
    have hp6 : w :: (0 : B256) :: slot ::
        f (s.getStorVal sevm.currentTarget slot) w :: y :: xs <<+ s6.stack :=
      Stack.prefix_of_swap (n := 2) (by simp [Stack.Swap, Stack.SwapCore])
        (of_run_swap h6) hp5
    have hp8 := prefix_of_pop (of_run_pop h8) (prefix_of_pop (of_run_pop h7) hp6)
    have hp9 := prefix_of_dup_val h9 (by show_nth) hp8
    exact Stack.prefix_of_swap (n := 0) (by simp [Stack.Swap, Stack.SwapCore])
      (of_run_swap h10) hp9
  · rw [← hst10, ← (hopStor h5).1, ← hst4]
  · rw [← hbal10, ← (hopStor h5).2, ← hbal4]

theorem sub_walk {sevm : Sevm} {slot w y : B256} {xs : Stack} {s s' : Devm}
    (hp : slot :: w :: y :: xs <<+ s.stack) (run : Line.Run sevm s (updLine (.reg .sub)) s') :
    slot :: (s.getStorVal sevm.currentTarget slot - w) ::
        (s.getStorVal sevm.currentTarget slot - w) :: y :: xs <<+ s'.stack ∧
      Devm.getStor s' = Devm.getStor s ∧ s'.getBal = s.getBal :=
  upd_walk (f := fun a b => a - b) (fun h hp => prefix_of_sub h hp)
    (fun h => ⟨Line.of_inv Devm.getStor (by line_inv) (.cons h .nil),
      Line.of_inv Devm.getBal (by line_inv) (.cons h .nil)⟩) hp run

theorem add_walk {sevm : Sevm} {slot w y : B256} {xs : Stack} {s s' : Devm}
    (hp : slot :: w :: y :: xs <<+ s.stack) (run : Line.Run sevm s (updLine (.reg .add)) s') :
    slot :: (s.getStorVal sevm.currentTarget slot + w) ::
        (s.getStorVal sevm.currentTarget slot + w) :: y :: xs <<+ s'.stack ∧
      Devm.getStor s' = Devm.getStor s ∧ s'.getBal = s.getBal :=
  upd_walk (f := fun a b => a + b) (fun h hp => prefix_of_add h hp)
    (fun h => ⟨Line.of_inv Devm.getStor (by line_inv) (.cons h .nil),
      Line.of_inv Devm.getBal (by line_inv) (.cons h .nil)⟩) hp run

/-- Two words popped by a `JUMPI`. -/
theorem prefix_of_popBurn2 {s s' : Devm} {a b d w : B256} {xs : Stack}
    (hp : a :: b :: xs <<+ s.stack) (h : Devm.PopBurn [d, w] s s') :
    a = d ∧ b = w ∧ xs <<+ s'.stack := by
  have hs : s.stack = d :: w :: s'.stack := h.stack
  rcases hp with ⟨t, ht⟩
  have ht' : s.stack = a :: b :: (xs ++ t) := ht
  rw [hs] at ht'
  injection ht' with h1 ht'
  injection ht' with h2 ht'
  exact ⟨h1.symm, h2.symm, t, ht'⟩

theorem not_run_revert_tail {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} {devm : Devm}
    {o : Outcome} :
    ¬ SFunc.RunP P fs sevm devm
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


/-- Persistent storage and balances shared by two machine states. -/
structure Same (a b : Devm) : Prop where
  stor : Devm.getStor a = Devm.getStor b
  bal : a.getBal = b.getBal

theorem Same.of_state {a b : Devm} (h : a.state = b.state) : Same a b :=
  ⟨funext (getStor_eq_of_state_eq h), funext (getBal_eq_of_state_eq h)⟩

theorem Same.trans {a b c : Devm} (h : Same a b) (h' : Same b c) : Same a c :=
  ⟨h.stor.trans h'.stor, h.bal.trans h'.bal⟩

/-- `Same`, and the code of every account as well. -/
structure SameCode (a b : Devm) : Prop where
  stor : Devm.getStor a = Devm.getStor b
  bal : a.getBal = b.getBal
  code : a.getCode = b.getCode

theorem SameCode.toSame {a b : Devm} (h : SameCode a b) : Same a b := ⟨h.stor, h.bal⟩

theorem SameCode.of_state {a b : Devm} (h : a.state = b.state) : SameCode a b :=
  ⟨funext (getStor_eq_of_state_eq h), funext (getBal_eq_of_state_eq h),
    funext (getCode_eq_of_state_eq h)⟩

theorem SameCode.trans {a b c : Devm} (h : SameCode a b) (h' : SameCode b c) :
    SameCode a c :=
  ⟨h.stor.trans h'.stor, h.bal.trans h'.bal, h.code.trans h'.code⟩

/-- The empty entry set is trivially closed. -/
theorem silentSet_nil : SilentSet prog [] = true := rfl

/-- Forgetting the callvalue in flight. -/
theorem solvent_zero {s : Stor} {v b : B256} (h : Solvent s v b) : Solvent s 0 b := by
  unfold Solvent at h ⊢
  rw [B256.toNat_zero]
  omega

end Blanc.Lift.Weth9
