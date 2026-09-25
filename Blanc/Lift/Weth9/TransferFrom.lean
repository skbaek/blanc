import Blanc.Lift.Weth9.Premise
import Blanc.Lift.Silent

/-!
# WETH9 `transferFrom` and `transfer` preserve solvency

Entry 9 of the lifted WETH9 (`t_068c_c9`, pc `0x68c`, frame `[wad, dst, src, ret]`):

```
require(balanceOf[src] >= wad);
if (src != msg.sender && allowance[src][msg.sender] != uint(-1)) {
    require(allowance[src][msg.sender] >= wad);
    allowance[src][msg.sender] -= wad;
}
balanceOf[src] -= wad;  balanceOf[dst] += wad;  Transfer(src, dst, wad);  return true;
```

The walk is explicit, one basic block at a time, as in `Deposit.lean`.  The
three mapping-slot computations share one line (`hashLine`) and the two
read-modify-write updates share another (`updLine`).  Each block lemma
concludes `XferEff`: the ether balances are untouched and the storage of the
current target is the two balance writes (`xferStor`), optionally preceded by a
write to the allowance slot, which happens only when `src ≠ caller`.

Entry 3 (`transfer`) calls entry 9 with `src = caller`, so the allowance
branch, and with it the collision premise, disappears.
-/

namespace Blanc.Lift

open Jaune
open Blanc
open Weth9

namespace Weth9

/-- The storage after `balanceOf[src] -= wad; balanceOf[dst] += wad`. -/
def xferStor (s : Stor) (src dst : Adr) (wad : B256) : Stor :=
  (s.set (balSlot src) (s.get (balSlot src) - wad)).set (balSlot dst)
    ((s.set (balSlot src) (s.get (balSlot src) - wad)).get (balSlot dst) + wad)

end Weth9

private theorem ff20_and_word (x : B256) :
    (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& x) =
      x.toAdr.toB256 := by
  rw [ff20_eq]
  exact addressSlotReadWord_eq_toAdr_toB256 x

private theorem and_mask_word (x : B256) : (x &&& ~~~ addressMask) = x.toAdr.toB256 := by
  rw [B256.and_comm]
  exact addressSlotReadWord_eq_toAdr_toB256 x

private theorem w04_eq : Bytes.toB256 [0x04] = 4 := by decide

/-- `mstore(0, addr(x)); mstore(32, base); keccak256(0, 64)`, entered with the
word `x` above `0 :: base`. -/
private def hashLine : List Ninst :=
  [.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
     0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
   .reg .and,
   .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
     0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
   .reg .and, .reg (.dup 1), .reg .mstore,
   .push [0x20] (by decide), .reg .add, .reg (.swap 0), .reg (.dup 1),
   .reg .mstore, .push [0x20] (by decide), .reg .add,
   .push [0x00] (by decide), .reg .keccak256]

/-- `slot, w, y` ↦ `slot, f(sload slot, w), f(sload slot, w), y`: the part of a
read-modify-write before its `SSTORE`. -/
private def updLine (op : Ninst) : List Ninst :=
  [.push [0x00] (by decide), .reg (.dup 2), .reg (.dup 2), .reg .sload, op,
   .reg (.swap 2), .reg .pop, .reg .pop, .reg (.dup 1), .reg (.swap 0)]

private theorem hash_walk {sevm : Sevm} {s s' : Devm} {x base : B256} {ys : Stack}
    (hp : x :: (0 : B256) :: base :: ys <<+ s.stack) (run : Line.Run sevm s hashLine s') :
    mapSlot x.toAdr.toB256 base :: ys <<+ s'.stack ∧
      Devm.getStor s' = Devm.getStor s ∧ s'.getBal = s.getBal := by
  have hstor : Devm.getStor s = Devm.getStor s' :=
    Line.of_inv Devm.getStor (by line_inv) run
  have hbal : s.getBal = s'.getBal := Line.of_inv Devm.getBal (by line_inv) run
  refine ⟨?_, hstor.symm, hbal.symm⟩
  have hmem2 : ∀ μ : Mem,
      (((μ.write 0 x.toAdr.toB256.toBytes).write 32 base.toBytes).read 0 64).1 =
        x.toAdr.toB256.toBytes ++ base.toBytes := fun μ =>
    Mem.read_two_word_writes_at_raw μ 0 x.toAdr.toB256 base
  unfold hashLine at run
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
  cases run
  have hp2 : x.toAdr.toB256 :: (0 : B256) :: base :: ys <<+ s2.stack := by
    have := prefix_of_and h2 (prefix_of_push (of_run_push h1) hp)
    rwa [ff20_and_word] at this
  have hp4 : x.toAdr.toB256 :: (0 : B256) :: base :: ys <<+ s4.stack := by
    have := prefix_of_and h4 (prefix_of_push (of_run_push h3) hp2)
    rwa [ff20_and_word, toAdr_toB256] at this
  have hp5 : (0 : B256) :: x.toAdr.toB256 :: (0 : B256) :: base :: ys <<+ s5.stack :=
    prefix_of_dup_val h5 (by show_nth) hp4
  have hB := prefix_of_mstore_val h6 hp5
  have hp6 : (0 : B256) :: base :: ys <<+ s6.stack := hB.1
  have hp7 : (32 : B256) :: (0 : B256) :: base :: ys <<+ s7.stack := by
    have := prefix_of_push (of_run_push h7) hp6
    rwa [w20_eq] at this
  have hp8 : (32 : B256) :: base :: ys <<+ s8.stack := by
    have := prefix_of_add h8 hp7
    rwa [w32_add_0] at this
  have hp9 : base :: (32 : B256) :: ys <<+ s9.stack :=
    Stack.prefix_of_swap (n := 0) (by simp [Stack.Swap, Stack.SwapCore])
      (of_run_swap h9) hp8
  have hp10 : (32 : B256) :: base :: (32 : B256) :: ys <<+ s10.stack :=
    prefix_of_dup_val h10 (by show_nth) hp9
  have hm10 : s6.memory = s10.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (.cons h7 (.cons h8 (.cons h9 (.cons h10 .nil))))
  have hC := prefix_of_mstore_val h11 hp10
  have hp11 : (32 : B256) :: ys <<+ s11.stack := hC.1
  have hm11 : s11.memory =
      (s5.memory.write 0 x.toAdr.toB256.toBytes).write 32 base.toBytes := by
    rw [hC.2, ← hm10, hB.2, w0_toNat, w32_toNat]
  have hp12 : (32 : B256) :: (32 : B256) :: ys <<+ s12.stack := by
    have := prefix_of_push (of_run_push h12) hp11
    rwa [w20_eq] at this
  have hp13 : (64 : B256) :: ys <<+ s13.stack := by
    have := prefix_of_add h13 hp12
    rwa [w32_add_32] at this
  have hp14 : (0 : B256) :: (64 : B256) :: ys <<+ s14.stack := by
    have := prefix_of_push (of_run_push h14) hp13
    rwa [w00_eq] at this
  have hm14 : s11.memory = s14.memory :=
    Line.of_inv Devm.memory (by line_inv) (.cons h12 (.cons h13 (.cons h14 .nil)))
  have := (prefix_of_keccak256_val h15 hp14).1
  rw [← hm14, hm11, w0_toNat, w64_toNat, hmem2] at this
  exact this

/-- The read-modify-write line, for an operation `op` computing `f`. -/
private theorem upd_walk {sevm : Sevm} {s s' : Devm} {op : Ninst} {f : B256 → B256 → B256}
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

/-- Persistent observations shared by two machine states. -/
private def Same (a b : Devm) : Prop := Devm.getStor a = Devm.getStor b ∧ a.getBal = b.getBal

private theorem Same.trans {a b c : Devm} (h : Same a b) (h' : Same b c) : Same a c :=
  ⟨h.1.trans h'.1, h.2.trans h'.2⟩

private theorem Same.of_state {a b : Devm} (h : a.state = b.state) : Same a b :=
  ⟨funext (getStor_eq_of_state_eq h), funext (getBal_eq_of_state_eq h)⟩

private theorem silentSet_nil : SilentSet prog [] = true := rfl

private def pre08cf : List Ninst :=
  [.reg (.dup 1), .push [0x03] (by decide), .push [0x00] (by decide), .reg (.dup 6)]

private def mid08cf : List Ninst :=
  [.reg .pop, .reg (.dup 1), .push [0x03] (by decide), .push [0x00] (by decide),
   .reg (.dup 5)]

private theorem tree_08cf : ∃ tail : SFunc,
    t_08cf_c9 = .dest (chain (pre08cf ++ hashLine ++ updLine (.reg .sub) ++
      [Ninst.sstore] ++ mid08cf ++ hashLine ++ updLine (.reg .add) ++ [Ninst.sstore]) tail) ∧
    tail.silent = true ∧ tail.refs.all (· ∈ ([] : List Nat)) = true :=
  ⟨_, rfl, by decide, by decide⟩

private theorem sub_walk {sevm : Sevm} {slot w y : B256} {xs : Stack} {s s' : Devm}
    (hp : slot :: w :: y :: xs <<+ s.stack) (run : Line.Run sevm s (updLine (.reg .sub)) s') :
    slot :: (s.getStorVal sevm.currentTarget slot - w) ::
        (s.getStorVal sevm.currentTarget slot - w) :: y :: xs <<+ s'.stack ∧
      Devm.getStor s' = Devm.getStor s ∧ s'.getBal = s.getBal :=
  upd_walk (f := fun a b => a - b) (fun h hp => prefix_of_sub h hp)
    (fun h => ⟨Line.of_inv Devm.getStor (by line_inv) (.cons h .nil),
      Line.of_inv Devm.getBal (by line_inv) (.cons h .nil)⟩) hp run

private theorem add_walk {sevm : Sevm} {slot w y : B256} {xs : Stack} {s s' : Devm}
    (hp : slot :: w :: y :: xs <<+ s.stack) (run : Line.Run sevm s (updLine (.reg .add)) s') :
    slot :: (s.getStorVal sevm.currentTarget slot + w) ::
        (s.getStorVal sevm.currentTarget slot + w) :: y :: xs <<+ s'.stack ∧
      Devm.getStor s' = Devm.getStor s ∧ s'.getBal = s.getBal :=
  upd_walk (f := fun a b => a + b) (fun h hp => prefix_of_add h hp)
    (fun h => ⟨Line.of_inv Devm.getStor (by line_inv) (.cons h .nil),
      Line.of_inv Devm.getBal (by line_inv) (.cons h .nil)⟩) hp run

/-- Block `0x8cf`: the two balance writes, then the event and the return. -/
private theorem xfer_08cf {sevm : Sevm} {d : Devm} {o : Outcome}
    {y wad dst src : B256} {xs : Stack}
    (hp : y :: wad :: dst :: src :: xs <<+ d.stack)
    (run : SFunc.Run prog sevm d t_08cf_c9 o) :
    (Outcome.devm o).getBal = d.getBal ∧
      Devm.getStor (Outcome.devm o) sevm.currentTarget =
        xferStor (Devm.getStor d sevm.currentTarget) src.toAdr dst.toAdr wad := by
  obtain ⟨tail, htree, hsil, hrefs⟩ := tree_08cf
  rw [htree] at run
  cases run with
  | dest burn run =>
  rename_i d0
  obtain ⟨d1, r1, run⟩ := run_chain_prefix pre08cf _ run
  obtain ⟨d2, r2, run⟩ := run_chain_prefix hashLine _ run
  obtain ⟨d3, r3, run⟩ := run_chain_prefix (updLine (.reg .sub)) _ run
  obtain ⟨d4, r4, run⟩ := run_chain_prefix [Ninst.sstore] _ run
  obtain ⟨d5, r5, run⟩ := run_chain_prefix mid08cf _ run
  obtain ⟨d6, r6, run⟩ := run_chain_prefix hashLine _ run
  obtain ⟨d7, r7, run⟩ := run_chain_prefix (updLine (.reg .add)) _ run
  obtain ⟨d8, r8, run⟩ := run_chain_prefix [Ninst.sstore] [] run
  have htail := SFunc.Run.state_of_silent silentSet_nil hsil hrefs run
  have s00 : Same d d0 := Same.of_state burn.state
  have hp0 : y :: wad :: dst :: src :: xs <<+ d0.stack := by
    rw [← burn.stack]; exact hp
  -- DUP2; PUSH 3; PUSH 0; DUP7
  have s01 : Same d0 d1 :=
    ⟨Line.of_inv Devm.getStor (by line_inv) r1, Line.of_inv Devm.getBal (by line_inv) r1⟩
  have hp1 : src :: (0 : B256) :: (3 : B256) :: wad :: y :: wad :: dst :: src :: xs
      <<+ d1.stack := by
    unfold pre08cf at r1
    obtain ⟨a1, h1, r1⟩ := Line.of_run_cons r1
    obtain ⟨a2, h2, r1⟩ := Line.of_run_cons r1
    obtain ⟨a3, h3, r1⟩ := Line.of_run_cons r1
    obtain ⟨a4, h4, r1⟩ := Line.of_run_cons r1
    cases r1
    have q1 : wad :: y :: wad :: dst :: src :: xs <<+ a1.stack :=
      prefix_of_dup_val h1 (by show_nth) hp0
    have q2 : (3 : B256) :: wad :: y :: wad :: dst :: src :: xs <<+ a2.stack := by
      have := prefix_of_push (of_run_push h2) q1
      rwa [w03_eq] at this
    have q3 : (0 : B256) :: (3 : B256) :: wad :: y :: wad :: dst :: src :: xs
        <<+ a3.stack := by
      have := prefix_of_push (of_run_push h3) q2
      rwa [w00_eq] at this
    exact prefix_of_dup_val h4 (by show_nth) q3
  obtain ⟨hp2, hs2, hb2⟩ := hash_walk hp1 r2
  obtain ⟨hp3, hs3, hb3⟩ := sub_walk hp2 r3
  have h4 := of_run_singleton r4
  have hset4 := sstore_getStor_set h4 hp3
  have hp4 := prefix_of_sstore h4 hp3
  have hb4 : d3.getBal = d4.getBal := Ninst.Hinv.inv h4
  -- POP; DUP2; PUSH 3; PUSH 0; DUP6
  have s45 : Same d4 d5 :=
    ⟨Line.of_inv Devm.getStor (by line_inv) r5, Line.of_inv Devm.getBal (by line_inv) r5⟩
  have hp5 : dst :: (0 : B256) :: (3 : B256) :: wad :: y :: wad :: dst :: src :: xs
      <<+ d5.stack := by
    unfold mid08cf at r5
    obtain ⟨a0, h0, r5⟩ := Line.of_run_cons r5
    obtain ⟨a1, h1, r5⟩ := Line.of_run_cons r5
    obtain ⟨a2, h2, r5⟩ := Line.of_run_cons r5
    obtain ⟨a3, h3, r5⟩ := Line.of_run_cons r5
    obtain ⟨a4, h4, r5⟩ := Line.of_run_cons r5
    cases r5
    have q0 : y :: wad :: dst :: src :: xs <<+ a0.stack :=
      prefix_of_pop (of_run_pop h0) hp4
    have q1 : wad :: y :: wad :: dst :: src :: xs <<+ a1.stack :=
      prefix_of_dup_val h1 (by show_nth) q0
    have q2 : (3 : B256) :: wad :: y :: wad :: dst :: src :: xs <<+ a2.stack := by
      have := prefix_of_push (of_run_push h2) q1
      rwa [w03_eq] at this
    have q3 : (0 : B256) :: (3 : B256) :: wad :: y :: wad :: dst :: src :: xs
        <<+ a3.stack := by
      have := prefix_of_push (of_run_push h3) q2
      rwa [w00_eq] at this
    exact prefix_of_dup_val h4 (by show_nth) q3
  obtain ⟨hp6, hs6, hb6⟩ := hash_walk hp5 r6
  obtain ⟨hp7, hs7, hb7⟩ := add_walk hp6 r7
  have h8 := of_run_singleton r8
  have hset8 := sstore_getStor_set h8 hp7
  have hb8 : d7.getBal = d8.getBal := Ninst.Hinv.inv h8
  have s8o : Same d8 (Outcome.devm o) := Same.of_state htail.symm
  -- assemble
  have s02 : Same d d2 := s00.trans (s01.trans ⟨hs2.symm, hb2.symm⟩)
  have s47 : Same d4 d7 := s45.trans ⟨hs6.symm.trans hs7.symm, hb6.symm.trans hb7.symm⟩
  refine ⟨?_, ?_⟩
  · rw [← s8o.2, ← hb8, ← s47.2, ← hb4, hb3, ← s02.2]
  · have hv2 : d2.getStorVal sevm.currentTarget (mapSlot src.toAdr.toB256 3) =
        (Devm.getStor d sevm.currentTarget).get (balSlot src.toAdr) := by
      show (Devm.getStor d2 sevm.currentTarget).get _ = _
      rw [← s02.1]
      rfl
    have hv6 : d6.getStorVal sevm.currentTarget (mapSlot dst.toAdr.toB256 3) =
        (Devm.getStor d4 sevm.currentTarget).get (balSlot dst.toAdr) := by
      show (Devm.getStor d6 sevm.currentTarget).get _ = _
      rw [hs6, ← s45.1]
      rfl
    rw [← s8o.1, hset8, hv6, hs7, hs6, ← s45.1, hset4, hv2, hs3, ← s02.1]
    rfl

/-! ### The allowance branch -/

/-- What every block from `0x6dc` on does to the persistent state: balances are
untouched, and the storage is the two balance writes, possibly preceded by an
allowance write that happens only when `src ≠ caller`. -/
private def XferEff (sevm : Sevm) (d : Devm) (o : Outcome) (wad dst src : B256) : Prop :=
  (Outcome.devm o).getBal = d.getBal ∧
    (Devm.getStor (Outcome.devm o) sevm.currentTarget =
        xferStor (Devm.getStor d sevm.currentTarget) src.toAdr dst.toAdr wad ∨
      (src.toAdr.toB256 ≠ sevm.caller.toB256 ∧ ∃ w,
        Devm.getStor (Outcome.devm o) sevm.currentTarget =
          xferStor ((Devm.getStor d sevm.currentTarget).set
            (allowKey src.toAdr.toB256 sevm.caller.toB256) w) src.toAdr dst.toAdr wad))

private theorem XferEff.of_same {sevm : Sevm} {d d' : Devm} {o : Outcome} {wad dst src : B256}
    (h : Same d d') (e : XferEff sevm d' o wad dst src) : XferEff sevm d o wad dst src := by
  unfold XferEff at *
  rw [h.1, h.2]
  exact e

/-- `iszero(iszero(iszero(lt(bal, wad))))` is nonzero only when `wad ≤ bal`. -/
private theorem le_of_check {bal wad : B256}
    (h : ((((bal <? wad) =? 0) =? 0) =? 0) ≠ 0) : wad ≤ bal := by
  rw [← B256.not_lt]
  intro hlt
  apply h
  rw [B256.ltCheck, ite_eq_left_of_eq_true _ _ (eq_true hlt)]
  decide

private theorem eq_zero_of_isz_ne {x : B256} (h : (x =? 0) ≠ 0) : x = 0 := by
  unfold B256.eqCheck at h
  split at h
  · assumption
  · exact absurd rfl h

private theorem ne_zero_of_isz_eq {x : B256} (h : (x =? 0) = 0) : x ≠ 0 := by
  intro hx
  subst hx
  revert h
  decide

private theorem ne_of_eqc_eq {x y : B256} (h : (x =? y) = 0) : x ≠ y := by
  intro hx
  subst hx
  unfold B256.eqCheck at h
  rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)] at h
  revert h
  decide

/-- Two words popped by a `JUMPI`. -/
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

/-- `allowance[src][caller]`: two nested slot computations. -/
private def allowLine : List Ninst :=
  hashLine ++ [.push [0x00] (by decide), .reg .caller] ++ hashLine

private theorem allow_walk {sevm : Sevm} {s s' : Devm} {src z : B256} {ys : Stack}
    (hp : src :: (0 : B256) :: (4 : B256) :: z :: ys <<+ s.stack)
    (run : Line.Run sevm s allowLine s') :
    allowKey src.toAdr.toB256 sevm.caller.toB256 :: z :: ys <<+ s'.stack ∧ Same s s' := by
  unfold allowLine at run
  obtain ⟨s1, r1, run⟩ := of_run_append hashLine run
  obtain ⟨s2, r2, r3⟩ := of_run_append [.push [0x00] (by decide), .reg .caller] run
  obtain ⟨hp1, hs1, hb1⟩ := hash_walk hp r1
  have s12 : Same s1 s2 :=
    ⟨Line.of_inv Devm.getStor (by line_inv) r2, Line.of_inv Devm.getBal (by line_inv) r2⟩
  have hp2 : sevm.caller.toB256 :: (0 : B256) :: mapSlot src.toAdr.toB256 4 :: z :: ys
      <<+ s2.stack := by
    obtain ⟨a1, h1, r2⟩ := Line.of_run_cons r2
    obtain ⟨a2, h2, r2⟩ := Line.of_run_cons r2
    cases r2
    have q1 : (0 : B256) :: mapSlot src.toAdr.toB256 4 :: z :: ys <<+ a1.stack := by
      have := prefix_of_push (of_run_push h1) hp1
      rwa [w00_eq] at this
    exact prefix_of_push (of_run_caller h2) q1
  obtain ⟨hp3, hs3, hb3⟩ := hash_walk hp2 r3
  rw [toAdr_toB256] at hp3
  exact ⟨hp3, Same.trans (⟨hs1.symm, hb1.symm⟩ : Same s s1) (s12.trans ⟨hs3.symm, hb3.symm⟩)⟩

/-- The `require` comparison: `iszero(iszero(iszero(lt(sload slot, w))))`, then
the jump destination. -/
private def cmpLine (bs : Bytes) (h : bs.length ≤ 32) : List Ninst :=
  [.reg .sload, .reg .lt, .reg .iszero, .reg .iszero, .reg .iszero, .push bs h]

private theorem cmp_walk {sevm : Sevm} {s s' : Devm} {bs : Bytes} {hbs : bs.length ≤ 32}
    {slot w : B256} {ys : Stack}
    (hp : slot :: w :: ys <<+ s.stack) (run : Line.Run sevm s (cmpLine bs hbs) s') :
    (∃ p, p :: ((((s.getStorVal sevm.currentTarget slot <? w) =? 0) =? 0) =? 0) :: ys
      <<+ s'.stack) ∧ Same s s' := by
  unfold cmpLine at run
  refine ⟨?_, Line.of_inv Devm.getStor (by line_inv) run,
    Line.of_inv Devm.getBal (by line_inv) run⟩
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

/-- `DUP2; PUSH1 4; PUSH1 0; DUP7`. -/
private def aPre : List Ninst :=
  [.reg (.dup 1), .push [0x04] (by decide), .push [0x00] (by decide), .reg (.dup 6)]

private theorem aPre_walk {sevm : Sevm} {s s' : Devm} {y wad dst src : B256} {xs : Stack}
    (hp : y :: wad :: dst :: src :: xs <<+ s.stack) (run : Line.Run sevm s aPre s') :
    src :: (0 : B256) :: (4 : B256) :: wad :: y :: wad :: dst :: src :: xs <<+ s'.stack ∧
      Same s s' := by
  unfold aPre at run
  refine ⟨?_, Line.of_inv Devm.getStor (by line_inv) run,
    Line.of_inv Devm.getBal (by line_inv) run⟩
  obtain ⟨a1, h1, run⟩ := Line.of_run_cons run
  obtain ⟨a2, h2, run⟩ := Line.of_run_cons run
  obtain ⟨a3, h3, run⟩ := Line.of_run_cons run
  obtain ⟨a4, h4, run⟩ := Line.of_run_cons run
  cases run
  have q1 : wad :: y :: wad :: dst :: src :: xs <<+ a1.stack :=
    prefix_of_dup_val h1 (by show_nth) hp
  have q2 : (4 : B256) :: wad :: y :: wad :: dst :: src :: xs <<+ a2.stack := by
    have := prefix_of_push (of_run_push h2) q1
    rwa [w04_eq] at this
  have q3 : (0 : B256) :: (4 : B256) :: wad :: y :: wad :: dst :: src :: xs
      <<+ a3.stack := by
    have := prefix_of_push (of_run_push h3) q2
    rwa [w00_eq] at this
  exact prefix_of_dup_val h4 (by show_nth) q3

private theorem tree_0844 :
    t_0844_c9 = .dest (chain (aPre ++ allowLine ++ updLine (.reg .sub) ++
      [Ninst.sstore, .reg .pop]) t_08cf_c9) := rfl

/-- Block `0x844`: the allowance debit, then block `0x8cf`. -/
private theorem xfer_0844 {sevm : Sevm} {d : Devm} {o : Outcome}
    {y wad dst src : B256} {xs : Stack}
    (hne : src.toAdr.toB256 ≠ sevm.caller.toB256)
    (hp : y :: wad :: dst :: src :: xs <<+ d.stack)
    (run : SFunc.Run prog sevm d t_0844_c9 o) :
    XferEff sevm d o wad dst src := by
  rw [tree_0844] at run
  cases run with
  | dest burn run =>
  rename_i d0
  obtain ⟨d1, r1, run⟩ := run_chain_prefix aPre _ run
  obtain ⟨d2, r2, run⟩ := run_chain_prefix allowLine _ run
  obtain ⟨d3, r3, run⟩ := run_chain_prefix (updLine (.reg .sub)) _ run
  obtain ⟨d4, r4, run⟩ := run_chain_prefix [Ninst.sstore] _ run
  obtain ⟨d5, r5, run⟩ := run_chain_prefix [.reg .pop] [] run
  have s00 : Same d d0 := Same.of_state burn.state
  have hp0 : y :: wad :: dst :: src :: xs <<+ d0.stack := by
    rw [← burn.stack]; exact hp
  obtain ⟨hp1, s01⟩ := aPre_walk hp0 r1
  obtain ⟨hp2, s12⟩ := allow_walk hp1 r2
  obtain ⟨hp3, hs3, hb3⟩ := sub_walk hp2 r3
  have h4 := of_run_singleton r4
  have hset4 := sstore_getStor_set h4 hp3
  have hp4 := prefix_of_sstore h4 hp3
  have hb4 : d3.getBal = d4.getBal := Ninst.Hinv.inv h4
  have h5 := of_run_singleton r5
  have hp5 := prefix_of_pop (of_run_pop h5) hp4
  have s45 : Same d4 d5 :=
    ⟨Line.of_inv Devm.getStor (by line_inv) r5, Line.of_inv Devm.getBal (by line_inv) r5⟩
  obtain ⟨hbo, hso⟩ := xfer_08cf hp5 run
  have s02 : Same d d2 := s00.trans (s01.trans s12)
  refine ⟨?_, Or.inr ⟨hne,
    d2.getStorVal sevm.currentTarget (allowKey src.toAdr.toB256 sevm.caller.toB256) - wad, ?_⟩⟩
  · rw [hbo, ← s45.2, ← hb4, hb3, ← s02.2]
  · rw [hso, ← s45.1, hset4, hs3, ← s02.1]

private theorem tree_07ba :
    t_07ba_c9 = chain (aPre ++ allowLine ++ cmpLine [0x08, 0x44] (by decide))
      (.branch t_0840_c9 t_0844_c9) := rfl

/-- Block `0x7ba`: the allowance `require`, then block `0x844`. -/
private theorem xfer_07ba {sevm : Sevm} {d : Devm} {o : Outcome}
    {y wad dst src : B256} {xs : Stack}
    (hne : src.toAdr.toB256 ≠ sevm.caller.toB256)
    (hp : y :: wad :: dst :: src :: xs <<+ d.stack)
    (run : SFunc.Run prog sevm d t_07ba_c9 o) :
    XferEff sevm d o wad dst src := by
  rw [tree_07ba] at run
  obtain ⟨d1, r1, run⟩ := run_chain_prefix aPre _ run
  obtain ⟨d2, r2, run⟩ := run_chain_prefix allowLine _ run
  obtain ⟨d3, r3, run⟩ := run_chain_prefix (cmpLine [0x08, 0x44] (by decide)) [] run
  obtain ⟨hp1, s01⟩ := aPre_walk hp r1
  obtain ⟨hp2, s12⟩ := allow_walk hp1 r2
  obtain ⟨⟨pd, hp3⟩, s23⟩ := cmp_walk hp2 r3
  change SFunc.Run prog sevm d3 (.branch t_0840_c9 t_0844_c9) o at run
  cases run with
  | zero _ _ run => exact absurd run not_run_revert_tail
  | succ dw w hwnz pop run =>
  rename_i d4
  obtain ⟨-, -, hp4⟩ := prefix_of_popBurn2 hp3 pop
  exact XferEff.of_same (s01.trans (s12.trans (s23.trans (Same.of_state pop.state))))
    (xfer_0844 hne hp4 run)

private theorem tree_07b4 :
    t_07b4_c9 = .dest (chain [.reg .iszero, .push [0x08, 0xcf] (by decide)]
      (.branch t_07ba_c9 t_08cf_c9)) := rfl

/-- Block `0x7b4`: the join of the two `&&` operands; `v ≠ 0` enters the
allowance debit, which needs `src ≠ caller`. -/
private theorem xfer_07b4 {sevm : Sevm} {d : Devm} {o : Outcome}
    {v y wad dst src : B256} {xs : Stack}
    (hv : v ≠ 0 → src.toAdr.toB256 ≠ sevm.caller.toB256)
    (hp : v :: y :: wad :: dst :: src :: xs <<+ d.stack)
    (run : SFunc.Run prog sevm d t_07b4_c9 o) :
    XferEff sevm d o wad dst src := by
  rw [tree_07b4] at run
  cases run with
  | dest burn run =>
  rename_i d0
  obtain ⟨d1, r1, run⟩ := run_chain_prefix [.reg .iszero, .push [0x08, 0xcf] (by decide)] [] run
  have hp0 : v :: y :: wad :: dst :: src :: xs <<+ d0.stack := by
    rw [← burn.stack]; exact hp
  have s01 : Same d d1 := Same.trans (Same.of_state burn.state)
    ⟨Line.of_inv Devm.getStor (by line_inv) r1, Line.of_inv Devm.getBal (by line_inv) r1⟩
  have hp1 : ∃ pd, pd :: (v =? 0) :: y :: wad :: dst :: src :: xs <<+ d1.stack := by
    obtain ⟨a1, h1, r1⟩ := Line.of_run_cons r1
    obtain ⟨a2, h2, r1⟩ := Line.of_run_cons r1
    cases r1
    exact ⟨_, prefix_of_push (of_run_push h2) (prefix_of_iszero h1 hp0)⟩
  obtain ⟨pd, hp1⟩ := hp1
  change SFunc.Run prog sevm d1 (.branch t_07ba_c9 t_08cf_c9) o at run
  cases run with
  | zero _ pop run =>
    rename_i d2
    obtain ⟨-, hc, hp2⟩ := prefix_of_popBurn2 hp1 pop
    exact XferEff.of_same (s01.trans (Same.of_state pop.state))
      (xfer_07ba (hv (ne_zero_of_isz_eq hc)) hp2 run)
  | succ dw w hwnz pop run =>
    rename_i d2
    obtain ⟨-, -, hp2⟩ := prefix_of_popBurn2 hp1 pop
    obtain ⟨hbo, hso⟩ := xfer_08cf hp2 run
    have s02 := s01.trans (Same.of_state pop.state)
    exact ⟨hbo.trans s02.2.symm, Or.inl (by rw [hso, ← s02.1])⟩

private def pre0713 : List Ninst :=
  [.reg .pop, .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff] (by decide), .push [0x04] (by decide), .push [0x00] (by decide), .reg (.dup 6)]

private theorem tree_0713 :
    t_0713_c9 = chain (pre0713 ++ allowLine ++ [.reg .sload, .reg .eq, .reg .iszero])
      t_07b4_c9 := rfl

/-- Block `0x713`: `src ≠ caller`, so the allowance is read and compared with
`uint(-1)`. -/
private theorem xfer_0713 {sevm : Sevm} {d : Devm} {o : Outcome}
    {ne y wad dst src : B256} {xs : Stack}
    (hne : src.toAdr.toB256 ≠ sevm.caller.toB256)
    (hp : ne :: y :: wad :: dst :: src :: xs <<+ d.stack)
    (run : SFunc.Run prog sevm d t_0713_c9 o) :
    XferEff sevm d o wad dst src := by
  rw [tree_0713] at run
  obtain ⟨d1, r1, run⟩ := run_chain_prefix pre0713 _ run
  obtain ⟨d2, r2, run⟩ := run_chain_prefix allowLine _ run
  obtain ⟨d3, r3, run⟩ := run_chain_prefix [.reg .sload, .reg .eq, .reg .iszero] [] run
  have s01 : Same d d1 :=
    ⟨Line.of_inv Devm.getStor (by line_inv) r1, Line.of_inv Devm.getBal (by line_inv) r1⟩
  have hp1 : ∃ m, src :: (0 : B256) :: (4 : B256) :: m :: y :: wad :: dst :: src :: xs
      <<+ d1.stack := by
    unfold pre0713 at r1
    obtain ⟨a0, h0, r1⟩ := Line.of_run_cons r1
    obtain ⟨a1, h1, r1⟩ := Line.of_run_cons r1
    obtain ⟨a2, h2, r1⟩ := Line.of_run_cons r1
    obtain ⟨a3, h3, r1⟩ := Line.of_run_cons r1
    obtain ⟨a4, h4, r1⟩ := Line.of_run_cons r1
    cases r1
    have q0 : y :: wad :: dst :: src :: xs <<+ a0.stack := prefix_of_pop (of_run_pop h0) hp
    obtain ⟨M, q1⟩ : ∃ M : B256, M :: y :: wad :: dst :: src :: xs <<+ a1.stack :=
      ⟨_, prefix_of_push (of_run_push h1) q0⟩
    have q2 : (4 : B256) :: M :: y :: wad :: dst :: src :: xs <<+ a2.stack := by
      have := prefix_of_push (of_run_push h2) q1
      rwa [w04_eq] at this
    have q3 : (0 : B256) :: (4 : B256) :: M :: y :: wad :: dst :: src :: xs <<+ a3.stack := by
      have := prefix_of_push (of_run_push h3) q2
      rwa [w00_eq] at this
    exact ⟨_, prefix_of_dup_val h4 (by show_nth) q3⟩
  obtain ⟨m, hp1⟩ := hp1
  obtain ⟨hp2, s12⟩ := allow_walk hp1 r2
  have s23 : Same d2 d3 :=
    ⟨Line.of_inv Devm.getStor (by line_inv) r3, Line.of_inv Devm.getBal (by line_inv) r3⟩
  have hp3 : ∃ v, v :: y :: wad :: dst :: src :: xs <<+ d3.stack := by
    obtain ⟨a1, h1, r3⟩ := Line.of_run_cons r3
    obtain ⟨a2, h2, r3⟩ := Line.of_run_cons r3
    obtain ⟨a3, h3, r3⟩ := Line.of_run_cons r3
    cases r3
    obtain ⟨al, q1, -⟩ := prefix_of_sload h1 hp2
    exact ⟨_, prefix_of_iszero h3 (prefix_of_eq h2 q1)⟩
  obtain ⟨v, hp3⟩ := hp3
  exact XferEff.of_same (s01.trans (s12.trans s23)) (xfer_07b4 (fun _ => hne) hp3 run)

private def line06dc : List Ninst :=
  [.reg .caller, .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide), .reg .and, .reg (.dup 4), .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide), .reg .and,
   .reg .eq, .reg .iszero, .reg (.dup 0), .reg .iszero, .push [0x07, 0xb4] (by decide)]

private theorem tree_06dc :
    t_06dc_c9 = .dest (chain line06dc (.branch t_0713_c9 t_07b4_c9)) := rfl

/-- Block `0x6dc`: the `src != msg.sender` test. -/
private theorem xfer_06dc {sevm : Sevm} {d : Devm} {o : Outcome}
    {y wad dst src : B256} {xs : Stack}
    (hp : y :: wad :: dst :: src :: xs <<+ d.stack)
    (run : SFunc.Run prog sevm d t_06dc_c9 o) :
    XferEff sevm d o wad dst src := by
  rw [tree_06dc] at run
  cases run with
  | dest burn run =>
  rename_i d0
  obtain ⟨d1, r1, run⟩ := run_chain_prefix line06dc [] run
  have hp0 : y :: wad :: dst :: src :: xs <<+ d0.stack := by
    rw [← burn.stack]; exact hp
  have s01 : Same d d1 := Same.trans (Same.of_state burn.state)
    ⟨Line.of_inv Devm.getStor (by line_inv) r1, Line.of_inv Devm.getBal (by line_inv) r1⟩
  have hp1 : ∃ pd, pd ::
      ((((src.toAdr.toB256 =? sevm.caller.toB256) =? 0) =? 0)) ::
      ((src.toAdr.toB256 =? sevm.caller.toB256) =? 0) :: y :: wad :: dst :: src :: xs
      <<+ d1.stack := by
    unfold line06dc at r1
    obtain ⟨a1, h1, r1⟩ := Line.of_run_cons r1
    obtain ⟨a2, h2, r1⟩ := Line.of_run_cons r1
    obtain ⟨a3, h3, r1⟩ := Line.of_run_cons r1
    obtain ⟨a4, h4, r1⟩ := Line.of_run_cons r1
    obtain ⟨a5, h5, r1⟩ := Line.of_run_cons r1
    obtain ⟨a6, h6, r1⟩ := Line.of_run_cons r1
    obtain ⟨a7, h7, r1⟩ := Line.of_run_cons r1
    obtain ⟨a8, h8, r1⟩ := Line.of_run_cons r1
    obtain ⟨a9, h9, r1⟩ := Line.of_run_cons r1
    obtain ⟨a10, h10, r1⟩ := Line.of_run_cons r1
    obtain ⟨a11, h11, r1⟩ := Line.of_run_cons r1
    cases r1
    have q1 : sevm.caller.toB256 :: y :: wad :: dst :: src :: xs <<+ a1.stack :=
      prefix_of_push (of_run_caller h1) hp0
    have q3 : sevm.caller.toB256 :: y :: wad :: dst :: src :: xs <<+ a3.stack := by
      have := prefix_of_and h3 (prefix_of_push (of_run_push h2) q1)
      rwa [ff20_and_adr] at this
    have q4 : src :: sevm.caller.toB256 :: y :: wad :: dst :: src :: xs <<+ a4.stack :=
      prefix_of_dup_val h4 (by show_nth) q3
    have q6 : src.toAdr.toB256 :: sevm.caller.toB256 :: y :: wad :: dst :: src :: xs
        <<+ a6.stack := by
      have := prefix_of_and h6 (prefix_of_push (of_run_push h5) q4)
      rwa [ff20_and_word] at this
    have q8 := prefix_of_iszero h8 (prefix_of_eq h7 q6)
    have q9 := prefix_of_dup_val h9 (by show_nth) q8
    exact ⟨_, prefix_of_push (of_run_push h11) (prefix_of_iszero h10 q9)⟩
  obtain ⟨pd, hp1⟩ := hp1
  change SFunc.Run prog sevm d1 (.branch t_0713_c9 t_07b4_c9) o at run
  cases run with
  | zero _ pop run =>
    rename_i d2
    obtain ⟨-, hc, hp2⟩ := prefix_of_popBurn2 hp1 pop
    have hne : src.toAdr.toB256 ≠ sevm.caller.toB256 :=
      ne_of_eqc_eq (eq_zero_of_isz_ne (ne_zero_of_isz_eq hc))
    exact XferEff.of_same (s01.trans (Same.of_state pop.state)) (xfer_0713 hne hp2 run)
  | succ dw w hwnz pop run =>
    rename_i d2
    obtain ⟨-, hc, hp2⟩ := prefix_of_popBurn2 hp1 pop
    subst hc
    have h0 := eq_zero_of_isz_ne hwnz
    exact XferEff.of_same (s01.trans (Same.of_state pop.state))
      (xfer_07b4 (fun h => absurd h0 h) hp2 run)

private def pre068c : List Ninst :=
  [.push [0x00] (by decide), .reg (.dup 1), .push [0x03] (by decide),
   .push [0x00] (by decide), .reg (.dup 6)]

private theorem tree_068c :
    t_068c_c9 = .dest (chain (pre068c ++ hashLine ++ cmpLine [0x06, 0xdc] (by decide))
      (.branch t_06d8_c9 t_06dc_c9)) := rfl

/-- Entry 9 from its first instruction: the balance `require`, then block `0x6dc`. -/
private theorem xfer_068c {sevm : Sevm} {d : Devm} {o : Outcome}
    {wad dst src : B256} {xs : Stack}
    (hp : wad :: dst :: src :: xs <<+ d.stack)
    (run : SFunc.Run prog sevm d t_068c_c9 o) :
    XferEff sevm d o wad dst src ∧
      wad ≤ (Devm.getStor d sevm.currentTarget).get (balSlot src.toAdr) := by
  rw [tree_068c] at run
  cases run with
  | dest burn run =>
  rename_i d0
  obtain ⟨d1, r1, run⟩ := run_chain_prefix pre068c _ run
  obtain ⟨d2, r2, run⟩ := run_chain_prefix hashLine _ run
  obtain ⟨d3, r3, run⟩ := run_chain_prefix (cmpLine [0x06, 0xdc] (by decide)) [] run
  have hp0 : wad :: dst :: src :: xs <<+ d0.stack := by
    rw [← burn.stack]; exact hp
  have s01 : Same d d1 := Same.trans (Same.of_state burn.state)
    ⟨Line.of_inv Devm.getStor (by line_inv) r1, Line.of_inv Devm.getBal (by line_inv) r1⟩
  have hp1 : src :: (0 : B256) :: (3 : B256) :: wad :: (0 : B256) :: wad :: dst :: src :: xs
      <<+ d1.stack := by
    unfold pre068c at r1
    obtain ⟨a0, h0, r1⟩ := Line.of_run_cons r1
    obtain ⟨a1, h1, r1⟩ := Line.of_run_cons r1
    obtain ⟨a2, h2, r1⟩ := Line.of_run_cons r1
    obtain ⟨a3, h3, r1⟩ := Line.of_run_cons r1
    obtain ⟨a4, h4, r1⟩ := Line.of_run_cons r1
    cases r1
    have q0 : (0 : B256) :: wad :: dst :: src :: xs <<+ a0.stack := by
      have := prefix_of_push (of_run_push h0) hp0
      rwa [w00_eq] at this
    have q1 : wad :: (0 : B256) :: wad :: dst :: src :: xs <<+ a1.stack :=
      prefix_of_dup_val h1 (by show_nth) q0
    have q2 : (3 : B256) :: wad :: (0 : B256) :: wad :: dst :: src :: xs <<+ a2.stack := by
      have := prefix_of_push (of_run_push h2) q1
      rwa [w03_eq] at this
    have q3 : (0 : B256) :: (3 : B256) :: wad :: (0 : B256) :: wad :: dst :: src :: xs
        <<+ a3.stack := by
      have := prefix_of_push (of_run_push h3) q2
      rwa [w00_eq] at this
    exact prefix_of_dup_val h4 (by show_nth) q3
  obtain ⟨hp2, hs2, hb2⟩ := hash_walk hp1 r2
  obtain ⟨⟨pd, hp3⟩, s23⟩ := cmp_walk hp2 r3
  change SFunc.Run prog sevm d3 (.branch t_06d8_c9 t_06dc_c9) o at run
  cases run with
  | zero _ _ run => exact absurd run not_run_revert_tail
  | succ dw w hwnz pop run =>
  rename_i d4
  obtain ⟨-, hc, hp4⟩ := prefix_of_popBurn2 hp3 pop
  subst hc
  have s02 : Same d d2 := s01.trans ⟨hs2.symm, hb2.symm⟩
  refine ⟨XferEff.of_same (s02.trans (s23.trans (Same.of_state pop.state)))
    (xfer_06dc hp4 run), ?_⟩
  have hle := le_of_check hwnz
  have hv : d2.getStorVal sevm.currentTarget (mapSlot src.toAdr.toB256 3) =
      (Devm.getStor d sevm.currentTarget).get (balSlot src.toAdr) := by
    show (Devm.getStor d2 sevm.currentTarget).get _ = _
    rw [← s02.1]
    rfl
  rw [hv] at hle
  exact hle

/-! ### Solvency -/

private theorem solvent_of_same {sevm : Sevm} {a b : Devm} {v : B256} (h : Same a b)
    (ha : Solvent (Devm.getStor a sevm.currentTarget) v (a.getBal sevm.currentTarget)) :
    Solvent (Devm.getStor b sevm.currentTarget) v (b.getBal sevm.currentTarget) := by
  rw [← h.1, ← h.2]
  exact ha

private theorem solvent_of_xfer {sevm : Sevm} {d : Devm} {o : Outcome} {wad dst src : B256}
    (hoff : src.toAdr.toB256 ≠ sevm.caller.toB256 →
      ∀ a, balSlot a ≠ allowKey src.toAdr.toB256 sevm.caller.toB256)
    (e : XferEff sevm d o wad dst src)
    (hle : wad ≤ (Devm.getStor d sevm.currentTarget).get (balSlot src.toAdr))
    (h : Solvent (Devm.getStor d sevm.currentTarget) sevm.value
      (d.getBal sevm.currentTarget)) :
    Solvent (Devm.getStor (Outcome.devm o) sevm.currentTarget) 0
      ((Outcome.devm o).getBal sevm.currentTarget) := by
  obtain ⟨hb, hs⟩ := e
  have key : ∃ S1 : Stor, bookedSum S1 = bookedSum (Devm.getStor d sevm.currentTarget) ∧
      wad ≤ S1.get (balSlot src.toAdr) ∧
      Devm.getStor (Outcome.devm o) sevm.currentTarget =
        xferStor S1 src.toAdr dst.toAdr wad := by
    rcases hs with hs | ⟨hne, w, hs⟩
    · exact ⟨_, rfl, hle, hs⟩
    · have hk := hoff hne
      refine ⟨_, ?_, ?_, hs⟩
      · have hbk := booked_set_off (Devm.getStor d sevm.currentTarget)
          (allowKey src.toAdr.toB256 sevm.caller.toB256) w hk
        simpa [bookedSum] using congrArg sum hbk
      · rw [Stor.get_set_ne _ (fun e => hk _ e.symm)]
        exact hle
  obtain ⟨S1, hsum, hle1, hs1⟩ := key
  unfold Solvent at h ⊢
  have hlt := B256.toNat_lt (d.getBal sevm.currentTarget)
  have ht : bookedSum (xferStor S1 src.toAdr dst.toAdr wad) = bookedSum S1 :=
    bookedSum_transfer hle1 (by omega)
  rw [hs1, ht, hb, B256.toNat_zero]
  omega

/-- **WETH9 `transferFrom` (entry 9) preserves solvency**, for any frame whose
stack starts with the three arguments.  The allowance-slot premise is needed
only when the masked `src` differs from the caller, and is the local
collision premise of `Premise.lean` in its `allowKey owner spender` form. -/
theorem Weth9.transferFrom_solvent_of_prefix {sevm : Sevm} {d : Devm} {o : Outcome}
    {g : SFunc} {wad dst src : B256} {rest : Stack}
    (hg : prog[9]? = some g) (hp : wad :: dst :: src :: rest <<+ d.stack)
    (hoff : (src &&& ~~~ addressMask) ≠ sevm.caller.toB256 →
      ∀ a, balSlot a ≠ allowKey (src &&& ~~~ addressMask) sevm.caller.toB256)
    (h : Solvent (Devm.getStor d sevm.currentTarget) sevm.value
      (d.getBal sevm.currentTarget))
    (run : SFunc.Run prog sevm d g o) :
    Solvent (Devm.getStor (Outcome.devm o) sevm.currentTarget) 0
      ((Outcome.devm o).getBal sevm.currentTarget) := by
  have hg' : g = t_068c_c9 := by
    simpa [prog, Cert.prog, cert] using hg.symm
  subst g
  rw [and_mask_word] at hoff
  obtain ⟨e, hle⟩ := xfer_068c hp run
  exact solvent_of_xfer hoff e hle h

/-- **WETH9 `transferFrom` (entry 9) preserves solvency** (callee form). -/
theorem Weth9.transferFrom_solvent {sevm : Sevm} {d : Devm} {o : Outcome}
    {g : SFunc} {wad dst src : B256} {rest : Stack}
    (hg : prog[9]? = some g) (hstack : d.stack = wad :: dst :: src :: rest)
    (hoff : (src &&& ~~~ addressMask) ≠ sevm.caller.toB256 →
      ∀ a, balSlot a ≠ allowKey (src &&& ~~~ addressMask) sevm.caller.toB256)
    (h : Solvent (Devm.getStor d sevm.currentTarget) sevm.value
      (d.getBal sevm.currentTarget))
    (run : SFunc.Run prog sevm d g o) :
    Solvent (Devm.getStor (Outcome.devm o) sevm.currentTarget) 0
      ((Outcome.devm o).getBal sevm.currentTarget) := by
  have hp : wad :: dst :: src :: rest <<+ d.stack := ⟨[], by simp [Split, hstack]⟩
  exact Weth9.transferFrom_solvent_of_prefix hg hp hoff h run

private theorem solvent_zero {s : Stor} {v b : B256} (h : Solvent s v b) : Solvent s 0 b := by
  unfold Solvent at h ⊢
  rw [B256.toNat_zero]
  omega

/-- Entry 9 as a callee: a `callNext 9` from a frame whose stack starts with
`wad, dst, src`, continued by a state-silent tree, preserves solvency. -/
private theorem call9_solvent {sevm : Sevm} {d : Devm} {o : Outcome} {f : SFunc}
    {p wad dst src : B256} {rest : Stack}
    (hf : f.silent = true) (hrefs : f.refs.all (· ∈ ([] : List Nat)) = true)
    (hp : p :: wad :: dst :: src :: rest <<+ d.stack)
    (hoff : (src &&& ~~~ addressMask) ≠ sevm.caller.toB256 →
      ∀ a, balSlot a ≠ allowKey (src &&& ~~~ addressMask) sevm.caller.toB256)
    (h : Solvent (Devm.getStor d sevm.currentTarget) sevm.value
      (d.getBal sevm.currentTarget))
    (run : SFunc.Run prog sevm d (.callNext 9 f) o) :
    Solvent (Devm.getStor (Outcome.devm o) sevm.currentTarget) 0
      ((Outcome.devm o).getBal sevm.currentTarget) := by
  cases run with
  | callHalt dd lookup pop run =>
    rename_i d1 _
    have hp1 := prefix_of_pop ⟨_, pop⟩ hp
    exact Weth9.transferFrom_solvent_of_prefix lookup hp1 hoff
      (solvent_of_same (Same.of_state pop.state) h) run
  | callRet dd lookup pop run tail =>
    rename_i d1 d2 _
    have hp1 := prefix_of_pop ⟨_, pop⟩ hp
    have hc := Weth9.transferFrom_solvent_of_prefix lookup hp1 hoff
      (solvent_of_same (Same.of_state pop.state) h) run
    have hst := SFunc.Run.state_of_silent silentSet_nil hf hrefs tail
    exact solvent_of_same (Same.of_state hst.symm) hc

private theorem tree_0bce :
    t_0bce_c3 = .dest (chain [.push [0x00] (by decide), .push [0x0b, 0xdb] (by decide),
      .reg .caller, .reg (.dup 4), .reg (.dup 4), .push [0x06, 0x8c] (by decide)]
      (.callNext 9 t_0bdb_c3)) := rfl

/-- **WETH9 `transfer` (entry 3) preserves solvency**, unconditionally: it is
`transferFrom(msg.sender, dst, wad)`, which never writes an allowance. -/
theorem Weth9.transfer_solvent {sevm : Sevm} {d : Devm} {o : Outcome} {g : SFunc}
    (hg : prog[3]? = some g)
    (h : Solvent (Devm.getStor d sevm.currentTarget) sevm.value
      (d.getBal sevm.currentTarget))
    (run : SFunc.Run prog sevm d g o) :
    Solvent (Devm.getStor (Outcome.devm o) sevm.currentTarget) 0
      ((Outcome.devm o).getBal sevm.currentTarget) := by
  have hg' : g = t_0bce_c3 := by
    simpa [prog, Cert.prog, cert] using hg.symm
  subst g
  rw [tree_0bce] at run
  cases run with
  | dest burn run =>
  rename_i d0
  obtain ⟨d1, r1, run⟩ := run_chain_prefix [.push [0x00] (by decide),
    .push [0x0b, 0xdb] (by decide), .reg .caller, .reg (.dup 4), .reg (.dup 4),
    .push [0x06, 0x8c] (by decide)] [] run
  have s01 : Same d d1 := Same.trans (Same.of_state burn.state)
    ⟨Line.of_inv Devm.getStor (by line_inv) r1, Line.of_inv Devm.getBal (by line_inv) r1⟩
  have hp1 : ∃ p x y z q : B256,
      p :: y :: x :: sevm.caller.toB256 :: q :: z :: d0.stack <<+ d1.stack := by
    obtain ⟨a1, h1, r1⟩ := Line.of_run_cons r1
    obtain ⟨a2, h2, r1⟩ := Line.of_run_cons r1
    obtain ⟨a3, h3, r1⟩ := Line.of_run_cons r1
    obtain ⟨a4, h4, r1⟩ := Line.of_run_cons r1
    obtain ⟨a5, h5, r1⟩ := Line.of_run_cons r1
    obtain ⟨a6, h6, r1⟩ := Line.of_run_cons r1
    cases r1
    have q0 : d0.stack <<+ d0.stack := ⟨[], (List.append_nil _).symm⟩
    have q1 := prefix_of_push (of_run_push h1) q0
    have q2 := prefix_of_push (of_run_push h2) q1
    have q3 := prefix_of_push (of_run_caller h3) q2
    obtain ⟨x, -, pb4⟩ := of_run_dup h4
    have q4 := prefix_of_push pb4 q3
    obtain ⟨y, -, pb5⟩ := of_run_dup h5
    have q5 := prefix_of_push pb5 q4
    exact ⟨_, x, y, _, _, prefix_of_push (of_run_push h6) q5⟩
  obtain ⟨p, x, y, z, q, hp1⟩ := hp1
  have hoff : (sevm.caller.toB256 &&& ~~~ addressMask) ≠ sevm.caller.toB256 →
      ∀ a, balSlot a ≠ allowKey (sevm.caller.toB256 &&& ~~~ addressMask)
        sevm.caller.toB256 := by
    intro hne
    rw [and_mask_word, toAdr_toB256] at hne
    exact absurd rfl hne
  exact call9_solvent (by decide) (by decide) hp1 hoff (solvent_of_same s01 h) run

private theorem entry3_lookup : prog[3]? = some t_0bce_c3 := by
  simp [prog, Cert.prog, cert]

private theorem hzero_weth9 {j : Nat} {g : SFunc} (hj : j ∈ Weth9.silentSet)
    (hjg : prog[j]? = some g) : g.silentCalls Weth9.silentSet 0 = true := by
  have h := (List.all_eq_true.mp Weth9.silentSet_no_calls) j hj
  rw [hjg] at h
  exact h

private theorem solvent_stable {v : B256} {a b : Devm} (hs : a.state = b.state)
    {sevm : Sevm}
    (ha : Solvent (Devm.getStor a sevm.currentTarget) v (a.getBal sevm.currentTarget)) :
    Solvent (Devm.getStor b sevm.currentTarget) v (b.getBal sevm.currentTarget) :=
  solvent_of_same (Same.of_state hs) ha

/-- **The `transfer(address,uint256)` selector wrapper (entry 20) preserves
solvency**, unconditionally. -/
theorem Weth9.transfer_wrapper_solvent {sevm : Sevm} {d : Devm} {o : Outcome} {g : SFunc}
    (hg : prog[20]? = some g)
    (h : Solvent (Devm.getStor d sevm.currentTarget) sevm.value
      (d.getBal sevm.currentTarget))
    (run : SFunc.Run prog sevm d g o) :
    Solvent (Devm.getStor (Outcome.devm o) sevm.currentTarget) 0
      ((Outcome.devm o).getBal sevm.currentTarget) := by
  have hg' : g = t_0370_c20 := by
    simpa [prog, Cert.prog, cert] using hg.symm
  subst g
  exact SFunc.Run.hoare_wrapper (S := Weth9.silentSet) (k := 3)
    (Φ₀ := fun d => Solvent (Devm.getStor d sevm.currentTarget) sevm.value
      (d.getBal sevm.currentTarget))
    (Φ₁ := fun d => Solvent (Devm.getStor d sevm.currentTarget) 0
      (d.getBal sevm.currentTarget))
    Weth9.silentSet_closed hzero_weth9 (fun _ hd => solvent_zero hd)
    (fun hs hd => solvent_stable hs hd) (fun hs hd => solvent_stable hs hd)
    entry3_lookup (fun hd hr => Weth9.transfer_solvent entry3_lookup hd hr)
    (by decide +kernel) (by decide +kernel) run h

/-! ### The `transferFrom(address,address,uint256)` selector wrapper -/

/-- One ABI address argument: `DUP1; CALLDATALOAD; mask; SWAP1; PUSH 32; ADD;
SWAP1; SWAP2; SWAP1`. -/
private def argM : List Ninst :=
  [.reg (.dup 0), .reg .calldataload, .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
     0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide), .reg .and, .reg (.swap 0),
   .push [0x20] (by decide), .reg .add, .reg (.swap 0), .reg (.swap 1), .reg (.swap 0)]

/-- One ABI word argument, unmasked. -/
private def argU : List Ninst :=
  [.reg (.dup 0), .reg .calldataload, .reg (.swap 0),
   .push [0x20] (by decide), .reg .add, .reg (.swap 0), .reg (.swap 1), .reg (.swap 0)]

private theorem argM_walk {sevm : Sevm} {s s' : Devm} {o b : B256} {ys : Stack}
    (hp : o :: b :: ys <<+ s.stack) (run : Line.Run sevm s argM s') :
    (∃ o', o' :: b :: (Sevm.dataWord sevm o).toAdr.toB256 :: ys <<+ s'.stack) ∧
      Same s s' := by
  unfold argM at run
  refine ⟨?_, Line.of_inv Devm.getStor (by line_inv) run,
    Line.of_inv Devm.getBal (by line_inv) run⟩
  obtain ⟨a1, h1, run⟩ := Line.of_run_cons run
  obtain ⟨a2, h2, run⟩ := Line.of_run_cons run
  obtain ⟨a3, h3, run⟩ := Line.of_run_cons run
  obtain ⟨a4, h4, run⟩ := Line.of_run_cons run
  obtain ⟨a5, h5, run⟩ := Line.of_run_cons run
  obtain ⟨a6, h6, run⟩ := Line.of_run_cons run
  obtain ⟨a7, h7, run⟩ := Line.of_run_cons run
  obtain ⟨a8, h8, run⟩ := Line.of_run_cons run
  obtain ⟨a9, h9, run⟩ := Line.of_run_cons run
  obtain ⟨a10, h10, run⟩ := Line.of_run_cons run
  cases run
  have q1 : o :: o :: b :: ys <<+ a1.stack := prefix_of_dup_val h1 (by show_nth) hp
  have q2 := prefix_of_calldataload_val h2 q1
  have q4 : (Sevm.dataWord sevm o).toAdr.toB256 :: o :: b :: ys <<+ a4.stack := by
    have := prefix_of_and h4 (prefix_of_push (of_run_push h3) q2)
    rwa [ff20_and_word] at this
  have q5 : o :: (Sevm.dataWord sevm o).toAdr.toB256 :: b :: ys <<+ a5.stack :=
    Stack.prefix_of_swap (n := 0) (by simp [Stack.Swap, Stack.SwapCore])
      (of_run_swap h5) q4
  obtain ⟨o', q7⟩ : ∃ o' : B256, o' :: (Sevm.dataWord sevm o).toAdr.toB256 :: b :: ys
      <<+ a7.stack := ⟨_, prefix_of_add h7 (prefix_of_push (of_run_push h6) q5)⟩
  have q8 : (Sevm.dataWord sevm o).toAdr.toB256 :: o' :: b :: ys <<+ a8.stack :=
    Stack.prefix_of_swap (n := 0) (by simp [Stack.Swap, Stack.SwapCore])
      (of_run_swap h8) q7
  have q9 : b :: o' :: (Sevm.dataWord sevm o).toAdr.toB256 :: ys <<+ a9.stack :=
    Stack.prefix_of_swap (n := 1) (by simp [Stack.Swap, Stack.SwapCore])
      (of_run_swap h9) q8
  exact ⟨o', Stack.prefix_of_swap (n := 0) (by simp [Stack.Swap, Stack.SwapCore])
      (of_run_swap h10) q9⟩

private theorem argU_walk {sevm : Sevm} {s s' : Devm} {o b : B256} {ys : Stack}
    (hp : o :: b :: ys <<+ s.stack) (run : Line.Run sevm s argU s') :
    (∃ o', o' :: b :: Sevm.dataWord sevm o :: ys <<+ s'.stack) ∧ Same s s' := by
  unfold argU at run
  refine ⟨?_, Line.of_inv Devm.getStor (by line_inv) run,
    Line.of_inv Devm.getBal (by line_inv) run⟩
  obtain ⟨a1, h1, run⟩ := Line.of_run_cons run
  obtain ⟨a2, h2, run⟩ := Line.of_run_cons run
  obtain ⟨a3, h3, run⟩ := Line.of_run_cons run
  obtain ⟨a4, h4, run⟩ := Line.of_run_cons run
  obtain ⟨a5, h5, run⟩ := Line.of_run_cons run
  obtain ⟨a6, h6, run⟩ := Line.of_run_cons run
  obtain ⟨a7, h7, run⟩ := Line.of_run_cons run
  obtain ⟨a8, h8, run⟩ := Line.of_run_cons run
  cases run
  have q1 : o :: o :: b :: ys <<+ a1.stack := prefix_of_dup_val h1 (by show_nth) hp
  have q2 : Sevm.dataWord sevm o :: o :: b :: ys <<+ a2.stack :=
    prefix_of_calldataload_val h2 q1
  have q3 : o :: Sevm.dataWord sevm o :: b :: ys <<+ a3.stack :=
    Stack.prefix_of_swap (n := 0) (by simp [Stack.Swap, Stack.SwapCore])
      (of_run_swap h3) q2
  obtain ⟨o', q5⟩ : ∃ o' : B256, o' :: Sevm.dataWord sevm o :: b :: ys <<+ a5.stack :=
    ⟨_, prefix_of_add h5 (prefix_of_push (of_run_push h4) q3)⟩
  have q6 : Sevm.dataWord sevm o :: o' :: b :: ys <<+ a6.stack :=
    Stack.prefix_of_swap (n := 0) (by simp [Stack.Swap, Stack.SwapCore])
      (of_run_swap h6) q5
  have q7 : b :: o' :: Sevm.dataWord sevm o :: ys <<+ a7.stack :=
    Stack.prefix_of_swap (n := 1) (by simp [Stack.Swap, Stack.SwapCore])
      (of_run_swap h7) q6
  exact ⟨o', Stack.prefix_of_swap (n := 0) (by simp [Stack.Swap, Stack.SwapCore])
      (of_run_swap h8) q7⟩

private def head01d5 : List Ninst :=
  [.push [0x02, 0x29] (by decide), .push [0x04] (by decide), .reg (.dup 0)]

private def tail01d5 : List Ninst :=
  [.reg .pop, .reg .pop, .push [0x06, 0x8c] (by decide)]

private theorem tree_01d5 :
    t_01d5_c25 = .dest (chain (head01d5 ++ argM ++ argM ++ argU ++ tail01d5)
      (.callNext 9 t_0229_c25)) := rfl

private theorem tree_01ca :
    t_01ca_c25 = .dest (chain [.reg .callvalue, .reg .iszero, .push [0x01, 0xd5] (by decide)]
      (.branch t_01d1_c25 t_01d5_c25)) := rfl

/-- **The `transferFrom(address,address,uint256)` selector wrapper (entry 25)
preserves solvency** under the frame's allowance-collision premise. -/
theorem Weth9.transferFrom_wrapper_solvent {sevm : Sevm} {d : Devm} {o : Outcome}
    {g : SFunc} (hg : prog[25]? = some g) (hadm : AllowAdmitted sevm)
    (h : Solvent (Devm.getStor d sevm.currentTarget) sevm.value
      (d.getBal sevm.currentTarget))
    (run : SFunc.Run prog sevm d g o) :
    Solvent (Devm.getStor (Outcome.devm o) sevm.currentTarget) 0
      ((Outcome.devm o).getBal sevm.currentTarget) := by
  have hg' : g = t_01ca_c25 := by
    simpa [prog, Cert.prog, cert] using hg.symm
  subst g
  rw [tree_01ca] at run
  cases run with
  | dest burn run =>
  rename_i d0
  obtain ⟨d1, r1, run⟩ := run_chain_prefix [.reg .callvalue, .reg .iszero,
    .push [0x01, 0xd5] (by decide)] [] run
  have s01 : Same d d1 := Same.trans (Same.of_state burn.state)
    ⟨Line.of_inv Devm.getStor (by line_inv) r1, Line.of_inv Devm.getBal (by line_inv) r1⟩
  change SFunc.Run prog sevm d1 (.branch t_01d1_c25 t_01d5_c25) o at run
  cases run with
  | zero _ _ run => exact absurd run not_run_revert_tail
  | succ dw w hwnz pop run =>
  rename_i d2
  have s02 := s01.trans (Same.of_state pop.state)
  rw [tree_01d5] at run
  cases run with
  | dest burn' run =>
  rename_i d3
  have s03 := s02.trans (Same.of_state burn'.state)
  obtain ⟨d4, r4, run⟩ := run_chain_prefix head01d5 _ run
  obtain ⟨d5, r5, run⟩ := run_chain_prefix argM _ run
  obtain ⟨d6, r6, run⟩ := run_chain_prefix argM _ run
  obtain ⟨d7, r7, run⟩ := run_chain_prefix argU _ run
  obtain ⟨d8, r8, run⟩ := run_chain_prefix tail01d5 [] run
  have s34 : Same d3 d4 :=
    ⟨Line.of_inv Devm.getStor (by line_inv) r4, Line.of_inv Devm.getBal (by line_inv) r4⟩
  have s78 : Same d7 d8 :=
    ⟨Line.of_inv Devm.getStor (by line_inv) r8, Line.of_inv Devm.getBal (by line_inv) r8⟩
  have hp4 : ∃ r : B256, (4 : B256) :: (4 : B256) :: r :: d3.stack <<+ d4.stack := by
    unfold head01d5 at r4
    obtain ⟨a1, h1, r4⟩ := Line.of_run_cons r4
    obtain ⟨a2, h2, r4⟩ := Line.of_run_cons r4
    obtain ⟨a3, h3, r4⟩ := Line.of_run_cons r4
    cases r4
    have q0 : d3.stack <<+ d3.stack := ⟨[], (List.append_nil _).symm⟩
    obtain ⟨r, q1⟩ : ∃ r : B256, r :: d3.stack <<+ a1.stack :=
      ⟨_, prefix_of_push (of_run_push h1) q0⟩
    have q2 : (4 : B256) :: r :: d3.stack <<+ a2.stack := by
      have := prefix_of_push (of_run_push h2) q1
      rwa [w04_eq] at this
    exact ⟨r, prefix_of_dup_val h3 (by show_nth) q2⟩
  obtain ⟨r, hp4⟩ := hp4
  obtain ⟨⟨o5, hp5⟩, s45⟩ := argM_walk hp4 r5
  obtain ⟨⟨o6, hp6⟩, s56⟩ := argM_walk hp5 r6
  obtain ⟨⟨o7, hp7⟩, s67⟩ := argU_walk hp6 r7
  have hp8 : ∃ p : B256, p :: Sevm.dataWord sevm o6 ::
      (Sevm.dataWord sevm o5).toAdr.toB256 :: (Sevm.dataWord sevm 4).toAdr.toB256 ::
      r :: d3.stack <<+ d8.stack := by
    unfold tail01d5 at r8
    obtain ⟨a1, h1, r8⟩ := Line.of_run_cons r8
    obtain ⟨a2, h2, r8⟩ := Line.of_run_cons r8
    obtain ⟨a3, h3, r8⟩ := Line.of_run_cons r8
    cases r8
    exact ⟨_, prefix_of_push (of_run_push h3)
      (prefix_of_pop (of_run_pop h2) (prefix_of_pop (of_run_pop h1) hp7))⟩
  obtain ⟨p, hp8⟩ := hp8
  have hoff : ((Sevm.dataWord sevm 4).toAdr.toB256 &&& ~~~ addressMask) ≠
        sevm.caller.toB256 →
      ∀ a, balSlot a ≠ allowKey ((Sevm.dataWord sevm 4).toAdr.toB256 &&& ~~~ addressMask)
        sevm.caller.toB256 := by
    intro _
    have h2 := hadm.2
    rw [allowArg, and_mask_word] at h2
    rw [and_mask_word, toAdr_toB256]
    exact h2
  have s08 : Same d d8 :=
    s03.trans (s34.trans (s45.trans (s56.trans (s67.trans s78))))
  exact call9_solvent (by decide) (by decide) hp8 hoff (solvent_of_same s08 h) run

end Blanc.Lift
