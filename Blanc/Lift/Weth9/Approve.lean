import Blanc.Lift.Weth9.Premise

/-!
# WETH9 `approve` preserves solvency under the local collision premise

Entry 11 (`t_057b_c11`, pc `0x57b`) is the body of `approve(guy, wad)`: it
forms `allowance[msg.sender][guy]` with two nested SHA3s, stores `wad` there,
emits `Approval`, and returns `1`.  Wrapper entry 27 (`t_0147_c27`, pc
`0x147`) is its selector wrapper.  The only storage write is the allowance
SSTORE, so solvency is preserved exactly when that key is off the balance
image; `approve_collision_breaks_solvency` shows the premise is necessary.
-/

namespace Blanc.Lift

open Jaune
open Blanc
open Weth9

namespace Weth9

private theorem w04_eq : Bytes.toB256 [0x04] = 4 := by decide

private theorem ff20_and_and (x : B256) :
    (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&&
    (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& x)) =
      x &&& ~~~ addressMask := by
  rw [ff20_eq, B256.and_comm (~~~ addressMask) x,
    B256.and_comm (~~~ addressMask) (x &&& ~~~ addressMask), B256.and_idem_right]

private theorem ff20_and_dataWord (sevm : Sevm) :
    (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&&
      Sevm.dataWord sevm 4) = allowArg sevm := by
  rw [B256.and_comm, allowArg_eq]

private theorem allowArg_mask (sevm : Sevm) :
    allowArg sevm &&& ~~~ addressMask = allowArg sevm := by
  unfold allowArg
  exact B256.and_idem_right _ _

/-- The storage/balance pair a solvency statement reads at the contract. -/
private theorem solvent_transport {ca : Adr} {v : B256} {d d' : Devm}
    (hs : Devm.getStor d' = Devm.getStor d) (hb : Devm.getBal d' = Devm.getBal d)
    (h : Solvent (Devm.getStor d ca) v (Devm.getBal d ca)) :
    Solvent (Devm.getStor d' ca) v (Devm.getBal d' ca) := by
  rw [hs, hb]; exact h

private theorem getStor_of_state {d d' : Devm} (h : d'.state = d.state) :
    Devm.getStor d' = Devm.getStor d := by
  funext a; unfold Devm.getStor Devm.getAcct; rw [h]

private theorem getBal_of_state {d d' : Devm} (h : d'.state = d.state) :
    Devm.getBal d' = Devm.getBal d := by
  funext a; unfold Devm.getBal Devm.getAcct; rw [h]

/-! ## Entry 11: the approve body -/

private abbrev pF : Ninst :=
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)

/-- `mapSlot a b` from stack `a :: 0 :: b`: two MSTOREs and a SHA3. -/
private def hashBlock : List Ninst :=
  [.reg (.dup 1), .reg .mstore, .push [0x20] (by decide), .reg .add,
   .reg (.swap 0), .reg (.dup 1), .reg .mstore, .push [0x20] (by decide),
   .reg .add, .push [0x00] (by decide), .reg .keccak256]

private def approveA : List Ninst :=
  [.push [0x00] (by decide), .reg (.dup 1), .push [0x04] (by decide),
   .push [0x00] (by decide), .reg .caller, pF, .reg .and, pF, .reg .and]

private def approveB : List Ninst :=
  [.push [0x00] (by decide), .reg (.dup 5), pF, .reg .and, pF, .reg .and]

private def approveC : List Ninst := [.reg (.dup 1), .reg (.swap 0)]

private def approvePost : List Ninst :=
  [.reg .pop, .reg (.dup 2), pF, .reg .and, .reg .caller, pF, .reg .and,
   .push [0x8c, 0x5b, 0xe1, 0xe5, 0xeb, 0xec, 0x7d, 0x5b, 0xd1, 0x4f, 0x71,
     0x42, 0x7d, 0x1e, 0x84, 0xf3, 0xdd, 0x03, 0x14, 0xc0, 0xf7, 0xb2, 0x29,
     0x1e, 0x5b, 0x20, 0x0a, 0xc8, 0xc7, 0xc3, 0xb9, 0x25] (by decide),
   .reg (.dup 4), .push [0x40] (by decide), .reg .mload, .reg (.dup 0),
   .reg (.dup 2), .reg (.dup 1), .reg .mstore, .push [0x20] (by decide),
   .reg .add, .reg (.swap 1), .reg .pop, .reg .pop, .push [0x40] (by decide),
   .reg .mload, .reg (.dup 0), .reg (.swap 1), .reg .sub, .reg (.swap 0),
   .reg (.log 3), .push [0x01] (by decide), .reg (.swap 0), .reg .pop,
   .reg (.swap 2), .reg (.swap 1), .reg .pop, .reg .pop]

private theorem approve_tree_eq :
    t_057b_c11 = .dest (chain (approveA ++ (hashBlock ++ (approveB ++
      (hashBlock ++ (approveC ++ ([Ninst.sstore] ++ approvePost)))))) .ret) := by
  simp [t_057b_c11, approveA, approveB, approveC, approvePost, hashBlock, pF, chain]

private theorem hash_block {sevm : Sevm} {s s' : Devm} {a b : B256} {xs : Stack}
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

private theorem approve_segA {sevm : Sevm} {s s' : Devm} {v sp : B256} {xs : Stack}
    (run : Line.Run sevm s approveA s') (hp : v :: sp :: xs <<+ s.stack) :
    sevm.caller.toB256 :: (0 : B256) :: (4 : B256) :: v :: (0 : B256) :: v :: sp :: xs
      <<+ s'.stack := by
  unfold approveA pF at run
  obtain ⟨s1, h1, run⟩ := Line.of_run_cons run
  obtain ⟨s2, h2, run⟩ := Line.of_run_cons run
  obtain ⟨s3, h3, run⟩ := Line.of_run_cons run
  obtain ⟨s4, h4, run⟩ := Line.of_run_cons run
  obtain ⟨s5, h5, run⟩ := Line.of_run_cons run
  obtain ⟨s6, h6, run⟩ := Line.of_run_cons run
  obtain ⟨s7, h7, run⟩ := Line.of_run_cons run
  obtain ⟨s8, h8, run⟩ := Line.of_run_cons run
  obtain ⟨s9, h9, run⟩ := Line.of_run_cons run
  cases run
  have hp1 : (0 : B256) :: v :: sp :: xs <<+ s1.stack := by
    have := prefix_of_push (of_run_push h1) hp
    rwa [w00_eq] at this
  have hp2 : v :: (0 : B256) :: v :: sp :: xs <<+ s2.stack :=
    prefix_of_dup_val h2 (by show_nth) hp1
  have hp3 : (4 : B256) :: v :: (0 : B256) :: v :: sp :: xs <<+ s3.stack := by
    have := prefix_of_push (of_run_push h3) hp2
    rwa [w04_eq] at this
  have hp4 : (0 : B256) :: (4 : B256) :: v :: (0 : B256) :: v :: sp :: xs
      <<+ s4.stack := by
    have := prefix_of_push (of_run_push h4) hp3
    rwa [w00_eq] at this
  have hp5 := prefix_of_push (of_run_caller h5) hp4
  have hp7 : sevm.caller.toB256 :: (0 : B256) :: (4 : B256) :: v :: (0 : B256) :: v ::
      sp :: xs <<+ s7.stack := by
    have := prefix_of_and h7 (prefix_of_push (of_run_push h6) hp5)
    rwa [ff20_and_adr] at this
  have := prefix_of_and h9 (prefix_of_push (of_run_push h8) hp7)
  rwa [ff20_and_adr] at this

private theorem approve_segB {sevm : Sevm} {s s' : Devm} {k v sp : B256} {xs : Stack}
    (run : Line.Run sevm s approveB s')
    (hp : k :: v :: (0 : B256) :: v :: sp :: xs <<+ s.stack) :
    (sp &&& ~~~ addressMask) :: (0 : B256) :: k :: v :: (0 : B256) :: v :: sp :: xs
      <<+ s'.stack := by
  unfold approveB pF at run
  obtain ⟨s1, h1, run⟩ := Line.of_run_cons run
  obtain ⟨s2, h2, run⟩ := Line.of_run_cons run
  obtain ⟨s3, h3, run⟩ := Line.of_run_cons run
  obtain ⟨s4, h4, run⟩ := Line.of_run_cons run
  obtain ⟨s5, h5, run⟩ := Line.of_run_cons run
  obtain ⟨s6, h6, run⟩ := Line.of_run_cons run
  cases run
  have hp1 : (0 : B256) :: k :: v :: (0 : B256) :: v :: sp :: xs <<+ s1.stack := by
    have := prefix_of_push (of_run_push h1) hp
    rwa [w00_eq] at this
  have hp2 : sp :: (0 : B256) :: k :: v :: (0 : B256) :: v :: sp :: xs <<+ s2.stack :=
    prefix_of_dup_val h2 (by show_nth) hp1
  have hp4 := prefix_of_and h4 (prefix_of_push (of_run_push h3) hp2)
  have := prefix_of_and h6 (prefix_of_push (of_run_push h5) hp4)
  rwa [ff20_and_and] at this

private theorem approve_segC {sevm : Sevm} {s s' : Devm} {k v : B256} {xs : Stack}
    (run : Line.Run sevm s approveC s') (hp : k :: v :: xs <<+ s.stack) :
    k :: v :: v :: xs <<+ s'.stack := by
  unfold approveC at run
  obtain ⟨s1, h1, run⟩ := Line.of_run_cons run
  obtain ⟨s2, h2, run⟩ := Line.of_run_cons run
  cases run
  have hp1 : v :: k :: v :: xs <<+ s1.stack := prefix_of_dup_val h1 (by show_nth) hp
  exact Stack.prefix_of_swap (n := 0) (by simp [Stack.Swap, Stack.SwapCore])
    (of_run_swap h2) hp1

/-- The storage and balance effect of entry 11: exactly one SSTORE, of the
top-of-stack `value` at the allowance key of `(caller, spender & mask)`. -/
theorem approve_effect {sevm : Sevm} {d : Devm} {o : Outcome} {g : SFunc}
    {value spender : B256} {xs : Stack}
    (hg : prog[11]? = some g) (hstk : value :: spender :: xs <<+ d.stack)
    (run : SFunc.Run prog sevm d g o) :
    Devm.getStor (Outcome.devm o) sevm.currentTarget =
        (Devm.getStor d sevm.currentTarget).set
          (allowKey sevm.caller.toB256 (spender &&& ~~~ addressMask)) value ∧
      Devm.getBal (Outcome.devm o) = Devm.getBal d := by
  have hg' : g = t_057b_c11 := by
    simpa [prog, Cert.prog, cert] using hg.symm
  subst g
  rw [approve_tree_eq] at run
  cases run with
  | dest burn rest =>
    rename_i d0
    rcases run_chain_prefix approveA _ rest with ⟨d1, hA, rest⟩
    rcases run_chain_prefix hashBlock _ rest with ⟨d2, hH1, rest⟩
    rcases run_chain_prefix approveB _ rest with ⟨d3, hB, rest⟩
    rcases run_chain_prefix hashBlock _ rest with ⟨d4, hH2, rest⟩
    rcases run_chain_prefix approveC _ rest with ⟨d5, hC, rest⟩
    rcases run_chain_prefix [Ninst.sstore] _ rest with ⟨d6, hS, rest⟩
    rcases run_chain_prefix approvePost [] rest with ⟨d7, hPost, rest⟩
    cases rest with
    | @ret _ dd w hret =>
      have hs0 : value :: spender :: xs <<+ d0.stack := by rw [← burn.stack]; exact hstk
      have hs5 := approve_segC hC (hash_block hH2 (approve_segB hB
        (hash_block hH1 (approve_segA hA hs0))))
      have hsstore := of_run_singleton hS
      have hset := sstore_getStor_set hsstore hs5
      have i1 : Devm.getStor d0 = Devm.getStor d1 := Line.of_inv Devm.getStor (by line_inv) hA
      have i2 : Devm.getStor d1 = Devm.getStor d2 := Line.of_inv Devm.getStor (by line_inv) hH1
      have i3 : Devm.getStor d2 = Devm.getStor d3 := Line.of_inv Devm.getStor (by line_inv) hB
      have i4 : Devm.getStor d3 = Devm.getStor d4 := Line.of_inv Devm.getStor (by line_inv) hH2
      have i5 : Devm.getStor d4 = Devm.getStor d5 := Line.of_inv Devm.getStor (by line_inv) hC
      have i7 : Devm.getStor d6 = Devm.getStor d7 :=
        Line.of_inv Devm.getStor (by line_inv) hPost
      have b1 : Devm.getBal d0 = Devm.getBal d1 := Line.of_inv Devm.getBal (by line_inv) hA
      have b2 : Devm.getBal d1 = Devm.getBal d2 := Line.of_inv Devm.getBal (by line_inv) hH1
      have b3 : Devm.getBal d2 = Devm.getBal d3 := Line.of_inv Devm.getBal (by line_inv) hB
      have b4 : Devm.getBal d3 = Devm.getBal d4 := Line.of_inv Devm.getBal (by line_inv) hH2
      have b5 : Devm.getBal d4 = Devm.getBal d5 := Line.of_inv Devm.getBal (by line_inv) hC
      have b6 : Devm.getBal d5 = Devm.getBal d6 := Ninst.Hinv.inv hsstore
      have b7 : Devm.getBal d6 = Devm.getBal d7 := Line.of_inv Devm.getBal (by line_inv) hPost
      have hretStor : Devm.getStor dd = Devm.getStor d7 := by
        funext a; exact Devm.PopBurn.getStor hret a
      have hretBal : Devm.getBal dd = Devm.getBal d7 := by
        funext a; exact Devm.PopBurn.getBal hret a
      have hburnStor : Devm.getStor d0 = Devm.getStor d := by
        funext a; exact Devm.Burn.getStor burn a
      have hburnBal : Devm.getBal d0 = Devm.getBal d := by
        funext a; exact Devm.Burn.getBal burn a
      refine ⟨?_, ?_⟩
      · show Devm.getStor dd sevm.currentTarget = _
        rw [hretStor, ← i7, hset, ← i5, ← i4, ← i3, ← i2, ← i1, hburnStor]
        rfl
      · show Devm.getBal dd = _
        rw [hretBal, ← b7, ← b6, ← b5, ← b4, ← b3, ← b2, ← b1, hburnBal]

/-- **Entry 11 callee spec.**  From a frame whose stack starts
`value :: spender`, if the allowance key `(caller, spender & mask)` is off the
balance image, solvency with the callvalue in flight becomes solvency with
nothing in flight. -/
theorem approve_solvent {sevm : Sevm} {d : Devm} {o : Outcome} {g : SFunc}
    {value spender : B256} {xs : Stack}
    (hg : prog[11]? = some g) (hstk : value :: spender :: xs <<+ d.stack)
    (hoff : ∀ a, balSlot a ≠ allowKey sevm.caller.toB256 (spender &&& ~~~ addressMask))
    (h : Solvent (Devm.getStor d sevm.currentTarget) sevm.value
      (Devm.getBal d sevm.currentTarget))
    (run : SFunc.Run prog sevm d g o) :
    Solvent (Devm.getStor (Outcome.devm o) sevm.currentTarget) 0
      (Devm.getBal (Outcome.devm o) sevm.currentTarget) := by
  obtain ⟨hs, hb⟩ := approve_effect hg hstk run
  exact solvent_of_off_write hs hb hoff h

/-! ## O4 control: the collision premise is necessary -/

/-- If the allowance key is a balance slot, storing any value above the
contract's ether balance there breaks solvency, whatever the rest of storage. -/
theorem approve_collision_breaks_solvency (s : Stor) {a : Adr} {k value b : B256}
    (hk : balSlot a = k) (hlt : b.toNat < value.toNat) :
    ¬ Solvent (s.set k value) 0 b := by
  intro h
  obtain ⟨r, hr, hra⟩ := exists_balRep a
  have h1 : booked (s.set k value) r = value := by
    rw [booked_rep _ hr hra, hk, Stor.get_set_self]
  have h2 : (booked (s.set k value) r).toNat ≤ bookedSum (s.set k value) := le_sum
  unfold Solvent at h
  rw [h1] at h2
  rw [B256.toNat_zero] at h
  omega

/-- Machine-level control: a run of entry 11 whose allowance key collides with
`balSlot a` and whose `value` exceeds the contract's balance ends insolvent,
from any pre-state (in particular a solvent one). -/
theorem approve_collision_control {sevm : Sevm} {d : Devm} {o : Outcome} {g : SFunc}
    {value spender : B256} {xs : Stack} {a : Adr}
    (hg : prog[11]? = some g) (hstk : value :: spender :: xs <<+ d.stack)
    (hcol : allowKey sevm.caller.toB256 (spender &&& ~~~ addressMask) = balSlot a)
    (hlt : (Devm.getBal d sevm.currentTarget).toNat < value.toNat)
    (run : SFunc.Run prog sevm d g o) :
    ¬ Solvent (Devm.getStor (Outcome.devm o) sevm.currentTarget) 0
      (Devm.getBal (Outcome.devm o) sevm.currentTarget) := by
  obtain ⟨hs, hb⟩ := approve_effect hg hstk run
  rw [hs, hb]
  exact approve_collision_breaks_solvency _ hcol.symm hlt

/-! ## Entry 27: the `approve` selector wrapper -/

private def wrapLine : List Ninst :=
  [.push [0x01, 0x87] (by decide), .push [0x04] (by decide), .reg (.dup 0),
   .reg (.dup 0), .reg .calldataload, pF, .reg .and, .reg (.swap 0),
   .push [0x20] (by decide), .reg .add, .reg (.swap 0), .reg (.swap 1),
   .reg (.swap 0), .reg (.dup 0), .reg .calldataload, .reg (.swap 0),
   .push [0x20] (by decide), .reg .add, .reg (.swap 0), .reg (.swap 1),
   .reg (.swap 0), .reg .pop, .reg .pop, .push [0x05, 0x7b] (by decide)]

private theorem wrap_tree_eq :
    t_0152_c27 = .dest (chain (wrapLine ++ []) (.callNext 11 t_0187_c27)) := by
  simp [t_0152_c27, wrapLine, pF, chain]

private theorem wrap_line_stack {sevm : Sevm} {s s' : Devm}
    (run : Line.Run sevm s wrapLine s') :
    ∃ t v : B256, ∃ ys : Stack, t :: v :: allowArg sevm :: ys <<+ s'.stack := by
  unfold wrapLine pF at run
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
  obtain ⟨s24, h24, run⟩ := Line.of_run_cons run
  cases run
  obtain ⟨r, hp1⟩ : ∃ r : B256, [r] <<+ s1.stack :=
    ⟨_, prefix_of_push (of_run_push h1) nil_pref⟩
  have hp2 : [(4 : B256), r] <<+ s2.stack := by
    have := prefix_of_push (of_run_push h2) hp1
    rwa [w04_eq] at this
  have hp3 : [(4 : B256), 4, r] <<+ s3.stack := prefix_of_dup_val h3 (by show_nth) hp2
  have hp4 : [(4 : B256), 4, 4, r] <<+ s4.stack := prefix_of_dup_val h4 (by show_nth) hp3
  have hp5 := prefix_of_calldataload_val h5 hp4
  have hp7 : [allowArg sevm, 4, 4, r] <<+ s7.stack := by
    have := prefix_of_and h7 (prefix_of_push (of_run_push h6) hp5)
    rwa [ff20_and_dataWord] at this
  have hp8 : [(4 : B256), allowArg sevm, 4, r] <<+ s8.stack :=
    Stack.prefix_of_swap (n := 0) (by simp [Stack.Swap, Stack.SwapCore])
      (of_run_swap h8) hp7
  have hp9 : [(32 : B256), 4, allowArg sevm, 4, r] <<+ s9.stack := by
    have := prefix_of_push (of_run_push h9) hp8
    rwa [w20_eq] at this
  have hp10 : [(32 : B256) + 4, allowArg sevm, 4, r] <<+ s10.stack :=
    prefix_of_add h10 hp9
  have hp11 : [allowArg sevm, (32 : B256) + 4, 4, r] <<+ s11.stack :=
    Stack.prefix_of_swap (n := 0) (by simp [Stack.Swap, Stack.SwapCore])
      (of_run_swap h11) hp10
  have hp12 : [(4 : B256), (32 : B256) + 4, allowArg sevm, r] <<+ s12.stack :=
    Stack.prefix_of_swap (n := 1) (by simp [Stack.Swap, Stack.SwapCore])
      (of_run_swap h12) hp11
  have hp13 : [(32 : B256) + 4, 4, allowArg sevm, r] <<+ s13.stack :=
    Stack.prefix_of_swap (n := 0) (by simp [Stack.Swap, Stack.SwapCore])
      (of_run_swap h13) hp12
  have hp14 : [(32 : B256) + 4, (32 : B256) + 4, 4, allowArg sevm, r] <<+ s14.stack :=
    prefix_of_dup_val h14 (by show_nth) hp13
  obtain ⟨v, hp15⟩ : ∃ v : B256, [v, (32 : B256) + 4, 4, allowArg sevm, r] <<+ s15.stack :=
    ⟨_, prefix_of_calldataload_val h15 hp14⟩
  have hp16 : [(32 : B256) + 4, v, 4, allowArg sevm, r] <<+ s16.stack :=
    Stack.prefix_of_swap (n := 0) (by simp [Stack.Swap, Stack.SwapCore])
      (of_run_swap h16) hp15
  obtain ⟨u, hp18⟩ : ∃ u : B256, [u, v, 4, allowArg sevm, r] <<+ s18.stack :=
    ⟨_, prefix_of_add h18 (prefix_of_push (of_run_push h17) hp16)⟩
  have hp19 : [v, u, 4, allowArg sevm, r] <<+ s19.stack :=
    Stack.prefix_of_swap (n := 0) (by simp [Stack.Swap, Stack.SwapCore])
      (of_run_swap h19) hp18
  have hp20 : [(4 : B256), u, v, allowArg sevm, r] <<+ s20.stack :=
    Stack.prefix_of_swap (n := 1) (by simp [Stack.Swap, Stack.SwapCore])
      (of_run_swap h20) hp19
  have hp21 : [u, (4 : B256), v, allowArg sevm, r] <<+ s21.stack :=
    Stack.prefix_of_swap (n := 0) (by simp [Stack.Swap, Stack.SwapCore])
      (of_run_swap h21) hp20
  have hp23 := prefix_of_pop (of_run_pop h23) (prefix_of_pop (of_run_pop h22) hp21)
  exact ⟨_, v, [r], prefix_of_push (of_run_push h24) hp23⟩

private theorem solvent_zero {s : Stor} {v b : B256} (h : Solvent s v b) : Solvent s 0 b := by
  unfold Solvent at h ⊢
  rw [B256.toNat_zero]
  omega

/-- **Entry 27 wrapper spec.**  Under the local allowance-collision premise,
the `approve` selector wrapper turns solvency with the callvalue in flight into
solvency with nothing in flight, on both its revert and its call branch. -/
theorem approve_wrapper_solvent {sevm : Sevm} {d : Devm} {o : Outcome} {w : SFunc}
    (hw : prog[27]? = some w) (hadm : AllowAdmitted sevm)
    (h : Solvent (Devm.getStor d sevm.currentTarget) sevm.value
      (Devm.getBal d sevm.currentTarget))
    (run : SFunc.Run prog sevm d w o) :
    Solvent (Devm.getStor (Outcome.devm o) sevm.currentTarget) 0
      (Devm.getBal (Outcome.devm o) sevm.currentTarget) := by
  have hw' : w = t_0147_c27 := by
    simpa [prog, Cert.prog, cert] using hw.symm
  subst w
  unfold t_0147_c27 at run
  cases run with
  | dest burn r =>
  cases r with
  | next h1 r =>
  cases r with
  | next h2 r =>
  cases r with
  | next h3 r =>
  rename_i d0 d1 d2 d3
  have hs3 : Solvent (Devm.getStor d3 sevm.currentTarget) sevm.value
      (Devm.getBal d3 sevm.currentTarget) := by
    refine solvent_transport (d := d0) ?_ ?_ (solvent_transport (d := d) (d' := d0) ?_ ?_ h)
    · exact (Line.of_inv Devm.getStor (by line_inv) (.cons h1 (.cons h2 (.cons h3 .nil)))).symm
    · exact (Line.of_inv Devm.getBal (by line_inv) (.cons h1 (.cons h2 (.cons h3 .nil)))).symm
    · funext a; exact Devm.Burn.getStor burn a
    · funext a; exact Devm.Burn.getBal burn a
  cases r with
  | zero x pop r =>
    rename_i d4
    have hs4 := solvent_transport (d := d3) (d' := d4)
      (getStor_of_state pop.state.symm) (getBal_of_state pop.state.symm) hs3
    have hst := SFunc.Run.state_of_silent (S := []) rfl (by decide) (by decide) r
    exact solvent_zero (solvent_transport (getStor_of_state hst) (getBal_of_state hst) hs4)
  | succ x ww hnz pop r =>
    rename_i d4
    have hs4 := solvent_transport (d := d3) (d' := d4)
      (getStor_of_state pop.state.symm) (getBal_of_state pop.state.symm) hs3
    rw [wrap_tree_eq] at r
    cases r with
    | dest burn2 r =>
    rename_i d5
    have hs5 := solvent_transport (d := d4) (d' := d5)
      (getStor_of_state burn2.state.symm) (getBal_of_state burn2.state.symm) hs4
    rcases run_chain_prefix wrapLine [] r with ⟨d6, hl, r⟩
    have hs6 : Solvent (Devm.getStor d6 sevm.currentTarget) sevm.value
        (Devm.getBal d6 sevm.currentTarget) :=
      solvent_transport (Line.of_inv Devm.getStor (by line_inv) hl).symm
        (Line.of_inv Devm.getBal (by line_inv) hl).symm hs5
    obtain ⟨t, v, ys, hstk⟩ := wrap_line_stack hl
    have hoff : ∀ a, balSlot a ≠
        allowKey sevm.caller.toB256 (allowArg sevm &&& ~~~ addressMask) := by
      rw [allowArg_mask]; exact hadm.1
    change SFunc.Run prog sevm d6 (.callNext 11 t_0187_c27) o at r
    cases r with
    | @callHalt _ d7 _ _ _ g x lookup pop2 rc =>
      have hs7 := solvent_transport (d := d6) (d' := d7)
        (getStor_of_state pop2.state.symm) (getBal_of_state pop2.state.symm) hs6
      exact approve_solvent lookup (popBurn_pref pop2 hstk).2 hoff hs7 rc
    | @callRet _ d7 d8 _ _ g _ x lookup pop2 rc tail =>
      have hs7 := solvent_transport (d := d6) (d' := d7)
        (getStor_of_state pop2.state.symm) (getBal_of_state pop2.state.symm) hs6
      have hc := approve_solvent lookup (popBurn_pref pop2 hstk).2 hoff hs7 rc
      have hst := SFunc.Run.state_of_silent (S := []) rfl (by decide) (by decide) tail
      exact solvent_transport (getStor_of_state hst) (getBal_of_state hst) hc

end Weth9

end Blanc.Lift
