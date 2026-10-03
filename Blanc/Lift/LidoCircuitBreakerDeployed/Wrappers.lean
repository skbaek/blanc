import Blanc.Lift.LidoCircuitBreakerDeployed.Contract
import Blanc.Lift.LidoCircuitBreakerDeployed.Silent
import Blanc.Lift.LidoCircuitBreakerDeployed.Foreign
import Blanc.Lift.InvWalkWorld

/-!
# The deployed Lido CircuitBreaker's non-registry writers

Ladder unit (e)-small.  The three writers whose only storage write is off the
Registry layout, each as a Hoare statement over `RegInv` (the storage abstracts
some Registry model state, `lidoSpec.Inv` with the value and balance ignored):

* `heartbeat` (wrapper 52 → body 14 → `_setHeartbeatExpiry`, entry 22), which
  writes `heartbeatExpiry[msg.sender]` at `mapSlot caller 2`;
* `setPauseDuration` (wrapper 44 → decoder 8 → `onlyAdmin` guard 9 →
  `_setPauseDuration`, entry 30), which writes slot `0`;
* `setHeartbeatInterval` (wrapper 48 → 8 → guard 12 → entry 31), which writes
  slot `1`.

Each carries exactly the one `ForeignApart (2 ^ 160) w` premise for its written
slot `w`, and preservation is `RegistryWitness.of_foreign_set_160`.  Revert arms
have no successful synthetic run (`Linst.run .revert` is never `.ok`), so they
need no separate case; the `onlyAdmin` and bounds guards are covered by the
same walks.
-/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune
open Blanc
open Blanc.Lift
open Blanc.LidoCircuitBreaker

/-- The frame invariant on a storage map: it abstracts some Registry state. -/
def RegInv (s : Stor) : Prop := ∃ entries, RegistryWitness (solRegistryStorage s) entries

theorem RegInv.set_foreign {s : Stor} {w v : B256} (hw : ForeignApart (2 ^ 160) w)
    (h : RegInv s) : RegInv (s.set w v) := by
  obtain ⟨entries, h⟩ := h
  exact ⟨entries, RegistryWitness.of_foreign_set_160 hw h⟩

private theorem ff20_and (x : B256) :
    (x &&& Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) = x.toAdr.toB256 := by
  rw [show Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] = ~~~ addressMask by decide,
    B256.and_comm]
  exact addressSlotReadWord_eq_toAdr_toB256 x

/-! ## Entry 22: `_setHeartbeatExpiry(p, v)` -/

/-- Entry 22 writes exactly `mapSlot (addr p) 2`, `p` being the second stack word. -/
theorem entry22_stor {sevm : Sevm} {d : Devm} {o : Outcome} {v p : B256} {xs : Stack}
    (hstk : v :: p :: xs <<+ d.stack)
    (run : SFunc.Run prog sevm d t_0cd5_c22 o) :
    Devm.getStor (Outcome.devm o) sevm.currentTarget =
      (Devm.getStor d sevm.currentTarget).set (mapSlot p.toAdr.toB256 2) v := by
  unfold t_0cd5_c22 at run
  cases run with
  | dest burn r =>
  cases r with | next h1 r =>
  cases r with | next h2 r =>
  cases r with | next h3 r =>
  cases r with | next h4 r =>
  cases r with | next h5 r =>
  cases r with | next h6 r =>
  cases r with | next h7 r =>
  cases r with | next h8 r =>
  cases r with | next h9 r =>
  cases r with | next h10 r =>
  cases r with | next h11 r =>
  cases r with | next h12 r =>
  cases r with | next h13 r =>
  cases r with | next h14 r =>
  cases r with | next h15 r =>
  cases r with | next h16 r =>
  cases r with | next h17 r =>
  cases r with | next h18 r =>
  rename_i d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18
  have hp0 : v :: p :: xs <<+ d0.stack := by rw [← burn.stack]; exact hstk
  set q := p.toAdr.toB256 with hq
  have hp1 := prefix_of_push (of_run_push h1) hp0
  have hp2 := prefix_of_dup_val h2 (by show_nth) hp1
  have hp3 : q :: v :: p :: xs <<+ d3.stack := by
    have := prefix_of_and h3 hp2
    rwa [ff20_and] at this
  have hp4 : (0 : B256) :: q :: v :: p :: xs <<+ d4.stack :=
    prefix_of_push (of_run_push h4) hp3
  have hp5 : q :: (0 : B256) :: q :: v :: p :: xs <<+ d5.stack :=
    prefix_of_dup_val h5 (by show_nth) hp4
  have hp6 : (0 : B256) :: q :: (0 : B256) :: q :: v :: p :: xs <<+ d6.stack :=
    prefix_of_dup_val h6 (by show_nth) hp5
  have hA := prefix_of_mstore_val h7 hp6
  have hp9 : (32 : B256) :: (2 : B256) :: (0 : B256) :: q :: v :: p :: xs <<+ d9.stack :=
    prefix_of_push (of_run_push h9) (prefix_of_push (of_run_push h8) hA.1)
  have hB := prefix_of_mstore_val h10 hp9
  have hp11 : (64 : B256) :: (0 : B256) :: q :: v :: p :: xs <<+ d11.stack :=
    prefix_of_push (of_run_push h11) hB.1
  have hp12 : (0 : B256) :: (64 : B256) :: q :: v :: p :: xs <<+ d12.stack :=
    Stack.prefix_of_swap (n := 0) (by simp only [Stack.Swap, Stack.SwapCore, and_self])
      (of_run_swap h12) hp11
  have hp13 : (64 : B256) :: (0 : B256) :: (64 : B256) :: q :: v :: p :: xs <<+ d13.stack :=
    prefix_of_dup_val h13 (by show_nth) hp12
  have hp14 : (0 : B256) :: (64 : B256) :: (64 : B256) :: q :: v :: p :: xs <<+ d14.stack :=
    Stack.prefix_of_swap (n := 0) (by simp only [Stack.Swap, Stack.SwapCore, and_self])
      (of_run_swap h14) hp13
  have hm8 : d7.memory = d9.memory :=
    Line.of_inv Devm.memory (by line_inv) (.cons h8 (.cons h9 .nil))
  have hm11 : d10.memory = d14.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (.cons h11 (.cons h12 (.cons h13 (.cons h14 .nil))))
  have hm4 : d3.memory = d6.memory :=
    Line.of_inv Devm.memory (by line_inv) (.cons h4 (.cons h5 (.cons h6 .nil)))
  have hmem : d14.memory = (d3.memory.write 0 q.toBytes).write 32
      (2 : B256).toBytes := by
    rw [← hm11, hB.2, ← hm8, hA.2, ← hm4]
    rfl
  have hK := (prefix_of_keccak256_val h15 hp14).1
  rw [hmem, show (0 : B256).toNat = 0 from rfl, show (64 : B256).toNat = 64 from rfl,
    Mem.read_two_word_writes_at_raw] at hK
  have hp16 : v :: mapSlot q 2 :: (64 : B256) :: q :: v :: p :: xs <<+ d16.stack :=
    prefix_of_dup_val h16 (by show_nth) hK
  have hp17 : mapSlot q 2 :: v :: (64 : B256) :: q :: v :: p :: xs <<+ d17.stack :=
    Stack.prefix_of_swap (n := 0) (by simp only [Stack.Swap, Stack.SwapCore, and_self])
    (of_run_swap h17) hp16
  have hset := sstore_getStor_set h18 hp17
  have hpre : Devm.getStor d0 = Devm.getStor d17 :=
    Line.of_inv Devm.getStor (by line_inv)
      (.cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 (.cons h6 (.cons h7 (.cons h8
        (.cons h9 (.cons h10 (.cons h11 (.cons h12 (.cons h13 (.cons h14 (.cons h15
        (.cons h16 (.cons h17 .nil)))))))))))))))))
  have hburn : Devm.getStor d0 = Devm.getStor d := by
    funext a; exact Devm.Burn.getStor burn a
  have htail := SFunc.Run.state_of_silent silent_entries (by decide) (by decide) r
  rw [getStor_eq_of_state_eq htail, hset, ← hpre, hburn]


/-! ## Shared steps -/


/-- A run of a state-silent entry keeps the persistent state. -/
theorem silent_entry_state {sevm : Sevm} {d : Devm} {o : Outcome} {k : Nat} {g : SFunc}
    (hk : k ∈ silentEntries) (hg : prog[k]? = some g) (run : SFunc.Run prog sevm d g o) :
    (Outcome.devm o).state = d.state := by
  have h := (List.all_eq_true.mp silent_entries) k hk
  rw [hg] at h
  simp only [Bool.and_eq_true] at h
  exact SFunc.Run.state_of_silent silent_entries h.1 h.2 run

/-- The two words a conditional branch pops leave the rest of a known prefix. -/
theorem pop2_tail {s s' : Devm} {a b dd w : B256} {xs : Stack}
    (hp : a :: b :: xs <<+ s.stack) (h : Devm.PopBurn [dd, w] s s') : xs <<+ s'.stack := by
  obtain ⟨t, ht⟩ := hp
  have hs : s.stack = dd :: w :: s'.stack := h.stack
  have ht' : s.stack = a :: b :: (xs ++ t) := ht
  rw [hs] at ht'
  simp only [List.cons.injEq] at ht'
  exact ⟨t, ht'.2.2⟩

/-- `RegInv` of the frame's storage is a property of the persistent state. -/
theorem regInv_of_state {sevm : Sevm} {d d' : Devm} (hs : d'.state = d.state)
    (h : RegInv (Devm.getStor d sevm.currentTarget)) :
    RegInv (Devm.getStor d' sevm.currentTarget) := by
  rw [getStor_eq_of_state_eq hs]; exact h

/-! ## Entry 23: the checked addition's return shape -/

/-- Entry 23 (checked `a + b`, returning through entry 3) returns with one word
above the caller's remaining stack; its panic arm (entry 38) never returns. -/
theorem entry23_ret {sevm : Sevm} {d d' : Devm} {a b ra : B256} {xs : Stack}
    (hstk : a :: b :: ra :: xs <<+ d.stack)
    (run : SFunc.Run prog sevm d t_10a8_c23 (.returned d')) :
    ∃ w, w :: xs <<+ d'.stack := by
  unfold t_10a8_c23 at run
  cases run with
  | dest burn r =>
  cases r with | next h1 r =>
  cases r with | next h2 r =>
  cases r with | next h3 r =>
  cases r with | next h4 r =>
  cases r with | next h5 r =>
  cases r with | next h6 r =>
  cases r with | next h7 r =>
  cases r with | next h8 r =>
  rename_i d0 d1 d2 d3 d4 d5 d6 d7 d8
  have hp0 : a :: b :: ra :: xs <<+ d0.stack := by rw [← burn.stack]; exact hstk
  have hp1 : a :: a :: b :: ra :: xs <<+ d1.stack := prefix_of_dup_val h1 (by show_nth) hp0
  have hp2 : b :: a :: a :: b :: ra :: xs <<+ d2.stack := prefix_of_dup_val h2 (by show_nth) hp1
  have hp3 : (b + a) :: a :: b :: ra :: xs <<+ d3.stack := prefix_of_add h3 hp2
  have hp4 : (b + a) :: (b + a) :: a :: b :: ra :: xs <<+ d4.stack :=
    prefix_of_dup_val h4 (by show_nth) hp3
  have hp5 : a :: (b + a) :: (b + a) :: a :: b :: ra :: xs <<+ d5.stack :=
    prefix_of_dup_val h5 (by show_nth) hp4
  have hp6 := prefix_of_gt h6 hp5
  have hp7 := prefix_of_iszero h7 hp6
  have hp8 := prefix_of_push (of_run_push h8) hp7
  cases r with
  | toZero dd pop r =>
    cases r with | next _ r =>
    cases r with | next _ r =>
    cases r with | jump _ lookup _ r =>
    have h38 : prog[38]? = some t_107b_c38 := rfl
    rw [h38] at lookup
    cases lookup
    exact (SFunc.RunCutP.false_of_noOk (SFunc.Run.cut r) (by decide)).elim
  | toSucc dd w hnz lookup pop r =>
    have h3 : prog[3]? = some t_051a_c3 := rfl
    rw [h3] at lookup
    cases lookup
    have hp9 : (b + a) :: a :: b :: ra :: xs <<+ _ := pop2_tail hp8 pop
    unfold t_051a_c3 at r
    cases r with
    | dest burn2 r =>
    cases r with | next g1 r =>
    cases r with | next g2 r =>
    cases r with | next g3 r =>
    cases r with | next g4 r =>
    cases r with | ret dd2 pop2 =>
    rename_i e0 e1 e2 e3 e4
    have q0 : (b + a) :: a :: b :: ra :: xs <<+ e0.stack := by rw [← burn2.stack]; exact hp9
    have q1 : ra :: a :: b :: (b + a) :: xs <<+ e1.stack :=
      Stack.prefix_of_swap (n := 2) (by simp only [Stack.Swap, Stack.SwapCore, and_self]) (of_run_swap g1) q0
    have q2 : b :: a :: ra :: (b + a) :: xs <<+ e2.stack :=
      Stack.prefix_of_swap (n := 1) (by simp only [Stack.Swap, Stack.SwapCore, and_self]) (of_run_swap g2) q1
    have q4 := prefix_of_pop (of_run_pop g4) (prefix_of_pop (of_run_pop g3) q2)
    exact ⟨b + a, (popBurn_pref pop2 q4).2⟩


/-! ## Entry 14: the `heartbeat()` body -/

/-- Entry 14 (`heartbeat`: the `pausableCount[msg.sender] > 0` and liveness
guards, then `_setHeartbeatExpiry(msg.sender, now + heartbeatInterval)`)
preserves `RegInv` when `heartbeatExpiry[msg.sender]` is off the Registry. -/
theorem entry14_regInv {sevm : Sevm} {d : Devm} {o : Outcome}
    (hfa : ForeignApart (2 ^ 160) (mapSlot sevm.caller.toB256 2))
    (h : RegInv (Devm.getStor d sevm.currentTarget))
    (run : SFunc.Run prog sevm d t_0450_c14 o) :
    RegInv (Devm.getStor (Outcome.devm o) sevm.currentTarget) := by
  unfold t_0450_c14 at run
  cases run with
  | dest burn r =>
  cases r with | next h1 r =>
  cases r with | next h2 r =>
  cases r with | next h3 r =>
  cases r with | next h4 r =>
  cases r with | next h5 r =>
  cases r with | next h6 r =>
  cases r with | next h7 r =>
  cases r with | next h8 r =>
  cases r with | next h9 r =>
  cases r with | next h10 r =>
  cases r with | next h11 r =>
  cases r with | next h12 r =>
  cases r with | next h13 r =>
  have i0 := regInv_of_state burn.state.symm h
  have i1 := Line.of_inv Devm.getStor (by line_inv)
      (.cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 (.cons h6 (.cons h7 (.cons h8
        (.cons h9 (.cons h10 (.cons h11 (.cons h12 (.cons h13 .nil)))))))))))))
  rw [i1] at i0
  cases r with
  | zero _ _ r => exact (SFunc.RunCutP.false_of_noOk (SFunc.Run.cut r) (by decide)).elim
  | succ _ _ _ pop r =>
  have i2 := regInv_of_state pop.state.symm i0
  unfold t_0495_c14 at r
  cases r with
  | dest burn2 r =>
  cases r with | next g1 r =>
  cases r with | next g2 r =>
  cases r with | next g3 r =>
  cases r with | next g4 r =>
  cases r with | next g5 r =>
  cases r with | next g6 r =>
  cases r with | next g7 r =>
  cases r with | next g8 r =>
  cases r with | next g9 r =>
  cases r with | next g10 r =>
  cases r with | next g11 r =>
  cases r with | next g12 r =>
  cases r with | next g13 r =>
  cases r with | next g14 r =>
  cases r with | next g15 r =>
  have i3 := regInv_of_state burn2.state.symm i2
  have i4 := Line.of_inv Devm.getStor (by line_inv)
      (.cons g1 (.cons g2 (.cons g3 (.cons g4 (.cons g5 (.cons g6 (.cons g7 (.cons g8
        (.cons g9 (.cons g10 (.cons g11 (.cons g12 (.cons g13 (.cons g14 (.cons g15
        .nil)))))))))))))))
  rw [i4] at i3
  cases r with
  | zero _ _ r => exact (SFunc.RunCutP.false_of_noOk (SFunc.Run.cut r) (by decide)).elim
  | succ _ _ _ pop2 r =>
  have i5 := regInv_of_state pop2.state.symm i3
  unfold t_04dc_c14 at r
  cases r with
  | dest burn3 r =>
  cases r with | next k1 r =>
  cases r with | next k2 r =>
  cases r with | next k3 r =>
  cases r with | next k4 r =>
  cases r with | next k5 r =>
  cases r with | next k6 r =>
  cases r with | next k7 r =>
  cases r with | next k8 r =>
  cases r with | next k9 r =>
  rename_i e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  have hE : Devm.getStor e0 = Devm.getStor e9 :=
    Line.of_inv Devm.getStor (by line_inv)
      (.cons k1 (.cons k2 (.cons k3 (.cons k4 (.cons k5 (.cons k6 (.cons k7 (.cons k8
        (.cons k9 .nil)))))))))
  have h9 : RegInv (Devm.getStor e9 sevm.currentTarget) := by
    rw [← hE]; exact regInv_of_state burn3.state.symm i5
  -- the stack at the call to entry 23
  have p1 : (Bytes.toB256 [0x04, 0xee]) :: [] <<+ e1.stack :=
    prefix_of_push (of_run_push k1) nil_pref
  have p2 := prefix_of_push (of_run_caller k2) p1
  have p3 := prefix_of_push (of_run_push k3) p2
  obtain ⟨y, p4, -⟩ := prefix_of_sload k4 p3
  have p5 := prefix_of_timestamp p4 k5
  have p6 := prefix_of_push (of_run_push k6) p5
  have p7 : y :: sevm.benvStat.time :: Bytes.toB256 [0x04, 0x46] :: sevm.caller.toB256 ::
      Bytes.toB256 [0x04, 0xee] :: [] <<+ e7.stack :=
    Stack.prefix_of_swap (n := 1) (by simp only [Stack.Swap, List.cons_append, List.nil_append,
      List.append_eq, Stack.SwapCore, and_self]) (of_run_swap k7) p6
  have p8 : sevm.benvStat.time :: y :: Bytes.toB256 [0x04, 0x46] :: sevm.caller.toB256 ::
      Bytes.toB256 [0x04, 0xee] :: [] <<+ e8.stack :=
    Stack.prefix_of_swap (n := 0) (by simp only [Stack.Swap, Stack.SwapCore, and_self]) (of_run_swap k8) p7
  have p9 := prefix_of_push (of_run_push k9) p8
  have h23 : prog[23]? = some t_10a8_c23 := rfl
  have h22 : prog[22]? = some t_0cd5_c22 := rfl
  cases r with
  | callHalt _ lookup pop3 r =>
    rw [h23] at lookup; cases lookup
    exact regInv_of_state (silent_entry_state (by decide) h23 r)
      (regInv_of_state pop3.state.symm h9)
  | callRet _ lookup pop3 r tail =>
    rw [h23] at lookup; cases lookup
    have q0 := (popBurn_pref pop3 p9).2
    obtain ⟨w, q1⟩ := entry23_ret q0 r
    have hf1 := regInv_of_state (silent_entry_state (by decide) h23 r)
        (regInv_of_state pop3.state.symm h9)
    unfold t_0446_c14 at tail
    cases tail with
    | dest burn4 tail =>
    cases tail with | next m1 tail =>
    have hf3 := regInv_of_state burn4.state.symm hf1
    rw [Line.of_inv Devm.getStor (by line_inv) (.cons m1 .nil)] at hf3
    have q3 := prefix_of_push (of_run_push m1) (by rw [← burn4.stack]; exact q1)
    have hkey : mapSlot (sevm.caller.toB256).toAdr.toB256 2 = mapSlot sevm.caller.toB256 2 := by
      rw [toAdr_toB256]
    cases tail with
    | callHalt _ lookup pop4 r4 =>
      rw [h22] at lookup; cases lookup
      have q4 := (popBurn_pref pop4 q3).2
      rw [entry22_stor q4 r4, hkey]
      exact RegInv.set_foreign hfa (regInv_of_state pop4.state.symm hf3)
    | callRet _ lookup pop4 r4 tail4 =>
      rw [h22] at lookup; cases lookup
      have q4 := (popBurn_pref pop4 q3).2
      have hs := entry22_stor q4 r4
      simp only [Outcome.devm] at hs
      have hst := SFunc.Run.state_of_silent (S := []) rfl (by decide) (by decide) tail4
      rw [getStor_eq_of_state_eq hst, hs, hkey]
      exact RegInv.set_foreign hfa (regInv_of_state pop4.state.symm hf3)


/-! ## Entries 30 and 31: the constant-slot setters -/

/-- Entry 30 (`_setPauseDuration`: the `MIN`/`MAX` bounds, then `pauseDuration = v`, `emit`) writes only slot `0`. -/
theorem entry30_regInv {sevm : Sevm} {d : Devm} {o : Outcome}
    (hfa : ForeignApart (2 ^ 160) 0)
    (h : RegInv (Devm.getStor d sevm.currentTarget))
    (run : SFunc.Run prog sevm d t_0ea0_c30 o) :
    RegInv (Devm.getStor (Outcome.devm o) sevm.currentTarget) := by
  unfold t_0ea0_c30 at run
  cases run with
  | dest burn r =>
  cases r with | next a1 r =>
  cases r with | next a2 r =>
  cases r with | next a3 r =>
  cases r with | next a4 r =>
  cases r with | next a5 r =>
  have i0 := regInv_of_state burn.state.symm h
  rw [Line.of_inv Devm.getStor (by line_inv) (.cons a1 (.cons a2 (.cons a3 (.cons a4 (.cons a5 .nil)))))] at i0
  cases r with
  | zero _ _ r => exact (SFunc.RunCutP.false_of_noOk (SFunc.Run.cut r) (by decide)).elim
  | succ _ _ _ pop r =>
  have i1 := regInv_of_state pop.state.symm i0
  unfold t_0efa_c30 at r
  cases r with
  | dest burn2 r =>
  cases r with | next b1 r =>
  cases r with | next b2 r =>
  cases r with | next b3 r =>
  cases r with | next b4 r =>
  cases r with | next b5 r =>
  have i2 := regInv_of_state burn2.state.symm i1
  rw [Line.of_inv Devm.getStor (by line_inv) (.cons b1 (.cons b2 (.cons b3 (.cons b4 (.cons b5 .nil)))))] at i2
  cases r with
  | zero _ _ r => exact (SFunc.RunCutP.false_of_noOk (SFunc.Run.cut r) (by decide)).elim
  | succ _ _ _ pop2 r =>
  have i3 := regInv_of_state pop2.state.symm i2
  unfold t_0f54_c30 at r
  cases r with
  | dest burn3 r =>
  cases r with | next c1 r =>
  cases r with | next c2 r =>
  cases r with | next c3 r =>
  cases r with | next c4 r =>
  cases r with | next c5 r =>
  cases r with | next c6 r =>
  cases r with | next c7 r =>
  cases r with | next c8 r =>
  cases r with | next c9 r =>
  cases r with | next c10 r =>
  cases r with | next c11 r =>
  cases r with | next c12 r =>
  cases r with | next c13 r =>
  cases r with | next c14 r =>
  cases r with | next c15 r =>
  cases r with | next c16 r =>
  cases r with | next c17 r =>
  cases r with | next c18 r =>
  cases r with | next c19 r =>
  cases r with | next c20 r =>
  cases r with | next c21 r =>
  cases r with | next c22 r =>
  cases r with | next c23 r =>
  cases r with | next c24 r =>
  cases r with | next c25 r =>
  cases r with | next c26 r =>
  cases r with
  | ret _ pop4 =>
  have i4 := regInv_of_state burn3.state.symm i3
  rw [Line.of_inv Devm.getStor (by line_inv) (.cons c1 (.cons c2 (.cons c3 (.cons c4 (.cons c5 (.cons c6 (.cons c7 (.cons c8 (.cons c9 (.cons c10 (.cons c11 (.cons c12 (.cons c13 (.cons c14 (.cons c15 (.cons c16 (.cons c17 (.cons c18 (.cons c19 (.cons c20 (.cons c21 (.cons c22 (.cons c23 (.cons c24 (.cons c25 .nil)))))))))))))))))))))))))] at i4
  have hk : (0 : B256) :: [] <<+ _ := prefix_of_push (of_run_push c25) nil_pref
  obtain ⟨v, hv⟩ := sstore_getStor_setStorVal c26 hk
  have i5 := RegInv.set_foreign (v := v) hfa i4
  rw [← hv] at i5
  exact regInv_of_state pop4.state.symm i5

/-- Entry 31 (`_setHeartbeatInterval`: the bounds, then `heartbeatInterval = v`, `emit`) writes only slot `1`. -/
theorem entry31_regInv {sevm : Sevm} {d : Devm} {o : Outcome}
    (hfa : ForeignApart (2 ^ 160) 1)
    (h : RegInv (Devm.getStor d sevm.currentTarget))
    (run : SFunc.Run prog sevm d t_0dab_c31 o) :
    RegInv (Devm.getStor (Outcome.devm o) sevm.currentTarget) := by
  unfold t_0dab_c31 at run
  cases run with
  | dest burn r =>
  cases r with | next a1 r =>
  cases r with | next a2 r =>
  cases r with | next a3 r =>
  cases r with | next a4 r =>
  cases r with | next a5 r =>
  have i0 := regInv_of_state burn.state.symm h
  rw [Line.of_inv Devm.getStor (by line_inv) (.cons a1 (.cons a2 (.cons a3 (.cons a4 (.cons a5 .nil)))))] at i0
  cases r with
  | zero _ _ r => exact (SFunc.RunCutP.false_of_noOk (SFunc.Run.cut r) (by decide)).elim
  | succ _ _ _ pop r =>
  have i1 := regInv_of_state pop.state.symm i0
  unfold t_0e05_c31 at r
  cases r with
  | dest burn2 r =>
  cases r with | next b1 r =>
  cases r with | next b2 r =>
  cases r with | next b3 r =>
  cases r with | next b4 r =>
  cases r with | next b5 r =>
  have i2 := regInv_of_state burn2.state.symm i1
  rw [Line.of_inv Devm.getStor (by line_inv) (.cons b1 (.cons b2 (.cons b3 (.cons b4 (.cons b5 .nil)))))] at i2
  cases r with
  | zero _ _ r => exact (SFunc.RunCutP.false_of_noOk (SFunc.Run.cut r) (by decide)).elim
  | succ _ _ _ pop2 r =>
  have i3 := regInv_of_state pop2.state.symm i2
  unfold t_0e5f_c31 at r
  cases r with
  | dest burn3 r =>
  cases r with | next c1 r =>
  cases r with | next c2 r =>
  cases r with | next c3 r =>
  cases r with | next c4 r =>
  cases r with | next c5 r =>
  cases r with | next c6 r =>
  cases r with | next c7 r =>
  cases r with | next c8 r =>
  cases r with | next c9 r =>
  cases r with | next c10 r =>
  cases r with | next c11 r =>
  cases r with | next c12 r =>
  cases r with | next c13 r =>
  cases r with | next c14 r =>
  cases r with | next c15 r =>
  cases r with | next c16 r =>
  cases r with | next c17 r =>
  cases r with | next c18 r =>
  cases r with | next c19 r =>
  cases r with | next c20 r =>
  cases r with | next c21 r =>
  cases r with | next c22 r =>
  cases r with | next c23 r =>
  cases r with | next c24 r =>
  cases r with | next c25 r =>
  cases r with | next c26 r =>
  cases r with
  | ret _ pop4 =>
  have i4 := regInv_of_state burn3.state.symm i3
  rw [Line.of_inv Devm.getStor (by line_inv) (.cons c1 (.cons c2 (.cons c3 (.cons c4 (.cons c5 (.cons c6 (.cons c7 (.cons c8 (.cons c9 (.cons c10 (.cons c11 (.cons c12 (.cons c13 (.cons c14 (.cons c15 (.cons c16 (.cons c17 (.cons c18 (.cons c19 (.cons c20 (.cons c21 (.cons c22 (.cons c23 (.cons c24 (.cons c25 .nil)))))))))))))))))))))))))] at i4
  have hk : (1 : B256) :: [] <<+ _ := prefix_of_push (of_run_push c25) nil_pref
  obtain ⟨v, hv⟩ := sstore_getStor_setStorVal c26 hk
  have i5 := RegInv.set_foreign (v := v) hfa i4
  rw [← hv] at i5
  exact regInv_of_state pop4.state.symm i5


/-! ## Calls, the `onlyAdmin` guards and the selector wrappers -/

/-- A `callNext` whose callee and continuation both preserve `RegInv`. -/
theorem callNext_regInv {sevm : Sevm} {d : Devm} {o : Outcome} {k : Nat} {g f : SFunc}
    (hk : prog[k]? = some g)
    (hspec : ∀ {d o}, RegInv (Devm.getStor d sevm.currentTarget) →
      SFunc.Run prog sevm d g o → RegInv (Devm.getStor (Outcome.devm o) sevm.currentTarget))
    (htail : ∀ {d o}, RegInv (Devm.getStor d sevm.currentTarget) →
      SFunc.Run prog sevm d f o → RegInv (Devm.getStor (Outcome.devm o) sevm.currentTarget))
    (h : RegInv (Devm.getStor d sevm.currentTarget))
    (run : SFunc.Run prog sevm d (.callNext k f) o) :
    RegInv (Devm.getStor (Outcome.devm o) sevm.currentTarget) := by
  cases run with
  | callHalt _ lookup pop r =>
    rw [hk] at lookup; cases lookup
    exact hspec (regInv_of_state pop.state.symm h) r
  | callRet _ lookup pop r tail =>
    rw [hk] at lookup; cases lookup
    exact htail (hspec (regInv_of_state pop.state.symm h) r) tail

/-- A state-silent tree with no references keeps `RegInv`. -/
theorem silentTail_regInv {sevm : Sevm} {d : Devm} {o : Outcome} {f : SFunc}
    (hf : f.silent = true := by decide) (hr : f.refs.all (· ∈ ([] : List Nat)) = true := by decide)
    (h : RegInv (Devm.getStor d sevm.currentTarget))
    (run : SFunc.Run prog sevm d f o) :
    RegInv (Devm.getStor (Outcome.devm o) sevm.currentTarget) :=
  regInv_of_state (SFunc.Run.state_of_silent (S := []) rfl hf hr run) h

/-- A silent entry, as a callee, keeps `RegInv`. -/
theorem silentCallee_regInv {sevm : Sevm} {d : Devm} {o : Outcome} {k : Nat} {g : SFunc}
    (hk : k ∈ silentEntries) (hg : prog[k]? = some g)
    (h : RegInv (Devm.getStor d sevm.currentTarget))
    (run : SFunc.Run prog sevm d g o) :
    RegInv (Devm.getStor (Outcome.devm o) sevm.currentTarget) :=
  regInv_of_state (silent_entry_state hk hg run) h

/-- Entry 9 (`setPauseDuration` body: `onlyAdmin`, then `_setPauseDuration`, entry 30). -/
theorem entry9_regInv {sevm : Sevm} {d : Devm} {o : Outcome}
    (hfa : ForeignApart (2 ^ 160) 0)
    (h : RegInv (Devm.getStor d sevm.currentTarget))
    (run : SFunc.Run prog sevm d t_08bc_c9 o) :
    RegInv (Devm.getStor (Outcome.devm o) sevm.currentTarget) := by
  unfold t_08bc_c9 at run
  cases run with
  | dest burn r =>
  cases r with | next a1 r =>
  cases r with | next a2 r =>
  cases r with | next a3 r =>
  cases r with | next a4 r =>
  cases r with | next a5 r =>
  cases r with | next a6 r =>
  have i0 := regInv_of_state burn.state.symm h
  rw [Line.of_inv Devm.getStor (by line_inv) (.cons a1 (.cons a2 (.cons a3 (.cons a4 (.cons a5 (.cons a6 .nil))))))] at i0
  cases r with
  | zero _ _ r => exact (SFunc.RunCutP.false_of_noOk (SFunc.Run.cut r) (by decide)).elim
  | succ _ _ _ pop r =>
  have i1 := regInv_of_state pop.state.symm i0
  unfold t_092b_c9 at r
  cases r with
  | dest burn2 r =>
  cases r with | next b1 r =>
  cases r with | next b2 r =>
  cases r with | next b3 r =>
  have i2 := regInv_of_state burn2.state.symm i1
  rw [Line.of_inv Devm.getStor (by line_inv) (.cons b1 (.cons b2 (.cons b3 .nil)))] at i2
  exact callNext_regInv rfl (fun h' r' => entry30_regInv hfa h' r') silentTail_regInv i2 r

/-- Entry 12 (`setHeartbeatInterval` body: `onlyAdmin`, then `_setHeartbeatInterval`, entry 31). -/
theorem entry12_regInv {sevm : Sevm} {d : Devm} {o : Outcome}
    (hfa : ForeignApart (2 ^ 160) 1)
    (h : RegInv (Devm.getStor d sevm.currentTarget))
    (run : SFunc.Run prog sevm d t_0531_c12 o) :
    RegInv (Devm.getStor (Outcome.devm o) sevm.currentTarget) := by
  unfold t_0531_c12 at run
  cases run with
  | dest burn r =>
  cases r with | next a1 r =>
  cases r with | next a2 r =>
  cases r with | next a3 r =>
  cases r with | next a4 r =>
  cases r with | next a5 r =>
  cases r with | next a6 r =>
  have i0 := regInv_of_state burn.state.symm h
  rw [Line.of_inv Devm.getStor (by line_inv) (.cons a1 (.cons a2 (.cons a3 (.cons a4 (.cons a5 (.cons a6 .nil))))))] at i0
  cases r with
  | zero _ _ r => exact (SFunc.RunCutP.false_of_noOk (SFunc.Run.cut r) (by decide)).elim
  | succ _ _ _ pop r =>
  have i1 := regInv_of_state pop.state.symm i0
  unfold t_05a0_c12 at r
  cases r with
  | dest burn2 r =>
  cases r with | next b1 r =>
  cases r with | next b2 r =>
  cases r with | next b3 r =>
  have i2 := regInv_of_state burn2.state.symm i1
  rw [Line.of_inv Devm.getStor (by line_inv) (.cons b1 (.cons b2 (.cons b3 .nil)))] at i2
  exact callNext_regInv rfl (fun h' r' => entry31_regInv hfa h' r') silentTail_regInv i2 r


/-- **`heartbeat()` wrapper (entry 52).**  With `heartbeatExpiry[msg.sender]`
off the Registry, the whole selector wrapper preserves `RegInv`. -/
theorem heartbeat_wrapper_regInv {sevm : Sevm} {d : Devm} {o : Outcome} {w : SFunc}
    (hw : prog[52]? = some w) (hfa : ForeignApart (2 ^ 160) (mapSlot sevm.caller.toB256 2))
    (h : RegInv (Devm.getStor d sevm.currentTarget))
    (run : SFunc.Run prog sevm d w o) :
    RegInv (Devm.getStor (Outcome.devm o) sevm.currentTarget) := by
  rw [show prog[52]? = some t_01bc_c52 from rfl] at hw
  cases hw
  unfold t_01bc_c52 at run
  cases run with
  | dest burn r =>
  cases r with | next a1 r =>
  cases r with | next a2 r =>
  have i0 := regInv_of_state burn.state.symm h
  rw [Line.of_inv Devm.getStor (by line_inv) (.cons a1 (.cons a2 .nil))] at i0
  exact callNext_regInv rfl (fun h' r' => entry14_regInv hfa h' r') silentTail_regInv i0 r

/-- **`setPauseDuration(uint64)` wrapper (entry 44).**  With slot `0` off the Registry, the wrapper (decoder 8, then the `onlyAdmin` body 9) preserves `RegInv`. -/
theorem setPauseDuration_wrapper_regInv {sevm : Sevm} {d : Devm} {o : Outcome} {w : SFunc}
    (hw : prog[44]? = some w) (hfa : ForeignApart (2 ^ 160) 0)
    (h : RegInv (Devm.getStor d sevm.currentTarget))
    (run : SFunc.Run prog sevm d w o) :
    RegInv (Devm.getStor (Outcome.devm o) sevm.currentTarget) := by
  rw [show prog[44]? = some t_02c2_c44 from rfl] at hw
  cases hw
  unfold t_02c2_c44 at run
  cases run with
  | dest burn r =>
  cases r with | next a1 r =>
  cases r with | next a2 r =>
  cases r with | next a3 r =>
  cases r with | next a4 r =>
  cases r with | next a5 r =>
  have i0 := regInv_of_state burn.state.symm h
  rw [Line.of_inv Devm.getStor (by line_inv)
    (.cons a1 (.cons a2 (.cons a3 (.cons a4 (.cons a5 .nil)))))] at i0
  refine callNext_regInv rfl (silentCallee_regInv (k := 8) (by decide) rfl) ?_ i0 r
  intro d1 o1 h1 r1
  unfold t_02d0_c44 at r1
  cases r1 with
  | dest burn1 r1 =>
  cases r1 with | next b1 r1 =>
  have i1 := regInv_of_state burn1.state.symm h1
  rw [Line.of_inv Devm.getStor (by line_inv) (.cons b1 .nil)] at i1
  exact callNext_regInv rfl (fun h' r' => entry9_regInv hfa h' r') silentTail_regInv i1 r1

/-- **`setHeartbeatInterval(uint64)` wrapper (entry 48).**  With slot `1` off the Registry, the wrapper (decoder 8, then the `onlyAdmin` body 12) preserves `RegInv`. -/
theorem setHeartbeatInterval_wrapper_regInv {sevm : Sevm} {d : Devm} {o : Outcome} {w : SFunc}
    (hw : prog[48]? = some w) (hfa : ForeignApart (2 ^ 160) 1)
    (h : RegInv (Devm.getStor d sevm.currentTarget))
    (run : SFunc.Run prog sevm d w o) :
    RegInv (Devm.getStor (Outcome.devm o) sevm.currentTarget) := by
  rw [show prog[48]? = some t_01f5_c48 from rfl] at hw
  cases hw
  unfold t_01f5_c48 at run
  cases run with
  | dest burn r =>
  cases r with | next a1 r =>
  cases r with | next a2 r =>
  cases r with | next a3 r =>
  cases r with | next a4 r =>
  cases r with | next a5 r =>
  have i0 := regInv_of_state burn.state.symm h
  rw [Line.of_inv Devm.getStor (by line_inv)
    (.cons a1 (.cons a2 (.cons a3 (.cons a4 (.cons a5 .nil)))))] at i0
  refine callNext_regInv rfl (silentCallee_regInv (k := 8) (by decide) rfl) ?_ i0 r
  intro d1 o1 h1 r1
  unfold t_0203_c48 at r1
  cases r1 with
  | dest burn1 r1 =>
  cases r1 with | next b1 r1 =>
  have i1 := regInv_of_state burn1.state.symm h1
  rw [Line.of_inv Devm.getStor (by line_inv) (.cons b1 .nil)] at i1
  exact callNext_regInv rfl (fun h' r' => entry12_regInv hfa h' r') silentTail_regInv i1 r1

end Blanc.Lift.LidoCircuitBreakerDeployed
