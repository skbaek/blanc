import Blanc.Lift.LidoCircuitBreakerDeployed.Prog
import Blanc.Lift.WalkSteps
import Blanc.LidoCircuitBreakerCore
import Blanc.Lift.Weth9.Words
import Blanc.Lift.Vyper
import Blanc.Lift.MapSlot

/-! Inversion of the deployed CircuitBreaker's checked-arithmetic helper
entries on a successful run: entry 40 (checked decrement), entry 24 (checked
increment), entry 25 (checked subtraction).  Each helper's overflow arm
reaches a `Panic(0x11)` revert block, so a returned run excludes it.  Also
entry 5, `setPauser`'s shared tail: the `PauserSet` `LOG4` and the return. -/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune
open Blanc.LidoCircuitBreaker

/-- The all-ones word the checked helpers push. -/
abbrev ffWord : B256 := Bytes.toB256
  [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
   0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
   0xff, 0xff]

section

variable {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}

/-- The Solidity mapping-slot scratch idiom: two word stores at 0 and 32 of a
well-formed, word-aligned image, hashed over `[0, 64)`, give `mapSlot key base`
without extending memory, and keep the image well-formed and aligned. -/
theorem scratch_mapSlot {M : Mem} (hmem : Mem.Wf M) (halign : M.size % 32 = 0)
    (key base : B256) :
    ((((M.write 0 key.toBytes).write 32 base.toBytes).read 0 64).1).keccak =
        mapSlot key base ∧
      (((M.write 0 key.toBytes).write 32 base.toBytes).read 0 64).2 =
        (M.write 0 key.toBytes).write 32 base.toBytes ∧
      Mem.Wf ((M.write 0 key.toBytes).write 32 base.toBytes) ∧
      ((M.write 0 key.toBytes).write 32 base.toBytes).size % 32 = 0 := by
  have hsize1 : (M.write 0 key.toBytes).size % 32 = 0 := by
    rw [Mem.size_write_word_at]
    split_ifs
    · exact halign
    · decide
  have hsize2 : ((M.write 0 key.toBytes).write 32 base.toBytes).size % 32 = 0 := by
    rw [Mem.size_write_word_at]
    split_ifs
    · exact hsize1
    · decide
  have hsize64 : 64 ≤ ((M.write 0 key.toBytes).write 32 base.toBytes).size := by
    rw [Mem.size_write_word_at]
    split_ifs with h
    · exact h
    · decide
  refine ⟨?_, Mem.read_snd_eq_self (memExtSize_of_le hsize2 (by omega)),
    (hmem.write 0 _).write 32 _, hsize2⟩
  rw [Mem.read_two_word_writes_at hmem (Mem.reads_data M) 0 key base]
  rfl

/-- A one-word scratch store at 0 of a well-formed, word-aligned image,
hashed over `[0, 32)`: the dynamic-array base idiom. -/
theorem scratch_word {M : Mem} (hmem : Mem.Wf M) (halign : M.size % 32 = 0) (v : B256) :
    ((M.write 0 v.toBytes).read 0 32).1.keccak = v.toBytes.keccak ∧
      ((M.write 0 v.toBytes).read 0 32).2 = M.write 0 v.toBytes ∧
      Mem.Wf (M.write 0 v.toBytes) ∧ (M.write 0 v.toBytes).size % 32 = 0 := by
  have hsize1 : (M.write 0 v.toBytes).size % 32 = 0 := by
    rw [Mem.size_write_word_at]
    split_ifs
    · exact halign
    · decide
  have hsize32 : 32 ≤ (M.write 0 v.toBytes).size := by
    rw [Mem.size_write_word_at]
    split_ifs with h
    · exact h
    · decide
  refine ⟨?_, Mem.read_snd_eq_self (memExtSize_of_le hsize1 (by omega)),
    hmem.write 0 _, hsize1⟩
  rw [Mem.read_write_word_of_wf hmem 0 v]

/-- `b'` agrees with `b` except in the contract's own storage, which is `s`
(access sets may differ): every other account's storage and the log list are
unchanged. -/
structure StorStep (sevm : Sevm) (b b' : Devm) (s : Stor) : Prop where
  self : Devm.getStor b' sevm.currentTarget = s
  other : ∀ a, a ≠ sevm.currentTarget → Devm.getStor b' a = Devm.getStor b a
  logs : b'.logs = b.logs

theorem getStorVal_eq_getStor (d : Devm) (a : Adr) (k : B256) :
    d.getStorVal a k = (Devm.getStor d a).get k := rfl

/-- Any chain of selected loads and stores is a `StorStep` from its base, with
the contract storage read off the chain. -/
theorem StorStep.of_getStor {sevm : Sevm} {b b' : Devm}
    (other : ∀ a, a ≠ sevm.currentTarget → Devm.getStor b' a = Devm.getStor b a)
    (logs : b'.logs = b.logs) :
    StorStep sevm b b' (Devm.getStor b' sevm.currentTarget) :=
  ⟨rfl, other, logs⟩

theorem StorStep.refl (sevm : Sevm) (b : Devm) :
    StorStep sevm b b (Devm.getStor b sevm.currentTarget) :=
  ⟨rfl, fun _ _ => rfl, rfl⟩

theorem StorStep.getStorVal {sevm : Sevm} {b b' : Devm} {s : Stor} (h : StorStep sevm b b' s)
    (k : B256) : b'.getStorVal sevm.currentTarget k = s.get k := by
  show (Devm.getStor b' sevm.currentTarget).get k = _
  rw [h.self]

theorem StorStep.sload {sevm : Sevm} {b b' : Devm} {s : Stor} (h : StorStep sevm b b' s)
    (k : B256) : StorStep sevm b (afterSload sevm b' k) s :=
  ⟨by rw [afterSload_getStor, h.self],
   fun a ha => by rw [afterSload_getStor, h.other a ha],
   by rw [afterSload_logs, h.logs]⟩

theorem StorStep.sstore {sevm : Sevm} {b b' : Devm} {s : Stor} (h : StorStep sevm b b' s)
    (k v : B256) : StorStep sevm b (afterSstore sevm b' k v) (s.set k v) :=
  ⟨by rw [afterSstore_getStor_self, h.self],
   fun a ha => by rw [afterSstore_getStor_ne _ _ _ _ _ (Ne.symm ha), h.other a ha],
   by rw [afterSstore_logs, h.logs]⟩

theorem StorStep.congr {sevm : Sevm} {b b' : Devm} {s s' : Stor} (h : StorStep sevm b b' s)
    (e : s = s') : StorStep sevm b b' s' :=
  e ▸ h

theorem StorStep.trans {sevm : Sevm} {b b' b'' : Devm} {s s' : Stor}
    (h : StorStep sevm b b' s) (h' : StorStep sevm b' b'' s') : StorStep sevm b b'' s' :=
  ⟨h'.self, fun a ha => by rw [h'.other a ha, h.other a ha], by rw [h'.logs, h.logs]⟩

theorem B256.or_comm' (x y : B256) : x ||| y = y ||| x := by
  rcases x with ⟨⟨xh0, xh1⟩, ⟨xl0, xl1⟩⟩
  rcases y with ⟨⟨yh0, yh1⟩, ⟨yl0, yl1⟩⟩
  apply Prod.ext <;> apply Prod.ext <;> exact UInt64.or_comm _ _

theorem B256.or_zero' (x : B256) : x ||| 0 = x := by
  rcases x with ⟨⟨xh0, xh1⟩, ⟨xl0, xl1⟩⟩
  apply Prod.ext <;> apply Prod.ext <;> exact UInt64.or_zero

/-- Solidity's `Panic(code)` revert block: selector and code stores, then
`REVERT`.  It never completes successfully. -/
theorem panicBlock_not_run {C : List Nat} {S : List B256} {r : Seg}
    {p1 p2 p3 p4 p5 p6 : Bytes} {h1 : p1.length ≤ 32} {h2 : p2.length ≤ 32}
    {h3 : p3.length ≤ 32} {h4 : p4.length ≤ 32} {h5 : p5.length ≤ 32} {h6 : p6.length ≤ 32}
    (run : SFunc.RunCut prog sevm C (St b S M G)
      (.dest (.next (.push p1 h1) (.next (.push p2 h2) (.next (.reg .mstore)
        (.next (.push p3 h3) (.next (.push p4 h4) (.next (.reg .mstore)
          (.next (.push p5 h5) (.next (.push p6 h6) (.last .revert)))))))))) r) :
    False := by
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G5, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G6, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G7, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G8, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G9, rfl⟩ := ri_push s1
  exact ric_revert run

/-- The arithmetic `Panic(0x11)` blocks (entries 38, 39, 42). -/
theorem panic42_not_run {C : List Nat} {S : List B256} {r : Seg}
    (run : SFunc.RunCut prog sevm C (St b S M G) t_107b_c42 r) : False :=
  panicBlock_not_run run

theorem panic39_not_run {C : List Nat} {S : List B256} {r : Seg}
    (run : SFunc.RunCut prog sevm C (St b S M G) t_107b_c39 r) : False :=
  panicBlock_not_run run

theorem panic38_not_run {C : List Nat} {S : List B256} {r : Seg}
    (run : SFunc.RunCut prog sevm C (St b S M G) t_107b_c38 r) : False :=
  panicBlock_not_run run

/-- The array-bounds `Panic(0x32)` blocks (entries 26, 27). -/
theorem panic26_not_run {C : List Nat} {S : List B256} {r : Seg}
    (run : SFunc.RunCut prog sevm C (St b S M G) t_1158_c26 r) : False :=
  panicBlock_not_run run

theorem panic27_not_run {C : List Nat} {S : List B256} {r : Seg}
    (run : SFunc.RunCut prog sevm C (St b S M G) t_1158_c27 r) : False :=
  panicBlock_not_run run

/-- The empty-array-pop `Panic(0x31)` block (entry 28). -/
theorem panic28_not_run {C : List Nat} {S : List B256} {r : Seg}
    (run : SFunc.RunCut prog sevm C (St b S M G) t_1185_c28 r) : False :=
  panicBlock_not_run run

/-- Entry 40, the checked decrement: a returned run had a nonzero operand and
returns `ff..ff + x` (that is, `x - 1`) over the caller's remaining stack. -/
theorem entry40_returned_inv {x r : B256} {R : List B256} {D : Devm}
    (run : SFunc.Run prog sevm (St b (x :: r :: R) M G) t_10da_c40 (.returned D)) :
    x ≠ 0 ∧ ∃ G', D = St b ((ffWord + x) :: R) M G' := by
  have run := run.cut
  unfold t_10da_c40 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_dup (w := x) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨_, G5, run⟩ | ⟨hnz, G5, run⟩
  · unfold t_10e1_c40 at run
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G6, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G7, rfl⟩ := ri_push s1
    obtain ⟨G8, run⟩ := ric_jump (List.not_mem_nil) entry42_lookup run
    exact (panic42_not_run run).elim
  · refine ⟨hnz, ?_⟩
    unfold t_10e8_c40 at run
    obtain ⟨G6, run⟩ := ric_dest run
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G7, rfl⟩ := ri_pop s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G8, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G9, rfl⟩ := ri_add s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G10, rfl⟩ := ri_swap (n := 0) rfl s1
    obtain ⟨G11, hr⟩ := ric_ret run
    cases hr
    exact ⟨G11, rfl⟩

/-- Entry 24, the checked increment: a returned run had an operand other than
`ff..ff` and returns `1 + x` over the caller's remaining stack. -/
theorem entry24_returned_inv {x r : B256} {R : List B256} {D : Devm}
    (run : SFunc.Run prog sevm (St b (x :: r :: R) M G) t_110e_c24 (.returned D)) :
    x - ffWord ≠ 0 ∧ ∃ G', D = St b ((1 + x) :: R) M G' := by
  have run := run.cut
  unfold t_110e_c24 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_dup (w := x) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G5, rfl⟩ := ri_sub s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G6, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨_, G7, run⟩ | ⟨hnz, G7, run⟩
  · unfold t_1137_c24 at run
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G8, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G9, rfl⟩ := ri_push s1
    obtain ⟨G10, run⟩ := ric_jump (List.not_mem_nil) entry39_lookup run
    exact (panic39_not_run run).elim
  · refine ⟨hnz, ?_⟩
    unfold t_113e_c24 at run
    obtain ⟨G8, run⟩ := ric_dest run
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G9, rfl⟩ := ri_pop s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G10, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G11, rfl⟩ := ri_add s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G12, rfl⟩ := ri_swap (n := 0) rfl s1
    obtain ⟨G13, hr⟩ := ric_ret run
    cases hr
    exact ⟨G13, rfl⟩

/-- Entry 25, the checked subtraction `x - y`: a returned run had no
underflow (`x - y` not above `x`) and returns `x - y` over the caller's
remaining stack, through entry 3's return shuffle. -/
theorem entry25_returned_inv {x y r : B256} {R : List B256} {D : Devm}
    (run : SFunc.Run prog sevm (St b (x :: y :: r :: R) M G) t_1145_c25 (.returned D)) :
    B256.eqCheck (B256.gtCheck (x - y) x) 0 ≠ 0 ∧ ∃ G', D = St b ((x - y) :: R) M G' := by
  have run := run.cut
  unfold t_1145_c25 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_dup (w := y) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_dup (w := x) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_sub s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G5, rfl⟩ := ri_dup (w := x) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G6, rfl⟩ := ri_dup (w := x - y) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G7, rfl⟩ := ri_gt s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G8, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G9, rfl⟩ := ri_push s1
  rcases ric_branchTo (List.not_mem_nil) entry3_lookup run with
    ⟨_, G10, run⟩ | ⟨hnz, G10, run⟩
  · unfold t_1151_c25 at run
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G11, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G12, rfl⟩ := ri_push s1
    obtain ⟨G13, run⟩ := ric_jump (List.not_mem_nil) entry38_lookup run
    exact (panic38_not_run run).elim
  · refine ⟨hnz, ?_⟩
    unfold t_051a_c3 at run
    obtain ⟨G11, run⟩ := ric_dest run
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G12, rfl⟩ := ri_swap (n := 2) rfl s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G13, rfl⟩ := ri_swap (n := 1) rfl s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G14, rfl⟩ := ri_pop s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G15, rfl⟩ := ri_pop s1
    obtain ⟨G16, hr⟩ := ric_ret run
    cases hr
    exact ⟨G16, rfl⟩

/-- The `PauserSet(target, previousPauser, newPauser)` event topic entry 5 pushes. -/
abbrev pauserSetTopic : B256 := Bytes.toB256
  [0xd9, 0x2c, 0x3c, 0x28, 0xed, 0x17, 0x46, 0x32, 0x68, 0xf8, 0x64, 0x77, 0x64, 0x63, 0xc4,
   0xc2, 0x15, 0x4f, 0x89, 0xb1, 0x81, 0x56, 0xd3, 0xed, 0xf7, 0x7c, 0x0e, 0x37, 0xd0, 0x47,
   0x69, 0x13]

theorem ff20_and_canonical {w : B256} (h : canonicalAddress w) :
    Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& w = w := by
  rw [Weth9.ff20_and_word, B256.toAdr_toB256_of_lt h]

theorem mask_and_canonical {w : B256} (h : canonicalAddress w) :
    w &&& Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] = w := by
  rw [B256.and_comm, Weth9.ff20_and_word, B256.toAdr_toB256_of_lt h]

/-- Entry 5, `setPauser`'s shared tail: from `oldPauser :: newPauser :: target
:: k :: ret :: base` it emits the `PauserSet` log with the three canonical
addresses as topics (over whatever memory window the free pointer names) and
returns to `base`, leaving storage untouched. -/
theorem entry5_inv {C : List Nat} {oldP newP target k ret : B256} {base : List B256}
    {post : Devm}
    (hold : canonicalAddress oldP) (hnew : canonicalAddress newP)
    (htarget : canonicalAddress target)
    (run : SFunc.RunCut prog sevm C (St b (oldP :: newP :: target :: k :: ret :: base) M G)
      t_0c5e_c5 (.done (.returned post))) :
    ∃ data M' G', post = St
      (b.addLog ⟨sevm.currentTarget, [pauserSetTopic, target, oldP, newP], data⟩) base M' G' := by
  unfold t_0c5e_c5 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_dup (w := newP) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_and s1
  rw [ff20_and_canonical hnew] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G5, rfl⟩ := ri_dup (w := oldP) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G6, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G7, rfl⟩ := ri_and s1
  rw [ff20_and_canonical hold] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G8, rfl⟩ := ri_dup (w := target) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G9, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G10, rfl⟩ := ri_and s1
  rw [ff20_and_canonical htarget] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G11, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G12, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G13, rfl⟩ := ri_mload s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G14, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G15, rfl⟩ := ri_mload s1
  generalize (Bytes.toB256 [0x40] : B256) = p at run
  generalize hM1 : (M.read p.toNat 32) = r1 at run
  generalize hM2 : (r1.2.read p.toNat 32) = r2 at run
  generalize Bytes.toB256 r1.1 = f1 at run
  generalize Bytes.toB256 r2.1 = f2 at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G16, rfl⟩ := ri_dup (w := f2) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G17, rfl⟩ := ri_swap (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G18, rfl⟩ := ri_sub s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G19, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G20, rfl⟩ := ri_log4 s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G21, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G22, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G23, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G24, rfl⟩ := ri_pop s1
  obtain ⟨G25, hr⟩ := ric_ret run
  cases hr
  exact ⟨_, _, G25, rfl⟩

end

end Blanc.Lift.LidoCircuitBreakerDeployed
