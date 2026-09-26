import Blanc.Lift.Curve3Crv.Spec
import Blanc.Lift.InvWalkWorld

/-!
# The dispatcher (entry 0 up to the thirteen bodies)

`CALLDATASIZE < 4` jumps to the fallback (entry 7, `revert(0, 0)`); otherwise the Vyper prologue
(`vyPrologue`) and a linear chain of thirteen tests `mload(0) == sel`, each `EQ ISZERO PUSH2 next
JUMPI`, falling through into its body on a hit; the last miss (`t_08dd_c0`) reverts.

* `safe_dispatch` (safety): a successful run from the frame's start entered body `k` with the
  selector `sels[k]`, from `entrySt`;
* `live_dispatch` (liveness): body `k`'s run from `entrySt` is a run of entry 0, for
  `dispatchGas k` more gas;
* `decodeCall_at`: the call `decodeCall` reads is the one body `k` implements.
-/

namespace Blanc.Lift.Curve3Crv

open Jaune
open Blanc.Curve3Crv (Call)

/-- The first selector test, inline in `t_000d_c0` after the prologue. -/
def test0 : SFunc :=
  .next (.push [0x16, 0x52, 0xe9, 0xfc] (by simp)) (.next (.push [0x00] (by simp))
    (.next (.reg .mload) (.next (.reg .eq) (.next (.reg .iszero)
      (.next (.push [0x00, 0xe2] (by simp)) (.branch t_00b0_c0 t_00e2_c0))))))

theorem t_000d_eq : t_000d_c0 = .dest (vyPrologue test0) := rfl

section Tests

variable {sevm : Sevm} {b : Devm} {o : Outcome} {c0 c1 c2 c3 h l : UInt8} {f nxt : SFunc}

local notation "Mv" => vyMem Mem.empty (Sevm.dataWord sevm 0)

/-- One selector test's tree. -/
def selTest (c0 c1 c2 c3 h l : UInt8) (f nxt : SFunc) : SFunc :=
  .next (.push [c0, c1, c2, c3] (by simp)) (.next (.push [0x00] (by simp))
    (.next (.reg .mload) (.next (.reg .eq) (.next (.reg .iszero)
      (.next (.push [h, l] (by simp)) (.branch f nxt))))))

theorem mload_selector :
    Bytes.toB256 ((Mv).read (Bytes.toB256 [0x00]).toNat 32).1 = Sevm.selector sevm ∧
      ((Mv).read (Bytes.toB256 [0x00]).toNat 32).2 = Mv := by
  have h0 : (Bytes.toB256 [0x00]).toNat = 0 := by decide
  rw [h0, (vyMem_reads Mem.wf_empty Mem.reads_empty _).read, vyImg_selector]
  exact ⟨rfl, read_covered (vyMem_empty_size _) (by decide) (by decide)⟩

private theorem test_rx {v : B256} (hv : B256.eqCheck (B256.eqCheck (Sevm.selector sevm)
      (Bytes.toB256 [c0, c1, c2, c3])) 0 = v) {G : Nat}
    (k : SFunc.RunExact prog sevm (St b [Bytes.toB256 [h, l], v] Mv G) (.branch f nxt) o) :
    SFunc.RunExact prog sevm (St b [] Mv (G + 18)) (selTest c0 c1 c2 c3 h l f nxt) o := by
  obtain ⟨hs, hM⟩ := mload_selector (sevm := sevm)
  unfold selTest
  rw [show G + 18 = G + 3 + 3 + 3 + 3 + 3 + 3 by omega]
  refine rx_push rfl (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_mload (c := 3) ?_ hs hM (by simp) ?_
  · rw [St, Devm.extCost_zero_of_le (by rw [vyMem_empty_size]) (by
      rw [vyMem_empty_size]; decide)]; rfl
  refine rx_eq rfl (by simp) ?_
  refine rx_iszero hv (by simp) ?_
  exact rx_push rfl (by simp) k

/-- A missed test: control passes to the next test. -/
theorem test_miss (hne : Sevm.selector sevm ≠ Bytes.toB256 [c0, c1, c2, c3]) {G : Nat}
    (k : SFunc.RunExact prog sevm (St b [] Mv G) nxt o) :
    SFunc.RunExact prog sevm (St b [] Mv (G + 28)) (selTest c0 c1 c2 c3 h l f nxt) o := by
  rw [show G + 28 = G + 10 + 18 by omega]
  exact test_rx (v := 1) (by simp [B256.eqCheck, hne]) (rx_branch_succ (by decide) k)

/-- A hit: control falls into the body. -/
theorem test_hit (heq : Sevm.selector sevm = Bytes.toB256 [c0, c1, c2, c3]) {G : Nat}
    (k : SFunc.RunExact prog sevm (St b [] Mv G) f o) :
    SFunc.RunExact prog sevm (St b [] Mv (G + 28)) (selTest c0 c1 c2 c3 h l f nxt) o := by
  rw [show G + 28 = G + 10 + 18 by omega]
  exact test_rx (v := 0) (by simp [B256.eqCheck, heq]) (rx_branch_zero k)

/-- The size test and the prologue, forward (100 gas). -/
theorem disp_prefix (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256) {G : Nat}
    (k : SFunc.RunExact prog sevm (St b [] Mv G) test0 o) :
    SFunc.RunExact prog sevm (St b [] Mem.empty (G + 75 + 1 + 24)) t_0000_c0 o := by
  unfold t_0000_c0
  rw [show G + 75 + 1 + 24 = G + 75 + 1 + 10 + 3 + 3 + 3 + 2 + 3 by omega]
  refine rx_push rfl (by simp) ?_
  refine rx_calldatasize (by simp) ?_
  refine rx_lt (v := 0) ?_ (by simp) ?_
  · have h4 : (Bytes.toB256 [0x04]).toNat = 4 := by decide
    simp only [B256.ltCheck, B256.lt_iff_toNat_lt_toNat, h4,
      B256.toNat_toB256_of_lt hcd]
    rw [ite_eq_right_iff]; intro h; omega
  refine rx_iszero (v := 1) (by simp [B256.eqCheck]) (by simp) ?_
  refine rx_push rfl (by simp) ?_
  refine rx_branch_succ (by decide) ?_
  rw [t_000d_eq]
  exact rx_dest (rx_vyPrologue (by simp) k)

/-- A test, inverted. -/
theorem test_inv {C : List Nat} {r : Seg} {G : Nat}
    (run : SFunc.RunCut prog sevm C (St b [] Mv G) (selTest c0 c1 c2 c3 h l f nxt) r) :
    (Sevm.selector sevm = Bytes.toB256 [c0, c1, c2, c3] ∧
      ∃ G', SFunc.RunCut prog sevm C (St b [] Mv G') f r) ∨
    (Sevm.selector sevm ≠ Bytes.toB256 [c0, c1, c2, c3] ∧
      ∃ G', SFunc.RunCut prog sevm C (St b [] Mv G') nxt r) := by
  obtain ⟨hs, hM⟩ := mload_selector (sevm := sevm)
  unfold selTest at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_mload s1
  rw [hs, hM] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_eq s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨hw, G7, run⟩ | ⟨hw, G7, run⟩
  · left
    refine ⟨?_, G7, run⟩
    by_contra hne
    have h10 : (1 : B256) ≠ 0 := by decide
    simp [B256.eqCheck, hne, h10] at hw
  · right
    refine ⟨fun he => ?_, G7, run⟩
    simp [B256.eqCheck, he] at hw

/-- The size test and the prologue, inverted. -/
theorem disp_prefix_inv {r : Seg} {G : Nat} (hcd : sevm.data.length < 2 ^ 256)
    (run : SFunc.RunCut prog sevm [] (St b [] Mem.empty G) t_0000_c0 r) :
    4 ≤ sevm.data.length ∧ ∃ G', SFunc.RunCut prog sevm [] (St b [] Mv G') test0 r := by
  unfold t_0000_c0 at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_calldatasize s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_lt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G6, run⟩ | ⟨hw, G6, run⟩
  · unfold t_0009_c0 at run
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_push s1
    obtain ⟨G8, run⟩ := ric_jump (g := t_08de_c7) (by simp) rfl run
    exact (run.false_of_noOk (by decide)).elim
  rw [t_000d_eq] at run
  obtain ⟨G7, run⟩ := ric_dest run
  obtain ⟨G8, run⟩ := ric_vyPrologue run
  refine ⟨?_, G8, run⟩
  by_contra hlt
  apply hw
  have h4 : (Bytes.toB256 [0x04]).toNat = 4 := by decide
  have hl : sevm.data.length.toB256.toNat = sevm.data.length := B256.toNat_toB256_of_lt hcd
  simp [B256.eqCheck, B256.ltCheck, B256.lt_iff_toNat_lt_toNat, h4, hl]
  intro h
  exact h (by omega)

end Tests

-- SEGMENT: safeDispatch (about 150 nodes: prologue 19, size test 6, 13 tests of 8)
/-- **Dispatcher inversion.**

Proof sketch.  `run.cut`; `t_0000_c0`: `ri_push`, `ri_calldatasize`, `ri_lt`, `ri_iszero`,
`ri_push`, `ric_branch`: the fall-through arm is `t_0009_c0` (`PUSH2 0x08de; JUMP 7`), whose
target entry 7 (`t_08de_c7`) is `noOk`, so `ric_jump` then `false_of_noOk`; the taken arm gives
`4 ≤ sevm.data.length` (`toNat_ge_of_ltCheck_eq_zero`-style: `iszero (lt size 4) ≠ 0`).
`t_000d_c0` is `.dest (vyPrologue _)` by `rfl`: `ric_dest`, `ric_vyPrologue`.  Each test is
`PUSH4 sel PUSH1 0 MLOAD EQ ISZERO PUSH2 next JUMPI`: `ri_mload` at 0 reads the selector
(the prologue image `vyImg [] w` at `0 … 32` is 28 zero bytes and `w`'s first four bytes, so
`Bytes.toB256` of it is `w >>> 224 = Sevm.selector sevm`: a byte lemma to prove once, via
`Bytes.sliceD_writeAt_before`/`inside` and `B256.toBytes`), `read_covered` keeps the memory,
`ri_eq`, `ri_iszero`, `ri_push`, `ric_branch`; the zero arm is the body with `sels[k]` equal to
the selector, the other arm `ric_dest` into the next test.  The final miss `t_08dd_c0` is `noOk`.
Gas is irrelevant: each step's successor is some `St pre S M G'`. -/
theorem safe_dispatch {sevm : Sevm} {b post : Devm} {G : Nat} (hcd : sevm.data.length < 2 ^ 256)
    (run : SFunc.Run prog sevm (St b [] Mem.empty G) t_0000_c0 (.halted post)) :
    ∃ (k : Nat) (f : SFunc) (sel : B256) (G' : Nat), bodies[k]? = some f ∧ sels[k]? = some sel ∧ Sevm.selector sevm = sel ∧
      4 ≤ sevm.data.length ∧ SFunc.Run prog sevm (entrySt sevm b G') f (.halted post) := by
  have run := run.cut
  obtain ⟨hlen, G0, run⟩ := disp_prefix_inv hcd run
  rcases test_inv run with ⟨he, G1, run⟩ | ⟨-, G1, run⟩
  · exact ⟨0, _, _, G1, rfl, rfl, he.trans (by decide), hlen, run.uncut⟩
  obtain ⟨G2, run⟩ := ric_dest run
  rcases test_inv run with ⟨he, G1, run⟩ | ⟨-, G1, run⟩
  · exact ⟨1, _, _, G1, rfl, rfl, he.trans (by decide), hlen, run.uncut⟩
  obtain ⟨G2, run⟩ := ric_dest run
  rcases test_inv run with ⟨he, G1, run⟩ | ⟨-, G1, run⟩
  · exact ⟨2, _, _, G1, rfl, rfl, he.trans (by decide), hlen, run.uncut⟩
  obtain ⟨G2, run⟩ := ric_dest run
  rcases test_inv run with ⟨he, G1, run⟩ | ⟨-, G1, run⟩
  · exact ⟨3, _, _, G1, rfl, rfl, he.trans (by decide), hlen, run.uncut⟩
  obtain ⟨G2, run⟩ := ric_dest run
  rcases test_inv run with ⟨he, G1, run⟩ | ⟨-, G1, run⟩
  · exact ⟨4, _, _, G1, rfl, rfl, he.trans (by decide), hlen, run.uncut⟩
  obtain ⟨G2, run⟩ := ric_dest run
  rcases test_inv run with ⟨he, G1, run⟩ | ⟨-, G1, run⟩
  · exact ⟨5, _, _, G1, rfl, rfl, he.trans (by decide), hlen, run.uncut⟩
  obtain ⟨G2, run⟩ := ric_dest run
  rcases test_inv run with ⟨he, G1, run⟩ | ⟨-, G1, run⟩
  · exact ⟨6, _, _, G1, rfl, rfl, he.trans (by decide), hlen, run.uncut⟩
  obtain ⟨G2, run⟩ := ric_dest run
  rcases test_inv run with ⟨he, G1, run⟩ | ⟨-, G1, run⟩
  · exact ⟨7, _, _, G1, rfl, rfl, he.trans (by decide), hlen, run.uncut⟩
  obtain ⟨G2, run⟩ := ric_dest run
  rcases test_inv run with ⟨he, G1, run⟩ | ⟨-, G1, run⟩
  · exact ⟨8, _, _, G1, rfl, rfl, he.trans (by decide), hlen, run.uncut⟩
  obtain ⟨G2, run⟩ := ric_dest run
  rcases test_inv run with ⟨he, G1, run⟩ | ⟨-, G1, run⟩
  · exact ⟨9, _, _, G1, rfl, rfl, he.trans (by decide), hlen, run.uncut⟩
  obtain ⟨G2, run⟩ := ric_dest run
  rcases test_inv run with ⟨he, G1, run⟩ | ⟨-, G1, run⟩
  · exact ⟨10, _, _, G1, rfl, rfl, he.trans (by decide), hlen, run.uncut⟩
  obtain ⟨G2, run⟩ := ric_dest run
  rcases test_inv run with ⟨he, G1, run⟩ | ⟨-, G1, run⟩
  · exact ⟨11, _, _, G1, rfl, rfl, he.trans (by decide), hlen, run.uncut⟩
  obtain ⟨G2, run⟩ := ric_dest run
  rcases test_inv run with ⟨he, G1, run⟩ | ⟨-, G1, run⟩
  · exact ⟨12, _, _, G1, rfl, rfl, he.trans (by decide), hlen, run.uncut⟩
  exact (run.false_of_noOk (by decide)).elim

-- SEGMENT: liveDispatch (about 150 nodes, as `safeDispatch`)
/-- **Dispatcher, forward.**  `dispatchGas k = 128 + 29 k`: the size test 24, `JUMPDEST` 1,
the prologue 75, and per test 28 (`PUSH4` 3, `PUSH1` 3, `MLOAD` 3, `EQ` 3, `ISZERO` 3, `PUSH2` 3,
`JUMPI` 10) plus 1 for each missed test's `JUMPDEST`.

Proof sketch.  `rx_push`, `rx_calldatasize`, `rx_lt (v := 0)` (`4 ≤ size`), `rx_iszero (v := 1)`,
`rx_push`, `rx_branch_succ`, `rx_dest`, `rx_vyPrologue`; then induction-free: a `match` on `k`
(13 cases), each `k` misses `k` tests (`rx_mload` of the selector as in `safeDispatch`, `rx_eq
(v := 0)` from the selectors' distinctness, `decide`; `rx_iszero (v := 1)`, `rx_branch_succ`,
`rx_dest`) and hits the `k`-th (`rx_eq (v := 1)`, `rx_iszero (v := 0)`, `rx_branch_zero`).
A helper for one missed test and one for the hit, over `vyMem Mem.empty w`, keeps each case to a
few lines. -/
theorem live_dispatch {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome} {k : Nat} {f : SFunc}
    {sel : B256} (hk : bodies[k]? = some f) (hs : sels[k]? = some sel)
    (hsel : Sevm.selector sevm = sel) (hlen : 4 ≤ sevm.data.length)
    (hcd : sevm.data.length < 2 ^ 256)
    (hrun : SFunc.RunExact prog sevm (entrySt sevm b G) f o) :
    SFunc.RunExact prog sevm (St b [] Mem.empty (G + dispatchGas k)) t_0000_c0 o := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  all_goals simp only [bodies, sels, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.some.injEq, List.getElem?_nil, reduceCtorEq] at hk hs
  all_goals try (subst hk; subst hs)
  · rw [show G + dispatchGas 0 = G + 28 + 75 + 1 + 24 by unfold dispatchGas; omega]
    refine disp_prefix hlen hcd ?_
    refine test_hit ?_ hrun
    rw [hsel]; decide
  · rw [show G + dispatchGas 1 = G + 28 + 1 + 28 + 75 + 1 + 24 by unfold dispatchGas; omega]
    refine disp_prefix hlen hcd ?_
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_hit ?_ hrun
    rw [hsel]; decide
  · rw [show G + dispatchGas 2 = G + 28 + 1 + 28 + 1 + 28 + 75 + 1 + 24 by unfold dispatchGas; omega]
    refine disp_prefix hlen hcd ?_
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_hit ?_ hrun
    rw [hsel]; decide
  · rw [show G + dispatchGas 3 = G + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 75 + 1 + 24 by unfold dispatchGas; omega]
    refine disp_prefix hlen hcd ?_
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_hit ?_ hrun
    rw [hsel]; decide
  · rw [show G + dispatchGas 4 = G + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 75 + 1 + 24 by unfold dispatchGas; omega]
    refine disp_prefix hlen hcd ?_
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_hit ?_ hrun
    rw [hsel]; decide
  · rw [show G + dispatchGas 5 = G + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 75 + 1 + 24 by unfold dispatchGas; omega]
    refine disp_prefix hlen hcd ?_
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_hit ?_ hrun
    rw [hsel]; decide
  · rw [show G + dispatchGas 6 = G + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 75 + 1 + 24 by unfold dispatchGas; omega]
    refine disp_prefix hlen hcd ?_
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_hit ?_ hrun
    rw [hsel]; decide
  · rw [show G + dispatchGas 7 = G + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 75 + 1 + 24 by unfold dispatchGas; omega]
    refine disp_prefix hlen hcd ?_
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_hit ?_ hrun
    rw [hsel]; decide
  · rw [show G + dispatchGas 8 = G + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 75 + 1 + 24 by unfold dispatchGas; omega]
    refine disp_prefix hlen hcd ?_
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_hit ?_ hrun
    rw [hsel]; decide
  · rw [show G + dispatchGas 9 = G + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 75 + 1 + 24 by unfold dispatchGas; omega]
    refine disp_prefix hlen hcd ?_
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_hit ?_ hrun
    rw [hsel]; decide
  · rw [show G + dispatchGas 10 = G + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 75 + 1 + 24 by unfold dispatchGas; omega]
    refine disp_prefix hlen hcd ?_
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_hit ?_ hrun
    rw [hsel]; decide
  · rw [show G + dispatchGas 11 = G + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 75 + 1 + 24 by unfold dispatchGas; omega]
    refine disp_prefix hlen hcd ?_
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_hit ?_ hrun
    rw [hsel]; decide
  · rw [show G + dispatchGas 12 = G + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 1 + 28 + 75 + 1 + 24 by unfold dispatchGas; omega]
    refine disp_prefix hlen hcd ?_
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_miss ?_ (rx_dest ?_)
    · rw [hsel]; decide
    refine test_hit ?_ hrun
    rw [hsel]; decide

/-- The call the model receives in the frame of body `k`. -/
def callAt (sevm : Sevm) : Nat → Call
  | 0 => .setMinter (Sevm.argWord sevm 0)
  | 1 => .setName (strArg sevm 0) (strArg sevm 1)
  | 2 => .totalSupply
  | 3 => .allowance (Sevm.argWord sevm 0) (Sevm.argWord sevm 1)
  | 4 => .transfer (Sevm.argWord sevm 0) (Sevm.argWord sevm 1)
  | 5 => .transferFrom (Sevm.argWord sevm 0) (Sevm.argWord sevm 1) (Sevm.argWord sevm 2)
  | 6 => .approve (Sevm.argWord sevm 0) (Sevm.argWord sevm 1)
  | 7 => .mint (Sevm.argWord sevm 0) (Sevm.argWord sevm 1)
  | 8 => .burnFrom (Sevm.argWord sevm 0) (Sevm.argWord sevm 1)
  | 9 => .name
  | 10 => .symbol
  | 11 => .decimals
  | 12 => .balanceOf (Sevm.argWord sevm 0)
  | _ => .other

/-- The selector of body `k` makes `decodeCall` read body `k`'s call. -/
theorem decodeCall_at {sevm : Sevm} {k : Nat} {sel : B256} (hs : sels[k]? = some sel)
    (hsel : Sevm.selector sevm = sel) (hlen : 4 ≤ sevm.data.length) :
    decodeCall sevm = callAt sevm k := by
  have hlen' : ¬ sevm.data.length < 4 := by omega
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  all_goals simp only [sels, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.some.injEq, List.getElem?_nil, reduceCtorEq] at hs
  all_goals
    subst hs
    simp (config := { decide := true }) only [decodeCall, hlen', hsel, callAt, selSetMinter,
      selSetName, selTotalSupply, selAllowance, selTransfer, selTransferFrom, selApprove, selMint,
      selBurnFrom, selName, selSymbol, selDecimals, selBalanceOf, ite_true, ite_false]

end Blanc.Lift.Curve3Crv
