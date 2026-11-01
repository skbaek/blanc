import Blanc.Lift.Curve3Crv.Spec
import Blanc.Lift.InvWalkWorld
import Blanc.Lift.VyperDispatchExact

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
  .next (.push [0x16, 0x52, 0xe9, 0xfc] (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLeDiff])) (.next (.push [0x00] (by simp only [List.length_cons,
    List.length_nil, zero_add, Nat.one_le_ofNat]))
    (.next (.reg .mload) (.next (.reg .eq) (.next (.reg .iszero)
      (.next (.push [0x00, 0xe2] (by simp only [List.length_cons, List.length_nil, zero_add,
        Nat.reduceAdd, Nat.reduceLeDiff])) (.branch t_00b0_c0 t_00e2_c0))))))

theorem t_000d_eq : t_000d_c0 = .dest (vyPrologue test0) := rfl

section Tests

variable {sevm : Sevm} {b : Devm} {o : Outcome} {c0 c1 c2 c3 h l : UInt8} {f nxt : SFunc}

local notation "Mv" => vyMem Mem.empty (Sevm.dataWord sevm 0)

/-- One selector test's tree. -/
def selTest (c0 c1 c2 c3 h l : UInt8) (f nxt : SFunc) : SFunc :=
  .next (.push [c0, c1, c2, c3] (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLeDiff])) (.next (.push [0x00] (by simp only [List.length_cons,
    List.length_nil, zero_add, Nat.one_le_ofNat]))
    (.next (.reg .mload) (.next (.reg .eq) (.next (.reg .iszero)
      (.next (.push [h, l] (by simp only [List.length_cons, List.length_nil, zero_add,
        Nat.reduceAdd, Nat.reduceLeDiff])) (.branch f nxt))))))

/-- The size test and the prologue, forward (100 gas). -/
theorem disp_prefix (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256) {G : Nat}
    (k : SFunc.RunExact prog sevm (St b [] Mv G) test0 o) :
    SFunc.RunExact prog sevm (St b [] Mem.empty (G + 75 + 1 + 24)) t_0000_c0 o := by
  unfold t_0000_c0
  rw [show G + 75 + 1 + 24 = G + 75 + 1 + 10 + 3 + 3 + 3 + 2 + 3 by omega]
  refine rx_push rfl (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
  refine rx_calldatasize (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.one_lt_ofNat]) ?_
  refine rx_lt (v := 0) ?_ (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
  · have h4 : (Bytes.toB256 [0x04]).toNat = 4 := by decide
    simp only [B256.ltCheck, B256.lt_iff_toNat_lt_toNat, h4,
      B256.toNat_toB256_of_lt hcd]
    rw [ite_eq_right_iff]; intro h; omega
  refine rx_iszero (v := 1) (by simp only [B256.eqCheck, ↓reduceIte]) (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
  refine rx_branch_succ (by decide) ?_
  rw [t_000d_eq]
  exact rx_dest (rx_vyPrologue (by simp only [List.length_nil, zero_add, Nat.reduceLT]) k)

/-- A test, inverted. -/
theorem test_inv {C : List Nat} {r : Seg} {G : Nat}
    (run : SFunc.RunCut prog sevm C (St b [] Mv G) (selTest c0 c1 c2 c3 h l f nxt) r) :
    (Sevm.selector sevm = Bytes.toB256 [c0, c1, c2, c3] ∧
      ∃ G', SFunc.RunCut prog sevm C (St b [] Mv G') f r) ∨
    (Sevm.selector sevm ≠ Bytes.toB256 [c0, c1, c2, c3] ∧
      ∃ G', SFunc.RunCut prog sevm C (St b [] Mv G') nxt r) := by
  obtain ⟨hs, hM⟩ := vyMem_mload_selector (sevm := sevm)
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
    simp only [B256.eqCheck, hne, ↓reduceIte, h10] at hw
  · right
    refine ⟨fun he => ?_, G7, run⟩
    simp only [B256.eqCheck, he, ↓reduceIte, ne_eq, ite_eq_right_iff, imp_self,
      not_true_eq_false] at hw

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
    obtain ⟨G8, run⟩ := ric_jump (g := t_08de_c7) (by simp only [List.not_mem_nil,
      not_false_eq_true]) rfl run
    exact (run.false_of_noOk (by decide)).elim
  rw [t_000d_eq] at run
  obtain ⟨G7, run⟩ := ric_dest run
  obtain ⟨G8, run⟩ := ric_vyPrologue run
  refine ⟨?_, G8, run⟩
  by_contra hlt
  apply hw
  have h4 : (Bytes.toB256 [0x04]).toNat = 4 := by decide
  have hl : sevm.data.length.toB256.toNat = sevm.data.length := B256.toNat_toB256_of_lt hcd
  simp only [B256.eqCheck, B256.ltCheck, B256.lt_iff_toNat_lt_toNat, hl, h4, ite_eq_right_iff]
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

The chain after the prologue is evaluated by `SFunc.vyFwd` (`Blanc/Lift/VyperDispatchExact.lean`):
for each of the thirteen bodies the kernel checks that it reaches body `k` for `28 + 29 k` gas. -/
theorem live_dispatch {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome} {k : Nat} {f : SFunc}
    {sel : B256} (hk : bodies[k]? = some f) (hs : sels[k]? = some sel)
    (hsel : Sevm.selector sevm = sel) (hlen : 4 ≤ sevm.data.length)
    (hcd : sevm.data.length < 2 ^ 256)
    (hrun : SFunc.RunExact prog sevm (entrySt sevm b G) f o) :
    SFunc.RunExact prog sevm (St b [] Mem.empty (G + dispatchGas k)) t_0000_c0 o := by
  have hfwd : SFunc.vyFwd sel 32 test0 = (f, dispatchGas k - 100) := by
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
    all_goals simp only [bodies, sels, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq, List.getElem?_nil, reduceCtorEq] at hk hs
    all_goals try (subst hk; subst hs)
    all_goals kernel_rfl
  rw [show G + dispatchGas k = G + (dispatchGas k - 100) + 75 + 1 + 24 by unfold dispatchGas; omega]
  refine disp_prefix hlen hcd ?_
  have h := rx_vyFwd (S := []) hsel (by decide) 32 test0 (G := G) (by rw [hfwd]; exact hrun)
  rwa [hfwd] at h

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
