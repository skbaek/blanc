import Blanc.Lift.UniswapV2Pair.PairCallSitesCheck
import Blanc.Lift.UniswapV2Pair.PairCallSiteShape
import Blanc.Lift.UniswapV2Pair.Check

/-!
# Every CALL of a Pair frame is at one of its three sites

`pair_call_site`: a node of a Pair frame's chain that decodes `CALL` sits at the swap callback's
CALL (`t_09aa_c4`) or at `_safeTransfer`'s CALL (`t_20e1_c57`, `t_20e1_c71`), by the kernel-checked
`cert_callSites` kept along the stateful reach of `reach_of_parentPrefix`.

`CallbackSiteShape` is the callback site's analogue of `TransferSiteShape`: at the callback's CALL
the input window carries the `uniswapV2Call` selector `0x10d1e85c`.  It is this lane's open
obligation (see its docstring for what blocks it).
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- LANE-OPEN OBLIGATION (second host): discharged by a backward walk over the straight block
`t_08e8_c4` → `t_09aa_c4` together with a reachable-state free-pointer fact at its entry.  At the
callback's CALL, the input window carries the `uniswapV2Call` selector.  The block reads the free
pointer `p = mload(0x40)`, writes `uniswapV2Call`'s selector word at `p`, the head words at
`p + 4 … p + 0x84`, copies `data.length` calldata bytes to `p + 0xa4`, zeroes the word after them,
and CALLs with input offset `mload(0x40)` read again.  The selector survives exactly when no write
reaches `[0x40, 0x60)` or `[p, p + 4)`: this needs `0x5c ≤ p` and no wrap of `p + 0xa4 + len`
modulo `2 ^ 256`, which no local argument gives (a pointer below `0x5c`, or a wrapped one, lets the
attacker-chosen amounts overwrite the pointer); the bound `ChainMemoryBelow R (2 ^ 160)` rules out
the wrap but not a low pointer.  `swapCallbackCall_inv` has these facts as premises
(`PtrMem q`, `128 ≤ q < 2 ^ 162`, `len ≤ 2 ^ 32`), supplied by the forward swap walk on a synthetic
run; the open step is carrying them to the actual node (a reach-to-run determinism link, or a global
free-pointer invariant over the certificate). -/
def CallbackSiteShape : Prop :=
  ∀ {R N : Exec.Deriv} {κ : Cursor} {g : SFunc} {post : Devm},
    R.pc = 0 → R.sevm.code = code → CoveredFork R.sevm.benvStat.fork →
    R.devm.stack = [] → R.devm.memory = Mem.empty → ChainMemoryBelow R (2 ^ 160) → R.exn = .ok post →
    Exec.Deriv.ParentPrefix R N →
    Reach (StepIn R) cert.prog R.sevm ((Cursor.start cert).conf R.devm) (κ.conf N.devm) →
    CursorOK code cert N κ →
    κ.f = .next (.exec .call) g →
    SFunc.LineSuffix κ.f t_09aa_c4 →
    CallInputSelector N 0x10d1e85c

/-- **The Pair's CALL sites.**  A node of a Pair frame's chain that decodes `CALL` sits at a cursor,
reached from entry `0`, whose tree is the CALL node of the swap callback or of one of
`_safeTransfer`'s two clones. -/
theorem pair_call_site {R N : Exec.Deriv} (pcZero : R.pc = 0) (codeEq : R.sevm.code = code)
    (fork : CoveredFork R.sevm.benvStat.fork) (chain : Exec.Deriv.ParentPrefix R N)
    (hat : Ninst.At N.sevm.code N.pc (.exec .call)) :
    ∃ (κ : Cursor) (g : SFunc),
      Reach (StepIn R) cert.prog R.sevm ((Cursor.start cert).conf R.devm) (κ.conf N.devm) ∧
      CursorOK code cert N κ ∧ κ.f = .next (.exec .call) g ∧
      (SFunc.LineSuffix κ.f t_09aa_c4 ∨ SFunc.LineSuffix κ.f t_20e1_c57 ∨
        SFunc.LineSuffix κ.f t_20e1_c71) := by
  obtain ⟨κ, reach, ok⟩ := reach_of_parentPrefix cert_check pcZero codeEq fork chain
  obtain ⟨g, tree, site⟩ := ok.nodesSatisfy_exec (Reach.nodesSatisfy cert_callSites reach).1 hat
  refine ⟨κ, g, reach, ok, tree, ?_⟩
  simp only [pairCallOk, Bool.or_eq_true, beq_iff_eq] at site
  rw [tree]
  rcases site with (h | h) | h <;> rw [h]
  · exact Or.inl (SFunc.lineSuffix_lineDrop 3 t_09aa_c4)
  · exact Or.inr (Or.inl (SFunc.lineSuffix_lineDrop 44 t_20e1_c57))
  · exact Or.inr (Or.inr (SFunc.lineSuffix_lineDrop 44 t_20e1_c71))

end Blanc.Lift.UniswapV2Pair
