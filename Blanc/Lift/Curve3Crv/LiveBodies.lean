import Blanc.Lift.Curve3Crv.ViewBodies
import Blanc.Lift.Curve3Crv.Refine
import Blanc.Lift.StaticCall

/-!
# Liveness: the bodies, forward with exact gas

Each segment builds a gas-exact run of one function body inside entry 0 from its entry state
(`BodyLive`), for a raw effect that succeeds: the converse of the matching `SafeBodies`
segment, with the same walk read forwards (`rx_vyNonpayable`, `rx_vyAddrArg`, `rx_caller`,
`rx_keccak` with `vySlot_keccak`, `rx_sload_sel`, `rx_sstore` at its selected cost, `rx_log3`,
`rx_return`).  The word views are proved in `ViewBodies.lean`; `live_at` assembles all bodies
but `set_name`, whose call to an unknown contract makes its gas inexact (`live_setName`).
-/

namespace Blanc.Lift.Curve3Crv

open Jaune

section

variable {sevm : Sevm} {b : Devm}

local notation "stor₀" => Devm.getStor b sevm.currentTarget

-- SEGMENT: liveSetMinter (36 nodes)
/-- `set_minter`.  Proof sketch: `rx_vyNonpayable`, `rx_vyAddrArg`, `rx_push`, `rx_sload_sel`,
`rx_caller`, `rx_eq (v := 1)`, `rx_push`, `rx_branch_succ`, `rx_dest`, `rx_push`,
`rx_calldataload`, `rx_push`, `rx_sstore` (sentry: `gCallStipend < G` suffices, the charge
after the `SSTORE` is 0), `.last` of `STOP`.  Cost:
`19 + 34 + 3 + sloadCost + 2 + 3 + 3 + 10 + 1 + 3 + 3 + 3 + sstoreCost`. -/
theorem live_setMinter (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    {r : Raw} (hr : rawSetMinter sevm stor₀ = some r) : BodyLive sevm b t_00b0_c0 r := by
  unfold rawSetMinter at hr
  split_ifs at hr with hg
  obtain ⟨hv, hm, hmin⟩ := hg
  cases hr
  set m := Sevm.argWord sevm 0
  set b1 := afterSload sevm b vyMinterSlot
  have hm4 : Sevm.dataWord sevm (Bytes.toB256 [0x04]) = m := rfl
  have hM := vyMem_empty_size (Sevm.dataWord sevm 0)
  refine ⟨sstoreCost sevm b1 vyMinterSlot m + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 2 +
    sloadCost sevm b vyMinterSlot + 3 + 34 + 19, fun G hG => ?_⟩
  refine ⟨St (afterSstore sevm b1 vyMinterSlot m) [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G,
    ?_, rfl, ?_⟩
  · unfold entrySt
    rw [show G + (sstoreCost sevm b1 vyMinterSlot m + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 2 +
      sloadCost sevm b vyMinterSlot + 3 + 34 + 19) = G + sstoreCost sevm b1 vyMinterSlot m + 3 + 3
      + 3 + 1 + 10 + 3 + 3 + 2 + sloadCost sevm b vyMinterSlot + 3 + 34 + 19 by omega]
    refine rx_vyNonpayable (h := 0x00) (l := 0xba) (fail := t_00b6_c0) hv (by simp) ?_
    refine rx_vyAddrArg (p := 0x04) (h := 0x00) (l := 0xcb) (fail := t_00c7_c0)
      (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyImg_clamps _ _) (by rw [hM]) (by rw [hM]; omega)
      (by rw [hm4]; exact hm) (by simp) ?_
    refine rx_push (w := vyMinterSlot) rfl (by simp) ?_
    refine rx_sload_sel hfork (by simp) ?_
    refine rx_caller (by simp) ?_
    refine rx_eq (v := 1) ?_ (by simp) ?_
    · have : b.getStorVal sevm.currentTarget vyMinterSlot = sevm.caller.toB256 := hmin
      simp [B256.eqCheck, this]
    refine rx_push rfl (by simp) ?_
    refine rx_branch_succ (by decide) ?_
    refine rx_dest ?_
    refine rx_push rfl (by simp) ?_
    refine rx_calldataload (by simp) ?_
    rw [hm4]
    refine rx_push (w := vyMinterSlot) rfl (by simp) ?_
    refine rx_sstore hfork (by omega) hstatic ?_
    exact .last rfl
  · refine ⟨?_, fun a ha => ?_, ?_, fun o ho => by cases ho⟩
    · show Devm.getStor (afterSstore sevm b1 vyMinterSlot m) _ = _
      rw [afterSstore_getStor_self, afterSload_getStor]
    · show Devm.getStor (afterSstore sevm b1 vyMinterSlot m) _ = _
      rw [afterSstore_getStor_ne _ _ _ _ _ (Ne.symm ha), afterSload_getStor]
    · show (afterSstore sevm b1 vyMinterSlot m).logs = _
      rw [afterSstore_logs, afterSload_logs, List.append_nil]

-- SEGMENT: liveTransfer (107 nodes)
/-- `transfer`.  Proof sketch: the walk of `safeTransfer` forwards; the two slots by the
scratch sequence (`slot_seq`-style helper as in `ViewBodies.lean`, generalised to a stack
tail), the guards' flags from `rawTransfer`'s conditions, the `SSTORE`s at `sstoreCost` over
the evolving base (`afterSload`, `afterSstore`), `rx_log3` (static frame excluded by
`hstatic`), `rx_return` of `(1 : B256).toBytes`.  The cost is a sum of constants and the two
`sloadCost`/`sstoreCost` terms, all fixed by `b`. -/
theorem live_transfer (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    {r : Raw} (hr : rawTransfer sevm stor₀ = some r) : BodyLive sevm b t_02ce_c0 r := by
  sorry

-- SEGMENT: liveTransferFrom (172 nodes)
/-- `transferFrom`: forwards of `safeTransferFrom`, the minter branch decided by `rawTransferFrom`'s
`spend`: `rx_branchTo_succ` into entry 3 when the caller is the minter, the allowance block
otherwise; the shared tail proved once over an arbitrary base. -/
theorem live_transferFrom (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) {r : Raw} (hr : rawTransferFrom sevm stor₀ = some r) :
    BodyLive sevm b t_0390_c0 r := by
  sorry

-- SEGMENT: liveApprove (97 nodes)
/-- `approve`: forwards of `safeApprove`; the zero-value arm (`.jump 4`) or the read arm, joined
at entry 4. -/
theorem live_approve (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    {r : Raw} (hr : rawApprove sevm stor₀ = some r) : BodyLive sevm b t_04ab_c0 r := by
  sorry

-- SEGMENT: liveMintBurn (121 + 117 nodes)
/-- `mint` and `burnFrom`: forwards of `safeMintBurn`. -/
theorem live_mint (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    {r : Raw} (hr : rawMint sevm stor₀ = some r) : BodyLive sevm b t_056e_c0 r := by
  sorry

-- SEGMENT: liveMintBurn (see `live_mint`)
theorem live_burnFrom (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    {r : Raw} (hr : rawBurnFrom sevm stor₀ = some r) : BodyLive sevm b t_0644_c0 r := by
  sorry

-- SEGMENT: liveStringViews (116 + 116 nodes; `name` and `symbol`, one shape)
/-- `name()` and `symbol()`.  Proof sketch: guard; `mstore(0xc0, slot); keccak(0xc0, 0x20)` is
the base; the loop (first iteration inlined, then entry 9 / 10 with join 5 / 6) copies storage
words `base + i` to memory `0x180 + 32 i` while `32 i ≤ L + 32` and `i < 3` (`2` for `symbol`),
counter at `0x120`: `SFunc.RunExactCut.iterate` with the invariant "memory reads the first `i`
words"; then the join: `CALLDATACOPY` from `CALLDATASIZE` zero-fills `ceil32 L - L` bytes after the
string (the `(L - 1) mod 32` arithmetic is `ceil32`, including `L = 0` by wrapping), `mstore(0x160,
0x20)`, `return(0x160, ceil32 (0x40 + L))`, which reads `abiString (vyStrOf stor base n)`.
The same loop shape as `set_name`'s, reversed (storage to memory): one generic lemma serves both
views. -/
theorem live_name (hfork : CoveredFork sevm.benvStat.fork) {r : Raw}
    (hr : rawName sevm stor₀ = some r) : BodyLive sevm b t_0716_c0 r := by
  sorry

-- SEGMENT: liveStringViews (see `live_name`)
theorem live_symbol (hfork : CoveredFork sevm.benvStat.fork) {r : Raw}
    (hr : rawSymbol sevm stor₀ = some r) : BodyLive sevm b t_07ca_c0 r := by
  sorry

end

/-- The raw effect of body `k` succeeds with `r` and body `k` runs to it (all bodies but
`set_name`). -/
theorem live_at {sevm : Sevm} {b : Devm} (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) {k : Nat} {f : SFunc} {ow : Option B256} {r : Raw}
    (hk1 : k ≠ 1) (hf : bodies[k]? = some f)
    (hr : rawOf k sevm ow (Devm.getStor b sevm.currentTarget) = some r) : BodyLive sevm b f r := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  all_goals simp only [bodies, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.some.injEq, List.getElem?_nil, reduceCtorEq] at hf
  all_goals try subst hf
  · exact live_setMinter hfork hstatic hr
  · exact absurd rfl hk1
  · exact live_totalSupply hfork hr
  · exact live_allowance hfork hr
  · exact live_transfer hfork hstatic hr
  · exact live_transferFrom hfork hstatic hr
  · exact live_approve hfork hstatic hr
  · exact live_mint hfork hstatic hr
  · exact live_burnFrom hfork hstatic hr
  · exact live_name hfork hr
  · exact live_symbol hfork hr
  · exact live_decimals hfork hr
  · exact live_balanceOf hfork hr

/-! ## `set_name`: live when the owner answers -/

/-- The static call `set_name` makes answers `w` whenever it is made with at least `Gc` gas and
the owner calldata in its input window, and leaves at least `R` gas: a premise about the
contract at the stored minter, over any call-site memory and stack below. -/
def OwnerCallOk (sevm : Sevm) (b : Devm) (w : B256) (R Gc : Nat) : Prop :=
  ∀ (S : List B256) (M : Mem) (G : Nat), Gc ≤ G → G < 2 ^ 256 →
    (M.read 0x23c 4).1 = ownerCalldata →
    ∃ d out, Ninst.RunCompiled sevm
        (St (afterSload sevm b vyMinterSlot) (Nat.toB256 G ::
          b.getStorVal sevm.currentTarget vyMinterSlot :: 0x23c :: 4 :: 0x280 :: 0x20 :: S) M G)
        (.exec .staticcall) d ∧
      StaticCallPost (afterSload sevm b vyMinterSlot) d S M 0x23c 4 0x280 0x20 1 out ∧
      32 ≤ out.length ∧ Bytes.toB256 (out.take 32) = w ∧ R ≤ d.gasLeft

-- SEGMENT: liveSetName (217 nodes; after `safeSetName`, whose loop lemma it mirrors)
/-- **`set_name`, forward**, given the owner's answer.  There are a gas amount `R` the rest of
the body needs after the call and a prefix cost `P` (both fixed by `b`) such that, if the owner
call answers the caller leaving at least `R` gas whenever made with at least `Gc`, every frame
gas `G ≥ Gc + P` runs the body to the raw effect.  Gas after the call is the callee's business,
so the final gas is not stated.

Proof sketch: the forward walk of `safeSetName`'s prefix (`rx_calldatacopy`s with their
expansion to `0x200`, length guards from `rawSetName`), `mstore(0x220, sel)` (expansion to
`0x240`), `rx_sload_sel`, `rx_gas` (pushes the gas left, `G - P + …`, below `2^256`), then the
call step from `OwnerCallOk` (`rx_staticcall`'s continuation form, flag `1`), the three checks,
and the two copy loops by `SFunc.RunExactCut.iterate` at the `sstoreCost`s of the string
slots, all within `R`. -/
theorem live_setName {sevm : Sevm} {b : Devm} (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) {r : Raw}
    (hr : rawSetName sevm (Devm.getStor b sevm.currentTarget) (some sevm.caller.toB256) =
      some r) :
    ∃ R P, ∀ Gc, OwnerCallOk sevm b sevm.caller.toB256 R Gc → ∀ G, Gc + P ≤ G → G < 2 ^ 256 →
      ∃ post, SFunc.RunExact prog sevm (entrySt sevm b G) t_00f1_c0 (.halted post) ∧
        Lands sevm b post r := by
  sorry

end Blanc.Lift.Curve3Crv
