import Blanc.Lift.Usdc.ImplFrames
import Blanc.Lift.Usdc.SpawnExact
import Blanc.Lift.Usdc.Lib.Contract
import Blanc.Lift.CallSiteChildren
import Blanc.Lift.CallChildren
import Blanc.CallSpawnExact
import Blanc.ExecutionEntryAccounting

/-!
# What the FiatTokenV2_2 implementation spawns (C2b, nested level)

`impl_children`: a frame running the implementation runtime `Impl.code` from pc `0`, with the library
code installed at `usdcLib`, spawns by `DELEGATECALL` only into the library (at the frame's storage
owner, with the frame's caller, value and static flag, and the library's code), and otherwise only
by `CALL` with value `0` (`rescueERC20`), whose child the frame calls and which keeps the static
flag.

The proof is a cursor argument over the refined certificate `certL` (`ImplFrames.lean`): every
cursor-placed node of the frame decodes `CALL` or `DELEGATECALL`, and at such a node the frame
constant (`certL_framesSat`) is the actual operand: the library address, or the value word `0`.
The library's code is kept along the frame's prefix (it is nonempty), it is no EIP-7702
designator, so the child enters it (`Xinst.step_delegatecall_spawn_exact`).
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift

/-- External instructions the implementation certificate admits. -/
def implKinds (x : Xinst) : Bool := x == .call || x == .delegatecall

theorem impl_kinds : ∀ f ∈ certL.prog, f.execsSatisfy implKinds = true := by
  rw [certL_prog]
  decide +kernel

theorem lib_undelegated : getDelegatedCodeAddress Lib.code = none := by
  decide +kernel

theorem lib_toList_ne_nil : Lib.code.toList ≠ [] := by
  intro h
  have hlen := congrArg List.length h
  rw [ByteArray.toList_eq_toList_data, Array.length_toList] at hlen
  exact absurd hlen (by decide +kernel)

private theorem stack_seven {l : List B256} (h : 7 ≤ l.length) :
    ∃ (g c v ii is oi os : B256) (rest : List B256), l = g :: c :: v :: ii :: is :: oi :: os :: rest :=
  match l, h with
  | g :: c :: v :: ii :: is :: oi :: os :: rest, _ => ⟨g, c, v, ii, is, oi, os, rest, rfl⟩

/-- The implementation delegates only to the linked library (same storage owner, caller, value,
static flag), and otherwise calls out only by `CALL` with itself as caller (`rescueERC20`). -/
theorem impl_children {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (codeEq : sevm.code = Impl.code) (fork : CoveredFork sevm.benvStat.fork)
    (libCode : pre.state.getCode usdcLib = Lib.code) :
    ∀ c ∈ Exec.childFrames run,
      (c.sevm.currentTarget = sevm.currentTarget ∧ c.sevm.codeAddress = some usdcLib ∧
        c.sevm.caller = sevm.caller ∧ c.sevm.value = sevm.value ∧
        c.sevm.isStatic = sevm.isStatic ∧ c.sevm.code = Lib.code) ∨
      (c.sevm.caller = sevm.currentTarget ∧ c.sevm.value = 0 ∧ c.sevm.isStatic = sevm.isStatic) := by
  intro c member
  obtain ⟨N, f, rsm, pc', cevm, chain, step, enter, childEq⟩ :=
    Exec.childFrames_spawnedAt run (.refl _) c member
  obtain ⟨x, hat, hx, -⟩ := Evm.step_spawn_inv step
  have sevmEq : N.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  have nodeFork : CoveredFork N.sevm.benvStat.fork := by rw [sevmEq]; exact fork
  obtain ⟨κ, reach, ok⟩ := cursor_of_parentPrefix certL_check
    (F := ⟨0, sevm, pre, out, run⟩) rfl codeEq fork chain
  have frames := Cursor.framesSat_of_reachable certL_framesSat certL_framesSat_head reach
  have hP := ok.framesSat_exec frames hat
  have kind := ok.execsSatisfy (Cursor.execsSatisfy_of_reachable impl_kinds reach) hat
  obtain ⟨benv, -, hcevm⟩ := Frame.enter_run_inv enter
  subst hcevm
  rw [childEq]
  cases x with
  | call =>
      right
      simp only [implP, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hP
      have hv := ok.stack_const hP.1
      have hlen : 7 ≤ N.devm.stack.length := by
        obtain ⟨S, rest, hstack, matched, -⟩ := ok.stack
        have := (frameMatches_matches matched).length
        simp only [List.length_map] at this
        rw [hstack, List.length_append]
        omega
      obtain ⟨g, t, v, ii, is, oi, os, rest, hs7⟩ := stack_seven hlen
      rw [hs7] at hv
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hv
      subst hv
      have hn : Ninst.step ⟨N.pc, N.sevm, N.devm⟩ Ninst.call = .spawn f rsm (N.pc + 1) := by
        rw [Ninst.call, Ninst.step_exec]
        simp only [hx, XStep.toStep]
      obtain ⟨_, _, _, _, _, -, -, -, -, -, hframe, -⟩ := Ninst.step_call_spawn_exact hn hs7 nodeFork
      subst hframe
      refine ⟨?_, rfl, ?_⟩
      · show N.sevm.currentTarget = sevm.currentTarget
        rw [sevmEq]
      · show (false || N.sevm.isStatic) = sevm.isStatic
        rw [sevmEq, Bool.false_or]
  | delegatecall =>
      left
      simp only [implP, beq_iff_eq] at hP
      have hw := ok.stack_const hP
      obtain ⟨g, a, rest, hs⟩ := Xinst.step_delegatecall_spawn_stack hx
      rw [hs] at hw
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hw
      subst hw
      have nodeCode : N.devm.getCode usdcLib = Lib.code := by
        have keep := (Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode chain).2 usdcLib
          (by change (pre.state.getCode usdcLib).toList ≠ []; rw [libCode]; exact lib_toList_ne_nil)
        exact keep.trans libCode
      have adr : usdcLib.toB256.toAdr = usdcLib := toAdr_toB256 _
      obtain ⟨hT, hA, hC, hV, hS, hK, -⟩ := Xinst.step_delegatecall_spawn_exact nodeFork hx hs
        (by rw [adr, nodeCode]; exact lib_undelegated)
      rw [adr] at hA hK
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · show f.inner.currentTarget = _
        rw [hT, sevmEq]
      · show f.inner.codeAddress = _
        exact hA
      · show f.inner.caller = _
        rw [hC, sevmEq]
      · show f.inner.value = _
        rw [hV, sevmEq]
      · show f.inner.isStatic = _
        rw [hS, sevmEq]
      · show f.inner.code = _
        rw [hK, nodeCode]
  | _ => simp only [implKinds, reduceCtorEq, beq_iff_eq, Bool.or_eq_true, or_self] at kind

end Blanc.Lift.Usdc
