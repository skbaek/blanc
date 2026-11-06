import Blanc.Lift.Usdc.ImplFrames
import Blanc.Lift.SpawnExact
import Blanc.Lift.Usdc.Lib.Contract
import Blanc.Lift.CallSiteChildren
import Blanc.Lift.CallChildren
import Blanc.CallSpawnExact
import Blanc.ExecutionEntryAccounting
import Blanc.Lift.HistStaticCall

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

/-! ## The spawned frames of `CALL` and `DELEGATECALL` under the frame's actual rules

`Ninst.step_call_spawn_exact` and `Xinst.step_delegatecall_spawn_exact` take `CoveredFork`: a
covered fork selects EIP-2929 access and EIP-7702 delegation.  These twins read `stateGas = none`
alone and resolve both access schedules and the delegation flag (`ForkRules.accessDelegation`),
so they hold on every `HistFork`.  They state only the frame's shape. -/

/-- The frame a spawning `CALL` opens, under `rules.stateGas = none`: the parent's own target is
the child's caller, the stack's value word its value, and the child is not static by itself. -/
theorem step_call_spawn_frameH
    {pc pc' : Nat} {sevm : Sevm} {s : Devm}
    {g c v ii is oi os : B256} {rest : Stack}
    {f : Frame} {rsm : Resume}
    (hspawn : Ninst.step ⟨pc, sevm, s⟩ Ninst.call = .spawn f rsm pc')
    (hstack : s.stack = g :: c :: v :: ii :: is :: oi :: os :: rest)
    (hsg : sevm.benvStat.rules.stateGas = none) :
    ∃ (parent : Devm) (gas : Nat) (na : Adr) (code : ByteArray) (dp : Bool) (data : Bytes),
      f = Frame.ofCall
        (callMsg sevm parent gas v sevm.currentTarget c.toAdr na true false data code dp) := by
  have hx : Xinst.step sevm s .call = .spawn f rsm :=
    XStep.toStep_spawn (by
      simpa only [Ninst.call, Ninst.step_exec] using hspawn)
  simp only [Xinst.step, Bind.bind, Except.bind, Except.assert] at hx
  rw [hsg] at hx
  have hp : (g :: c :: v :: ii :: is :: oi :: os :: rest) <<+ s.stack := by
    rw [hstack]
    simpa only [List.append_nil] using
      (pref_append (g :: c :: v :: ii :: is :: oi :: os :: rest) [])
  rcases eq1 : Devm.pop s with _ | ⟨gas1, devm1⟩ <;>
    simp only [eq1] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  have f1 := Devm.pop_of_pop eq1
  have e1 := f1.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e1
  rw [e1] at hp
  have hv1 : g = gas1 := pref_head_unique hp (pref_append [gas1] devm1.stack)
  subst hv1
  replace hp := cons_pref_cons_inv hp
  rcases eq2 : Devm.popToAdr devm1 with _ | ⟨callee, devm2⟩ <;>
    simp only [eq2] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  rcases Devm.pop_of_popToAdr eq2 with ⟨x2, hx2, h_pop2⟩
  have f2 := Devm.pop_of_pop h_pop2
  have e2 := f2.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e2
  rw [e2] at hp
  have hv2 : c = x2 := pref_head_unique hp (pref_append [x2] devm2.stack)
  subst hv2
  subst hx2
  replace hp := cons_pref_cons_inv hp
  rcases eq3 : Devm.pop devm2 with _ | ⟨value, devm3⟩ <;>
    simp only [eq3] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  have f3 := Devm.pop_of_pop eq3
  have e3 := f3.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e3
  rw [e3] at hp
  have hv3 : v = value := pref_head_unique hp (pref_append [value] devm3.stack)
  subst hv3
  replace hp := cons_pref_cons_inv hp
  rcases eq4 : Devm.popToNat devm3 with _ | ⟨inputIndex, devm4⟩ <;>
    simp only [eq4] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  rcases Devm.pop_of_popToNat_val eq4 with ⟨x4, f4, hk4⟩
  have e4 := f4.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e4
  rw [e4] at hp
  have hv4 : ii = x4 := pref_head_unique hp (pref_append [x4] devm4.stack)
  subst hv4
  subst hk4
  replace hp := cons_pref_cons_inv hp
  rcases eq5 : Devm.popToNat devm4 with _ | ⟨inputSize, devm5⟩ <;>
    simp only [eq5] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  rcases Devm.pop_of_popToNat_val eq5 with ⟨x5, f5, hk5⟩
  have e5 := f5.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e5
  rw [e5] at hp
  have hv5 : is = x5 := pref_head_unique hp (pref_append [x5] devm5.stack)
  subst hv5
  subst hk5
  replace hp := cons_pref_cons_inv hp
  rcases eq6 : Devm.popToNat devm5 with _ | ⟨outputIndex, devm6⟩ <;>
    simp only [eq6] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  rcases Devm.pop_of_popToNat_val eq6 with ⟨x6, f6, hk6⟩
  have e6 := f6.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e6
  rw [e6] at hp
  have hv6 : oi = x6 := pref_head_unique hp (pref_append [x6] devm6.stack)
  subst hv6
  subst hk6
  replace hp := cons_pref_cons_inv hp
  rcases eq7 : Devm.popToNat devm6 with _ | ⟨outputSize, devm7⟩ <;>
    simp only [eq7] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  rcases Devm.pop_of_popToNat_val eq7 with ⟨x7, f7, hk7⟩
  have e7 := f7.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e7
  rw [e7] at hp
  have hv7 : os = x7 := pref_head_unique hp (pref_append [x7] devm7.stack)
  subst hv7
  subst hk7
  replace hp := cons_pref_cons_inv hp
  have e_stack : s.stack
      = g :: c :: v :: ii :: is :: oi :: os :: devm7.stack := by
    rw [e1, e2, e3, e4, e5, e6, e7]
  have h_st7 : s.state = devm7.state :=
    (f1.state).trans ((f2.state).trans ((f3.state).trans ((f4.state).trans
      ((f5.state).trans ((f6.state).trans f7.state)))))
  have h_mem7 : s.memory = devm7.memory :=
    (f1.memory).trans ((f2.memory).trans ((f3.memory).trans ((f4.memory).trans
      ((f5.memory).trans ((f6.memory).trans f7.memory)))))
  clear e1 e2 e3 e4 e5 e6 e7 f1 f2 f3 f4 f5 f6 f7
  clear eq1 eq2 eq3 eq4 eq5 eq6 eq7 h_pop2
  rcases hac : sevm.benvStat.rules.access with gflat | _
  swap
  · simp only [hac] at hx
    rcases hp11 : sevm.benvStat.rules.accessDelegation (addAccessedAddress devm7 c.toAdr)
      c.toAdr with ⟨dp, na, code0, dagc, devm9⟩
    simp only [hp11] at hx
    repeat' split at hx
    all_goals try simp only [XStep.ofExcept, Pure.pure, Except.pure, reduceCtorEq] at hx
    all_goals first
      | (obtain ⟨hf, -⟩ := genericCall_step_spawn_exact hx
         exact ⟨_, _, _, _, _, _, hf⟩)
  · simp only [hac] at hx
    rcases hp11 : sevm.benvStat.rules.accessDelegation devm7 c.toAdr with
      ⟨dp, na, code0, dagc, devm9⟩
    simp only [hp11] at hx
    repeat' split at hx
    all_goals try simp only [XStep.ofExcept, Pure.pure, Except.pure, reduceCtorEq] at hx
    all_goals first
      | (obtain ⟨hf, -⟩ := genericCall_step_spawn_exact hx
         exact ⟨_, _, _, _, _, _, hf⟩)

theorem step_delegatecall_spawn_shapeH {sevm : Sevm} {devm : Devm}
    {f : Frame} {rsm : Resume} {g w : B256} {s : List B256}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (spawn : Xinst.step sevm devm .delegatecall = .spawn f rsm)
    (hstack : devm.stack = g :: w :: s)
    (undelegated : getDelegatedCodeAddress (devm.getCode w.toAdr) = none) :
    f.inner.currentTarget = sevm.currentTarget ∧ f.inner.codeAddress = w.toAdr ∧
      f.inner.caller = sevm.caller ∧ f.inner.value = sevm.value ∧
      f.inner.isStatic = sevm.isStatic ∧ f.inner.code = devm.getCode w.toAdr := by
  have hx := spawn
  simp only [Xinst.step, Bind.bind, Except.bind, Except.assert] at hx
  rw [hsg] at hx
  have hp : (g :: w :: s) <<+ devm.stack := by
    rw [hstack]
    simpa only [List.append_nil] using (pref_append (g :: w :: s) [])
  rcases eq1 : Devm.pop devm with _ | ⟨gas1, devm1⟩ <;> simp only [eq1] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  have f1 := Devm.pop_of_pop eq1
  have e1 := f1.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e1
  rw [e1] at hp
  have hv1 : g = gas1 := pref_head_unique hp (pref_append [gas1] devm1.stack)
  subst hv1
  replace hp := cons_pref_cons_inv hp
  rcases eq2 : Devm.popToAdr devm1 with _ | ⟨callee, devm2⟩ <;> simp only [eq2] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  rcases Devm.pop_of_popToAdr eq2 with ⟨x2, hx2, h_pop2⟩
  have f2 := Devm.pop_of_pop h_pop2
  have e2 := f2.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e2
  rw [e2] at hp
  have hv2 : w = x2 := pref_head_unique hp (pref_append [x2] devm2.stack)
  subst hv2
  subst hx2
  replace hp := cons_pref_cons_inv hp
  rcases eq4 : Devm.popToNat devm2 with _ | ⟨inputIndex, devm4⟩ <;> simp only [eq4] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  rcases Devm.pop_of_popToNat_val eq4 with ⟨x4, f4, hk4⟩
  have e4 := f4.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e4
  rcases eq5 : Devm.popToNat devm4 with _ | ⟨inputSize, devm5⟩ <;> simp only [eq5] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  rcases Devm.pop_of_popToNat_val eq5 with ⟨x5, f5, hk5⟩
  have e5 := f5.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e5
  rcases eq6 : Devm.popToNat devm5 with _ | ⟨outputIndex, devm6⟩ <;> simp only [eq6] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  rcases Devm.pop_of_popToNat_val eq6 with ⟨x6, f6, hk6⟩
  have e6 := f6.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e6
  rcases eq7 : Devm.popToNat devm6 with _ | ⟨outputSize, devm7⟩ <;> simp only [eq7] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  rcases Devm.pop_of_popToNat_val eq7 with ⟨x7, f7, hk7⟩
  have e7 := f7.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e7
  subst hk4 hk5 hk6 hk7
  have hs : s = x4 :: x5 :: x6 :: x7 :: devm7.stack := by
    have := hstack.symm.trans (by rw [e1, e2, e4, e5, e6, e7])
    simp only [List.cons.injEq] at this
    exact this.2.2
  have h_st7 : devm.state = devm7.state :=
    (f1.state).trans ((f2.state).trans ((f4.state).trans ((f5.state).trans
      ((f6.state).trans f7.state))))
  have h_mem7 : devm.memory = devm7.memory :=
    (f1.memory).trans ((f2.memory).trans ((f4.memory).trans ((f5.memory).trans
      ((f6.memory).trans f7.memory))))
  clear e1 e2 e4 e5 e6 e7 f1 f2 f4 f5 f6 f7 eq1 eq2 eq4 eq5 eq6 eq7 h_pop2 hp
  rcases hac : sevm.benvStat.rules.access with gflat | _
  swap
  · simp only [hac] at hx
    rcases hp11 : sevm.benvStat.rules.accessDelegation (addAccessedAddress devm7 w.toAdr)
      w.toAdr with ⟨dp, na, code0, dagc, devm9⟩
    simp only [hp11] at hx
    have h_cc := callCodeH_of_accessDelegation (D := addAccessedAddress devm7 w.toAdr)
      (s := devm) h_st7.symm hp11
    have h_del : na = w.toAdr ∧ code0 = devm.getCode w.toAdr := by
      unfold CallCodeH at h_cc
      split at h_cc
      · rcases h_cc with ⟨-, h1, h2, -⟩ | ⟨d, hd, -⟩
        · exact ⟨h1, h2⟩
        · rw [undelegated] at hd
          cases hd
      · exact ⟨h_cc.1, h_cc.2.1⟩
    obtain ⟨rfl, rfl⟩ := h_del
    repeat' split at hx
    all_goals try simp only [XStep.ofExcept, Pure.pure, Except.pure, reduceCtorEq] at hx
    all_goals first
      | (obtain ⟨hf, -⟩ := genericCall_step_spawn_exact hx
         subst hf
         exact ⟨rfl, rfl, rfl, rfl, by simp only [Frame.ofCall, callMsg, Bool.false_or], rfl⟩)
  · simp only [hac] at hx
    rcases hp11 : sevm.benvStat.rules.accessDelegation devm7 w.toAdr with
      ⟨dp, na, code0, dagc, devm9⟩
    simp only [hp11] at hx
    have h_cc := callCodeH_of_accessDelegation (D := devm7) (s := devm) h_st7.symm hp11
    have h_del : na = w.toAdr ∧ code0 = devm.getCode w.toAdr := by
      unfold CallCodeH at h_cc
      split at h_cc
      · rcases h_cc with ⟨-, h1, h2, -⟩ | ⟨d, hd, -⟩
        · exact ⟨h1, h2⟩
        · rw [undelegated] at hd
          cases hd
      · exact ⟨h_cc.1, h_cc.2.1⟩
    obtain ⟨rfl, rfl⟩ := h_del
    repeat' split at hx
    all_goals try simp only [XStep.ofExcept, Pure.pure, Except.pure, reduceCtorEq] at hx
    all_goals first
      | (obtain ⟨hf, -⟩ := genericCall_step_spawn_exact hx
         subst hf
         exact ⟨rfl, rfl, rfl, rfl, by simp only [Frame.ofCall, callMsg, Bool.false_or], rfl⟩)

private theorem stack_seven {l : List B256} (h : 7 ≤ l.length) :
    ∃ (g c v ii is oi os : B256) (rest : List B256), l = g :: c :: v :: ii :: is :: oi :: os :: rest :=
  match l, h with
  | g :: c :: v :: ii :: is :: oi :: os :: rest, _ => ⟨g, c, v, ii, is, oi, os, rest, rfl⟩

/-- The implementation delegates only to the linked library (same storage owner, caller, value,
static flag), and otherwise calls out only by `CALL` with itself as caller (`rescueERC20`). -/
theorem impl_children {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (codeEq : sevm.code = Impl.code) (fork : HistFork sevm.benvStat.fork)
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
  have nodeFork : HistFork N.sevm.benvStat.fork := by rw [sevmEq]; exact fork
  obtain ⟨κ, reach, ok⟩ := cursor_of_parentPrefix_noStateGas certL_check
    (F := ⟨0, sevm, pre, out, run⟩) rfl codeEq fork.stateGas_none chain
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
      obtain ⟨_, _, _, _, _, _, hframe⟩ := step_call_spawn_frameH hn hs7 nodeFork.stateGas_none
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
      obtain ⟨hT, hA, hC, hV, hS, hK⟩ := step_delegatecall_spawn_shapeH nodeFork.stateGas_none hx hs
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
