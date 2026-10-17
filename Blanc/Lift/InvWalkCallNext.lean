import Blanc.Lift.InvWalkWorld
import Blanc.Lift.ExactWalkCutOps

/-!
# Internal calls in lifted code: the `callNext` node and the `PC` call idiom

A lifted internal call is a `callNext k f` node: a `JUMP` into entry `k` that runs it as a
callee, continuing with `f` (the tree at the return tag) when the callee returns.  The cut run
relation admits two ways through it (`SFunc.RunCutP.callRet`, `.callHalt`); `ric_call`
(`Blanc/Lift/InvWalkWorld.lean`) inverts it into that disjunction.  This module removes the
halting arm by a kernel scan and packages the call idiom Vyper 0.2.x emits.

* `entryReach fs fuel todo seen` collects the entries reachable from `todo` through gotos and
  calls (fuel-bounded); `calleeNeverHalts fs k fuel` checks that entry `k` is in its own
  reach and that the reach is a `NoHaltSet` (no `STOP`/`RETURN`/`SELFDESTRUCT` leaf anywhere
  in the callee's entry closure).  Its soundness needs nothing of `entryReach`: `NoHaltSet`
  checks closure itself.  A too-small fuel only makes the scan answer `false`.
* `ric_callNext`: under the scan, a cut run of `callNext k f` *is* a callee run to
  `.returned D` followed by a cut run of `f` from `D`.
* `ric_pcAt` / `rxc_pcAt`: the `PC` node at pc `p` pushes `p`.
* `pcCallTree p t0 t1 k f` is the idiom `PUSH1 6; PC; ADD; PUSH2 t; JUMP` (the lifter emits it
  as `.next (.push [6]) (.pcAt p (.next add (.next (.push [t0, t1]) (.callNext k f))))`):
  the return address `p + 6` is computed from the program counter.  `ric_pcCall` inverts it
  to a callee run from `St b (Nat.toB256 (p + 6) :: S) M G'` and the continuation;
  `rxc_pcCall` composes an exact callee run and an exact continuation at cost `19`.

A callee walk proves one lemma per callee over `SFunc.Run fs sevm (St b (ret :: args) M G)
(entry tree) (.returned d)` and is reused at every call site through `ric_pcCall` (safety) and,
with the callee's exact twin, `rxc_pcCall` (liveness).

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-! ## The callee's entry closure -/

/-- The entries reachable from `todo` (and already in `seen`) through goto and call
references, explored for at most `fuel` steps. -/
def entryReach (fs : List SFunc) : Nat → List Nat → List Nat → List Nat
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | n + 1, k :: todo, seen =>
    if seen.contains k then entryReach fs n todo seen
    else match fs[k]? with
      | some g => entryReach fs n (g.refs ++ todo) (k :: seen)
      | none => entryReach fs n todo (k :: seen)

/-- **The never-halts scan.**  Entry `k` lies in its explored closure, and that closure is a
`NoHaltSet`: closed under references, with no successful halting leaf. -/
def calleeNeverHalts (fs : List SFunc) (k fuel : Nat) : Bool :=
  (entryReach fs fuel [k] []).contains k && NoHaltSet fs (entryReach fs fuel [k] [])

/-- A run of a callee that passes the scan never halts the frame. -/
theorem calleeNeverHalts.not_halted {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc}
    {k fuel : Nat} (hnh : calleeNeverHalts fs k fuel = true) {g : SFunc} (hk : fs[k]? = some g)
    {sevm : Sevm} {devm D : Devm} (run : SFunc.RunP P fs sevm devm g (.halted D)) : False := by
  simp only [calleeNeverHalts, Bool.and_eq_true, List.contains_iff_mem] at hnh
  exact SFunc.RunP.not_halted_entry hnh.2 hnh.1 hk run rfl

section Control

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {G : Nat} {f g : SFunc} {r : Seg}

/-- **An internal call whose callee never halts**: the callee runs from the state with the
destination popped to `.returned D`, and the continuation runs from `D`. -/
theorem ric_callNext {k fuel : Nat} {dd : B256} (hnh : calleeNeverHalts fs k fuel = true)
    (hk : fs[k]? = some g)
    (run : SFunc.RunCut fs sevm C (St b (dd :: S) M G) (.callNext k f) r) :
    ∃ G' D, SFunc.Run fs sevm (St b S M G') g (.returned D) ∧ SFunc.RunCut fs sevm C D f r := by
  obtain ⟨G', ⟨D, hc, hcont⟩ | ⟨D, hc, -⟩⟩ := ric_call hk run
  · exact ⟨G', D, hc, hcont⟩
  · exact (calleeNeverHalts.not_halted hnh hk hc).elim

/-! ## The `PC` node -/

/-- A `PC` step at pc `p` is the push of `p`. -/
theorem pushItem_of_stepRun_pc {p : Nat} {d d' : Devm}
    (h : Ninst.StepRun p sevm d (.reg .pc) .none (.ok d')) :
    pushItem (Nat.toB256 p) gBase d = .ok d' := by
  simp only [Ninst.StepRun, Ninst.step, Step.run_ofExecution, true_and] at h
  simp only [Rinst.run, Rinst.runCore] at h
  exact h.symm

/-- `PC` at pc `p`, inverted. -/
theorem ric_pcAt {p : Nat}
    (run : SFunc.RunCut fs sevm C (St b S M G) (.pcAt p f) r) :
    ∃ G', SFunc.RunCut fs sevm C (St b (Nat.toB256 p :: S) M G') f r := by
  cases run with
  | pcAt _ hstep k =>
    have hp := Devm.pushBurn_of_pushItem (pushItem_of_stepRun_pc hstep)
    have hs : _ := hp.stack
    simp only [Stack.Push, Split, St.stack, List.cons_append, List.nil_append] at hs
    have e := St.of_stackRel hp
    rw [hs] at e
    exact ⟨_, e ▸ k⟩

/-- `PC` at pc `p`, forward. -/
theorem stepRun_pc_St {p : Nat} (hroom : S.length < 1024) :
    Ninst.StepRun p sevm (St b S M (G + 2)) (.reg .pc) .none
      (.ok (St b (Nat.toB256 p :: S) M G)) := by
  simp only [Ninst.StepRun, Ninst.step, Step.run_ofExecution, true_and]
  simp only [Rinst.run, Rinst.runCore]
  rw [pushItem_eq_ok (by simp only [St.gasLeft, gBase, le_add_iff_nonneg_left, zero_le])
    (by simpa only [St.stack] using hroom)]
  simp only [St, Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach, Devm.stateGas_setMach, gBase, add_tsub_cancel_right]

theorem rxc_pcAt {p : Nat} (hroom : S.length < 1024)
    (k : SFunc.RunExactCut fs sevm C (St b (Nat.toB256 p :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b S M (G + 2)) (.pcAt p f) r :=
  .pcAt (stepRun_pc_St hroom) k

/-! ## The `PUSH1 6; PC; ADD; PUSH2 t; JUMP` call idiom -/

/-- The lifter's form of an internal call whose return address is computed from the program
counter: `PUSH1 6; PC (at p); ADD; PUSH2 [t0, t1]; JUMP` into entry `k`, returning to `f`
(the tree at `p + 6`). -/
def pcCallTree (p : Nat) (t0 t1 : UInt8) (k : Nat) (f : SFunc) : SFunc :=
  .next (.push [0x06] (by decide)) (.pcAt p (.next (.reg .add)
    (.next (.push [t0, t1] (by simp only [List.length_cons, List.length_nil, zero_add,
      Nat.reduceAdd, Nat.reduceLeDiff])) (.callNext k f))))

theorem pc_add_six {p : Nat} (hp : p + 6 < 2 ^ 256) :
    Nat.toB256 p + Bytes.toB256 [0x06] = Nat.toB256 (p + 6) := by
  rw [show Bytes.toB256 [0x06] = Nat.toB256 6 by decide, toB256_add_toB256 hp]

/-- **The call idiom, inverted**: the callee (entry `k`) runs from the return address
`p + 6` over the caller's stack to `.returned D`, and the continuation runs from `D`. -/
theorem ric_pcCall {p k fuel : Nat} {t0 t1 : UInt8} (hnh : calleeNeverHalts fs k fuel = true)
    (hk : fs[k]? = some g) (hp : p + 6 < 2 ^ 256)
    (run : SFunc.RunCut fs sevm C (St b S M G) (pcCallTree p t0 t1 k f) r) :
    ∃ G' D, SFunc.Run fs sevm (St b (Nat.toB256 (p + 6) :: S) M G') g (.returned D) ∧
      SFunc.RunCut fs sevm C D f r := by
  unfold pcCallTree at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_push s1
  obtain ⟨G2, run⟩ := ric_pcAt run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_add s1
  rw [pc_add_six hp] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s1
  exact ric_callNext hnh hk run

/-- **The call idiom, forward**: an exact callee run from the return address `p + 6` and an
exact continuation make an exact run of the idiom, at cost `3 + 2 + 3 + 3 + 8`. -/
theorem rxc_pcCall {p k : Nat} {t0 t1 : UInt8} {D : Devm} (hk : fs[k]? = some g)
    (hp : p + 6 < 2 ^ 256) (hroom : S.length + 2 < 1024)
    (hcall : SFunc.RunExact fs sevm (St b (Nat.toB256 (p + 6) :: S) M G) g (.returned D))
    (cont : SFunc.RunExactCut fs sevm C D f r) :
    SFunc.RunExactCut fs sevm C (St b S M (G + 19)) (pcCallTree p t0 t1 k f) r := by
  unfold pcCallTree
  refine rxc_push rfl (by omega) ?_
  refine rxc_pcAt (by simp only [List.length_cons]; omega) ?_
  refine rxc_add (by omega) ?_
  rw [pc_add_six hp]
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  exact rxc_callRet hk hcall cont

end Control

end Blanc.Lift
