import Blanc.LidoCircuitBreakerAttainment

/-!
# Routing to a `pause`-authorised Registry write: the empty-payload kit

`Blanc/LidoCircuitBreakerAttainment.lean` routes to the
`setPauser.assignment` `SSTORE` through `registerPauser` and pays for almost
none of its branch words: that walk ends `.ok`, and
`routeTo_branchLeft_of_rightRevertsOk` settles every crossing whose untaken arm
can only `REVERT`.

A `pause` walk cannot use that argument.  `pause` writes the Registry through
the shared kernel and *then* calls its target, so the only pause execution this
tree owns that reaches a Registry write is one whose target has no code, and
which therefore ends `.error (.revert, raw)`.

This module supplies the **dual** free crossing.  `Func.rev` reverts with an
empty payload, but every named runtime error reverts through
`Func.revSelector`, whose `REVERT` returns a four-byte window — so an untaken
error arm is refuted by the *outcome* exactly when the walk's own raw revert
carries no output at all.  `raw.output = []` therefore does for this route what
`.ok` does for the registration route: it settles the reentrancy-lock guard,
the caller-assignment guard, the heartbeat-liveness guard and the kernel's
target-zero test without computing a single storage, transient or memory word.

What it does not settle are the four crossings whose untaken arm is a bare
`Func.rev`: `runtimeMain`'s entry guard, `requireStaticArgs`, the
canonical-address guard and the three dispatcher selector pivots.  Those words
are calldata- and value-valued, so they cost no world threading either.

`Attainable` and the AT5 soundness statement are raw-occurrence claims, so a
write a later `REVERT` rolls back inhabits exactly the predicate soundness
quantifies over.  Nothing here says a pause *persists* a Registry change; it
says the write site is *reached*, in an execution that then reverts.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune

/-! ## Memory invariance at the three transient/time opcodes

`line_inv` synthesises `Ninst.Hinv Devm.memory i` for each instruction of a
crossed line, and Blanc had instances for every opcode an earlier walk met.
`pause` is the first body to use `TLOAD`, `TSTORE` and `TIMESTAMP` on a line
whose memory image has to survive, so the three instances live here.  They are
contract-neutral machinery; nothing outside this route has needed them. -/

instance : Rinst.Hinv Devm.memory Rinst.timestamp := by show_hinv_mem_push

/-- `TLOAD` pops a key and pushes a transient cell; memory is untouched. -/
instance : Rinst.Hinv Devm.memory Rinst.tload := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨_key, _s₁⟩, h1, run₁⟩
  exact (Devm.pop_of_pop h1).memory.trans
    (Devm.pushBurn_of_pushItem run₁).memory⟩

/-- `TSTORE` pops two words, charges gas and rewrites transient storage; every
intermediate state, and the final `setTransVal`, leaves memory alone. -/
instance : Rinst.Hinv Devm.memory Rinst.tstore := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨_key, _s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨_v, _s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨_s₃, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨_, _h4, h5⟩
  injection h5 with eq
  rw [← eq]
  exact ((Devm.pop_of_pop h1).memory.trans (Devm.pop_of_pop h2).memory).trans
    (Devm.burn_of_chargeGas h3).memory⟩

/-! ## Inverting a compiled walk one step at a time -/

private theorem of_runCompiledTo_next {fs : List Func} {sevm : Sevm}
    {devm : Devm} {i : Ninst} {body : Func} {out : Execution}
    (run : Func.RunCompiledTo fs sevm devm (.next i body) out) :
    ∃ devm', Ninst.RunCompiled sevm devm i devm' ∧
      Func.RunCompiledTo fs sevm devm' body out := by
  cases run with
  | next instructionRun tail => exact ⟨_, instructionRun, tail⟩

private theorem of_runCompiledTo_last {fs : List Func} {sevm : Sevm}
    {devm : Devm} {l : Linst} {out : Execution}
    (run : Func.RunCompiledTo fs sevm devm (.last l) out) :
    Linst.Run sevm devm l out := by
  cases run with
  | last terminalRun => exact terminalRun

/-! ## The revert payload

`REVERT` reads its window with `Devm.memRead`, and `Mem.read` returns as many
bytes as it is asked for whatever the backing array holds.  So a `REVERT` whose
size operand is four produces four bytes of output, and no fact about the
memory image is needed to know the payload is nonempty.

Both ways `REVERT` can fail before reading — a short stack, or too little gas
for the window's expansion — raise a `.halt` error rather than `.revert`, so
neither can masquerade as the frame's own revert outcome. -/

/-- A `REVERT` whose size operand is four leaves four bytes of output. -/
theorem output_ne_nil_of_run_rev {sevm : Sevm} {devm raw : Devm}
    {i sz : B256} {s : Stack}
    (hstack : devm.stack = i :: sz :: s)
    (hsize : sz.toNat = 4)
    (run : Linst.Run sevm devm .rev (.error (.revert, raw))) :
    raw.output ≠ [] := by
  simp only [Linst.Run, Linst.run] at run
  rw [Devm.popToNat_eq_ok hstack] at run
  simp only [bind, Except.bind] at run
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨sz :: s, devm.memory, devm.gasLeft⟩) rfl] at run
  dsimp only [bind, Except.bind] at run
  split at run
  · rename_i err heq
    rw [chargeGas_def] at heq
    split at heq
    · injection heq with hpair
      rw [← hpair] at run
      injection run with hfst
      exact absurd hfst (by simp)
    · exact absurd heq (by simp)
  · rename_i v _heq
    injection run with hpair
    rw [Prod.mk.injEq] at hpair
    rw [← hpair.2, hsize]
    simp [Devm.output, Devm.setMeta, Devm.withOutput, Devm.memRead, Mem.read,
      Array.sliceD, Array.sliceD.aux]

/-- A walk that reverts through the compact selector reverter carries a
nonempty payload.  Nothing about the memory image is used: the four bytes are
whatever the window holds. -/
theorem output_ne_nil_of_runCompiledTo_revSelector
    {fs : List Func} {sevm : Sevm} {devm raw : Devm}
    {data : Bytes} {hlen : data.length = 4}
    (run : Func.RunCompiledTo fs sevm devm (Func.revSelector data hlen)
      (.error (.revert, raw))) :
    raw.output ≠ [] := by
  unfold Func.revSelector at run
  rcases of_runCompiledTo_next run with ⟨_s1, _q1, run⟩
  rcases of_runCompiledTo_next run with ⟨_s2, _q2, run⟩
  rcases of_runCompiledTo_next run with ⟨_s3, _q3, run⟩
  rcases of_runCompiledTo_next run with ⟨s4, q4, run⟩
  rcases of_runCompiledTo_next run with ⟨s5, q5, run⟩
  have term := of_runCompiledTo_last run
  have p4 : (4 : B256) :: [] <<+ s4.stack :=
    prefix_of_push (of_run_pushB256 (Ninst.Run.of_runCompiled q4)) nil_pref
  have p5 : (28 : B256) :: (4 : B256) :: [] <<+ s5.stack :=
    prefix_of_push (of_run_pushB256 (Ninst.Run.of_runCompiled q5)) p4
  rcases p5 with ⟨rest, hrest⟩
  exact output_ne_nil_of_run_rev (i := 28) (sz := 4) hrest (by decide) term

/-- An untaken named-error arm, refuted by the walk's own empty payload. -/
theorem call_revSelector_refuted {fs : List Func} {sevm : Sevm}
    {devm raw : Devm} {slot : Nat} {data : Bytes} {hlen : data.length = 4}
    (lookup : fs[slot]? = some (Func.revSelector data hlen))
    (emptyOutput : raw.output = [])
    (run : Func.RunCompiledTo fs sevm devm (.call slot)
      (.error (.revert, raw))) : False := by
  cases run with
  | call lookup' _room _burn tail =>
      have bodyEq := Option.some.inj (lookup.symm.trans lookup')
      subst bodyEq
      exact output_ne_nil_of_runCompiledTo_revSelector tail emptyOutput

/-! ## The two free crossings

The mirror image of `routeTo_branchLeft_of_rightRevertsOk` and its sibling: a
refuted arm settles the branch, and the crossing's own pop is still handed to
the continuation. -/

/-- Take the fall-through arm when the jumped arm is refuted. -/
theorem routeTo_branchLeft_of_rightRefuted {fs : List Func} {sevm : Sevm}
    {devm : Devm} {out : Execution} {left right : Func}
    {functionIndex : Nat} {steps : List Prog.SourceStep}
    {target : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo fs sevm devm (.branch left right) out)
    (rightRefuted : ∀ devm' : Devm,
      Func.RunCompiledTo fs sevm devm' right out → False)
    (armRoute : ∀ devm' : Devm,
      Devm.PopBurnBy [0] (gVerylow + gHigh) devm devm' →
      ∀ tail : Func.RunCompiledTo fs sevm devm' left out,
        Func.RunCompiledTo.RouteTo ⟨functionIndex, steps ++ [.branchLeft]⟩
          tail target targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨functionIndex, steps⟩ h target
      targetInstruction := by
  cases h with
  | zero room pop tail =>
      exact .branchLeft (room := room) (pop := pop) (tail := tail)
        (armRoute _ pop tail)
  | succ _nonzero _room _pop tail => exact (rightRefuted _ tail).elim

/-- Take the jumped arm when the fall-through arm is refuted. -/
theorem routeTo_branchRight_of_leftRefuted {fs : List Func} {sevm : Sevm}
    {devm : Devm} {out : Execution} {left right : Func}
    {functionIndex : Nat} {steps : List Prog.SourceStep}
    {target : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo fs sevm devm (.branch left right) out)
    (leftRefuted : ∀ devm' : Devm,
      Func.RunCompiledTo fs sevm devm' left out → False)
    (armRoute : ∀ (devm' : Devm) (word : B256),
      Devm.PopBurnBy [word] (gVerylow + gHigh + gJumpdest) devm devm' →
      ∀ tail : Func.RunCompiledTo fs sevm devm' right out,
        Func.RunCompiledTo.RouteTo ⟨functionIndex, steps ++ [.branchRight]⟩
          tail target targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨functionIndex, steps⟩ h target
      targetInstruction := by
  cases h with
  | zero _room _pop tail => exact (leftRefuted _ tail).elim
  | succ nonzero room pop tail =>
      exact .branchRight (nonzero := nonzero) (room := room) (pop := pop)
        (tail := tail) (armRoute _ _ pop tail)

/-! ## The runtime's four refutable error endpoints -/

/-- Every named runtime error's payload is a four-byte selector. -/
theorem customErrorData_length (name : String) :
    (customErrorData name).length = 4 := by
  simp [customErrorData, B256.length_toBytes]

/-- A call to a named runtime error, refuted by the walk's empty payload. -/
theorem call_namedError_refuted {fs : List Func} {sevm : Sevm}
    {devm raw : Devm} {slot : Nat} (name : String)
    (lookup : fs[slot]? = some (Func.revSelector (customErrorData name)
      (customErrorData_length name)))
    (emptyOutput : raw.output = [])
    (run : Func.RunCompiledTo fs sevm devm (.call slot)
      (.error (.revert, raw))) : False :=
  call_revSelector_refuted lookup emptyOutput run

/-- The four named-error table entries this route's untaken arms call. -/
theorem runtime_error_lookups (dp : DeployParams) :
    ((runtime dp).main :: (runtime dp).aux)[pausableZeroErrorSlot]? =
        some pausableZeroError ∧
      ((runtime dp).main :: (runtime dp).aux)[senderNotPauserErrorSlot]? =
        some senderNotPauserError ∧
      ((runtime dp).main :: (runtime dp).aux)[heartbeatExpiredErrorSlot]? =
        some heartbeatExpiredError ∧
      ((runtime dp).main :: (runtime dp).aux)[reentrantCallErrorSlot]? =
        some reentrantCallError := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [runtime, aux, pausableZeroErrorSlot, senderNotPauserErrorSlot,
      heartbeatExpiredErrorSlot, reentrantCallErrorSlot]

/-! ## Stack-prefix primitives

Two crossings this route computes a branch word across had value-carrying
`of_run_*` inversions but no `<<+` form. -/

/-- `CALLDATASIZE` pushes the calldata length. -/
theorem prefix_of_calldatasize {e : Sevm} {s s' : Devm} {xs : Stack}
    (run : Ninst.Run e s Ninst.calldatasize s') (hp : xs <<+ s.stack) :
    e.data.length.toB256 :: xs <<+ s'.stack :=
  prefix_of_push (of_run_calldatasize run) hp

/-- `arg k ++ checkNonAddress`, the composite `canonicalAddressArg` guards on:
the masked word is zero exactly when the argument's head word is
address-shaped. -/
theorem prefix_of_argCheckNonAddress {e : Sevm} {s s' : Devm} {k : B256}
    {xs : Stack} (hp : xs <<+ s.stack)
    (run : Line.Run e s (arg k ++ checkNonAddress) s') :
    ∃ y, (y :: xs <<+ s'.stack) ∧ (y = 0 ↔ ValidAdr (Sevm.argWord e k)) := by
  rcases of_run_append (arg k) run with ⟨_mid, r1, r2⟩
  exact of_check_non_address (prefix_of_arg hp r1) r2

/-! ## The dispatcher crossing -/

/-- `Devm.getCode` depends only on the state, so a state-preserving relation
carries the whole account-code map. -/
theorem getCode_of_state {a b : Devm} (h : a.state = b.state) :
    Devm.getCode a = Devm.getCode b := by
  funext x; simp only [Devm.getCode, Devm.getAcct]; rw [h]

set_option maxRecDepth 617 in
/-- The three selector crossings of `hybridDispatchWith` on a walk whose
calldata selects `pause`: the outer pivot taken *fall-through* (the selector
equals the pivot, so `gt` yields zero), the third/fourth pivot taken jumped,
and then an immediate match on the head of the third linear group.

`pause` is the outer pivot, so this is three branch words where
`registerPauser` needs six.  All three are selector-valued, so no world
projection is *read* on this leg; storage and memory are threaded across it
anyway, because the kernel's own branches read both. -/
theorem dispatch_routeTo_pause (dp : DeployParams)
    {fs : List Func} {sevm : Sevm} {devm : Devm} {out : Execution}
    {functionIndex : Nat} {steps : List Prog.SourceStep}
    {targetPath : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo fs sevm devm
      (fsig +++ hybridDispatchWith fallbackSlot (funcs dp)) out)
    (selectorEq : Sevm.selector sevm = selector "pause" [.address])
    (bodyRoute : ∀ (current : Prog.SourcePath) (devm' : Devm),
      Devm.getStor devm' = Devm.getStor devm →
      devm'.memory = devm.memory →
      Devm.getCode devm' = Devm.getCode devm →
      ∀ tail : Func.RunCompiledTo fs sevm devm' pause out,
        Func.RunCompiledTo.RouteTo current tail targetPath targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨functionIndex, steps⟩ h targetPath
      targetInstruction := by
  refine routeTo_line fsig h (fun s0 run0 tail0 => ?_)
  have p0 : Sevm.selector sevm :: [] <<+ s0.stack := prefix_of_fsig nil_pref run0
  rw [selectorEq] at p0
  have g0 : Devm.getStor s0 = Devm.getStor devm :=
    (Line.of_inv Devm.getStor (by line_inv) run0).symm
  have m0 : s0.memory = devm.memory :=
    (Line.of_inv Devm.memory (by line_inv) run0).symm
  have d0 : Devm.getCode s0 = Devm.getCode devm :=
    (Line.of_inv Devm.getCode (by line_inv) run0).symm
  refine routeTo_line (splitTest (selector "pause" [.address])) tail0
    (fun _s1 run1 tail1 => ?_)
  have p1 := prefix_of_splitTest p0 run1
  have g1 := (Line.of_inv Devm.getStor (by line_inv) run1).symm.trans g0
  have m1 := (Line.of_inv Devm.memory (by line_inv) run1).symm.trans m0
  have d1 := (Line.of_inv Devm.getCode (by line_inv) run1).symm.trans d0
  refine routeTo_branchLeft_frame tail1
    (fun _w _rest hs => by rw [head_of_stack_prefix p1 hs]; decide)
    (fun _s2 hpop2 tail2 => ?_)
  have p2 := tail_of_stack_prefix p1 ⟨_, hpop2.stack⟩
  have g2 := (getStor_of_state hpop2.state).symm.trans g1
  have m2 := hpop2.memory.symm.trans m1
  have d2 := (getCode_of_state hpop2.state).symm.trans d1
  refine routeTo_line (splitTest (selector "MIN_HEARTBEAT_INTERVAL" [])) tail2
    (fun _s3 run3 tail3 => ?_)
  have p3 := prefix_of_splitTest p2 run3
  have g3 := (Line.of_inv Devm.getStor (by line_inv) run3).symm.trans g2
  have m3 := (Line.of_inv Devm.memory (by line_inv) run3).symm.trans m2
  have d3 := (Line.of_inv Devm.getCode (by line_inv) run3).symm.trans d2
  refine routeTo_branchRight_frame tail3
    (fun _w _rest hs => by rw [head_of_stack_prefix p3 hs]; decide)
    (fun _s4 _w4 hpop4 tail4 => ?_)
  have p4 := tail_of_stack_prefix p3 ⟨_, hpop4.stack⟩
  have g4 := (getStor_of_state hpop4.state).symm.trans g3
  have m4 := hpop4.memory.symm.trans m3
  have d4 := (getCode_of_state hpop4.state).symm.trans d3
  refine routeTo_line (linearTest (selector "pause" [.address])) tail4
    (fun _s5 run5 tail5 => ?_)
  have p5 := prefix_of_linearTest p4 run5
  have g5 := (Line.of_inv Devm.getStor (by line_inv) run5).symm.trans g4
  have m5 := (Line.of_inv Devm.memory (by line_inv) run5).symm.trans m4
  have d5 := (Line.of_inv Devm.getCode (by line_inv) run5).symm.trans d4
  refine routeTo_branchRight_frame tail5
    (fun _w _rest hs => by rw [head_of_stack_prefix p5 hs]; decide)
    (fun _s6 _w6 hpop6 tail6 => ?_)
  have g6 := (getStor_of_state hpop6.state).symm.trans g5
  have m6 := hpop6.memory.symm.trans m5
  have d6 := (getCode_of_state hpop6.state).symm.trans d5
  refine routeTo_line [Ninst.pop] tail6 (fun _s7 run7 tail7 => ?_)
  exact bodyRoute _ _
    ((Line.of_inv Devm.getStor (by line_inv) run7).symm.trans g6)
    ((Line.of_inv Devm.memory (by line_inv) run7).symm.trans m6)
    ((Line.of_inv Devm.getCode (by line_inv) run7).symm.trans d6) tail7

end Blanc.LidoCircuitBreaker
