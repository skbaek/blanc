import Blanc.Weth10AllowanceSweep

/-!
Region-agnostic occurrence dispatch spine for the compiled WETH10 runtime.

`Blanc/Weth10HolderFlowWriteCompleteness.lean` walks the compiled dispatcher
backwards from an actual balance `SSTORE`.  Every step of that walk except its
last mentions only `.reg .sstore`: the written key, the stored value and the
retained holder play no part in it.  This module restates the walk for an
arbitrary register instruction `.reg r`, so one spine serves the allowance
write side and the allowance read side without a second traversal.

Two deliberate differences from the balance chain:

* the dispatcher's fallback leaf is killed by a **semantic** certificate —
  `fallbackFree`, a proof that no occurrence survives inside the fallback
  body — rather than by a Boolean `Func.sstoreFreeWithin`.  Callers supply it
  from `Exec.Frame.CompiledCursor.no_sstoreOccurrence_of_free` or from
  `Exec.Frame.CompiledCursor.no_sloadOccurrence_of_free`, and both halves then
  share this traversal verbatim;
* every step additionally reports `Devm.DispatchSilent`, so a caller that
  reaches a selector body knows the generated dispatcher changed no state,
  memory, log or output.  Allowance keys are a `keccak` of memory, unlike
  balance keys, so a caller must relate the executed key to the frame's entry
  memory; the balance chain never needed that and so never produced it.

Full `Ninst` genericity is impossible below the branch and call glue: that
glue is `PUSH`/`JUMPI`/`JUMP`/`JUMPDEST`, so a `.push` occurrence genuinely
does live inside it.  `.reg r` is the widest instruction class the glue
traversal can carry, and it covers both storage instructions.  The two steps
that never meet the glue — the source-line skip and the frame-entry
`JUMPDEST` — are stated for an arbitrary `Ninst`.

The glue traversal itself is `Blanc/Weth10AllowanceSweep.lean`'s
`Exec.Frame.CompiledCursor.regOccurrence_branch` and `.regOccurrence_call`,
reused here rather than restated: the branch step already retains the flag
this spine needs.
-/

namespace Blanc

open Jaune

namespace Weth10

/-! ## Source-line traversal

Skipping a source line never meets the compiler's glue, so these two steps are
stated for an arbitrary `Ninst`. -/

/-- A source head different from the swept instruction cannot be the selected
occurrence, so the same occurrence is retained by the exact tail cursor.  The
executed head occurrence is returned as well. -/
theorem Exec.Frame.CompiledCursor.ninstOccurrence_next_ne
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {sourceTable : List (Nat × Func)}
    {source : Ninst} {tail : Func} {final : Devm}
    {n : Ninst} {stepPre stepPost : Devm} {slot : Xlot}
    (cursor : frame.CompiledCursor dp ca fs sourceTable
      (.next source tail) final)
    (notSwept : source ≠ n)
    (occurrence : frame.NinstOccurrenceFromCursor cursor n
      stepPre stepPost slot) :
    ∃ (tailCursor : frame.CompiledCursor dp ca fs sourceTable tail final)
        (sourceSlot : Xlot),
      frame.NinstOccurrence dp ca source cursor.pre tailCursor.pre
        sourceSlot ∧
      frame.NinstOccurrenceFromCursor tailCursor n
        stepPre stepPost slot := by
  rcases cursor.ninstOccurrenceFromCursor_head_or_tail occurrence with
    ⟨sourceEq, _preEq⟩ |
      ⟨tailCursor, sourceSlot, sourceOccurrence, remaining⟩
  · exact (notSwept sourceEq.symm).elim
  · exact ⟨tailCursor, sourceSlot, sourceOccurrence, remaining⟩

/-- Dynamically skip a source line that cannot host the swept instruction,
returning both its actual `Line.Run` — the raw material for a silence
certificate — and the retained occurrence in the exact suffix cursor. -/
theorem Exec.Frame.CompiledCursor.ninstOccurrence_after_line
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {sourceTable : List (Nat × Func)}
    {line : Line} {tail : Func} {final : Devm}
    {n : Ninst} {stepPre stepPost : Devm} {slot : Xlot}
    (cursor : frame.CompiledCursor dp ca fs sourceTable
      (line +++ tail) final)
    (notSwept : ∀ m ∈ line, m ≠ n)
    (occurrence : frame.NinstOccurrenceFromCursor cursor n
      stepPre stepPost slot) :
    ∃ tailCursor : frame.CompiledCursor dp ca fs sourceTable tail final,
      Line.Run frame.sevm cursor.pre line tailCursor.pre ∧
      frame.NinstOccurrenceFromCursor tailCursor n
        stepPre stepPost slot := by
  induction line with
  | nil => exact ⟨cursor, .nil, occurrence⟩
  | cons source line ih =>
      change frame.CompiledCursor dp ca fs sourceTable
        (.next source (line +++ tail)) final at cursor
      have sourceNotSwept : source ≠ n := notSwept source (by simp)
      rcases cursor.ninstOccurrence_next_ne sourceNotSwept occurrence with
        ⟨nextCursor, sourceSlot, sourceOccurrence, remaining⟩
      rcases ih nextCursor (fun m hm => notSwept m (by simp [hm]))
          remaining with
        ⟨tailCursor, tailRun, retained⟩
      exact ⟨tailCursor, .cons sourceOccurrence.run tailRun, retained⟩

/-! ## Frame entry

The runtime's leading `JUMPDEST` is the only instruction between the retained
frame root and the main body cursor, and a `Jinst` position hosts no `Ninst`
at all — so this step, too, is generic in `n`. -/

/-- Main-entry cursor with the hidden leading `JUMPDEST` retained both as an
explicit non-swept prefix and as its silence certificate. -/
private theorem Exec.Frame.compiledMainCursorWithNonSweptPrefix
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame} {n : Ninst}
    (context : frame.AuthenticContext dp ca) :
    ∃ cursor : frame.CompiledCursor dp ca
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux))
        (weth10 dp).main frame.post,
      Devm.DispatchSilent frame.pre cursor.pre ∧
      Exec.Deriv.ParentNonNinstPrefix dp ca n
        ⟨frame.pc, frame.sevm, frame.pre, frame.out, frame.run⟩
        ⟨cursor.pc, frame.sevm, cursor.pre, frame.out, cursor.current⟩ := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have hcode := context.invocation.2.2.2
      have hcompiled := Prog.runCompiled_of_exec e pre (weth10 dp) post
        (weth10_pcFree dp) run hcode
      rcases hcompiled with ⟨compiledMid, hcompiledBurn, hmain⟩
      have hget :
          (table 0 (((weth10 dp).main) :: weth10Aux))[0]? =
            some (0, (weth10 dp).main) := rfl
      rcases subcode_of_get?_eq_some hcode hget with
        ⟨jumpdestAt, sourceSlice⟩
      have sourceBoundary : noPushBefore e.code 1 32 = true :=
        (Prog.jumpable_of_get?_table hcode hget).2
      rcases jumpdest_at_exact run jumpdestAt with
        ⟨actualMid, continuation, hburn, hgas, _prec⟩
      have midEq : actualMid = compiledMid :=
        Devm.eq_of_burnBy
          (Devm.BurnBy.of_burn hburn hgas)
          hcompiledBurn
      subst compiledMid
      have entryStep : Evm.step ⟨0, e, pre⟩ = .cont 1 actualMid :=
        Evm.jumpdest_cont jumpdestAt
          (Devm.BurnBy.of_burn hburn hgas)
      have runEq : run = .cont entryStep continuation := Exec.unique _ _
      have entryEdge : Exec.Deriv.ParentStepActions dp ca
          ⟨1, e, actualMid, .ok post, continuation⟩
          ⟨0, e, pre, .ok post, run⟩ [] := by
        rw [runEq]
        exact .cont entryStep continuation
      have entryPrefix : Exec.Deriv.ParentPrefixActions dp ca
          ⟨0, e, pre, .ok post, run⟩
          ⟨1, e, actualMid, .ok post, continuation⟩ [] :=
        .step entryEdge (.refl _)
      let cursor : Exec.Frame.CompiledCursor dp ca
          ⟨0, e, pre, .ok post, run, committed⟩
          ((weth10 dp).main :: weth10Aux)
          (table 0 ((weth10 dp).main :: weth10Aux))
          (weth10 dp).main post :=
        ⟨1, actualMid, continuation, [], entryPrefix, hmain,
          sourceSlice, sourceBoundary⟩
      have notSwept : ¬ Ninst.At e.code 0 n :=
        fun sweptAt => Ninst.At.false_of_jinstAt sweptAt jumpdestAt
      exact ⟨cursor,
        Devm.DispatchSilent.of_burnBy (Devm.BurnBy.of_burn hburn hgas),
        .step entryEdge notSwept (.refl _)⟩

/-- An arbitrary actual instruction occurrence in an authentic committed frame
is retained by the compiled main-body cursor, whose pre-state still carries
the frame's entry observations. -/
theorem Exec.Frame.ninstOccurrence_fromMainCursor
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {n : Ninst} {stepPre stepPost : Devm} {slot : Xlot}
    (occurrence : frame.NinstOccurrence dp ca n stepPre stepPost slot)
    (context : frame.AuthenticContext dp ca) :
    ∃ mainCursor : frame.CompiledCursor dp ca
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux))
        (weth10 dp).main frame.post,
      Devm.DispatchSilent frame.pre mainCursor.pre ∧
      frame.NinstOccurrenceFromCursor mainCursor n
        stepPre stepPost slot := by
  rcases frame.compiledMainCursorWithNonSweptPrefix (n := n) context with
    ⟨mainCursor, silent, entryPrefix⟩
  have fromRoot : frame.NinstOccurrenceFromDeriv dp ca
      ⟨frame.pc, frame.sevm, frame.pre, frame.out, frame.run⟩
      n stepPre stepPost slot := occurrence
  exact ⟨mainCursor, silent, entryPrefix.trim_ninstOccurrence fromRoot⟩

/-! ## Dispatch spine -/

private theorem ninst_pushB256_ne_reg (word : B256) (r : Rinst) :
    Ninst.pushB256 word ≠ .reg r := by
  simp [Ninst.pushB256]

/-- The first source branch is selected from the actual calldata-size flag,
and the arbitrary occurrence is retained in exactly the dispatch or receive
arm chosen by that flag.  Neither arm's entry disturbs the observations. -/
theorem Exec.Frame.CompiledCursor.regOccurrence_main
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {r : Rinst} {stepPre stepPost : Devm} {slot : Xlot}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (weth10 dp).main frame.post)
    (entryFree : ∀ m ∈ [Ninst.calldatasize, Ninst.iszero], m ≠ .reg r)
    (occurrence : frame.NinstOccurrenceFromCursor cursor
      (.reg r) stepPre stepPost slot) :
    (∃ dispatchCursor : frame.CompiledCursor dp ca
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux))
        (fsig +++ dispatchWith fallbackSlot (weth10Tree dp)) frame.post,
      frame.sevm.data.length.toB256 ≠ 0 ∧
      Devm.DispatchSilent cursor.pre dispatchCursor.pre ∧
      frame.NinstOccurrenceFromCursor dispatchCursor (.reg r)
        stepPre stepPost slot) ∨
    (∃ receiveCursor : frame.CompiledCursor dp ca
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux))
        receiveEther frame.post,
      frame.sevm.data.length.toB256 = 0 ∧
      Devm.DispatchSilent cursor.pre receiveCursor.pre ∧
      frame.NinstOccurrenceFromCursor receiveCursor (.reg r)
        stepPre stepPost slot) := by
  unfold weth10 weth10Main at cursor
  change frame.CompiledCursor dp ca
    (weth10Main dp :: weth10Aux)
    (table 0 (weth10Main dp :: weth10Aux))
    ([Ninst.calldatasize, Ninst.iszero] +++
      (.branch (fsig +++ dispatchWith fallbackSlot (weth10Tree dp))
        receiveEther)) frame.post at cursor
  rcases cursor.ninstOccurrence_after_line entryFree occurrence with
    ⟨branchCursor, entryRun, atBranch⟩
  have entrySilent := Devm.DispatchSilent.of_entryFlag entryRun
  have flagPrefix :
      [frame.sevm.data.length.toB256 =? 0] <<+
        branchCursor.pre.stack := by
    rcases Line.of_run_cons entryRun with
      ⟨afterSize, sizeStep, restSize⟩
    rcases Line.of_run_cons restSize with
      ⟨afterZero, zeroStep, emptyLine⟩
    cases emptyLine
    have sizePrefix : [frame.sevm.data.length.toB256] <<+
        afterSize.stack :=
      prefix_of_push (of_run_calldatasize sizeStep) nil_pref
    exact prefix_of_iszero zeroStep sizePrefix
  rcases branchCursor.regOccurrence_branch atBranch with
    ⟨dispatchCursor, pop, inside⟩ |
      ⟨flag, nonzero, receiveCursor, pop, inside⟩
  · have zeroPrefix : [(0 : B256)] <<+ branchCursor.pre.stack :=
      pref_of_split pop.stack
    have flagEq : (frame.sevm.data.length.toB256 =? 0) = 0 :=
      pref_head_unique flagPrefix zeroPrefix
    have nonempty : frame.sevm.data.length.toB256 ≠ 0 := by
      intro empty
      rw [empty] at flagEq
      simp [B256.eqCheck] at flagEq
      exact (by decide : (1 : B256) ≠ 0) flagEq
    exact Or.inl ⟨dispatchCursor, nonempty,
      entrySilent.trans (Devm.DispatchSilent.of_popBurnBy pop), inside⟩
  · have selectedPrefix : [flag] <<+ branchCursor.pre.stack :=
      pref_of_split pop.stack
    have flagEq : (frame.sevm.data.length.toB256 =? 0) = flag :=
      pref_head_unique flagPrefix selectedPrefix
    have empty : frame.sevm.data.length.toB256 = 0 := by
      by_contra nonempty
      have checkZero : (frame.sevm.data.length.toB256 =? 0) = 0 := by
        simp [B256.eqCheck, nonempty]
      apply nonzero
      rw [← flagEq]
      exact checkZero
    exact Or.inr ⟨receiveCursor, empty,
      entrySilent.trans (Devm.DispatchSilent.of_popBurnBy pop), inside⟩

/-- Reverse traversal of generated dispatch syntax.  The exact selector word
is threaded on the live stack; compiler branch flags decide the recursive tree
arm, and a matched leaf proves selector equality, retention of the arbitrary
occurrence in that leaf's body, and silence of the whole comparison walk.

The fallback leaf is killed by the *semantic* certificate `fallbackFree`
rather than by a Boolean freeness test, which is what lets one spine serve
both the `SSTORE` and the `SLOAD` halves. -/
theorem Exec.Frame.CompiledCursor.regOccurrence_dispatchWith :
    ∀ {tree : DispatchTree} {sig : B256} {stack : Stack}
      {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
      {f₀ : Func} {aux : List Func} {k : Nat}
      {fallback : Func} {final stepPre stepPost : Devm}
      {r : Rinst} {slot : Xlot},
      (cursor : frame.CompiledCursor dp ca (f₀ :: aux)
        (table 0 (f₀ :: aux)) (dispatchWith k tree) final) →
      some frame.sevm.code.toList = Prog.compile ⟨f₀, aux⟩ →
      (f₀ :: aux)[k]? = some fallback →
      (∀ fallbackCursor : frame.CompiledCursor dp ca (f₀ :: aux)
          (table 0 (f₀ :: aux)) fallback final,
        frame.NinstOccurrenceFromCursor fallbackCursor (.reg r)
          stepPre stepPost slot → False) →
      (∀ m ∈ [Ninst.dup 0, Ninst.eq, Ninst.gt], m ≠ .reg r) →
      sig :: stack <<+ cursor.pre.stack →
      frame.NinstOccurrenceFromCursor cursor (.reg r)
        stepPre stepPost slot →
      ∃ body : Func, (sig, body) ∈ tree ∧
        ∃ bodyCursor : frame.CompiledCursor dp ca (f₀ :: aux)
            (table 0 (f₀ :: aux)) body final,
          stack <<+ bodyCursor.pre.stack ∧
          Devm.DispatchSilent cursor.pre bodyCursor.pre ∧
          frame.NinstOccurrenceFromCursor bodyCursor (.reg r)
            stepPre stepPost slot := by
  intro tree
  induction tree with
  | leaf word body =>
      intro sig stack dp ca frame f₀ aux k fallback final
        stepPre stepPost r slot cursor hcode fallbackLookup fallbackFree
        glueFree selectorPrefix occurrence
      rcases cursor.ninstOccurrence_after_line
          (line := [Ninst.pushB256 word, Ninst.eq])
          (tail := .branch (.call k) body)
          (by
            intro m hm
            rcases List.mem_cons.1 hm with rfl | hm
            · exact ninst_pushB256_ne_reg word r
            · rcases List.mem_cons.1 hm with rfl | hm
              · exact glueFree _ (by simp)
              · cases hm)
          occurrence with
        ⟨branchCursor, compareRun, atBranch⟩
      have compareSilent := Devm.DispatchSilent.of_pushEq compareRun
      have flagPrefix : (word =? sig) :: stack <<+
          branchCursor.pre.stack := by
        rcases Line.of_run_cons compareRun with
          ⟨afterPush, pushStep, restPush⟩
        rcases Line.of_run_cons restPush with
          ⟨afterEq, eqStep, emptyLine⟩
        cases emptyLine
        have pushed : word :: sig :: stack <<+ afterPush.stack := by
          simpa using prefix_of_push
            (of_run_pushB256 pushStep) selectorPrefix
        exact prefix_of_eq eqStep pushed
      rcases branchCursor.regOccurrence_branch atBranch with
        ⟨fallbackCursor, pop, insideFallback⟩ |
          ⟨flag, nonzero, bodyCursor, pop, insideBody⟩
      · rcases fallbackCursor.regOccurrence_call hcode insideFallback with
          ⟨actualFallback, actualLookup, fallbackBodyCursor,
            insideFallbackBody⟩
        have fallbackEq : actualFallback = fallback :=
          Option.some.inj (actualLookup.symm.trans fallbackLookup)
        subst actualFallback
        exact (fallbackFree fallbackBodyCursor insideFallbackBody).elim
      · have bodyStack : stack <<+ bodyCursor.pre.stack :=
          prefix_of_pop
            ⟨flag, Devm.PopBurn.of_popBurnBy pop⟩ flagPrefix
        have selectedPrefix : [flag] <<+ branchCursor.pre.stack :=
          pref_of_split pop.stack
        have flagEq : (word =? sig) = flag :=
          pref_head_unique flagPrefix selectedPrefix
        have wordEq : word = sig := by
          by_contra different
          have checkZero : (word =? sig) = 0 := by
            simp [B256.eqCheck, different]
          apply nonzero
          rw [← flagEq]
          exact checkZero
        subst sig
        exact ⟨body, rfl, bodyCursor, bodyStack,
          compareSilent.trans (Devm.DispatchSilent.of_popBurnBy pop),
          insideBody⟩
  | fork left right ihLeft ihRight =>
      intro sig stack dp ca frame f₀ aux k fallback final
        stepPre stepPost r slot cursor hcode fallbackLookup fallbackFree
        glueFree selectorPrefix occurrence
      rcases cursor.ninstOccurrence_after_line
          (line := [Ninst.dup 0, Ninst.pushB256 (leftmostFsig right),
            Ninst.gt])
          (tail := .branch (dispatchWith k right) (dispatchWith k left))
          (by
            intro m hm
            rcases List.mem_cons.1 hm with rfl | hm
            · exact glueFree _ (by simp)
            · rcases List.mem_cons.1 hm with rfl | hm
              · exact ninst_pushB256_ne_reg _ r
              · rcases List.mem_cons.1 hm with rfl | hm
                · exact glueFree _ (by simp)
                · cases hm)
          occurrence with
        ⟨branchCursor, compareRun, atBranch⟩
      have compareSilent := Devm.DispatchSilent.of_dupPushGt compareRun
      have flagPrefix :
          (leftmostFsig right >? sig) :: sig :: stack <<+
            branchCursor.pre.stack := by
        rcases Line.of_run_cons compareRun with
          ⟨afterDup, dupStep, restDup⟩
        rcases Line.of_run_cons restDup with
          ⟨afterPush, pushStep, restPush⟩
        rcases Line.of_run_cons restPush with
          ⟨afterGt, gtStep, emptyLine⟩
        cases emptyLine
        have duplicated : sig :: sig :: stack <<+ afterDup.stack :=
          prefix_of_dup_val dupStep (by show_nth) selectorPrefix
        have pushed : leftmostFsig right :: sig :: sig :: stack <<+
            afterPush.stack := by
          simpa using prefix_of_push
            (of_run_pushB256 pushStep) duplicated
        exact prefix_of_gt gtStep pushed
      rcases branchCursor.regOccurrence_branch atBranch with
        ⟨rightCursor, pop, insideRight⟩ |
          ⟨flag, nonzero, leftCursor, pop, insideLeft⟩
      · have rightStack : sig :: stack <<+ rightCursor.pre.stack :=
          prefix_of_pop
            ⟨0, Devm.PopBurn.of_popBurnBy pop⟩ flagPrefix
        rcases ihRight rightCursor hcode fallbackLookup fallbackFree
            glueFree rightStack insideRight with
          ⟨body, member, bodyCursor, bodyStack, bodySilent, insideBody⟩
        exact ⟨body, Or.inr member, bodyCursor, bodyStack,
          compareSilent.trans
            ((Devm.DispatchSilent.of_popBurnBy pop).trans bodySilent),
          insideBody⟩
      · have leftStack : sig :: stack <<+ leftCursor.pre.stack :=
          prefix_of_pop
            ⟨flag, Devm.PopBurn.of_popBurnBy pop⟩ flagPrefix
        rcases ihLeft leftCursor hcode fallbackLookup fallbackFree
            glueFree leftStack insideLeft with
          ⟨body, member, bodyCursor, bodyStack, bodySilent, insideBody⟩
        exact ⟨body, Or.inl member, bodyCursor, bodyStack,
          compareSilent.trans
            ((Devm.DispatchSilent.of_popBurnBy pop).trans bodySilent),
          insideBody⟩

/-- A retained non-receive occurrence reaches the exact source body selected
by the live calldata selector, together with the dispatcher's silence.  Unlike
the ordinary forward dispatch theorem, the returned cursor retains the
arbitrary occurrence selected by the caller. -/
theorem Exec.Frame.CompiledCursor.regOccurrence_selectorBody
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {r : Rinst} {stepPre stepPost : Devm} {slot : Xlot}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (weth10 dp).main frame.post)
    (context : frame.AuthenticContext dp ca)
    (nonempty : frame.sevm.data.length.toB256 ≠ 0)
    (entryFree : ∀ m ∈ [Ninst.calldatasize, Ninst.iszero], m ≠ .reg r)
    (fsigFree : ∀ m ∈ fsig, m ≠ .reg r)
    (glueFree : ∀ m ∈ [Ninst.dup 0, Ninst.eq, Ninst.gt], m ≠ .reg r)
    (fallbackFree : ∀ fallbackCursor : frame.CompiledCursor dp ca
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux)) Func.rev frame.post,
      frame.NinstOccurrenceFromCursor fallbackCursor (.reg r)
        stepPre stepPost slot → False)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg r) stepPre stepPost slot) :
    ∃ body : Func,
      (Sevm.selector frame.sevm, body) ∈ weth10Funcs dp ∧
      ∃ bodyCursor : frame.CompiledCursor dp ca
          ((weth10 dp).main :: weth10Aux)
          (table 0 ((weth10 dp).main :: weth10Aux)) body frame.post,
        [] <<+ bodyCursor.pre.stack ∧
        Devm.DispatchSilent cursor.pre bodyCursor.pre ∧
        frame.NinstOccurrenceFromCursor bodyCursor (.reg r)
          stepPre stepPost slot := by
  rcases cursor.regOccurrence_main entryFree fromCursor with
    ⟨dispatchPrefixCursor, _selectedNonempty, mainSilent, insideDispatch⟩ |
      ⟨_receiveCursor, selectedEmpty, _receiveSilent, _insideReceive⟩
  · rcases dispatchPrefixCursor.ninstOccurrence_after_line
        (line := fsig)
        (tail := dispatchWith fallbackSlot (weth10Tree dp))
        fsigFree insideDispatch with
      ⟨dispatchCursor, fsigRun, insideTree⟩
    have fsigSilent := Devm.DispatchSilent.of_fsig fsigRun
    have selectorPrefix : Sevm.selector frame.sevm :: [] <<+
        dispatchCursor.pre.stack :=
      prefix_of_fsig nil_pref fsigRun
    have fallbackLookup :
        (((weth10 dp).main :: weth10Aux)[fallbackSlot]?) =
          some Func.rev := by
      simp [fallbackSlot, weth10, weth10Aux]
    rcases dispatchCursor.regOccurrence_dispatchWith
        context.invocation.2.2.2 fallbackLookup fallbackFree glueFree
        selectorPrefix insideTree with
      ⟨body, treeMember, bodyCursor, bodyStack, treeSilent, insideBody⟩
    have listMember :
        (Sevm.selector frame.sevm, body) ∈ weth10Funcs dp :=
      DispatchTree.mem_of_mem_ofSorted
        (by simp [weth10Funcs]) (by simpa [weth10Tree] using treeMember)
    exact ⟨body, listMember, bodyCursor, bodyStack,
      mainSilent.trans (fsigSilent.trans treeSilent), insideBody⟩
  · exact (nonempty selectedEmpty).elim

/-- Strip the generated nonpayable guard while retaining an arbitrary
occurrence and the guard's silence.  The rejecting arm is discharged by the
caller's semantic certificate, so this step needs no compile witness and no
freeness Boolean. -/
theorem Exec.Frame.CompiledCursor.regOccurrence_nonpayable
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {sourceTable : List (Nat × Func)}
    {body : Func} {final stepPre stepPost : Devm}
    {r : Rinst} {slot : Xlot}
    (cursor : frame.CompiledCursor dp ca fs sourceTable
      (nonpayable body) final)
    (guardFree : ∀ m ∈ [Ninst.callvalue, Ninst.iszero], m ≠ .reg r)
    (revertFree : ∀ revertCursor : frame.CompiledCursor dp ca fs
        sourceTable Func.rev final,
      frame.NinstOccurrenceFromCursor revertCursor (.reg r)
        stepPre stepPost slot → False)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg r) stepPre stepPost slot) :
    ∃ bodyCursor : frame.CompiledCursor dp ca fs sourceTable body final,
      Devm.DispatchSilent cursor.pre bodyCursor.pre ∧
      frame.NinstOccurrenceFromCursor bodyCursor (.reg r)
        stepPre stepPost slot := by
  rcases cursor.ninstOccurrence_after_line
      (line := [Ninst.callvalue, Ninst.iszero])
      (tail := .branch Func.rev body)
      guardFree fromCursor with
    ⟨branchCursor, guardRun, atBranch⟩
  have guardSilent := Devm.DispatchSilent.of_callvalueFlag guardRun
  rcases branchCursor.regOccurrence_branch atBranch with
    ⟨revertCursor, pop, insideRevert⟩ |
      ⟨flag, _nonzero, bodyCursor, pop, insideBody⟩
  · exact (revertFree revertCursor insideRevert).elim
  · exact ⟨bodyCursor,
      guardSilent.trans (Devm.DispatchSilent.of_popBurnBy pop), insideBody⟩

/-- The nonpayable wrapper hosts no occurrence at all when its guarded body
hosts none. -/
theorem Exec.Frame.CompiledCursor.no_regOccurrence_nonpayable
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {sourceTable : List (Nat × Func)}
    {body : Func} {final stepPre stepPost : Devm}
    {r : Rinst} {slot : Xlot}
    (cursor : frame.CompiledCursor dp ca fs sourceTable
      (nonpayable body) final)
    (guardFree : ∀ m ∈ [Ninst.callvalue, Ninst.iszero], m ≠ .reg r)
    (revertFree : ∀ revertCursor : frame.CompiledCursor dp ca fs
        sourceTable Func.rev final,
      frame.NinstOccurrenceFromCursor revertCursor (.reg r)
        stepPre stepPost slot → False)
    (bodyFree : ∀ bodyCursor : frame.CompiledCursor dp ca fs
        sourceTable body final,
      frame.NinstOccurrenceFromCursor bodyCursor (.reg r)
        stepPre stepPost slot → False)
    (occurrence : frame.NinstOccurrenceFromCursor cursor
      (.reg r) stepPre stepPost slot) : False := by
  rcases cursor.regOccurrence_nonpayable guardFree revertFree occurrence with
    ⟨bodyCursor, _silent, insideBody⟩
  exact bodyFree bodyCursor insideBody

/-! ## Ready-made fallback certificates

The two instantiations both halves of the allowance obligation need: the
generated revert body hosts neither an `SSTORE` nor an `SLOAD`, so it
discharges `fallbackFree` and `revertFree` directly. -/

theorem Exec.Frame.CompiledCursor.no_sstoreOccurrence_rev
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {f₀ : Func} {aux : List Func} {final stepPre stepPost : Devm}
    {slot : Xlot}
    (hcode : some frame.sevm.code.toList = Prog.compile ⟨f₀, aux⟩)
    (cursor : frame.CompiledCursor dp ca (f₀ :: aux)
      (table 0 (f₀ :: aux)) Func.rev final)
    (occurrence : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot) : False :=
  cursor.no_sstoreOccurrence_of_free (fuel := 4) hcode rfl occurrence

theorem Exec.Frame.CompiledCursor.no_sloadOccurrence_rev
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {f₀ : Func} {aux : List Func} {final stepPre stepPost : Devm}
    {slot : Xlot}
    (hcode : some frame.sevm.code.toList = Prog.compile ⟨f₀, aux⟩)
    (cursor : frame.CompiledCursor dp ca (f₀ :: aux)
      (table 0 (f₀ :: aux)) Func.rev final)
    (occurrence : frame.NinstOccurrenceFromCursor cursor
      (.reg .sload) stepPre stepPost slot) : False :=
  cursor.no_sloadOccurrence_of_free (fuel := 4) hcode rfl occurrence

/-! ## Entry point

The whole spine, from an arbitrary actual register occurrence in an authentic
committed frame to the selector body that hosts it, with the dispatcher's
silence relating the body cursor's pre-state to the frame's entry state. -/

/-- An actual `.reg r` occurrence in an authentic committed non-receive frame
lies inside the exact listed selector body, whose pre-state still carries the
frame's entry state, memory, logs and output. -/
theorem Exec.Frame.regOccurrence_selectorBodyFromFrame
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {r : Rinst} {stepPre stepPost : Devm} {slot : Xlot}
    (occurrence : frame.NinstOccurrence dp ca (.reg r)
      stepPre stepPost slot)
    (context : frame.AuthenticContext dp ca)
    (nonempty : frame.sevm.data.length.toB256 ≠ 0)
    (entryFree : ∀ m ∈ [Ninst.calldatasize, Ninst.iszero], m ≠ .reg r)
    (fsigFree : ∀ m ∈ fsig, m ≠ .reg r)
    (glueFree : ∀ m ∈ [Ninst.dup 0, Ninst.eq, Ninst.gt], m ≠ .reg r)
    (fallbackFree : ∀ fallbackCursor : frame.CompiledCursor dp ca
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux)) Func.rev frame.post,
      frame.NinstOccurrenceFromCursor fallbackCursor (.reg r)
        stepPre stepPost slot → False) :
    ∃ body : Func,
      (Sevm.selector frame.sevm, body) ∈ weth10Funcs dp ∧
      ∃ bodyCursor : frame.CompiledCursor dp ca
          ((weth10 dp).main :: weth10Aux)
          (table 0 ((weth10 dp).main :: weth10Aux)) body frame.post,
        [] <<+ bodyCursor.pre.stack ∧
        Devm.DispatchSilent frame.pre bodyCursor.pre ∧
        frame.NinstOccurrenceFromCursor bodyCursor (.reg r)
          stepPre stepPost slot := by
  rcases frame.ninstOccurrence_fromMainCursor occurrence context with
    ⟨mainCursor, entrySilent, fromMain⟩
  rcases mainCursor.regOccurrence_selectorBody context nonempty
      entryFree fsigFree glueFree fallbackFree fromMain with
    ⟨body, listMember, bodyCursor, bodyStack, bodySilent, insideBody⟩
  exact ⟨body, listMember, bodyCursor, bodyStack,
    entrySilent.trans bodySilent, insideBody⟩

end Weth10

end Blanc
