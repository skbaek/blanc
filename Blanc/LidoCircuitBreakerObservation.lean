import Blanc.LidoCircuitBreakerCallBoundary

/-!
# What the CircuitBreaker does with the target's answer

The call-boundary module proved what `pauseAfterSet` **sends**: two messages,
both fully determined by the CircuitBreaker, for an arbitrary target carrying
arbitrary bytecode.  It stopped at the observation's edge and deliberately said
nothing about the answer.

This module says what the CircuitBreaker does with that answer, and it says it
for an **arbitrary** answer.

## The bar every statement here is held to

Every instruction in the decode reads **memory**, and the honest theorem is
about the **child's output**.  `MLOAD 0` pushes whatever the observation's
resume happened to leave at offset zero; a decode stated against that word is
trivially true of any program whatsoever and proves nothing about the target.

So each outcome below is indexed to `pausedAnswer child.output` — a projection
of the child's returned bytes, defined without reference to any machine state —
and the equality between that projection and what `loadWord 0` pushes is a
*theorem* (`pauseDecode_loadWord_eq_answer`), not a definition.

The short-return arm is the one place where no such projection exists.  When
the child returns fewer than 32 bytes the resume writes only those bytes, so
memory `[0, 32)` holds a mixture of the child's answer and whatever the
CircuitBreaker staged there earlier.  The length guard is what makes that
mixture unreachable, and outcome 4 is therefore decided on
`child.output.length` alone: **no premise about the CircuitBreaker's prior
memory, and no conclusion about the mixed word.**

## What this module does not claim

* **Accepting `1` is not evidence that the target is paused.**  A target that
  returns `1` without pausing is accepted, by construction; the CircuitBreaker
  cannot check it, and neither can any theorem here.  Every statement below is
  about the CircuitBreaker's **decision procedure**, never about the truth of
  the answer that procedure reads.  The differential manifest carries this case
  under the tag `target-truth-not-guaranteed`.
* **`isStatic = true` is still not a no-write theorem.**  It remains a property
  of the message the CircuitBreaker builds.  A static-context no-write theorem
  over arbitrary code does not exist in Jaune or Blanc and is not built here.
* **Nothing about liveness.**  These classify derivations that *reach* a
  result; no arm is claimed to be reached in any particular run, out-of-gas
  legs are carried explicitly rather than assumed away, and the published
  callback-visible liveness counterexample stands unchanged.
* **Nothing about Solidity.**  Source-exactness of the seven statuses rests on
  the port claim in `PORTING.md` and on differential rows against the pinned
  EELS oracle, not on any theorem in this repository.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune

/-! ## The answer, as a projection of the child's output

`pausedAnswer` is a function of **bytes**.  It cannot depend on the
CircuitBreaker's memory, its stack, or the enclosing frame, because none of
them is in scope.  That is the whole point: it is the object every outcome
below is indexed to, and `pauseDecode_loadWord_eq_answer` is what connects it
to the instruction that actually runs.

The shape is fmint's, whose callback pins its magic word the same way
(`Blanc/FlashSpec.lean`). -/

/-- The word the CircuitBreaker decodes out of an `isPaused()` answer: the
answer's first 32 bytes, zero-padded, read big-endian. -/
def pausedAnswer (out : Bytes) : B256 := Bytes.toB256 (out.sliceD 0 32 0)

/-! ## The 32-byte return window

The observation's resume writes `child.output.take 32` at offset zero, so the
window it can disturb is at most `[0, 32)`.  Two consequences, and the second
is as important as the first. -/

/-- **Any word staged at offset 32 or beyond survives the observation,
whatever the child returned.**

No premise constrains the callee, and none could help: the bound is
`(child.output.take 32).length ≤ 32`, which holds of every list without knowing
anything about it.  The next cut consumes this to carry the target and duration
words — at byte offsets 512 and 736 — through the observation and into
`pauseSuccess`. -/
theorem pauseStat_stagedWord_survives {sevm : Sevm} {target : Adr}
    {statPre statPost : Devm} {offset : Nat} {w : B256}
    (boundary : PauseStatBoundary sevm target statPre statPost)
    (h_past : 32 ≤ offset)
    (window : MemWordAt statPre offset w) :
    MemWordAt statPost offset w := by
  obtain ⟨parent, child, msg, xl, delegated, code, gasWord, childGas,
    -, -, hpmem, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hsmem, -, -⟩ := boundary
  have hmem : statPost.memory =
      (statPre.memory.extends [(0x11c, 4), (0, 32)]).write 0
        (child.output.take 32) := by rw [hsmem, hpmem]
  refine MemWordAt.acrossExtendsWrite hmem (Or.inr ?_) window
  have hlen : (child.output.take 32).length ≤ 32 := by
    simp [List.length_take]
  omega

/-- **The converse, and the reason `pauseSuccess` re-stages memory word zero.**

Whatever the child returned, the bytes the observation leaves at offset zero
are the child's own — the window is *clobbered*, not preserved.  A word staged
at offset zero before the observation therefore survives only if it already
equalled the answer, which is not something the CircuitBreaker can arrange.

Stated at the child's own length rather than at 32, so that it is true on the
short-return arm too: exactly `child.output.take 32` of the window is the
child's answer and the remainder is stale.  That mixture is what the length
guard exists to make unreachable, and it is why no statement below reads the
word on the short arm. -/
theorem pauseStat_window_holdsAnswer {sevm : Sevm} {target : Adr}
    {statPre statPost : Devm}
    (boundary : PauseStatBoundary sevm target statPre statPost) :
    ∃ child : Devm,
      statPost.returnData = child.output ∧
      (child.output ≠ [] →
        (statPost.memory.read 0 (child.output.take 32).length).1 =
          child.output.take 32) := by
  obtain ⟨parent, child, msg, xl, delegated, code, gasWord, childGas,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hsmem, hrd, -⟩ := boundary
  refine ⟨child, hrd, fun hne => ?_⟩
  rw [hsmem]
  exact Mem.read_write_zero parent.memory (by
    intro h
    exact hne (by simpa using h))

/-! ## Walking the observation's branch

The four inverters below are the shapes every arm theorem in this module
consumes.  They are stated **public** here deliberately: four modules
(`Blanc/RevertPayload.lean`, `Blanc/LidoCircuitBreakerPauseRoute.lean`,
`Blanc/LidoCircuitBreakerPauseSuffix.lean` and
`Blanc/LidoCircuitBreakerCallBoundary.lean`) each carry a private copy of the
`.next` inverter, and the predecessor cut recorded that duplication as debt
rather than adding to a module carrying a baselined elaboration row.  This
module is new, so it can be the public home instead of the fifth private
copy. -/

/-- `Func.RunCompiledTo` at a `.next` node. -/
theorem runCompiledTo_next_inv {fs : List Func} {sevm : Sevm}
    {devm : Devm} {i : Ninst} {f : Func} {ex : Execution}
    (h : Func.RunCompiledTo fs sevm devm (Func.next i f) ex) :
    ∃ mid, Ninst.RunCompiled sevm devm i mid ∧
      Func.RunCompiledTo fs sevm mid f ex := by
  cases h with | next hn hrest => exact ⟨_, hn, hrest⟩

/-- `Func.RunCompiledTo` at a `.branch` node: the word the branch pops decides
the arm, and the two arms are named by the word rather than by fiat. -/
theorem runCompiledTo_branch_inv {fs : List Func} {sevm : Sevm}
    {devm : Devm} {f g : Func} {ex : Execution}
    (h : Func.RunCompiledTo fs sevm devm (Func.branch f g) ex) :
    (∃ armPre, devm.stack = 0 :: armPre.stack ∧
        Devm.PopBurnBy [0] (gVerylow + gHigh) devm armPre ∧
        Func.RunCompiledTo fs sevm armPre f ex) ∨
      (∃ (w : B256) (armPre : Devm), w ≠ 0 ∧
        devm.stack = w :: armPre.stack ∧
        Devm.PopBurnBy [w] (gVerylow + gHigh + gJumpdest) devm armPre ∧
        Func.RunCompiledTo fs sevm armPre g ex) := by
  cases h with
  | zero hroom hpop harm => exact Or.inl ⟨_, hpop.stack, hpop, harm⟩
  | succ hne hroom hpop harm =>
    exact Or.inr ⟨_, _, hne, hpop.stack, hpop, harm⟩

/-- `Func.RunCompiledTo` at a `.call` node, against a known table entry. -/
theorem runCompiledTo_call_inv {fs : List Func} {sevm : Sevm}
    {devm : Devm} {k : Nat} {f : Func} {ex : Execution}
    (h_get : fs[k]? = some f)
    (h : Func.RunCompiledTo fs sevm devm (Func.call k) ex) :
    ∃ mid, Devm.BurnBy (gVerylow + gMid + gJumpdest) devm mid ∧
      Func.RunCompiledTo fs sevm mid f ex := by
  cases h with
  | call hget hroom hburn hrest =>
    cases Option.some.inj (hget.symm.trans h_get)
    exact ⟨_, hburn, hrest⟩

/-- A walk of a `Line`-prefixed body splits at the line's end. -/
theorem runCompiledTo_prepend_inv {fs : List Func} {sevm : Sevm}
    {l : Line} {f : Func} {ex : Execution} :
    ∀ {devm : Devm}, Func.RunCompiledTo fs sevm devm (l +++ f) ex →
      ∃ mid, Line.Run sevm devm l mid ∧
        Func.RunCompiledTo fs sevm mid f ex := by
  induction l with
  | nil => exact fun h => ⟨_, Line.Run.nil, h⟩
  | cons i l ih =>
    intro devm h
    obtain ⟨mid, hn, hrest⟩ := runCompiledTo_next_inv h
    obtain ⟨fin, hline, hf⟩ := ih hrest
    exact ⟨fin, Line.Run.cons (Ninst.Run.of_runCompiled hn) hline, hf⟩

/-- `ISZERO` at a known stack top: the word it pushes, the tail it leaves, and
the memory and return data it does not touch.  The memory conjunct is what the
predecessor's otherwise identical private copy lacks, and this module needs it:
the decode's `MLOAD` runs downstream of this instruction and must still read
the memory `PauseStatBoundary` describes. -/
theorem iszero_stack_inv {sevm : Sevm} {pre post : Devm} {w : B256}
    {rest : List B256}
    (run : Ninst.RunCompiled sevm pre Ninst.iszero post)
    (h_stk : pre.stack = w :: rest) :
    post.stack = (w =? 0) :: rest ∧ post.memory = pre.memory ∧
      post.returnData = pre.returnData := by
  rcases of_run_reg (Ninst.Run.of_runCompiled run) with ⟨pc, hrun⟩
  simp only [Rinst.run, Rinst.runCore] at hrun
  obtain ⟨x, hdiff⟩ := Devm.diffBurn_of_applyUnary hrun
  obtain ⟨mid, hpop, hpush⟩ := hdiff.stack
  have hpop' : w :: rest = x :: mid := by rw [← h_stk]; exact hpop
  injection hpop' with hw hrest
  subst hw
  subst hrest
  exact ⟨hpush, hdiff.memory.symm, hdiff.returnData.symm⟩

/-! ## The observation's two arms

`pauseAfterSet` runs the STATICCALL's flag through `ISZERO` before its branch
reads it, exactly as it does after the CALL.  So the bubble is the arm the
**failing** observation reaches and the decode is the **successful** one, and
which of the two a derivation took is settled by `child.error.isSome` — a fact
about the child that is *produced* here, never assumed. -/

/-- **The pause's post-observation branch, inverted: both arms.**

The continuation `g` is arbitrary; the program's own instance is
`decodePausedResult`.  No premise constrains the callee: `child.error.isSome`
is not assumed on either side, it is produced together with the arm the
derivation actually took.  The state entering either arm still carries the
observation's returndata **and** the memory `PauseStatBoundary` describes,
which is what lets the decode below read the child's answer rather than the
CircuitBreaker's stale bytes. -/
theorem pauseObservation_arms {fs : List Func} {sevm : Sevm} {target : Adr}
    {statPre statPost : Devm} {ex : Execution} {g : Func}
    (boundary : PauseStatBoundary sevm target statPre statPost)
    (run : Func.RunCompiledTo fs sevm statPost
      (Ninst.iszero ::: ((Func.call bubbleRevertSlot) <?> g)) ex) :
    ∃ (child armPre : Devm) (rest : List B256) (μ : Mem),
      statPost.stack = (if child.error.isSome then 0 else 1) :: rest ∧
      statPost.returnData = child.output ∧
      armPre.returnData = child.output ∧
      armPre.memory = μ.write 0 (child.output.take 32) ∧
      ((child.error.isSome = true ∧
          Func.RunCompiledTo fs sevm armPre (Func.call bubbleRevertSlot) ex) ∨
        (child.error.isSome = false ∧
          Func.RunCompiledTo fs sevm armPre g ex)) := by
  obtain ⟨parent, child, msg, xl, delegated, code, gasWord, childGas,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hsmem, hrd, hstk⟩ := boundary
  obtain ⟨mid, hn, hrest⟩ := runCompiledTo_next_inv run
  obtain ⟨hmidstk, hmidmem, hmidrd⟩ := iszero_stack_inv hn hstk
  rcases runCompiledTo_branch_inv hrest with
    ⟨armPre, hmid0, hpop, harm⟩ | ⟨w, armPre, hne, hmidw, hpop, harm⟩
  · -- the branch popped `0`: the `ISZERO` inverted a `1`, so the child succeeded
    have hw : ((if child.error.isSome then (0 : B256) else 1) =? 0) = 0 := by
      rw [hmidstk] at hmid0
      exact (List.cons.inj hmid0).1
    refine ⟨child, armPre, parent.stack, parent.memory, hstk, hrd,
      (hpop.returnData.symm.trans hmidrd).trans hrd,
      ((hpop.memory.symm.trans hmidmem).trans hsmem), Or.inr ⟨?_, harm⟩⟩
    revert hw
    cases hc : child.error.isSome
    · intro; rfl
    · intro h; exact absurd h (by decide)
  · -- the branch popped a nonzero word: the `ISZERO` inverted a `0`
    have hw : ((if child.error.isSome then (0 : B256) else 1) =? 0) = w := by
      rw [hmidstk] at hmidw
      exact (List.cons.inj hmidw).1
    refine ⟨child, armPre, parent.stack, parent.memory, hstk, hrd,
      (hpop.returnData.symm.trans hmidrd).trans hrd,
      ((hpop.memory.symm.trans hmidmem).trans hsmem), Or.inl ⟨?_, harm⟩⟩
    revert hw hne
    cases hc : child.error.isSome
    · intro hne hw; exact absurd (hw.symm.trans (by decide)) hne
    · intro _ _; rfl

/-! ## Outcome 3: a failing observation bubbles **its own** returndata

The distinction the name insists on is the whole content of this section.  Both
of `pauseAfterSet`'s bubbles are the same one-line body at the same table slot,
so nothing in the program text says which call's answer comes back out.  What
settles it is *which* boundary relation the arm is downstream of: the child
below is `PauseStatBoundary`'s, so `child.output` is what the **`isPaused()`
STATICCALL** returned, and the `pauseFor` CALL's returndata was overwritten by
the observation before this arm was reached. -/

/-- **The observation's failure arm reaches the bubble, holding the
observation's returndata.**

`h_fail` is the case hypothesis, discharged by a caller that has a flag, never
by an assumption about how the target behaves; `pauseObservation_arms` shows
the two arms exhaust the possibilities. -/
theorem pauseObservation_failureArm_bubbles {fs : List Func} {sevm : Sevm}
    {target : Adr} {statPre statPost : Devm} {ex : Execution} {g : Func}
    (h_bubble : fs[bubbleRevertSlot]? = some Func.revReturnData)
    (boundary : PauseStatBoundary sevm target statPre statPost)
    (h_fail : statPost.stack.head? = some 0)
    (run : Func.RunCompiledTo fs sevm statPost
      (Ninst.iszero ::: ((Func.call bubbleRevertSlot) <?> g)) ex) :
    ∃ child bubblePre : Devm,
      child.error.isSome = true ∧
      statPost.returnData = child.output ∧
      bubblePre.returnData = child.output ∧
      Func.RunCompiledTo fs sevm bubblePre Func.revReturnData ex := by
  obtain ⟨child, armPre, rest, μ, hstk, hrd, hard, -, harm⟩ :=
    pauseObservation_arms boundary run
  rcases harm with ⟨herr, hcall⟩ | ⟨herr, -⟩
  · obtain ⟨bubblePre, hburn, hbody⟩ := runCompiledTo_call_inv h_bubble hcall
    exact ⟨child, bubblePre, herr, hrd,
      (hburn.returnData.symm.trans hard), hbody⟩
  · exfalso
    rw [hstk, herr] at h_fail
    exact absurd (Option.some.inj h_fail) (by decide)

/-- **Outcome 3's payload: the bytes the failing observation returned.**

The two-leg disjunction is the predecessor's and is not removable here either:
without `memory.size % 32 = 0` the `REVERT`'s own memory-expansion charge is not
provably zero, so no honest inequality in `gasLeft` alone refutes the
out-of-gas leg.  Carrying it explicitly is the point — assuming it away would
be a liveness claim this cut does not make.

The output is stated raw, at the `B256` round trip of the returndata's length,
because that is what `RETURNDATACOPY` copies.  Reading it as `child.output`
needs `child.output.length < 2 ^ 256`, which is an invariant of every `Devm`
reachable under `Exec` rather than a fact about this edge, and belongs
upstream. -/
theorem pauseObservation_failureArm_payload {fs : List Func} {sevm : Sevm}
    {target : Adr} {statPre statPost : Devm} {ex : Execution} {g : Func}
    (h_bubble : fs[bubbleRevertSlot]? = some Func.revReturnData)
    (boundary : PauseStatBoundary sevm target statPre statPost)
    (h_fail : statPost.stack.head? = some 0)
    (run : Func.RunCompiledTo fs sevm statPost
      (Ninst.iszero ::: ((Func.call bubbleRevertSlot) <?> g)) ex) :
    ∃ child : Devm,
      child.error.isSome = true ∧
      statPost.returnData = child.output ∧
      ((∃ d, ex = .error (.halt (.outOfGas .none), d)) ∨
        (∃ post, ex = .error (.revert, post) ∧
          post.output =
            child.output.take child.output.length.toB256.toNat)) := by
  obtain ⟨child, bubblePre, herr, hrd, hard, hbody⟩ :=
    pauseObservation_failureArm_bubbles h_bubble boundary h_fail run
  refine ⟨child, herr, hrd, ?_⟩
  rcases Func.runCompiledTo_revReturnData_inv hbody with
    h_oog | ⟨post, hpost, hout⟩
  · exact Or.inl h_oog
  · exact Or.inr ⟨post, hpost, by rw [hout, hard]⟩

/-- **The observation's success arm reaches the decode.**  The sibling of
`pauseObservation_failureArm_bubbles`, and the entry point of everything
below: the state the decode starts from still carries the child's returndata
and the memory the observation's resume wrote. -/
theorem pauseObservation_successArm_reachesDecode {fs : List Func}
    {sevm : Sevm} {target : Adr} {statPre statPost : Devm} {ex : Execution}
    (boundary : PauseStatBoundary sevm target statPre statPost)
    (h_ok : statPost.stack.head? = some 1)
    (run : Func.RunCompiledTo fs sevm statPost
      (Ninst.iszero :::
        ((Func.call bubbleRevertSlot) <?> decodePausedResult)) ex) :
    ∃ (child decodePre : Devm) (μ : Mem),
      child.error.isSome = false ∧
      decodePre.returnData = child.output ∧
      decodePre.memory = μ.write 0 (child.output.take 32) ∧
      Func.RunCompiledTo fs sevm decodePre decodePausedResult ex := by
  obtain ⟨child, armPre, rest, μ, hstk, hrd, hard, hamem, harm⟩ :=
    pauseObservation_arms boundary run
  rcases harm with ⟨herr, -⟩ | ⟨herr, hdec⟩
  · exfalso
    rw [hstk, herr] at h_ok
    exact absurd (Option.some.inj h_ok) (by decide)
  · exact ⟨child, armPre, μ, herr, hard, hamem, hdec⟩

/-! ## The decode

`decodePausedResult` checks the answer's **length** before it reads any of it,
and that ordering is the whole argument for why the word it later reads is the
child's.  The section follows the program's order: length, then load, then the
zero test, then the canonical-`1` test.

### The flag words, as facts about the answer

`retdataShorterThan 32` pushes `ltCheck (length.toB256) 32`, so the guard's
flag is a function of `child.output.length` and of nothing else.  Two of the
three implications between that flag and the plain inequality are unconditional
and are the only two used below:

* `length < 32` forces the flag, because `Nat.toB256` is injective well below
  `2 ^ 256`; and
* a cleared flag forces `32 ≤ length`, by contraposition of the same fact.

The third — `32 ≤ length` forcing a cleared flag — is **false** for a list of
length `2 ^ 256` or more, which no execution can produce but the type does not
exclude. It is not used, and no theorem here needs a bounded-output premise as
a result. -/

private lemma ltCheck_ne_zero {a b : B256} (h : (a <? b) ≠ 0) : a < b := by
  unfold B256.ltCheck at h
  split at h
  · assumption
  · exact absurd rfl h

private lemma not_lt_of_ltCheck_eq_zero {a b : B256} (h : (a <? b) = 0) :
    ¬ a < b := by
  unfold B256.ltCheck at h
  split at h
  · exact absurd h (by decide)
  · assumption

private lemma eqCheck_ne_zero {a b : B256} (h : (a =? b) ≠ 0) : a = b := by
  unfold B256.eqCheck at h
  split at h
  · assumption
  · exact absurd rfl h

private lemma ne_of_eqCheck_eq_zero {a b : B256} (h : (a =? b) = 0) :
    a ≠ b := by
  unfold B256.eqCheck at h
  split at h
  · exact absurd h (by decide)
  · assumption

/-- A short answer sets the guard's flag. -/
lemma toB256_lt_32_of_lt {n : Nat} (h : n < 32) :
    (Nat.toB256 n) < (32 : B256) := by
  rw [B256.lt_iff_toNat_lt_toNat,
    B256.toNat_toB256_of_lt (by omega),
    show ((32 : B256)).toNat = 32 from rfl]
  exact h

/-- A cleared guard flag forces a full word of answer.  The contrapositive of
`toB256_lt_32_of_lt`, and the step that lets everything downstream read the
child's first word without any premise about the CircuitBreaker's memory. -/
lemma le_length_of_not_toB256_lt_32 {n : Nat}
    (h : ¬ (Nat.toB256 n) < (32 : B256)) : 32 ≤ n := by
  by_contra hlt
  exact h (toB256_lt_32_of_lt (by omega))

/-! ### The load

`loadWord 0` reads the observation's own 32-byte return window.  The word it
pushes is the child's, and proving that needs **no** memory image and **no**
well-formedness premise: `Mem.read_write_zero` reads a write back at offset
zero on the strength of the write alone, because each branch of `Mem.write`
allocates enough backing array for its own payload.  That is what makes D4 a
statement about `child.output` rather than about whatever the CircuitBreaker
had staged. -/

/-- `MLOAD` at offset zero against a memory that is a 32-byte write at offset
zero: the pushed word is that payload's, whatever the memory held before. -/
private lemma prefix_of_mload_write_zero {e : Sevm} {xs : Stack}
    {s s' : Devm} {μ : Mem} {ys : Bytes}
    (h0 : Ninst.Run e s Ninst.mload s') (h1 : (0 : B256) :: xs <<+ s.stack)
    (hmem : s.memory = μ.write 0 ys) (hlen : ys.length = 32) :
    (Bytes.toB256 ys :: xs <<+ s'.stack) ∧ s'.returnData = s.returnData := by
  rcases of_run_mload_val h0 with ⟨x', ⟨stk, h2, h3⟩, hm, hrd⟩
  have hx : (0 : B256) = x' :=
    (List.of_cons_pref_of_cons_pref h1 (pref_of_split h2)).left
  subst hx
  have heq : (s.memory.read ((0 : B256)).toNat 32).1 = ys := by
    rw [hmem, show ((0 : B256)).toNat = 0 from rfl, ← hlen]
    exact Mem.read_write_zero μ (by
      intro hnil
      rw [hnil] at hlen
      exact absurd hlen (by decide))
  rw [heq] at h3
  exact ⟨append_pref h3 (of_append_pref h2 h1), hrd⟩

/-- **D4: what `loadWord 0` pushes is the child's answer.**

The equality this cut exists to prove.  `pausedAnswer child.output` is defined
without reference to any machine state; this says the instruction that actually
runs pushes exactly that, given only the memory shape
`PauseStatBoundary` hands back and a full word of answer.  `μ` — the
CircuitBreaker's memory before the observation — is universally quantified and
appears in no hypothesis beyond the write itself, so nothing here is true only
of a cooperative callee or of a particular staging history. -/
theorem pauseDecode_loadWord_eq_answer {sevm : Sevm} {s s' : Devm} {μ : Mem}
    {out : Bytes} {xs : Stack}
    (h_mem : s.memory = μ.write 0 (out.take 32))
    (h_long : 32 ≤ out.length)
    (hp : xs <<+ s.stack)
    (run : Line.Run sevm s (loadWord 0) s') :
    (pausedAnswer out :: xs <<+ s'.stack) ∧ s'.returnData = s.returnData := by
  have hlen : (out.take 32).length = 32 := by
    rw [List.length_take]; omega
  have hslice : out.take 32 = out.sliceD 0 32 0 := by
    unfold List.sliceD
    rw [List.drop_zero, List.takeD_eq_take _ (by omega)]
  rcases Line.of_run_cons run with ⟨u1, q1, run⟩
  have hb1 := of_run_pushB256 q1
  have hp1 : (0 : B256) :: xs <<+ u1.stack := by
    have h := prefix_of_push hb1 hp
    rwa [show ((0 : B256) * 32) = (0 : B256) from by decide] at h
  rcases Line.of_run_cons run with ⟨u2, q2, hnil⟩
  cases hnil
  have hm1 : u1.memory = μ.write 0 (out.take 32) := by
    rw [← hb1.memory]; exact h_mem
  obtain ⟨hstk, hrd⟩ :=
    prefix_of_mload_write_zero q2 hp1 hm1 hlen
  refine ⟨?_, hrd.trans hb1.returnData.symm⟩
  rw [pausedAnswer, ← hslice]
  exact hstk

/-! ### The four-way classification

One walk of `decodePausedResult`, in the order the program checks: length,
then load, then the zero test, then the canonical-`1` test.  Following that
order is what satisfies the universality bar *by construction* — the length is
settled before anything reads the word, which is exactly the argument for why
the word the load pushes is the child's.

Every condition below is a function of the answer's bytes alone.  `μ` — the
CircuitBreaker's memory before the observation — is universally quantified and
constrained by nothing, so no clause is true only of a particular staging
history, and the short-return arm draws **no** conclusion about the word at
offset zero. -/

/-- **The decode's four outcomes, for an arbitrary answer.**

Reading the disjuncts: a short answer reverts empty without the word ever being
read; a full word of `0` reaches the `PauseFailed()` slot; a full word that is
neither `0` nor `1` reverts empty; and a full word of `1` reaches
`pauseSuccess`.

**No length equality appears anywhere on the accepting path.**  The last
disjunct asks for `32 ≤ out.length`, never `= 32`, so an answer of `1` followed
by any tail whatsoever is accepted — which is the behaviour the differential
rows measure against the oracle at tails from one byte up to 65 504.

The first disjunct's condition is the guard's own flag, `Nat.toB256
out.length < 32`, rather than `out.length < 32`.  The two agree on every answer
an execution can produce and differ only at a length of `2 ^ 256` or more;
`toB256_lt_32_of_lt` converts the plain inequality into it, and
`pauseDecode_shortReturn` below states outcome 4 in the plain form.  Stating it
this way is what lets every other disjunct avoid a bounded-output premise. -/
theorem pauseDecode_arms {fs : List Func} {sevm : Sevm} {decodePre : Devm}
    {μ : Mem} {out : Bytes} {ex : Execution}
    (h_mem : decodePre.memory = μ.write 0 (out.take 32))
    (h_rd : decodePre.returnData = out)
    (run : Func.RunCompiledTo fs sevm decodePre decodePausedResult ex) :
    ∃ armPre : Devm,
      ((Nat.toB256 out.length < (32 : B256) ∧
          Func.RunCompiledTo fs sevm armPre (Func.call emptyRevertSlot) ex) ∨
        (¬ Nat.toB256 out.length < (32 : B256) ∧ 32 ≤ out.length ∧
          pausedAnswer out = 0 ∧
          Func.RunCompiledTo fs sevm armPre
            (Func.call pauseFailedErrorSlot) ex) ∨
        (¬ Nat.toB256 out.length < (32 : B256) ∧ 32 ≤ out.length ∧
          pausedAnswer out ≠ 0 ∧ pausedAnswer out ≠ 1 ∧
          Func.RunCompiledTo fs sevm armPre (Func.call emptyRevertSlot) ex) ∨
        (¬ Nat.toB256 out.length < (32 : B256) ∧ 32 ≤ out.length ∧
          pausedAnswer out = 1 ∧
          Func.RunCompiledTo fs sevm armPre pauseSuccess ex)) := by
  rw [decodePausedResult] at run
  obtain ⟨s1, hguard, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨hflag, hs1mem, -⟩ := of_retdataShorterThan_val nil_pref hguard
  rw [h_rd] at hflag
  rcases runCompiledTo_branch_inv run with
    ⟨armPre, hz, hpop, harm⟩ | ⟨w, armPre, hne, hwstk, hpop, harm⟩
  · -- the flag was clear: at least a full word came back
    have hflag0 : (Nat.toB256 out.length <? (32 : B256)) = 0 := by
      obtain ⟨t, ht⟩ := hflag
      rw [ht] at hz
      exact (List.cons.inj hz).1
    have hnotshort : ¬ Nat.toB256 out.length < (32 : B256) :=
      not_lt_of_ltCheck_eq_zero hflag0
    have hlong : 32 ≤ out.length := le_length_of_not_toB256_lt_32 hnotshort
    have hmem2 : armPre.memory = μ.write 0 (out.take 32) := by
      rw [← hpop.memory, hs1mem, h_mem]
    -- the load: the word is the child's answer
    obtain ⟨s2, hload, run⟩ := runCompiledTo_prepend_inv harm
    obtain ⟨hans, -⟩ :=
      pauseDecode_loadWord_eq_answer hmem2 hlong nil_pref hload
    -- `DUP` preserves it for the later `EQ`, `ISZERO` tests it
    obtain ⟨s3, hdup, run⟩ := runCompiledTo_next_inv run
    have hdupp : pausedAnswer out :: [pausedAnswer out] <<+ s3.stack :=
      prefix_of_dup_val (Ninst.Run.of_runCompiled hdup) (by show_nth) hans
    obtain ⟨s4, hiz, run⟩ := runCompiledTo_next_inv run
    have hizp := prefix_of_iszero (Ninst.Run.of_runCompiled hiz) hdupp
    rcases runCompiledTo_branch_inv run with
      ⟨armPre2, hz2, hpop2, harm2⟩ | ⟨w2, armPre2, hne2, hw2, hpop2, harm2⟩
    · -- the answer is nonzero: on to the canonical test
      have hzc : (pausedAnswer out =? 0) = 0 := by
        obtain ⟨t, ht⟩ := hizp
        rw [ht] at hz2
        exact (List.cons.inj hz2).1
      have hne0 : pausedAnswer out ≠ 0 := ne_of_eqCheck_eq_zero hzc
      have hrest : [pausedAnswer out] <<+ armPre2.stack := by
        rw [hzc] at hizp
        exact of_append_pref hpop2.stack hizp
      obtain ⟨s5, hpush1, run⟩ := runCompiledTo_next_inv harm2
      have hp5 := prefix_of_push
        (of_run_pushB256 (Ninst.Run.of_runCompiled hpush1)) hrest
      obtain ⟨s6, heq, run⟩ := runCompiledTo_next_inv run
      have hp6 := prefix_of_eq (Ninst.Run.of_runCompiled heq) hp5
      rcases runCompiledTo_branch_inv run with
        ⟨armPre3, hz3, hpop3, harm3⟩ | ⟨w3, armPre3, hne3, hw3, hpop3, harm3⟩
      · -- neither `0` nor `1`: the empty revert
        have hec : ((1 : B256) =? pausedAnswer out) = 0 := by
          obtain ⟨t, ht⟩ := hp6
          rw [ht] at hz3
          exact (List.cons.inj hz3).1
        exact ⟨armPre3, Or.inr (Or.inr (Or.inl
          ⟨hnotshort, hlong, hne0,
            fun h => (ne_of_eqCheck_eq_zero hec) h.symm, harm3⟩))⟩
      · -- the canonical `1`: `pauseSuccess`
        have hec : ((1 : B256) =? pausedAnswer out) = w3 := by
          obtain ⟨t, ht⟩ := hp6
          rw [ht] at hw3
          exact (List.cons.inj hw3).1
        refine ⟨armPre3,
          Or.inr (Or.inr (Or.inr ⟨hnotshort, hlong, ?_, harm3⟩))⟩
        exact (eqCheck_ne_zero (fun h => hne3 (hec.symm.trans h))).symm
    · -- the answer is zero: `PauseFailed()`
      have hzc : (pausedAnswer out =? 0) = w2 := by
        obtain ⟨t, ht⟩ := hizp
        rw [ht] at hw2
        exact (List.cons.inj hw2).1
      exact ⟨armPre2, Or.inr (Or.inl
        ⟨hnotshort, hlong,
          eqCheck_ne_zero (fun h => hne2 (hzc.symm.trans h)), harm2⟩)⟩
  · -- the flag was set: fewer than 32 bytes came back, and nothing read a word
    have hflagw : (Nat.toB256 out.length <? (32 : B256)) = w := by
      obtain ⟨t, ht⟩ := hflag
      rw [ht] at hwstk
      exact (List.cons.inj hwstk).1
    exact ⟨armPre, Or.inl
      ⟨ltCheck_ne_zero (fun h => hne (hflagw.symm.trans h)), harm⟩⟩

/-! ## What the three revert arms output

Three of the decode's four outcomes end in a revert, and two of them end in the
*same* body — `emptyRevertSlot`'s `Func.rev`.  Neither that body nor
`pauseFailedErrorSlot`'s `Func.revSelector` had a payload inversion anywhere in
the repository: only the construction direction existed, which builds a revert
from an exact gas premise rather than reading one out of an arbitrary
derivation.  Both are supplied here.

The two differ in one respect that matters.  `Func.rev`'s `REVERT` window is
`(0, 0)`, and `Devm.extCost_empty_window` prices a zero-size window at zero
unconditionally, so its charge can never be refused and its inversion has **no
out-of-gas leg**.  `Func.revSelector`'s window is `(28, 4)`, whose expansion is
free only once memory is known to be word-aligned and at least 32 bytes wide;
alignment is a fact about the CircuitBreaker's prior memory that an arbitrary
derivation does not carry, so that inversion keeps the explicit out-of-gas
disjunct the predecessor's bubble payload also keeps. -/

/-- `Func.RunCompiledTo` at a `.last` node. -/
theorem runCompiledTo_last_inv {fs : List Func} {sevm : Sevm} {devm : Devm}
    {l : Linst} {ex : Execution}
    (h : Func.RunCompiledTo fs sevm devm (Func.last l) ex) :
    Linst.Run sevm devm l ex := by
  cases h with | last h => exact h

/-- `REVERT` over a `(0, 0)` window, inverted with no gas premise: the charge
for a zero-size window is zero, so the halt branch is unreachable and the
payload is empty. -/
private lemma of_run_rev_empty {sevm : Sevm} {devm : Devm} {s : List B256}
    {ex : Execution}
    (h_stk : devm.stack = (0 : B256) :: (0 : B256) :: s)
    (h_run : Linst.Run sevm devm .rev ex) :
    ∃ post, ex = .error (.revert, post) ∧ post.output = [] := by
  have h_eq : Linst.run sevm devm .rev = ex := h_run
  have h_gas : devm.extCost
      [⟨((0 : B256)).toNat, ((0 : B256)).toNat⟩] ≤ devm.gasLeft := by
    rw [show ((0 : B256)).toNat = 0 from rfl, Devm.extCost_empty_window]
    exact Nat.zero_le _
  refine ⟨_, h_eq.symm.trans (Linst.run_rev_eq_error h_stk h_gas rfl), ?_⟩
  show (devm.memory.read ((0 : B256)).toNat ((0 : B256)).toNat).1 = []
  rfl

/-- **`Func.rev` reverts with an empty payload, from an arbitrary walk.**  No
gas premise, no memory premise, and no out-of-gas disjunct. -/
theorem runCompiledTo_rev_inv {fs : List Func} {sevm : Sevm} {devm : Devm}
    {ex : Execution} (run : Func.RunCompiledTo fs sevm devm Func.rev ex) :
    ∃ post, ex = .error (.revert, post) ∧ post.output = [] := by
  rw [Func.rev] at run
  obtain ⟨d1, r1, run⟩ := runCompiledTo_next_inv run
  obtain ⟨d2, r2, run⟩ := runCompiledTo_next_inv run
  have hrev := runCompiledTo_last_inv run
  have p1 := of_run_pushB256 (Ninst.Run.of_runCompiled r1)
  have p2 := of_run_pushB256 (Ninst.Run.of_runCompiled r2)
  have hstk : d2.stack = (0 : B256) :: (0 : B256) :: devm.stack := by
    rw [p2.stack, p1.stack]; rfl
  exact of_run_rev_empty hstk hrev

/-- `REVERT` over a window whose two operands are known, inverted.  Both are
present, so neither pop can underflow, and the window's own expansion charge is
the walk's last chance to fail: either it does and the frame settles at an
out-of-gas halt, or the payload is the window read out of the frame's memory. -/
private lemma of_run_rev_window {sevm : Sevm} {devm : Devm} {i sz : B256}
    {s : List B256} {ex : Execution}
    (h_stk : devm.stack = i :: sz :: s)
    (h_run : Linst.Run sevm devm .rev ex) :
    (∃ d, ex = .error (.halt (.outOfGas .none), d)) ∨
      (∃ post, ex = .error (.revert, post) ∧
        post.output = (devm.memory.read i.toNat sz.toNat).1) := by
  have h_eq : Linst.run sevm devm .rev = ex := h_run
  rcases Nat.lt_or_ge devm.gasLeft (devm.extCost [⟨i.toNat, sz.toNat⟩])
    with h_gas | h_gas
  · have h_oog : Linst.run sevm devm .rev
        = .error ⟨.halt (.outOfGas .none),
            devm.setMach ⟨s, devm.memory, devm.gasLeft⟩⟩ := by
      show (do
        let ⟨index, d⟩ ← devm.popToNat
        let ⟨size, d⟩ ← d.popToNat
        let cost := d.extCost [⟨index, size⟩]
        let d ← chargeGas cost d
        let ⟨output, d⟩ := d.memRead index size
        let d := d.withOutput output
        Except.error ⟨.revert, d⟩) = _
      rw [Devm.popToNat_eq_ok h_stk]
      simp only [bind, Except.bind]
      rw [Devm.popToNat_eq_ok
        (devm := devm.setMach ⟨sz :: s, devm.memory, devm.gasLeft⟩) rfl]
      simp only [Devm.setMach_setMach, Devm.memory_setMach,
        Devm.gasLeft_setMach]
      have h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
          [⟨i.toNat, sz.toNat⟩] = devm.extCost [⟨i.toNat, sz.toNat⟩] := rfl
      rw [h_ext]
      have hcg : chargeGas (devm.extCost [⟨i.toNat, sz.toNat⟩])
          (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) =
            .error ⟨.halt (.outOfGas .none),
              devm.setMach ⟨s, devm.memory, devm.gasLeft⟩⟩ := by
        rw [chargeGas_def]
        have hs : safeSub (devm.setMach
            ⟨s, devm.memory, devm.gasLeft⟩).gasLeft
            (devm.extCost [⟨i.toNat, sz.toNat⟩]) = none := by
          unfold safeSub
          rw [if_neg (by simp only [Devm.gasLeft_setMach]; omega)]
        rw [hs]
      rw [hcg]
    exact Or.inl ⟨_, h_eq.symm.trans h_oog⟩
  · exact Or.inr ⟨_, h_eq.symm.trans (Linst.run_rev_eq_error h_stk h_gas rfl),
      rfl⟩

/-- The tail of a 32-byte word written at offset zero, read straight back.  No
well-formedness premise and no memory image: `Mem.read_write_zero` supplies the
whole window, and the four selector bytes are its last four. -/
private lemma read_selector_of_write_zero {μ : Mem} {ys : Bytes}
    (h : ys.length = 32) :
    ((μ.write 0 ys).read 28 4).1 = ys.drop 28 := by
  have hne : ys ≠ [] := by
    intro hn; rw [hn] at h; exact absurd h (by decide)
  have hfull := Mem.read_write_zero μ hne
  rw [h] at hfull
  have hshift : ∀ M : Mem, (M.read 28 4).1 = ((M.read 0 32).1).drop 28 := by
    intro M
    show Array.sliceD M.data 28 4 0 = (Array.sliceD M.data 0 32 0).drop 28
    rw [Array.sliceD_eq_map, Array.sliceD_eq_map]
    rfl
  rw [hshift, hfull]

/-- The selector word's low four bytes are the selector.  Re-derived here
because `Blanc/RevertPayload.lean`'s version is private. -/
private lemma toBytes_toB256_drop28 (data : Bytes) (h : data.length = 4) :
    data.toB256.toBytes.drop 28 = data := by
  have hp := Bytes.toBytes_toB256_of_length
    (xs := List.replicate 28 0 ++ data) (by simp [h])
  exact (by
    simpa [Bytes.toB256_zero_cons] using congrArg (List.drop 28) hp)

/-- **`Func.revSelector` reverts with exactly its four bytes, from an arbitrary
walk.**  The out-of-gas leg stays explicit: the `REVERT`'s `(28, 4)` window
expands for free only once memory is word-aligned and at least 32 bytes wide,
and alignment is a property of the CircuitBreaker's prior memory that an
arbitrary derivation does not carry.  Assuming it away would turn a payload
statement into a liveness claim. -/
theorem runCompiledTo_revSelector_inv {fs : List Func} {sevm : Sevm}
    {devm : Devm} {data : Bytes} {hlen : data.length = 4} {ex : Execution}
    (run : Func.RunCompiledTo fs sevm devm (Func.revSelector data hlen) ex) :
    (∃ d, ex = .error (.halt (.outOfGas .none), d)) ∨
      (∃ post, ex = .error (.revert, post) ∧ post.output = data) := by
  rw [Func.revSelector] at run
  obtain ⟨d1, r1, run⟩ := runCompiledTo_next_inv run
  obtain ⟨d2, r2, run⟩ := runCompiledTo_next_inv run
  obtain ⟨d3, r3, run⟩ := runCompiledTo_next_inv run
  obtain ⟨d4, r4, run⟩ := runCompiledTo_next_inv run
  obtain ⟨d5, r5, run⟩ := runCompiledTo_next_inv run
  have hrev := runCompiledTo_last_inv run
  have p1 := of_run_push (Ninst.Run.of_runCompiled r1)
  have p2 := of_run_pushB256 (Ninst.Run.of_runCompiled r2)
  have hp2 := prefix_of_push p2 (prefix_of_push p1 nil_pref)
  obtain ⟨-, hm3⟩ :=
    prefix_of_mstore_val (Ninst.Run.of_runCompiled r3) hp2
  have p4 := of_run_pushB256 (Ninst.Run.of_runCompiled r4)
  have p5 := of_run_pushB256 (Ninst.Run.of_runCompiled r5)
  have hm5 : d5.memory = d2.memory.write 0 data.toB256.toBytes := by
    rw [← p5.memory, ← p4.memory, hm3]; rfl
  have hstk5 : d5.stack = (28 : B256) :: (4 : B256) :: d3.stack := by
    rw [p5.stack, p4.stack]; rfl
  rcases of_run_rev_window hstk5 hrev with h_oog | ⟨post, hpost, hout⟩
  · exact Or.inl h_oog
  · refine Or.inr ⟨post, hpost, ?_⟩
    rw [hout, hm5,
      show ((28 : B256)).toNat = 28 from rfl,
      show ((4 : B256)).toNat = 4 from rfl,
      read_selector_of_write_zero (B256.length_toBytes _),
      toBytes_toB256_drop28 data hlen]

/-! ## The six outcomes, each with its reached slot and its exact payload

The table lookups below are discharged by the CircuitBreaker's own program, so
the statements are about *whatever* the table binds at those slots and a
witness settles it against the program actually running. -/

/-- The CircuitBreaker's table binds `emptyRevertSlot` to the zero-length
revert. -/
theorem runtime_emptyRevertSlot (dp : DeployParams) :
    ((runtime dp).main :: (runtime dp).aux)[emptyRevertSlot]? =
      some Func.rev := rfl

/-- The CircuitBreaker's table binds `pauseFailedErrorSlot` to
`PauseFailed()`'s named-error reverter. -/
theorem runtime_pauseFailedErrorSlot (dp : DeployParams) :
    ((runtime dp).main :: (runtime dp).aux)[pauseFailedErrorSlot]? =
      some pauseFailedError := rfl

/-- **Outcome 4: an answer shorter than a word reverts empty.**

D3 in its plain form: the hypothesis is `out.length < 32` and nothing else.
There is **no premise about the CircuitBreaker's memory before the
observation** — `μ` is universally quantified — and **no conclusion about the
word at offset zero**, because below 32 bytes that window holds a mixture of
the answer and whatever was staged earlier and no projection of the answer
names it.  The length guard is what makes the mixture unreachable, and this is
the theorem that shows it. -/
theorem pauseDecode_shortReturn_payload {fs : List Func} {sevm : Sevm}
    {decodePre : Devm} {μ : Mem} {out : Bytes} {ex : Execution}
    (h_empty : fs[emptyRevertSlot]? = some Func.rev)
    (h_mem : decodePre.memory = μ.write 0 (out.take 32))
    (h_rd : decodePre.returnData = out)
    (h_short : out.length < 32)
    (run : Func.RunCompiledTo fs sevm decodePre decodePausedResult ex) :
    ∃ post, ex = .error (.revert, post) ∧ post.output = [] := by
  obtain ⟨armPre, harm⟩ := pauseDecode_arms h_mem h_rd run
  have hshort : Nat.toB256 out.length < (32 : B256) :=
    toB256_lt_32_of_lt h_short
  rcases harm with ⟨-, hcall⟩ | ⟨hns, -⟩ | ⟨hns, -⟩ | ⟨hns, -⟩
  · obtain ⟨mid, -, hbody⟩ := runCompiledTo_call_inv h_empty hcall
    exact runCompiledTo_rev_inv hbody
  · exact absurd hshort hns
  · exact absurd hshort hns
  · exact absurd hshort hns

/-- **Outcome 5: a returned `false` reverts with `PauseFailed()`'s four
bytes.**

The out-of-gas leg is explicit, for the reason
`runCompiledTo_revSelector_inv` records.  `h_flag` is the guard's own verdict
on the answer — a function of its length — and is what
`pauseDecode_arms` produces on the arm that reads the word at all. -/
theorem pauseDecode_false_payload {fs : List Func} {sevm : Sevm}
    {decodePre : Devm} {μ : Mem} {out : Bytes} {ex : Execution}
    (h_failed : fs[pauseFailedErrorSlot]? = some pauseFailedError)
    (h_mem : decodePre.memory = μ.write 0 (out.take 32))
    (h_rd : decodePre.returnData = out)
    (h_flag : ¬ Nat.toB256 out.length < (32 : B256))
    (h_zero : pausedAnswer out = 0)
    (run : Func.RunCompiledTo fs sevm decodePre decodePausedResult ex) :
    (∃ d, ex = .error (.halt (.outOfGas .none), d)) ∨
      (∃ post, ex = .error (.revert, post) ∧
        post.output = customErrorData "PauseFailed") := by
  obtain ⟨armPre, harm⟩ := pauseDecode_arms h_mem h_rd run
  rcases harm with ⟨hs, -⟩ | ⟨-, -, -, hcall⟩ | ⟨-, -, hne0, -⟩ |
    ⟨-, -, hone, -⟩
  · exact absurd hs h_flag
  · obtain ⟨mid, -, hbody⟩ := runCompiledTo_call_inv h_failed hcall
    rw [show pauseFailedError =
      Func.revSelector (customErrorData "PauseFailed")
        (by simp [customErrorData, B256.length_toBytes]) from rfl] at hbody
    exact runCompiledTo_revSelector_inv hbody
  · exact absurd h_zero hne0
  · exact absurd (h_zero.symm.trans hone) (by decide)

/-- **Outcome 6: a word that is neither `0` nor `1` reverts empty.**

`false` has a named status and `true` is accepted; every other bit pattern is
rejected without one.  The differential rows measure this against the oracle at
`2`; the theorem covers every other word. -/
theorem pauseDecode_noncanonical_payload {fs : List Func} {sevm : Sevm}
    {decodePre : Devm} {μ : Mem} {out : Bytes} {ex : Execution}
    (h_empty : fs[emptyRevertSlot]? = some Func.rev)
    (h_mem : decodePre.memory = μ.write 0 (out.take 32))
    (h_rd : decodePre.returnData = out)
    (h_flag : ¬ Nat.toB256 out.length < (32 : B256))
    (h_ne0 : pausedAnswer out ≠ 0)
    (h_ne1 : pausedAnswer out ≠ 1)
    (run : Func.RunCompiledTo fs sevm decodePre decodePausedResult ex) :
    ∃ post, ex = .error (.revert, post) ∧ post.output = [] := by
  obtain ⟨armPre, harm⟩ := pauseDecode_arms h_mem h_rd run
  rcases harm with ⟨hs, -⟩ | ⟨-, -, hzero, -⟩ | ⟨-, -, -, -, hcall⟩ |
    ⟨-, -, hone, -⟩
  · exact absurd hs h_flag
  · exact absurd hzero h_ne0
  · obtain ⟨mid, -, hbody⟩ := runCompiledTo_call_inv h_empty hcall
    exact runCompiledTo_rev_inv hbody
  · exact absurd hone h_ne1

/-- **Outcome 7: a canonical `1` reaches `pauseSuccess`.**

What this does **not** say is the point of the module's header: reaching
`pauseSuccess` is not evidence that the target is paused.  A target that
returns `1` without pausing is accepted, by construction, and the
CircuitBreaker has no way to check it.  Nor does this say the pause completes —
the walk is handed on as a walk, and everything `pauseSuccess` does is the next
cut's business. -/
theorem pauseDecode_accepts_one {fs : List Func} {sevm : Sevm}
    {decodePre : Devm} {μ : Mem} {out : Bytes} {ex : Execution}
    (h_mem : decodePre.memory = μ.write 0 (out.take 32))
    (h_rd : decodePre.returnData = out)
    (h_flag : ¬ Nat.toB256 out.length < (32 : B256))
    (h_one : pausedAnswer out = 1)
    (run : Func.RunCompiledTo fs sevm decodePre decodePausedResult ex) :
    ∃ armPre : Devm, Func.RunCompiledTo fs sevm armPre pauseSuccess ex := by
  obtain ⟨armPre, harm⟩ := pauseDecode_arms h_mem h_rd run
  rcases harm with ⟨hs, -⟩ | ⟨-, -, hzero, -⟩ | ⟨-, -, -, hne1, -⟩ |
    ⟨-, -, -, hsucc⟩
  · exact absurd hs h_flag
  · exact absurd (hzero.symm.trans h_one) (by decide)
  · exact absurd h_one hne1
  · exact ⟨armPre, hsucc⟩

/-- **D6: a valid first word with any tail is accepted.**

The accepting path carries no length equality, so this is a corollary rather
than a new argument — but it is the one Stage 6 asks be stated, and it is
falsifiable: a premise `out.length = 32` anywhere upstream would make it
unprovable.  `tail` is arbitrary, including empty and including the 65 504
bytes the largest differential row returns. -/
theorem pauseDecode_accepts_one_withTail {fs : List Func} {sevm : Sevm}
    {decodePre : Devm} {μ : Mem} {word tail : Bytes} {ex : Execution}
    (h_word : word.length = 32)
    (h_one : Bytes.toB256 word = 1)
    (h_mem : decodePre.memory = μ.write 0 ((word ++ tail).take 32))
    (h_rd : decodePre.returnData = word ++ tail)
    (h_flag : ¬ Nat.toB256 (word ++ tail).length < (32 : B256))
    (run : Func.RunCompiledTo fs sevm decodePre decodePausedResult ex) :
    ∃ armPre : Devm, Func.RunCompiledTo fs sevm armPre pauseSuccess ex := by
  refine pauseDecode_accepts_one h_mem h_rd h_flag ?_ run
  have hslice : (word ++ tail).sliceD 0 32 0 = word := by
    unfold List.sliceD
    rw [List.drop_zero, List.takeD_eq_take _ (by simp [h_word]), ← h_word,
      List.take_left]
  rw [pausedAnswer, hslice]
  exact h_one

/-! ## The join

One theorem for everything downstream of the observation's edge: five of the
seven outcomes, each with the condition that selects it and the payload it
produces.  Outcome 2 — the `pauseFor` CALL's own failure — is the predecessor's
`pauseCall_failureArm_payload`, and outcome 1 is the code guard below; together
the seven are exhaustive.

This is a classification of derivations that **reach a result**, not a claim
that any arm is reached.  Both out-of-gas legs stay explicit disjuncts.  The
conditions are `child.error.isSome` and functions of `child.output`, so which
outcome a run lands in is settled by the target's behaviour alone — and nothing
here says the target's behaviour is constrained, or that an accepted answer is
true. -/

/-- **The observation's five outcomes, joined.**

Reading the disjuncts in order: the observation itself failed, and its own
returndata is bubbled (outcome 3 — **the observation's**, not the `pauseFor`
call's); the answer was shorter than a word (4); it was a full word of `0` (5);
a full word that is neither `0` nor `1` (6); or the canonical `1`, which
reaches `pauseSuccess` (7). -/
theorem pauseObservation_outcomes {fs : List Func} {sevm : Sevm} {target : Adr}
    {statPre statPost : Devm} {ex : Execution}
    (h_empty : fs[emptyRevertSlot]? = some Func.rev)
    (h_bubble : fs[bubbleRevertSlot]? = some Func.revReturnData)
    (h_failed : fs[pauseFailedErrorSlot]? = some pauseFailedError)
    (boundary : PauseStatBoundary sevm target statPre statPost)
    (run : Func.RunCompiledTo fs sevm statPost
      (Ninst.iszero :::
        ((Func.call bubbleRevertSlot) <?> decodePausedResult)) ex) :
    ∃ child : Devm,
      statPost.returnData = child.output ∧
      -- outcome 3: the observation failed; its own returndata is bubbled
      ((child.error.isSome = true ∧
          ((∃ d, ex = .error (.halt (.outOfGas .none), d)) ∨
            (∃ post, ex = .error (.revert, post) ∧
              post.output =
                child.output.take child.output.length.toB256.toNat))) ∨
        -- outcome 4: fewer than 32 bytes; no word is read
        (child.error.isSome = false ∧
          Nat.toB256 child.output.length < (32 : B256) ∧
          (∃ post, ex = .error (.revert, post) ∧ post.output = [])) ∨
        -- outcome 5: a returned `false`
        (child.error.isSome = false ∧
          ¬ Nat.toB256 child.output.length < (32 : B256) ∧
          32 ≤ child.output.length ∧ pausedAnswer child.output = 0 ∧
          ((∃ d, ex = .error (.halt (.outOfGas .none), d)) ∨
            (∃ post, ex = .error (.revert, post) ∧
              post.output = customErrorData "PauseFailed"))) ∨
        -- outcome 6: a non-canonical Boolean
        (child.error.isSome = false ∧
          ¬ Nat.toB256 child.output.length < (32 : B256) ∧
          32 ≤ child.output.length ∧ pausedAnswer child.output ≠ 0 ∧
          pausedAnswer child.output ≠ 1 ∧
          (∃ post, ex = .error (.revert, post) ∧ post.output = [])) ∨
        -- outcome 7: the canonical `1`
        (child.error.isSome = false ∧
          ¬ Nat.toB256 child.output.length < (32 : B256) ∧
          32 ≤ child.output.length ∧ pausedAnswer child.output = 1 ∧
          ∃ successPre : Devm,
            Func.RunCompiledTo fs sevm successPre pauseSuccess ex)) := by
  obtain ⟨child, armPre, rest, μ, hstk, hrd, hard, hamem, harm⟩ :=
    pauseObservation_arms boundary run
  refine ⟨child, hrd, ?_⟩
  rcases harm with ⟨herr, hcall⟩ | ⟨herr, hdec⟩
  · obtain ⟨bubblePre, hburn, hbody⟩ := runCompiledTo_call_inv h_bubble hcall
    have hbrd : bubblePre.returnData = child.output :=
      hburn.returnData.symm.trans hard
    rcases Func.runCompiledTo_revReturnData_inv hbody with
      h_oog | ⟨post, hpost, hout⟩
    · exact Or.inl ⟨herr, Or.inl h_oog⟩
    · exact Or.inl ⟨herr, Or.inr ⟨post, hpost, by rw [hout, hbrd]⟩⟩
  · obtain ⟨armPre2, harm2⟩ := pauseDecode_arms hamem hard hdec
    rcases harm2 with ⟨hs, hcall⟩ | ⟨hns, hlong, hzero, hcall⟩ |
      ⟨hns, hlong, hne0, hne1, hcall⟩ | ⟨hns, hlong, hone, hsucc⟩
    · obtain ⟨_, -, hbody⟩ := runCompiledTo_call_inv h_empty hcall
      exact Or.inr (Or.inl ⟨herr, hs, runCompiledTo_rev_inv hbody⟩)
    · obtain ⟨_, -, hbody⟩ := runCompiledTo_call_inv h_failed hcall
      rw [show pauseFailedError =
        Func.revSelector (customErrorData "PauseFailed")
          (by simp [customErrorData, B256.length_toBytes]) from rfl] at hbody
      exact Or.inr (Or.inr (Or.inl
        ⟨herr, hns, hlong, hzero, runCompiledTo_revSelector_inv hbody⟩))
    · obtain ⟨_, -, hbody⟩ := runCompiledTo_call_inv h_empty hcall
      exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨herr, hns, hlong, hne0, hne1, runCompiledTo_rev_inv hbody⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨herr, hns, hlong, hone, armPre2, hsucc⟩)))

/-! ## Outcome 1: the code guard

`pauseAfterSet` loads the staged target back, duplicates it, and tests
`EXTCODESIZE` for zero before it sends anything.  Blanc's only `EXTCODESIZE`
inversion leaves the pushed word anonymous and lives in a WETH10 module, which
a Lido module must not import — contracts are siblings — so the
value-carrying form is derived here. -/

/-- `EXTCODESIZE` at a known stack top, **with its value**: the word it pushes
is the code size of the account its operand names, read in the frame's own
state, and memory is untouched. -/
private lemma of_extcodesize_val {e : Sevm} {s r : Devm} {x : B256} {xs : Stack}
    (hp : x :: xs <<+ s.stack)
    (run : Ninst.Run e s Ninst.extcodesize r) :
    ((s.getCode x.toAdr).size.toB256 :: xs <<+ r.stack) ∧
      s.memory = r.memory := by
  rcases of_run_reg run with ⟨pc, hrun⟩
  simp only [Rinst.run, Rinst.runCore] at hrun
  rcases Except.bind_eq_ok hrun with ⟨⟨adr, d1⟩, hpopAdr, hrun⟩
  rw [Devm.popToAdr_def] at hpopAdr
  dsimp [(· <&> ·), Functor.mapRev, Functor.map, Except.map] at hpopAdr
  rcases hpop : Devm.pop s with _ | ⟨word, d0⟩ <;> simp [hpop] at hpopAdr
  rcases hpopAdr with ⟨rfl, rfl⟩
  have hpop' := Devm.pop_of_pop hpop
  have hx : x = word :=
    (List.of_cons_pref_of_cons_pref hp (pref_of_split hpop'.stack)).left
  subst word
  have htail : xs <<+ d0.stack := of_append_pref hpop'.stack hp
  split at hrun
  · rcases Except.bind_eq_ok hrun with ⟨d2, hgas, hpush⟩
    have hst : s.state = d2.state :=
      hpop'.state.trans (Devm.burn_of_chargeGas hgas).state
    have hcode : d2.getCode x.toAdr = s.getCode x.toAdr := by
      unfold Devm.getCode Devm.getAcct; rw [hst]
    refine ⟨?_, ?_⟩
    · rw [← hcode]
      exact append_pref (Devm.push_of_push hpush).stack
        (by rw [← (Devm.burn_of_chargeGas hgas).stack]; exact htail)
    · exact hpop'.memory.trans
        ((Devm.burn_of_chargeGas hgas).memory.trans
          (Devm.push_of_push hpush).memory)
  · rcases Except.bind_eq_ok hrun with ⟨d2, hgas, hpush⟩
    have hst : s.state = d2.state :=
      hpop'.state.trans
        ((show d0.state = (addAccessedAddress d0 x.toAdr).state from rfl).trans
          (Devm.burn_of_chargeGas hgas).state)
    have hcode : d2.getCode x.toAdr = s.getCode x.toAdr := by
      unfold Devm.getCode Devm.getAcct; rw [hst]
    refine ⟨?_, ?_⟩
    · rw [← hcode]
      exact append_pref (Devm.push_of_push hpush).stack
        (by rw [← (Devm.burn_of_chargeGas hgas).stack]; exact htail)
    · exact hpop'.memory.trans
        ((show d0.memory = (addAccessedAddress d0 x.toAdr).memory from rfl).trans
          ((Devm.burn_of_chargeGas hgas).memory.trans
            (Devm.push_of_push hpush).memory))

/-- **Outcome 1: a target with no code is rejected before anything is sent.**

The guard's word is the `EXTCODESIZE` of the *staged* target — the word the
CircuitBreaker itself put at `targetWord`, not one the callee supplied — and
when it is zero the empty revert is reached without a message leaving the
frame.  The condition is `(entry.getCode target).size.toB256 = 0` rather than
`.size = 0` for the same reason the length guard's is stated at `toB256`: that
is the word the machine actually tests, and the two agree on every code object
an execution can hold. -/
theorem pauseAfterSet_codeGuard_arms {fs : List Func} {sevm : Sevm}
    {entry : Devm} {target : Adr} {ex : Execution}
    (h_empty : fs[emptyRevertSlot]? = some Func.rev)
    (hTarget : MemWordAt entry (targetWord * 32).toNat target.toB256)
    (run : Func.RunCompiledTo fs sevm entry pauseAfterSet ex) :
    ((entry.getCode target).size.toB256 = 0 ∧
        ∃ post, ex = .error (.revert, post) ∧ post.output = []) ∨
      ((entry.getCode target).size.toB256 ≠ 0 ∧
        ∃ guardPost : Devm,
          Func.RunCompiledTo fs sevm guardPost
            (pauseCallStaging +++ (Ninst.call ::: pauseAfterCallBranch)) ex) := by
  rw [pauseAfterSet_eq_afterCall] at run
  obtain ⟨g1, hguard, run⟩ := runCompiledTo_prepend_inv run
  unfold pauseCodeGuard at hguard
  rcases of_run_append (loadWord targetWord) hguard with ⟨u0, hload, hrest⟩
  have hw0 : target.toB256 :: [] <<+ u0.stack :=
    prefix_of_loadWord_window hTarget nil_pref hload
  rcases Line.of_run_cons hrest with ⟨u1, qdup, hrest⟩
  have hw1 : target.toB256 :: [target.toB256] <<+ u1.stack :=
    prefix_of_dup_val qdup (by show_nth) hw0
  rcases Line.of_run_cons hrest with ⟨u2, qcs, hrest⟩
  obtain ⟨hw2, -⟩ := of_extcodesize_val hw1 qcs
  rcases Line.of_run_cons hrest with ⟨u3, qiz, hnil⟩
  cases hnil
  have hcode : u1.getCode = entry.getCode := by
    have hc0 : Devm.getCode entry = Devm.getCode u0 :=
      Line.of_inv Devm.getCode (by unfold loadWord; line_inv) hload
    have hc1 : Devm.getCode u0 = Devm.getCode u1 :=
      Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons qdup Line.Run.nil)
    exact (hc0.trans hc1).symm
  have htoadr : (target.toB256).toAdr = target := toAdr_toB256 target
  rw [htoadr, hcode] at hw2
  have hw3 := prefix_of_iszero qiz hw2
  rcases runCompiledTo_branch_inv run with
    ⟨armPre, hz, hpop, harm⟩ | ⟨w, armPre, hne, hwstk, hpop, harm⟩
  · -- the guard's word was nonzero: the target carries code
    have hflag0 : ((entry.getCode target).size.toB256 =? 0) = 0 := by
      obtain ⟨t, ht⟩ := hw3
      rw [ht] at hz
      exact (List.cons.inj hz).1
    exact Or.inr ⟨ne_of_eqCheck_eq_zero hflag0, armPre, harm⟩
  · -- the guard's word was zero: the empty revert, and nothing was sent
    have hflagw : ((entry.getCode target).size.toB256 =? 0) = w := by
      obtain ⟨t, ht⟩ := hw3
      rw [ht] at hwstk
      exact (List.cons.inj hwstk).1
    obtain ⟨_, -, hbody⟩ := runCompiledTo_call_inv h_empty harm
    exact Or.inl ⟨eqCheck_ne_zero (fun h => hne (hflagw.symm.trans h)),
      runCompiledTo_rev_inv hbody⟩

/-! ## All seven, in one statement

The two premises `h_call` and `h_observe` are the predecessor's boundary
theorems applied at whatever states *this* derivation reaches.  Neither
constrains the target: `pauseCall_boundary` and `pauseStat_boundary` are proved
for an arbitrary callee carrying arbitrary bytecode, and their remaining
hypotheses — the six staged operands and the argument window — are facts about
the CircuitBreaker's own staging lines.

Carrying them as premises rather than deriving them here is the one composition
step this cut does not close, and the reason is mechanical rather than
semantic: `pauseCallStaging_operands`, `pauseStatStaging_operands` and
`pauseStatStaging_calldata` are `private` to
`Blanc/LidoCircuitBreakerCallBoundary.lean`, and exporting them means editing a
module that carries a baselined elaboration row.  The whole-`pause`-to-CALL
composition therefore remains open exactly as the last two cuts left it. -/

/-- **`pauseAfterSet`'s seven outcomes, partitioned.**

Every derivation of `pauseAfterSet` that reaches a result lands in exactly one
disjunct, and each names the condition that selected it and the payload it
produced.  The conditions are the staged target's code size and, past the code
guard, `child.error.isSome` and functions of `child.output` — the target's
behaviour, and nothing else.

Two children appear and they are **not** the same: outcome 2's is the
`pauseFor` CALL's, outcomes 3 to 7's is the `isPaused()` STATICCALL's.  That
distinction is the whole content of outcome 3, because both bubbles are the
same one-line body at the same table slot.

This is a classification of derivations that reach a result.  It is **not** a
liveness claim: no arm is asserted to be reached, both out-of-gas legs stay
explicit, and outcome 7 ends at `pauseSuccess`'s entry rather than at a
completed pause.  And accepting `1` is still not evidence that the target is
paused. -/
theorem pauseAfterSet_outcomes {fs : List Func} {sevm : Sevm} {target : Adr}
    {duration : B256} {entry : Devm} {ex : Execution}
    (h_empty : fs[emptyRevertSlot]? = some Func.rev)
    (h_bubble : fs[bubbleRevertSlot]? = some Func.revReturnData)
    (h_failed : fs[pauseFailedErrorSlot]? = some pauseFailedError)
    (hTarget : MemWordAt entry (targetWord * 32).toNat target.toB256)
    (h_call : ∀ g p q : Devm, Line.Run sevm g pauseCallStaging p →
      Ninst.RunCompiled sevm p (.exec .call) q →
      PauseCallBoundary sevm target duration p q)
    (h_observe : ∀ a p q : Devm, Line.Run sevm a pauseStatStaging p →
      Ninst.RunCompiled sevm p (.exec .statcall) q →
      PauseStatBoundary sevm target p q)
    (run : Func.RunCompiledTo fs sevm entry pauseAfterSet ex) :
    -- 1: the target carries no code
    ((entry.getCode target).size.toB256 = 0 ∧
        ∃ post, ex = .error (.revert, post) ∧ post.output = []) ∨
      -- 2: the `pauseFor` CALL failed; its returndata is bubbled
      ((entry.getCode target).size.toB256 ≠ 0 ∧ ∃ callChild : Devm,
        callChild.error.isSome = true ∧
        ((∃ d, ex = .error (.halt (.outOfGas .none), d)) ∨
          (∃ post, ex = .error (.revert, post) ∧
            post.output =
              callChild.output.take callChild.output.length.toB256.toNat))) ∨
      -- 3 to 7: the observation happened, and its answer was read
      ((entry.getCode target).size.toB256 ≠ 0 ∧ ∃ child : Devm,
        ((child.error.isSome = true ∧
            ((∃ d, ex = .error (.halt (.outOfGas .none), d)) ∨
              (∃ post, ex = .error (.revert, post) ∧
                post.output =
                  child.output.take child.output.length.toB256.toNat))) ∨
          (child.error.isSome = false ∧
            Nat.toB256 child.output.length < (32 : B256) ∧
            (∃ post, ex = .error (.revert, post) ∧ post.output = [])) ∨
          (child.error.isSome = false ∧
            ¬ Nat.toB256 child.output.length < (32 : B256) ∧
            32 ≤ child.output.length ∧ pausedAnswer child.output = 0 ∧
            ((∃ d, ex = .error (.halt (.outOfGas .none), d)) ∨
              (∃ post, ex = .error (.revert, post) ∧
                post.output = customErrorData "PauseFailed"))) ∨
          (child.error.isSome = false ∧
            ¬ Nat.toB256 child.output.length < (32 : B256) ∧
            32 ≤ child.output.length ∧ pausedAnswer child.output ≠ 0 ∧
            pausedAnswer child.output ≠ 1 ∧
            (∃ post, ex = .error (.revert, post) ∧ post.output = [])) ∨
          (child.error.isSome = false ∧
            ¬ Nat.toB256 child.output.length < (32 : B256) ∧
            32 ≤ child.output.length ∧ pausedAnswer child.output = 1 ∧
            ∃ successPre : Devm,
              Func.RunCompiledTo fs sevm successPre pauseSuccess ex))) := by
  rcases pauseAfterSet_codeGuard_arms h_empty hTarget run with
    ⟨hzero, hpost⟩ | ⟨hne, guardPost, hrun⟩
  · exact Or.inl ⟨hzero, hpost⟩
  obtain ⟨callPre, hstaging, hrun⟩ := runCompiledTo_prepend_inv hrun
  obtain ⟨callPost, hcross, hrun⟩ := runCompiledTo_next_inv hrun
  have boundaryCall := h_call guardPost callPre callPost hstaging hcross
  rw [pauseAfterCallBranch] at hrun
  obtain ⟨callChild, armPre, rest, hstk, hrd, hard, harm⟩ :=
    pauseAfterCall_arms boundaryCall hrun
  rcases harm with ⟨herr, hcall⟩ | ⟨-, hstat⟩
  · refine Or.inr (Or.inl ⟨hne, callChild, herr, ?_⟩)
    obtain ⟨bubblePre, hburn, hbody⟩ := runCompiledTo_call_inv h_bubble hcall
    have hbrd : bubblePre.returnData = callChild.output :=
      hburn.returnData.symm.trans hard
    rcases Func.runCompiledTo_revReturnData_inv hbody with
      h_oog | ⟨post, hpost, hout⟩
    · exact Or.inl h_oog
    · exact Or.inr ⟨post, hpost, by rw [hout, hbrd]⟩
  · rw [pauseStatArm] at hstat
    obtain ⟨statPre, hstatStaging, hstat⟩ := runCompiledTo_prepend_inv hstat
    obtain ⟨statPost, hstatCross, hstat⟩ := runCompiledTo_next_inv hstat
    obtain ⟨child, hrd', houtcomes⟩ :=
      pauseObservation_outcomes h_empty h_bubble h_failed
        (h_observe armPre statPre statPost hstatStaging hstatCross) hstat
    exact Or.inr (Or.inr ⟨hne, child, houtcomes⟩)
