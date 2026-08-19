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
    ∃ (child armPre : Devm) (rest : List B256),
      statPost.stack = (if child.error.isSome then 0 else 1) :: rest ∧
      statPost.returnData = child.output ∧
      armPre.returnData = child.output ∧
      armPre.memory = statPost.memory ∧
      ((child.error.isSome = true ∧
          Func.RunCompiledTo fs sevm armPre (Func.call bubbleRevertSlot) ex) ∨
        (child.error.isSome = false ∧
          Func.RunCompiledTo fs sevm armPre g ex)) := by
  obtain ⟨parent, child, msg, xl, delegated, code, gasWord, childGas,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, hrd, hstk⟩ := boundary
  obtain ⟨mid, hn, hrest⟩ := runCompiledTo_next_inv run
  obtain ⟨hmidstk, hmidmem, hmidrd⟩ := iszero_stack_inv hn hstk
  rcases runCompiledTo_branch_inv hrest with
    ⟨armPre, hmid0, hpop, harm⟩ | ⟨w, armPre, hne, hmidw, hpop, harm⟩
  · -- the branch popped `0`: the `ISZERO` inverted a `1`, so the child succeeded
    have hw : ((if child.error.isSome then (0 : B256) else 1) =? 0) = 0 := by
      rw [hmidstk] at hmid0
      exact (List.cons.inj hmid0).1
    refine ⟨child, armPre, parent.stack, hstk, hrd,
      (hpop.returnData.symm.trans hmidrd).trans hrd,
      (hpop.memory.symm.trans hmidmem), Or.inr ⟨?_, harm⟩⟩
    revert hw
    cases hc : child.error.isSome
    · intro; rfl
    · intro h; exact absurd h (by decide)
  · -- the branch popped a nonzero word: the `ISZERO` inverted a `0`
    have hw : ((if child.error.isSome then (0 : B256) else 1) =? 0) = w := by
      rw [hmidstk] at hmidw
      exact (List.cons.inj hmidw).1
    refine ⟨child, armPre, parent.stack, hstk, hrd,
      (hpop.returnData.symm.trans hmidrd).trans hrd,
      (hpop.memory.symm.trans hmidmem), Or.inl ⟨?_, harm⟩⟩
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
  obtain ⟨child, armPre, rest, hstk, hrd, hard, -, harm⟩ :=
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
    ∃ child decodePre : Devm,
      child.error.isSome = false ∧
      decodePre.returnData = child.output ∧
      decodePre.memory = statPost.memory ∧
      Func.RunCompiledTo fs sevm decodePre decodePausedResult ex := by
  obtain ⟨child, armPre, rest, hstk, hrd, hard, hamem, harm⟩ :=
    pauseObservation_arms boundary run
  rcases harm with ⟨herr, -⟩ | ⟨herr, hdec⟩
  · exfalso
    rw [hstk, herr] at h_ok
    exact absurd (Option.some.inj h_ok) (by decide)
  · exact ⟨child, armPre, herr, hard, hamem, hdec⟩

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
        (32 ≤ out.length ∧ pausedAnswer out = 0 ∧
          Func.RunCompiledTo fs sevm armPre
            (Func.call pauseFailedErrorSlot) ex) ∨
        (32 ≤ out.length ∧ pausedAnswer out ≠ 0 ∧ pausedAnswer out ≠ 1 ∧
          Func.RunCompiledTo fs sevm armPre (Func.call emptyRevertSlot) ex) ∨
        (32 ≤ out.length ∧ pausedAnswer out = 1 ∧
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
    have hlong : 32 ≤ out.length :=
      le_length_of_not_toB256_lt_32 (not_lt_of_ltCheck_eq_zero hflag0)
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
          ⟨hlong, hne0, fun h => (ne_of_eqCheck_eq_zero hec) h.symm, harm3⟩))⟩
      · -- the canonical `1`: `pauseSuccess`
        have hec : ((1 : B256) =? pausedAnswer out) = w3 := by
          obtain ⟨t, ht⟩ := hp6
          rw [ht] at hw3
          exact (List.cons.inj hw3).1
        refine ⟨armPre3, Or.inr (Or.inr (Or.inr ⟨hlong, ?_, harm3⟩))⟩
        exact (eqCheck_ne_zero (fun h => hne3 (hec.symm.trans h))).symm
    · -- the answer is zero: `PauseFailed()`
      have hzc : (pausedAnswer out =? 0) = w2 := by
        obtain ⟨t, ht⟩ := hizp
        rw [ht] at hw2
        exact (List.cons.inj hw2).1
      exact ⟨armPre2, Or.inr (Or.inl
        ⟨hlong, eqCheck_ne_zero (fun h => hne2 (hzc.symm.trans h)), harm2⟩)⟩
  · -- the flag was set: fewer than 32 bytes came back, and nothing read a word
    have hflagw : (Nat.toB256 out.length <? (32 : B256)) = w := by
      obtain ⟨t, ht⟩ := hflag
      rw [ht] at hwstk
      exact (List.cons.inj hwstk).1
    exact ⟨armPre, Or.inl
      ⟨ltCheck_ne_zero (fun h => hne (hflagw.symm.trans h)), harm⟩⟩
