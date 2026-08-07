-- FmintReverts.lean : fmint's deliberate reverts, constructed rather than
-- ruled out.
--
-- `Blanc/FlashSpec.lean` says, of seven conditions, that no successful
-- execution exists, and — since `Blanc/CommonProofs.lean`'s
-- `exec_error_of_no_success` — that the call therefore settles with *some*
-- error.  Neither names the error, and neither is a claim that anything
-- *happens*: a frame that cannot succeed is still only excluded, not run.
--
-- This module is the other side.  Each theorem below constructs the frame's
-- execution instruction by instruction, from a precondition on the frame
-- alone, and lands on `.error (.revert, post)` with `post`'s output pinned to
-- `[]` — Blanc's first statements that a call *reverts*, with *this* error and
-- *no* revert data, on the deployed bytes.
--
-- Read the scope limits off each theorem's docstring; three of them bind every
-- statement in the file and are stated once here.
--
-- * **These are not exhaustiveness claims.**  Each says that a condition
--   reverts.  None says that only these conditions revert, and no consequence
--   of one may be read that way.  That is a strictly larger claim and this
--   module does not make it anywhere.
-- * **They do not subsume the no-success family, and are not subsumed by it.**
--   `no_success_of_token_ne_self` needs no gas premise, because "does not
--   succeed" is not a claim that the frame gets anywhere; "reverts" is, so it
--   needs enough gas for the whole path.  Neither theorem implies the other,
--   and `Blanc/FlashSpec.lean`'s rows are untouched.
-- * **They are message-call altitude, and about one selector each.**  `pre` is
--   a code frame, not a transaction: intrinsic gas, the 63/64 rule and
--   transaction validity are a further layer.  And `func_run` decides each
--   dispatch fork by evaluating a concrete comparison, so every statement here
--   fixes its selector; a universally quantified "any unknown selector" is a
--   different theorem and is not proved here.
--
-- Both targets end in `Func.rev` — `PUSH0; PUSH0; REVERT` — which is why the
-- error is `EvmError.revert` and the output is empty.  Neither path crosses a
-- `CALL`, so neither hands the error choice to a callee.

import Blanc.RevertPayload
import Blanc.FlashSpec

namespace Blanc
namespace Fmint

open Jaune

set_option maxRecDepth 8000

/-! ## Target E-1 — a selector fmint does not have

`fmint = ⟨Func.mainWith fallbackSlot fmintTree, fmintAux⟩` with
`fallbackSlot = 1` and `fmintAux = [Func.rev, burnAndReturn]`, and
`dispatchWith k (leaf w p) = pushB256 w ::: eq ::: (p <?> .call k)`.  So a
selector that misses takes the leaf's `.zero` arm into `.call 1`, which is
`Func.rev`.

That makes this the first walk in the repository to use `func_run`'s `.call`
rule at all.  The rule is `Func.runCompiledTo_call'`: a tail jump into the flat
table, carrying the table lookup, the headroom and `PUSH2; JUMP; JUMPDEST`'s
`gVerylow + gMid + gJumpdest` — and **no** `Xlot` obligation, because an
internal `.call` is not an external call. -/

/-- The selector this statement is about, and no other: `0xffffffff`, which is
larger than every entry of `fmintFuncs`.

**Deliberately a bare numeral rather than `selector "…" [...]`.**  A `selector`
application forces a `String.keccak`, which is the real per-target elaboration
floor here; the twelve keccaks the dispatch walk cannot avoid are enough. -/
abbrev unknownSelector : B256 := 0xffffffff

/-- The `.call` arm's table lookup, checked on its own rather than only inside
the walk that uses it: aux slot `fallbackSlot` really is `Func.rev`.

`func_run`'s `.call` rule had never run before this module — every earlier walk
was a dispatch *hit*, which takes the leaf's other arm — so its two mechanical
obligations are worth seeing separately.  This is the first; the second is the
`gVerylow + gMid + gJumpdest` an internal call hides, which `unknownSelectorGas`
below accounts for and which the walk would not close if it were wrong, because
`Func.RunCompiledTo`'s frames are gas-exact. -/
theorem fmint_fallback_is_rev :
    (fmint.main :: fmint.aux)[fallbackSlot]? = some Func.rev := rfl

/-- Every gas constant the unknown-selector path charges, in the order it
charges them: the program's entry `JUMPDEST`; `fsig`'s four instructions; three
dispatch forks, each falling through because `0xffffffff` is above every pivot;
the leaf's `PUSH`/`EQ` and its fall-through arm; the `.call` into aux slot 1;
and `Func.rev`'s two `PUSH0`s — the `REVERT` itself is free, its `(0, 0)` window
costing no expansion. -/
def unknownSelectorGas : Nat :=
  gJumpdest
    + (gBase + gVerylow + gVerylow + gVerylow)
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh))
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh))
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh))
    + (gVerylow + gVerylow + (gVerylow + gHigh))
    + (gVerylow + gMid + gJumpdest)
    + (gBase + gBase)

/-- 113 gas: the dispatcher's binary search, the miss, and three instructions
of revert. -/
theorem unknownSelectorGas_eq : unknownSelectorGas = 113 := by decide

/-! ### The witness

`func_run` walks `fmint`'s compiled `Func` from the program entry and applies
one `Func.RunCompiledTo` rule per node.  What it has to be told, in the order it
asks:

* `unknownSelector` — what `fsig`'s `SHR` produced, which is `h_sel`'s
  right-hand side;
* `0, 0, 0` — the three dispatch forks, each `GT` deciding that `0xffffffff` is
  not below the right subtree's leftmost signature, so each falls through to the
  right;
* `0` — the leaf's `EQ`, which does **not** match, so the `.call fallbackSlot`
  miss arm is taken.

Those last four hints are also where the absence of this selector is *proved*
rather than asserted: three `GT` obligations put the binary search at the
rightmost leaf, and the leaf's `EQ` obligation is exactly "the one entry the
search lands on is not this selector".  Nothing in the file asserts absence
separately, and nothing needs to.

The one obligation the walk hands back is the terminal `REVERT`, which ends the
frame and so has no successor for a walk to name. -/

/-- A call on `fmint` carrying a selector it does not have has a gas-exact walk
that reverts, with empty revert data. -/
theorem unknownSelector_runCompiledTo {sevm : Sevm} {pre : Devm}
    (h_sel : Sevm.selector sevm = unknownSelector)
    (h_stack : pre.stack = [])
    (h_gas : unknownSelectorGas ≤ pre.gasLeft) :
    ∃ post, Prog.RunCompiledTo sevm pre fmint (.error (.revert, post)) ∧
      Devm.output post = [] := by
  rw [unknownSelectorGas_eq] at h_gas
  set g := pre.gasLeft with hg
  exact
    ⟨_,
      Prog.runCompiledTo_intro (G := g - 1)
        (mid := pre.setMach ⟨[], pre.memory, g - 1⟩)
        (by simp only [gJumpdest]; omega)
        (by rw [h_stack])
        (by
          func_run [unknownSelector, 0, 0, 0, 0]
          exact Func.runCompiledTo_rev_of (i := 0) (sz := 0) (s := [])
            (G := g - 113) rfl Devm.extCost_empty_window rfl Devm.memRead_zero),
      rfl⟩

/-- **`fmint` reverts on a selector it does not have.**

The first statement in this repository that a contract call *reverts*: not that
it fails to succeed, and not that it settles with some error, but that this
frame settles with `EvmError.revert` and hands back no revert data.

What it does **not** say:

* **It is about `0xffffffff` and no other selector.**  The dispatcher's binary
  search is walked by evaluating three concrete comparisons, so a different
  absent selector is a different derivation — cheap to redo, but not this
  theorem.  Nothing here is quantified over selectors.
* **It is not exhaustiveness.**  It says this selector reverts, never that only
  unknown selectors do.
* **It is message-call altitude.**  113 is the frame's gas, not a
  transaction's, and it is exact rather than a bound: `Func.RunCompiledTo` pins
  every hidden instruction's cost under `Blanc/Compiled.lean`'s compiler-shape
  assumption.
* **The empty output is the contract's, not the EVM's.**  `Func.rev` reverts
  through a `(0, 0)` memory window on purpose; a bare `REVERT` would have
  returned whatever two words were on the stack as offset and size. -/
theorem fmint_unknown_selector_reverts {sevm : Sevm} {pre : Devm}
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = unknownSelector)
    (h_stack : pre.stack = [])
    (h_gas : unknownSelectorGas ≤ pre.gasLeft) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .error (.revert, post) ∧
      Devm.output post = [] := by
  obtain ⟨post, h_run, h_out⟩ := unknownSelector_runCompiledTo h_sel h_stack h_gas
  exact ⟨post, Prog.exec_of_runCompiledTo h_run h_code, h_out⟩

/-! ## Target E-2 — `flashLoan` with `token ≠ self`

ERC-3156 mandates a revert when the requested `token` is not the lender itself,
and fmint reaches it through one explicit guard placed *before* the bound check,
so the reason does not depend on `amount` (`FMINT_DEVIATIONS.md` row 5).  That
guard is the first thing `flashLoan` does:

    arg 1 +++ address ::: eq ::: iszero ::: .rev <?> …

and `a <?> b = Func.branch b a`, so a *nonzero* condition takes the `.succ` arm
into `Func.rev`.  `token ≠ self` makes the `EQ` `0` and the `ISZERO` `1`, which
is exactly that arm.

Two things make this the cleanest target in the genre.  **The path reads no
storage**, so unlike `totalSupply()` it needs no cold/warm premise at all.  And
it is the direct counterpart of `Blanc/FlashSpec.lean`'s
`no_success_of_token_ne_self`: the four premises below its own are that
theorem's verbatim, so the two can be read side by side.  They remain
independent statements — see this module's banner. -/

/-- Every gas constant the `token ≠ self` path charges, in the order it charges
them: the entry `JUMPDEST`; `fsig`; three dispatch forks, the first jumping and
the other two falling through; the leaf's `PUSH`/`EQ` and its taken arm; guard
(0)'s `PUSH`/`CALLDATALOAD`/`ADDRESS`/`EQ`/`ISZERO` and its jumped arm; and
`Func.rev`'s two `PUSH0`s. -/
def tokenNeSelfGas : Nat :=
  gJumpdest
    + (gBase + gVerylow + gVerylow + gVerylow)
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh + gJumpdest))
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh))
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh))
    + (gVerylow + gVerylow + (gVerylow + gHigh + gJumpdest))
    + (gVerylow + gVerylow + gBase + gVerylow + gVerylow
        + (gVerylow + gHigh + gJumpdest))
    + (gBase + gBase)

/-- 131 gas — 18 more than the unknown-selector miss, which is the cost of
being dispatched *to* `flashLoan` and then rejected by its first guard rather
than never arriving. -/
theorem tokenNeSelfGas_eq : tokenNeSelfGas = 131 := by decide

/-! ### The witness

The hints, in the order `func_run` asks: `flashLoanSelector` for `fsig`'s
`SHR`; `1, 0, 0` for the three dispatch forks; `1` for the leaf's `EQ`, which
matches, so `flashLoan`'s body is entered; then `0` for the guard's `EQ` and `1`
for its `ISZERO`.

`ADDRESS` takes no hint and neither does `CALLDATALOAD`: both push a word the
frame already determines rather than computing one, which is why the
`pushItem`-class rule this step added to `Blanc/Forward.lean` deliberately
consumes nothing.

Two obligations come back.  The guard's `EQ` is the interesting one — the walk
cannot know that this comparison fails, so it hands the value obligation back
and it is discharged from `h_dec` and `h_ne`, which is the tactic working as
designed.  The other is the terminal `REVERT`. -/

/-- A `flashLoan` call on `fmint` whose `token` is not `fmint` itself has a
gas-exact walk that reverts, with empty revert data. -/
theorem tokenNeSelf_runCompiledTo {sevm : Sevm} {pre : Devm}
    {receiver token amount : B256} {data : Bytes}
    (h_sel : Sevm.selector sevm = flashLoanSelector)
    (h_dec : Sevm.DecodesCallWithTail sevm flashLoanSelector
      [receiver, token, amount] data)
    (h_ne : token ≠ sevm.currentTarget.toB256)
    (h_stack : pre.stack = [])
    (h_gas : tokenNeSelfGas ≤ pre.gasLeft) :
    ∃ post, Prog.RunCompiledTo sevm pre fmint (.error (.revert, post)) ∧
      Devm.output post = [] := by
  rw [tokenNeSelfGas_eq] at h_gas
  set g := pre.gasLeft with hg
  exact
    ⟨_,
      Prog.runCompiledTo_intro (G := g - 1)
        (mid := pre.setMach ⟨[], pre.memory, g - 1⟩)
        (by simp only [gJumpdest]; omega)
        (by rw [h_stack])
        (by
          func_run [flashLoanSelector, 1, 0, 0, 1, 0, 1]
          · show B256.eqCheck sevm.currentTarget.toB256 (Sevm.argWord sevm 1) = 0
            rw [argWord_one_of_decodes h_dec]
            show (if sevm.currentTarget.toB256 = token then (1 : B256) else 0) = 0
            rw [if_neg (fun h => h_ne h.symm)]
          · exact Func.runCompiledTo_rev_of (i := 0) (sz := 0) (s := [])
              (G := g - 131) rfl Devm.extCost_empty_window rfl
              Devm.memRead_zero),
      rfl⟩

/-- **`fmint`'s `flashLoan` reverts when `token` is not `fmint`.**

The arc's headline, and the direct counterpart of
`Blanc/FlashSpec.lean`'s `no_success_of_token_ne_self`: same four leading
premises, and where that one rules every successful execution out, this one
produces the execution and names its error.

Neither theorem subsumes the other.  `no_success_of_token_ne_self` needs no gas
premise, because "does not succeed" is not a claim that the frame reaches
anything; "reverts" is, so 131 gas is not decoration here, it is what excludes
`outOfGas` and makes the deliberate `REVERT` the outcome.

The rest of the scope is this module's banner's: not exhaustiveness, one
selector, message-call altitude, and an exact frame gas figure rather than a
bound.  Nothing here says a *transaction* reverts, and nothing here says the
other six guarded conditions do — each of those is its own derivation. -/
theorem fmint_token_ne_self_reverts {sevm : Sevm} {pre : Devm}
    {receiver token amount : B256} {data : Bytes}
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = flashLoanSelector)
    (h_dec : Sevm.DecodesCallWithTail sevm flashLoanSelector
      [receiver, token, amount] data)
    (h_ne : token ≠ sevm.currentTarget.toB256)
    (h_stack : pre.stack = [])
    (h_gas : tokenNeSelfGas ≤ pre.gasLeft) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .error (.revert, post) ∧
      Devm.output post = [] := by
  obtain ⟨post, h_run, h_out⟩ :=
    tokenNeSelf_runCompiledTo h_sel h_dec h_ne h_stack h_gas
  exact ⟨post, Prog.exec_of_runCompiledTo h_run h_code, h_out⟩

/-! ## The frame: what fmint's caller is handed

Everything above is at the `exec` altitude — one code frame's execution, from
its entry machine to its outcome.  `Blanc/FlashSpec.lean`'s restoration family
is one altitude up, at the frame `processMessage` opened for a `Msg`: it says
that a frame which cannot succeed settles with `out.error.isSome` and comes
back with the world it entered with.  This section composes the two.

**What the composition buys.**  `out.error.isSome` becomes `out.error = some
.revert`, and the empty revert data travels with it.  The mechanism is
`executeCode.handleError`, which maps `.error ⟨.revert, evm⟩` to
`.ok (evm.withError (some .revert))`, and `exec_iff_exec_eq`, which forces the
slot's derivation to carry the total function's value — so the frame's slot
cannot disagree with the walk above.

**No determinism lemma is needed here, and that is not an accident.**  The
boundary-quantified premises of `rollback_of_callback_never_magic` and its
sibling exist because `CallbackBoundary`'s `parent` is unpinned, so the
callback's frame is not a function of anything the statement holds.  This
frame is fmint's *own*: `initSevm (msg.withBenv benv)` and
`initDevm (msg.withBenv benv)` are functions of `msg` and `benv`, both of which
are named in the premises, so a single `exec` equation determines the outcome
and nothing has to be quantified over.

**Still one frame, and still not a transaction.**  A failed inner call can be
caught by its caller while the surrounding transaction succeeds; nothing here
says the transaction reverted, and nothing here says anything about fmint's
caller.  And as everywhere in this module, this is not exhaustiveness: it says
this condition reverts the frame, never that only this condition does. -/

/-- **`token ≠ self` ⇒ fmint's frame settled with `.revert`, returned nothing,
and rolled back.**

The arc's payoff: `Blanc/FlashSpec.lean`'s `rollback_of_token_ne_self` says
this frame's `out.error.isSome`; this says *which* error, and that the frame
returned no data.

**It is a new theorem beside that one, not a strengthening of it.**
`rollback_of_token_ne_self` holds with **no gas premise**, because "cannot
succeed" is not a claim that the frame reaches anything, while this one cannot
be stated without `h_gas` — so neither theorem subsumes the other and both
rows stand.

Premises are `rollback_of_token_ne_self`'s verbatim, read at the same entry
machine, plus the gas premise.  `h_stack` does not appear because
`initDevm`'s stack is `[]` by construction, which is a fact about frame entry
rather than a premise about it.

Frame, altitude and exhaustiveness: see this section's banner. -/
theorem rollback_revert_of_token_ne_self {msg : Msg} {benv : Benv} {xl : Xlot}
    {out : Devm} {receiver token amount : B256} {data : Bytes}
    (h_pm : ProcessMessage msg xl (.ok out))
    (h_fill : Xlot.Filled xl)
    (h_bt : msg.benvAfterTransfer = .ok benv)
    (h_prec : ∀ adr, msg.codeAddress = some adr →
      ¬ (!msg.disablePrecompiles && decide (benv.stat.rules.isPrecomp adr)) = true)
    (h_code : some (initSevm (msg.withBenv benv)).code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector (initSevm (msg.withBenv benv)) = flashLoanSelector)
    (h_dec : Sevm.DecodesCallWithTail (initSevm (msg.withBenv benv))
      flashLoanSelector [receiver, token, amount] data)
    (h_ne : token ≠ (initSevm (msg.withBenv benv)).currentTarget.toB256)
    (h_gas : tokenNeSelfGas ≤ (initDevm (msg.withBenv benv)).gasLeft) :
    out.error = some .revert ∧ out.output = [] ∧
      out.state = msg.benv.state ∧
      out.transientStorage = msg.tenv.transientStorage := by
  obtain ⟨post, h_exec, h_out⟩ :=
    fmint_token_ne_self_reverts h_code h_sel h_dec h_ne rfl h_gas
  obtain ⟨h_err, h_o, h_st, h_tr⟩ :=
    rollback_revert_of_exec_revert h_pm h_fill h_bt h_prec h_exec
  exact ⟨h_err, h_o.trans h_out, h_st, h_tr⟩

end Fmint
end Blanc
