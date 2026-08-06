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

import Blanc.Reverts
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

end Fmint
end Blanc
