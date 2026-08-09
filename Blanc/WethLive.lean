import Blanc.Forward
import Blanc.Weth

namespace Blanc

open Jaune

set_option maxRecDepth 8000

/-! # WETH's `balanceOf(address)` call succeeds

The second forward-constructed execution witness in the repository, and the
first on WETH.  `Blanc/FmintLive.lean` is the first; this module exists to show
that `func_run` is not specific to the target it was built against, and to
measure what a second target costs.

Three things differ from `Blanc/Fmint.totalSupply`, and they are the reason this
target was chosen rather than a second view of the same shape:

* **The storage key comes from calldata.**  `totalSupply()` reads a constant
  slot (`NOT 0`); `balanceOf(address guy)` reads the slot `guy`, which is
  `arg 0` — a `CALLDATALOAD` at byte offset 4.  So the walk's `CALLDATALOAD`
  rule and `Sevm.dataWord` are exercised for the first time, the precondition's
  cold-key premise is about a calldata-derived word rather than a constant, and
  the conclusion is quantified over that word.
* **A different dispatcher.**  `wethTree` has ten entries where `fmintTree` has
  twelve, and `balanceOf()` sits in the *right* half of the first fork where
  `totalSupply()` sat in the left half of all three.  The walk therefore takes a
  four-fork path with a different pattern of taken and fall-through arms.
* **`Func.mainWith`, not `Func.main`.**  WETH's leaf miss arm is `.call 1` into
  the fallback rather than `.rev`.  That arm is not taken here — see the note at
  the end of this file.

Nothing was added to `Blanc/Forward.lean` for this target. -/

/-- Every gas constant the `balanceOf(address)` derivation charges, in the order
it charges them: the program's entry `JUMPDEST`; `fsig`'s four instructions;
four dispatch forks, the first and last falling through and the middle two taken
by the `.succ` arm; the leaf's `PUSH`/`EQ` and its taken arm; the `nonpayable`
guard's `CALLVALUE`/`ISZERO` and its taken arm; then `balanceOf`'s own body.

It is one fork longer than `Fmint.totalSupplyGas` because `wethTree` puts
`balanceOf()` four levels down, and one gas unit dearer per instruction at
`arg 0`, whose `PUSH1 4` costs `gVerylow` where `totalSupply`'s `PUSH0` costs
`gBase`. The guard group is WETH's own: fmint's dispatcher routes to its
bodies unguarded, WETH's ten entries each sit behind `nonpayable`
(`Blanc/Weth.lean`). -/
def balanceOfGas : Nat :=
  gJumpdest
    + (gBase + gVerylow + gVerylow + gVerylow)
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh))
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh + gJumpdest))
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh + gJumpdest))
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh))
    + (gVerylow + gVerylow + (gVerylow + gHigh + gJumpdest))
    + (gBase + gVerylow + (gVerylow + gHigh + gJumpdest))
    + (gVerylow + gVerylow + gasColdSload)
    + (gBase + (gVerylow + gMemory))
    + (gVerylow + gBase)

/-- 2260 gas, of which `gasColdSload`'s 2100 is the storage read and 19 the
`nonpayable` guard (`CALLVALUE 2 + ISZERO 3 + PUSH2 3 + JUMPI 10 +
JUMPDEST 1`). -/
theorem balanceOfGas_eq : balanceOfGas = 2260 := by decide

/-- The selector `balanceOf(address)` dispatches on.  Local to this module for
the reason `Blanc/FmintLive.lean` records for `tsSel`: the tree has no selector
abbreviations, and importing a module to reach a four-byte constant costs
seconds of elaboration. -/
abbrev boSel : B256 := selector "balanceOf" [.address]

/-! ### The witness

`func_run` walks `weth`'s compiled `Func` from the program entry and applies one
`Func.RunCompiled` rule per node.  What it has to be told, in the order it asks:

* `boSel` — what `fsig`'s `SHR` produced, which is `h_sel`'s right-hand side;
* `0, 1, 1, 0` — the four dispatch forks.  `balanceOf()` is entry 6 of ten and
  `DispatchTree.build` splits at `⌈n/2⌉`, so the path is right, left, left,
  right, and `GT` decides each fork by comparing the selector against the right
  subtree's leftmost signature;
* `1` — the leaf's `EQ`, which matches, so `balanceOf`'s guarded entry is taken
  and the `.call 1` miss arm is not;
* `1` — the `nonpayable` guard's fork.  `ISZERO` over `CALLVALUE` left
  `sevm.value =? 0` on the stack, which `h_value` makes `1`, so the body arm
  is taken and the guard's `Func.rev` arm is not;
* `3` — `MSTORE`'s memory-expansion charge, one word into empty memory.

Everything else is derived, including the `CALLDATALOAD` that reads the argument:
its value is `Sevm.dataWord sevm 4` by definition rather than by computation, so
it consumes no hint. -/

/-- A `balanceOf(guy)` call on `weth` has a gas-exact run, and it returns
`guy`'s balance slot.

Every premise is what a fresh top-level message frame supplies: an empty stack,
empty memory, a storage key not yet warmed, and enough gas.  The key is the
calldata word the call carries, not a constant — WETH indexes balances by the
raw argument word, so that is what both the premise and the conclusion name. -/
theorem weth_balanceOf_runCompiled {sevm : Sevm} {pre : Devm}
    (h_value : sevm.value = 0)
    (h_sel : Sevm.selector sevm = boSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_cold : (⟨sevm.currentTarget, Sevm.dataWord sevm 4⟩ : Adr × B256)
      ∉ pre.accessedStorageKeys)
    (h_gas : balanceOfGas ≤ pre.gasLeft) :
    ∃ post, Prog.RunCompiled sevm pre weth post ∧
      Devm.output post =
        (Devm.getStorVal pre sevm.currentTarget (Sevm.dataWord sevm 4)).toBytes := by
  rw [balanceOfGas_eq] at h_gas
  set g := pre.gasLeft with hg
  exact
    ⟨_,
      Prog.runCompiled_intro (G := g - 1)
        (mid := pre.setMach ⟨[], Mem.empty, g - 1⟩)
        (by simp only [gJumpdest]; omega)
        (by rw [h_stack, h_mem])
        (by
          have h_value_zero : B256.eqCheck sevm.value 0 = 1 := by
            simp [B256.eqCheck, h_value]
          func_run [boSel, 0, 1, 1, 0, 1, 1, 3]
          · exact Devm.extCost_empty_word
          · exact Func.runCompiled_ret_word (G := g - 2260) (e := 0) rfl
              (Devm.extCost_word_word Mem.size_write_word)
              (by simp only [Devm.gasLeft_setMach]; omega)
              (Devm.memRead_word_fst (by simp only [Devm.memory_setMach]; rfl))),
      rfl⟩

/-- **`weth`'s `balanceOf(address)` call succeeds.**

The second statement in this repository that a contract call *succeeds*, and the
first on a second contract.  `Blanc.Fmint.fmint_totalSupply_succeeds` is the
first; read that theorem's docstring for what a statement of this shape does and
does not claim, because every one of those limits applies here unchanged:

* it is one entrypoint of one contract, and it is unconditional only because
  `balanceOf` is call-free — its compiled path emits no spawning instruction;
* it is message-call altitude, not transaction level;
* it fixes the selector, and says nothing in either direction about calldata
  carrying a different one;
* it fixes the call value at zero — since the `nonpayable` conformance change
  every recognized WETH selector rejects nonzero value, so a value-carrying
  `balanceOf` call has no successful execution to witness;
* the gas figure is exact, not a bound.

One limit is this target's own.  `balanceOf` performs **no address validation**:
`arg 0` is used as a storage key verbatim, so a calldata word whose top twelve
bytes are nonzero names a slot no address can occupy.  That is WETH's behaviour,
not an artefact of this statement — the statement is quantified over the word,
so it holds of those calls too and asserts nothing about their meaning. -/
theorem weth_balanceOf_succeeds {sevm : Sevm} {pre : Devm}
    (h_code : some sevm.code.toList = Prog.compile weth)
    (h_value : sevm.value = 0)
    (h_sel : Sevm.selector sevm = boSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_cold : (⟨sevm.currentTarget, Sevm.dataWord sevm 4⟩ : Adr × B256)
      ∉ pre.accessedStorageKeys)
    (h_gas : balanceOfGas ≤ pre.gasLeft) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧
      Devm.output post =
        (Devm.getStorVal pre sevm.currentTarget (Sevm.dataWord sevm 4)).toBytes := by
  obtain ⟨post, h_run, h_out⟩ :=
    weth_balanceOf_runCompiled h_value h_sel h_stack h_mem h_cold h_gas
  exact ⟨post, Prog.exec_of_runCompiled h_run h_code, h_out⟩

/-! ### What this target still does not exercise

`func_run`'s `.call` rule — the internal tail jump into the flat table — is
still unexercised by any proof in the tree, and no *view* can exercise it.
`dispatchWith` emits `.call k` only as a leaf's **miss** arm, so the rule is
reached exactly when the selector matches nothing and control falls through to
WETH's fallback, which is `deposit`: an `SSTORE` and a `LOG1`, neither of which
the walk has a forward rule for, and a state change rather than a view.  A
target that exercises `.call` therefore needs the store-writing rules first;
that is a successor arc's business, not a missing hint here. -/

end Blanc
