import Blanc.Forward
import Blanc.Fmint

namespace Blanc
namespace Fmint

open Jaune

/-- Every gas constant the `totalSupply()` derivation charges, in the order it
charges them: the program's entry `JUMPDEST`; `fsig`'s four instructions; three
dispatch forks, two taken by the `.succ` arm and one falling through; the leaf's
`PUSH`/`EQ` and its taken arm; then `totalSupply`'s own body. -/
def totalSupplyGas : Nat :=
  gJumpdest
    + (gBase + gVerylow + gVerylow + gVerylow)
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh + gJumpdest))
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh + gJumpdest))
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh))
    + (gVerylow + gVerylow + (gVerylow + gHigh + gJumpdest))
    + (gBase + gVerylow + gasColdSload)
    + (gBase + (gVerylow + gMemory))
    + (gVerylow + gBase)

/-- 2218 gas, of which `gasColdSload`'s 2100 is the storage read. -/
theorem totalSupplyGas_eq : totalSupplyGas = 2218 := by decide

/-! ### The dispatch path

`fmint`'s dispatcher is `DispatchTree.ofSorted fmintFuncs` over twelve
selectors, so a call walks three forks and then a leaf.  `totalSupply()` is
entry 2 of twelve, and `DispatchTree.build` splits at `⌈n/2⌉`, which puts it in
the left half at every fork: the first two forks jump, and the third — whose
pivot *is* `totalSupply()` — falls through.  Nothing below names those pivots.
`func_run` reads the fork structure off the compiled `Func` itself and only has
to be told what each `GT` decided, which is the middle three hints. -/

/-- The selector `totalSupply()` dispatches on.  There is no
`totalSupplySelector` in the tree and this is not one: it is local to this
module, and reaching `Blanc/FlashSpec.lean` for its neighbourhood would cost
two seconds of elaboration for a four-byte constant. -/
abbrev tsSel : B256 := selector "totalSupply" []

/-! ### The witness

`func_run` walks `fmint`'s compiled `Func` from the program entry and applies
one `Func.RunCompiled` rule per node, naming every intermediate state and gas
account itself.  What it has to be told, in the order it asks:

* `tsSel` — what `fsig`'s `SHR` produced, which is `h_sel`'s right-hand side;
* `1, 1, 0` — the three dispatch forks, two jumping and one falling through;
* `1` — the leaf's `EQ`, which matches, so the selector's own body is taken
  and the `.call fallbackSlot` miss arm is not;
* `supplySlot` — what `NOT 0` produced;
* `3` — `MSTORE`'s memory-expansion charge, one word into empty memory.

Everything else is derived: twenty-two instruction steps, four branch decisions,
the whole chain of states, and every gas and stack-headroom side condition along
it.  The two obligations the walk hands back are the justification for that `3`
and the terminal `RETURN`, which ends the frame and so has no successor for a
walk to name. -/

set_option maxRecDepth 674 in
/-- A `totalSupply()` call on `fmint` has a gas-exact run, and it returns the
supply slot.

Every premise is what a fresh top-level message frame supplies: an empty stack,
empty memory, a storage key not yet warmed, and enough gas.  The conclusion
names the post-state's output, so this is not merely "some run exists". -/
theorem totalSupply_runCompiled {sevm : Sevm} {pre : Devm}
    (h_sel : Sevm.selector sevm = tsSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_cold : (⟨sevm.currentTarget, supplySlot⟩ : Adr × B256)
      ∉ pre.accessedStorageKeys)
    (h_gas : totalSupplyGas ≤ pre.gasLeft) :
    ∃ post, Prog.RunCompiled sevm pre fmint post ∧
      Devm.output post =
        (Devm.getStorVal pre sevm.currentTarget supplySlot).toBytes := by
  rw [totalSupplyGas_eq] at h_gas
  set g := pre.gasLeft with hg
  exact
    ⟨_,
      Prog.runCompiled_intro (G := g - 1)
        (mid := pre.setMach ⟨[], Mem.empty, g - 1⟩)
        (by simp only [gJumpdest]; omega)
        (by rw [h_stack, h_mem])
        (by
          func_run [tsSel, 1, 1, 0, 1, supplySlot, 3]
          · exact Devm.extCost_empty_word
          · exact Func.runCompiled_ret_word (G := g - 2218) (e := 0) rfl
              (Devm.extCost_word_word Mem.size_write_word)
              (by simp only [Devm.gasLeft_setMach]; omega)
              (Devm.memRead_word_fst (by simp only [Devm.memory_setMach]; rfl))),
      rfl⟩

/-- **`fmint`'s `totalSupply()` call succeeds.**

The first statement in this repository that a contract call *succeeds*.
Everything before it takes a successful execution as a hypothesis and factors
it; this one produces the execution, from a precondition on the frame alone.

What it does **not** say, so that nothing downstream overreads it:

* **It is one entrypoint of one contract.** `totalSupply()` is call-free — its
  compiled path emits no spawning instruction — which is exactly why the
  statement is unconditional. Every fmint entrypoint that makes an external
  call carries the callee's execution as a premise (`Xlot.Filled`) and cannot
  have a statement of this shape at all.
* **It is message-call altitude, not transaction level.** Intrinsic gas, the
  63/64 rule and transaction validity are a further layer; `pre` is a frame,
  and 2218 is the frame's gas, not a transaction's.
* **It says nothing about any other calldata.** The premise fixes the selector;
  a call with different calldata is a different execution about which this says
  nothing, in either direction.
* **The gas figure is exact, not a bound.** `Func.RunCompiled` pins each hidden
  instruction's cost, so 2218 is what this path charges under
  `Blanc/Compiled.lean`'s compiler-shape assumption — a `PUSH1` peephole or a
  shared-`JUMPDEST` optimisation would change it. -/
theorem fmint_totalSupply_succeeds {sevm : Sevm} {pre : Devm}
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = tsSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_cold : (⟨sevm.currentTarget, supplySlot⟩ : Adr × B256)
      ∉ pre.accessedStorageKeys)
    (h_gas : totalSupplyGas ≤ pre.gasLeft) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧
      Devm.output post =
        (Devm.getStorVal pre sevm.currentTarget supplySlot).toBytes := by
  obtain ⟨post, h_run, h_out⟩ :=
    totalSupply_runCompiled h_sel h_stack h_mem h_cold h_gas
  exact ⟨post, Prog.exec_of_runCompiled h_run h_code, h_out⟩

end Fmint
end Blanc
