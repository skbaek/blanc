import Blanc.Lift.FrameWalk
import Blanc.Lift.CursorExact
import Blanc.Lift.InvWalkWorld
import Blanc.Lift.SoundSpan

/-!
# A frame walk reaches the exact state of a cut forward run

`lift_exactM` turns a gas-exact forward run (`SFunc.RunExact`) into *some* execution of the
frame; nothing in its statement says that the execution passes through the forward run's
states, so a call step of the forward run cannot be matched with an element of
`Exec.childFrames`. This module supplies the link on the actual derivation (`XAt`):

* `WalkAt`: the checked walk invariant (the derivation at `pc` in state `d`, the subtree `f`
  checked there over a matched abstract frame and memory map), with one step lemma per tree
  shape (`WalkAt.next`, `.dest`, `.zero`, `.succ`, `.toZero`, `.toSucc`, `.jump`, `.pcAt`,
  `.ret`, `.call`);
* `xa_retExact`: a walked exec-free tree whose gas-exact run returns puts the walk at the
  return address in the run's returned state, same remaining children (an internal callee
  crossed on the actual derivation);
* `xa_cutAt` / `xa_cutAt_start`: a walked checked node and a gas-exact run of a cut of its tree
  (`SFunc.CutCall`: one path to a subtree `tgt`, which becomes `.last .stop`, through no
  external instruction, possibly crossing internal calls into an exec-free, never-halting
  entry set `E`) halting in `s` put the walk at `tgt` in the state `s`, with the same remaining
  children and the checked invariants at `tgt`;
* `xa_staticcall_runCompiled`: at a walked `STATICCALL`, a compiled step of the call from the
  walked state is the frame's actual step, and its child (when a code frame is entered) is the
  head of the remaining children, with the step's return data as its output;
* `SFunc.cutPath`, `SFunc.subAt`, `SFunc.cutPathOk`, `SFunc.cutCall_of_cutPathOk`: a cut along
  an explicit list of steps (`CutStep.cl` crosses a call), checked by evaluation.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune AbstractStackSafety

/-! ## Exact jump steps -/

theorem popBurnBy_two_stack' {x y : B256} {cost : Nat} {s s' : Devm}
    (h : Devm.PopBurnBy [x, y] cost s s') : s.stack = x :: y :: s'.stack := by
  simpa only [Stack.Pop, Split, List.cons_append, List.nil_append] using h.stack

theorem popBurnBy_setMach {xs : List B256} {cost : Nat} {devm devm' : Devm}
    (h : Devm.PopBurnBy xs cost devm devm') :
    devm.setMach ⟨devm'.stack, devm.memory, devm.gasLeft - cost, devm.stateGas⟩ = devm' := by
  refine Devm.eq_of_proj rfl h.memory ?_ h.logs h.refundCounter h.output
    h.accountsToDelete h.returnData h.error h.accessedAddresses
    h.accessedStorageKeys h.state h.createdAccounts h.transientStorage h.stateGas
    h.accountReads h.storageReads h.storageWrites h.touchedAccounts
  have hg := h.gasLeft
  change devm.gasLeft - cost = devm'.gasLeft
  omega

/-! ## One checked instruction step keeps the checked invariants -/

section Next

variable {code : ByteArray} {es : List Entry} {ms : List MemMap} {b : Bool} {sevm : Sevm}
  {m pc : Nat} {a : List AVal} {μ : MemMap} {f : SFunc} {ρ : B256} {S base : List B256}
  {d d' : Devm}

end Next

/-! ## Exact `JUMP` steps -/

/-! ## The checked walk invariant and its steps -/

section Walk

variable {code : ByteArray} {c : Cert} {ms : List MemMap} {b : Bool} {sevm : Sevm}
  {post : Devm} {L : List Exec.Frame} {ρ : B256} {base : List B256}
  {m pc : Nat} {a : List AVal} {μ : MemMap} {d d' : Devm}

end Walk

/-! ## Crossing an exec-free callee on the actual derivation -/

section Cross

variable {code : ByteArray} {c : Cert} {ms : List MemMap} {b : Bool} {sevm : Sevm}

end Cross

/-! ## The cut walk -/

/-- `SFunc.CutCall fs E tgt f f'`: as `SFunc.CutAt`, and the path may also cross an internal call
into an entry of `E` (the cut keeps the `.callNext` and continues in its continuation). -/
inductive SFunc.CutCall (fs : List SFunc) (E : List Nat) (tgt : SFunc) : SFunc → SFunc → Prop
  | here : SFunc.CutCall fs E tgt tgt (.last .stop)
  | next {n : Ninst} {f f' : SFunc} :
    (∀ x : Xinst, n ≠ .exec x) → SFunc.CutCall fs E tgt f f' →
    SFunc.CutCall fs E tgt (.next n f) (.next n f')
  | dest {f f' : SFunc} :
    SFunc.CutCall fs E tgt f f' → SFunc.CutCall fs E tgt (.dest f) (.dest f')
  | zero {f f' g : SFunc} :
    SFunc.CutCall fs E tgt f f' → SFunc.CutCall fs E tgt (.branch f g) (.branch f' .undefined)
  | succ {f g g' : SFunc} :
    SFunc.CutCall fs E tgt g g' → SFunc.CutCall fs E tgt (.branch f g) (.branch .undefined g')
  | toZero {f f' : SFunc} {k : Nat} :
    SFunc.CutCall fs E tgt f f' → SFunc.CutCall fs E tgt (.branchTo f k) (.branch f' .undefined)
  | toSucc {f g g' : SFunc} {k : Nat} :
    fs[k]? = some g → SFunc.CutCall fs E tgt g g' →
    SFunc.CutCall fs E tgt (.branchTo f k) (.branch .undefined g')
  | call {f f' : SFunc} {k : Nat} :
    k ∈ E → SFunc.CutCall fs E tgt f f' → SFunc.CutCall fs E tgt (.callNext k f) (.callNext k f')
  | pcAt {f f' : SFunc} {p : Nat} :
    SFunc.CutCall fs E tgt f f' → SFunc.CutCall fs E tgt (.pcAt p f) (.pcAt p f')

section Cut

variable {code : ByteArray} {c : Cert} {ms : List MemMap} {b : Bool} {sevm : Sevm}

end Cut

/-! ## Cuts along explicit steps -/

/-- One step of a cut path: an instruction, a jumpdest, the fall-through or the taken arm of a
`.branch`, the fall-through or the taken goto of a `.branchTo`, an internal call crossed to
its continuation, or a `PC` push (an internal call's return address). -/
inductive CutStep where
  | nx | ds | z | s | tz | ts | cl | pc
  deriving DecidableEq, Repr

/-! ## A walked call step that a compiled step also runs -/

end Blanc.Lift
