import Blanc.Compiled

/-!
# Synthetic programs for lifted bytecode

A sibling of `Func` for code that Blanc did not compile.  `Func` and its
layout (`Prog.compile`) stay untouched; this module family relates arbitrary
deployed bytes to a structured program through a checked certificate
(`Blanc/Lift/Check.lean`) and one generic theorem (`Blanc/Lift/Sound.lean`).

Every node except `callNext`'s continuation corresponds to exactly one
instruction of the bytes:

* `next n f` — the non-jump instruction `n`, then `f`;
* `last l` — the halting instruction `l`;
* `dest f` — a `JUMPDEST`, then `f` (an entry reached by a jump starts with one,
  and so does any block reached by falling through into a `JUMPDEST`);
* `branch f g` — a `JUMPI`: it pops the destination and the condition, falls
  through to `f` on zero and continues with `g` (the tree at the destination)
  otherwise;
* `branchTo f k` — a `JUMPI` whose destination is entry `k`, entered as a goto
  (a loop closed by a conditional back-edge); it falls through to `f` on zero;
* `jump k` — a `JUMP` to entry `k`, as a goto within the current frame: loop
  heads, join points and shared tails;
* `callNext k f` — a `JUMP` to entry `k` that runs it as a callee; if the callee
  returns, execution continues with `f` (the tree at the return tag);
* `ret` — a `JUMP` through a return tag: returns to the innermost pending
  `callNext`;
* `undefined` — a byte Jaune cannot decode (`0xFE` and unassigned opcodes).  It
  has no rule: reaching it never succeeds.

Return addresses stay on the stack: every jump rule pops exactly the words the
instruction pops, whatever their values.  That the popped destination is the
right one is the bridge's business, not the semantics'.

The relation is the safety relation, over successful frames only, with gas
weakened to `Devm.Burn` exactly as in `Func.Run`.
-/

namespace Blanc.Lift

open Jaune

inductive SFunc : Type
  | branch : SFunc → SFunc → SFunc
  | branchTo : SFunc → Nat → SFunc
  | last : Linst → SFunc
  | next : Ninst → SFunc → SFunc
  | dest : SFunc → SFunc
  | jump : Nat → SFunc
  | callNext : Nat → SFunc → SFunc
  | ret : SFunc
  | undefined : SFunc

/-- How a synthetic run ends: the frame halted successfully, or the current
callee returned to its caller. -/
inductive Outcome : Type
  | halted : Devm → Outcome
  | returned : Devm → Outcome

inductive SFunc.Run (fs : List SFunc) (sevm : Sevm) :
    Devm → SFunc → Outcome → Prop
  | zero {devm devm' : Devm} {f g : SFunc} {o : Outcome} (d : B256) :
    Devm.PopBurn [d, 0] devm devm' →
    SFunc.Run fs sevm devm' f o →
    SFunc.Run fs sevm devm (.branch f g) o
  | succ {devm devm' : Devm} {f g : SFunc} {o : Outcome} (d w : B256) :
    w ≠ 0 →
    Devm.PopBurn [d, w] devm devm' →
    SFunc.Run fs sevm devm' g o →
    SFunc.Run fs sevm devm (.branch f g) o
  | toZero {devm devm' : Devm} {f : SFunc} {k : Nat} {o : Outcome} (d : B256) :
    Devm.PopBurn [d, 0] devm devm' →
    SFunc.Run fs sevm devm' f o →
    SFunc.Run fs sevm devm (.branchTo f k) o
  | toSucc {devm devm' : Devm} {f g : SFunc} {k : Nat} {o : Outcome} (d w : B256) :
    w ≠ 0 →
    fs[k]? = some g →
    Devm.PopBurn [d, w] devm devm' →
    SFunc.Run fs sevm devm' g o →
    SFunc.Run fs sevm devm (.branchTo f k) o
  | last {devm devm' : Devm} {l : Linst} :
    Linst.Run sevm devm l (.ok devm') →
    SFunc.Run fs sevm devm (.last l) (.halted devm')
  | next {devm devm' : Devm} {n : Ninst} {f : SFunc} {o : Outcome} :
    Ninst.Run sevm devm n devm' →
    SFunc.Run fs sevm devm' f o →
    SFunc.Run fs sevm devm (.next n f) o
  | dest {devm devm' : Devm} {f : SFunc} {o : Outcome} :
    Devm.Burn devm devm' →
    SFunc.Run fs sevm devm' f o →
    SFunc.Run fs sevm devm (.dest f) o
  | jump {devm devm' : Devm} {k : Nat} {f : SFunc} {o : Outcome} (d : B256) :
    fs[k]? = some f →
    Devm.PopBurn [d] devm devm' →
    SFunc.Run fs sevm devm' f o →
    SFunc.Run fs sevm devm (.jump k) o
  | ret {devm devm' : Devm} (d : B256) :
    Devm.PopBurn [d] devm devm' →
    SFunc.Run fs sevm devm .ret (.returned devm')
  | callHalt {devm devm' devm'' : Devm} {k : Nat} {f g : SFunc} (d : B256) :
    fs[k]? = some g →
    Devm.PopBurn [d] devm devm' →
    SFunc.Run fs sevm devm' g (.halted devm'') →
    SFunc.Run fs sevm devm (.callNext k f) (.halted devm'')
  | callRet {devm devm' devm'' : Devm} {k : Nat} {f g : SFunc} {o : Outcome}
      (d : B256) :
    fs[k]? = some g →
    Devm.PopBurn [d] devm devm' →
    SFunc.Run fs sevm devm' g (.returned devm'') →
    SFunc.Run fs sevm devm'' f o →
    SFunc.Run fs sevm devm (.callNext k f) o

/-- A whole frame: entry `0` runs from the frame's initial state and halts. -/
def SProg.Run (fs : List SFunc) (sevm : Sevm) (devm devm' : Devm) : Prop :=
  ∃ f, fs[0]? = some f ∧ SFunc.Run fs sevm devm f (.halted devm')

/-- `undefined` never runs. -/
theorem SFunc.Run.not_undefined {fs : List SFunc} {sevm : Sevm} {devm : Devm}
    {o : Outcome} : ¬ SFunc.Run fs sevm devm .undefined o := by
  intro h; cases h

end Blanc.Lift
