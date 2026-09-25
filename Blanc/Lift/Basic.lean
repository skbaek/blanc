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

/-- The run relation of a synthetic tree, with the relation `P` for its
nonterminal instructions.  `SFunc.Run` is `P := Ninst.Run`; a stronger `P`
records more about each step (e.g. where its child derivation sits). -/
inductive SFunc.RunP (P : Sevm → Devm → Ninst → Devm → Prop) (fs : List SFunc) (sevm : Sevm) :
    Devm → SFunc → Outcome → Prop
  | zero {devm devm' : Devm} {f g : SFunc} {o : Outcome} (d : B256) :
    Devm.PopBurn [d, 0] devm devm' →
    SFunc.RunP P fs sevm devm' f o →
    SFunc.RunP P fs sevm devm (.branch f g) o
  | succ {devm devm' : Devm} {f g : SFunc} {o : Outcome} (d w : B256) :
    w ≠ 0 →
    Devm.PopBurn [d, w] devm devm' →
    SFunc.RunP P fs sevm devm' g o →
    SFunc.RunP P fs sevm devm (.branch f g) o
  | toZero {devm devm' : Devm} {f : SFunc} {k : Nat} {o : Outcome} (d : B256) :
    Devm.PopBurn [d, 0] devm devm' →
    SFunc.RunP P fs sevm devm' f o →
    SFunc.RunP P fs sevm devm (.branchTo f k) o
  | toSucc {devm devm' : Devm} {f g : SFunc} {k : Nat} {o : Outcome} (d w : B256) :
    w ≠ 0 →
    fs[k]? = some g →
    Devm.PopBurn [d, w] devm devm' →
    SFunc.RunP P fs sevm devm' g o →
    SFunc.RunP P fs sevm devm (.branchTo f k) o
  | last {devm devm' : Devm} {l : Linst} :
    Linst.Run sevm devm l (.ok devm') →
    SFunc.RunP P fs sevm devm (.last l) (.halted devm')
  | next {devm devm' : Devm} {n : Ninst} {f : SFunc} {o : Outcome} :
    P sevm devm n devm' →
    SFunc.RunP P fs sevm devm' f o →
    SFunc.RunP P fs sevm devm (.next n f) o
  | dest {devm devm' : Devm} {f : SFunc} {o : Outcome} :
    Devm.Burn devm devm' →
    SFunc.RunP P fs sevm devm' f o →
    SFunc.RunP P fs sevm devm (.dest f) o
  | jump {devm devm' : Devm} {k : Nat} {f : SFunc} {o : Outcome} (d : B256) :
    fs[k]? = some f →
    Devm.PopBurn [d] devm devm' →
    SFunc.RunP P fs sevm devm' f o →
    SFunc.RunP P fs sevm devm (.jump k) o
  | ret {devm devm' : Devm} (d : B256) :
    Devm.PopBurn [d] devm devm' →
    SFunc.RunP P fs sevm devm .ret (.returned devm')
  | callHalt {devm devm' devm'' : Devm} {k : Nat} {f g : SFunc} (d : B256) :
    fs[k]? = some g →
    Devm.PopBurn [d] devm devm' →
    SFunc.RunP P fs sevm devm' g (.halted devm'') →
    SFunc.RunP P fs sevm devm (.callNext k f) (.halted devm'')
  | callRet {devm devm' devm'' : Devm} {k : Nat} {f g : SFunc} {o : Outcome}
      (d : B256) :
    fs[k]? = some g →
    Devm.PopBurn [d] devm devm' →
    SFunc.RunP P fs sevm devm' g (.returned devm'') →
    SFunc.RunP P fs sevm devm'' f o →
    SFunc.RunP P fs sevm devm (.callNext k f) o

/-- The run relation of a synthetic tree over Jaune's instruction steps. -/
abbrev SFunc.Run (fs : List SFunc) (sevm : Sevm) : Devm → SFunc → Outcome → Prop :=
  SFunc.RunP Ninst.Run fs sevm

/-- A run under a step relation is a run under any weaker one. -/
theorem SFunc.RunP.mono {P Q : Sevm → Devm → Ninst → Devm → Prop}
    (hPQ : ∀ {s d n d'}, P s d n d' → Q s d n d')
    {fs : List SFunc} {sevm : Sevm} {devm : Devm} {f : SFunc} {o : Outcome}
    (run : SFunc.RunP P fs sevm devm f o) : SFunc.RunP Q fs sevm devm f o := by
  induction run with
  | zero d pop _ ih => exact .zero d pop ih
  | succ d w hnz pop _ ih => exact .succ d w hnz pop ih
  | toZero d pop _ ih => exact .toZero d pop ih
  | toSucc d w hnz lookup pop _ ih => exact .toSucc d w hnz lookup pop ih
  | last h => exact .last h
  | next h _ ih => exact .next (hPQ h) ih
  | dest burn _ ih => exact .dest burn ih
  | jump d lookup pop _ ih => exact .jump d lookup pop ih
  | ret d pop => exact .ret d pop
  | callHalt d lookup pop _ ih => exact .callHalt d lookup pop ih
  | callRet d lookup pop _ _ ihRun ihTail => exact .callRet d lookup pop ihRun ihTail

/-- A whole frame: entry `0` runs from the frame's initial state and halts. -/
def SProg.RunP (P : Sevm → Devm → Ninst → Devm → Prop) (fs : List SFunc) (sevm : Sevm)
    (devm devm' : Devm) : Prop :=
  ∃ f, fs[0]? = some f ∧ SFunc.RunP P fs sevm devm f (.halted devm')

/-- A whole frame over Jaune's instruction steps. -/
abbrev SProg.Run (fs : List SFunc) (sevm : Sevm) (devm devm' : Devm) : Prop :=
  SProg.RunP Ninst.Run fs sevm devm devm'

theorem SProg.RunP.mono {P Q : Sevm → Devm → Ninst → Devm → Prop}
    (hPQ : ∀ {s d n d'}, P s d n d' → Q s d n d')
    {fs : List SFunc} {sevm : Sevm} {devm devm' : Devm}
    (run : SProg.RunP P fs sevm devm devm') : SProg.RunP Q fs sevm devm devm' := by
  obtain ⟨f, hf, r⟩ := run
  exact ⟨f, hf, r.mono hPQ⟩

/-- `undefined` never runs. -/
theorem SFunc.RunP.not_undefined {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} {devm : Devm}
    {o : Outcome} : ¬ SFunc.RunP P fs sevm devm .undefined o := by
  intro h; cases h

theorem SFunc.Run.not_undefined {fs : List SFunc} {sevm : Sevm} {devm : Devm}
    {o : Outcome} : ¬ SFunc.Run fs sevm devm .undefined o := by
  intro h; cases h

end Blanc.Lift
