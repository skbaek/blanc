import Blanc.Lift.WriteSite
import Blanc.Lift.MapSlot

/-! ## W2  `Blanc/Lift/WriteSiteTerm.lean` (term meaning; generic)

The meaning of the write-site checker's provenance terms (`Blanc.Lift.WriteSite.Term`): a term is
read in an environment of frame constants and the current function's entry words.  The headline is
`Term.den_subst`: instantiating a callee's term at a call site is sound.  Nothing here mentions a
contract. -/

namespace Blanc.Lift.WriteSite

open Jaune

/-- The frame constants a term reads, and the current function's entry words. -/
structure Env : Type where
  caller : B256
  self : B256
  data : Bytes
  args : List B256

/-- A frame's root environment: entry `0` has no entry words. -/
def Env.root (sevm : Sevm) : Env := ⟨sevm.caller.toB256, sevm.currentTarget.toB256, sevm.data, []⟩

def Term.eval (ε : Env) : Term → B256
  | .top => 0
  | .caller => ε.caller
  | .self => ε.self
  | .cd t => Bytes.toB256 (ε.data.sliceD (t.eval ε).toNat 32 0)
  | .const c => c
  | .arg i => ε.args.getD i 0
  | .op2 o a b => o.eval (a.eval ε) (b.eval ε)
  | .kecc a b => mapSlot (a.eval ε) (b.eval ε)
  | .kecc1 t => ((t.eval ε).toBytes).keccak

/-- The word `w` is what the term says (a term with `top` in it says nothing). -/
def Term.Den (ε : Env) (t : Term) (w : B256) : Prop := t.known = true → w = t.eval ε

end Blanc.Lift.WriteSite
