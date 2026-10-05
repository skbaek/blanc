import Blanc.Lift.Cursor

/-!
# Certificate call sites: the vocabulary

A frame of certified bytes spawns its children only at nodes of its own same-frame chain, and
every such node sits at a checked certificate cursor (`reach_of_parentPrefix`).  A *call site* is
therefore named by the cursor's tree: `SFunc.LineSuffix t f` says the tree `t` is the generated
tree `f` with straight-line heads stripped, so a CALL inside the straight prefix of `f` is pinned by
`t = .next (.exec .call) g` and `SFunc.LineSuffix t f`.

`CallInputSelector N sel` is the fact a backward walk to a CALL node establishes: the CALL's input
window, as the node's memory holds it, carries the selector `sel`, read exactly as the spawned
child's `Blanc.Sevm.selector` reads its calldata (`Bytes.selector`).
-/

namespace Blanc.Lift

open Jaune

/-- `g` is `f` with zero or more straight-line heads (`.next`, `.dest`) stripped. -/
inductive SFunc.LineSuffix : SFunc → SFunc → Prop
  | refl (f : SFunc) : SFunc.LineSuffix f f
  | next {n : Ninst} {g f : SFunc} : SFunc.LineSuffix g f → SFunc.LineSuffix g (.next n f)
  | dest {g f : SFunc} : SFunc.LineSuffix g f → SFunc.LineSuffix g (.dest f)

/-- The selector calldata `d` carries, read as `Blanc.Sevm.selector` reads a frame's calldata:
the top four bytes of the zero-padded first word. -/
def Bytes.selector (d : Bytes) : B256 := Bytes.toB256 (d.sliceD 0 32 0) >>> 224

/-- The node's operand stack has CALL's layout (`gas`, `to`, `value`, input offset, input size,
…) and the input window its memory holds carries the selector `sel`. -/
def CallInputSelector (N : Exec.Deriv) (sel : B256) : Prop :=
  ∃ (g c v ii is : B256) (rest : List B256),
    N.devm.stack = g :: c :: v :: ii :: is :: rest ∧
      Bytes.selector (N.devm.memory.read ii.toNat is.toNat).1 = sel

end Blanc.Lift
