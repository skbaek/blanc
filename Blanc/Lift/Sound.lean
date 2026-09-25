import Blanc.Lift.Check

/-!
# The lifting theorem (safety direction)

`lift_sound`: if a certificate checks against the bytes, every successful Jaune
execution of those bytes from pc `0` with an empty stack is a synthetic run of
the certificate's program.  It is stated over arbitrary bytes and certificates;
a contract instantiates it with one kernel-checked `Cert.check … = true`.

The proof is one strong recursion over `Exec.Deriv` (`node_sound`).  Its
invariant relates the concrete operand stack to an abstract frame: the stack is
`S ++ base`, where `S` matches the frame word by word (`FrameMatches ρ`, with
`.ret` read as the current function's return address `ρ`) and `base` belongs to
the callers and is left untouched.  A node either halts, or returns: the current
function jumps to `ρ` leaving exactly `m` words above `base`, and the remaining
derivation from `ρ` is strictly smaller, which is what lets the caller's
`callNext` continue by recursion.
-/

namespace Blanc.Lift

open Jaune AbstractStackSafety

/-- One abstract word describes one concrete word, reading `.ret` as `ρ`. -/
def AVal.Matches (ρ : B256) : AVal → B256 → Prop
  | .const c, w => w = c
  | .ret, w => w = ρ
  | .unk, _ => True

def FrameMatches (ρ : B256) (a : List AVal) (s : List B256) : Prop :=
  List.Forall₂ (AVal.Matches ρ) a s

/-- The recursion invariant.  For a successful derivation at a node checked
with frame `a` and return arity `m`: the node's run halts with the derivation's
result, or the current function returns — then `.ret` occurs in the frame, the
run returns `devm'` whose stack is `S' ++ base` with `S'.length = m`, and the
rest of the execution is a strictly smaller derivation from `ρ`. -/
def NodeClaim (code : ByteArray) (c : Cert) (pk : Exec.Deriv) : Prop :=
  ∀ (post : Devm), pk.exn = .ok post → pk.sevm.code = code →
  ∀ (m : Nat) (a : List AVal) (f : SFunc) (ρ : B256) (S base : List B256),
    checkNode code c.entries m pk.pc a f = true →
    pk.devm.stack = S ++ base → FrameMatches ρ a S →
    SFunc.Run c.prog pk.sevm pk.devm f (.halted post) ∨
    (AVal.ret ∈ a ∧
      ∃ (devm' : Devm) (S' : List B256) (exc' : Exec ρ.toNat pk.sevm devm' (.ok post)),
        Exec.Deriv.lt ⟨ρ.toNat, pk.sevm, devm', .ok post, exc'⟩ pk ∧
        SFunc.Run c.prog pk.sevm pk.devm f (.returned devm') ∧
        devm'.stack = S' ++ base ∧ S'.length = m)

theorem node_sound {code : ByteArray} {c : Cert} (hc : Cert.check code c = true) :
    ∀ pk : Exec.Deriv, NodeClaim code c pk := by
  sorry

/-- **The lifting theorem.**  A successful execution of certified bytes from
pc `0` with an empty operand stack is a run of the certified program. -/
theorem lift_sound {code : ByteArray} {c : Cert} (hc : Cert.check code c = true)
    {sevm : Sevm} {pre post : Devm} (hcode : sevm.code = code)
    (hstack : pre.stack = []) (exc : Exec 0 sevm pre (.ok post)) :
    SProg.Run c.prog sevm pre post := by
  sorry

end Blanc.Lift
