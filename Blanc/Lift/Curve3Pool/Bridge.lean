import Blanc.Lift.Curve3Pool.Check
import Blanc.Lift.Curve3Pool.Callee.GetDMem
import Blanc.Lift.FrameWalkNode

/-!
# Crossing the 3pool's exec-free callees from walked frame states

A frame walk on the actual derivation (`XAt`) that reaches an internal call into one of the
pool's exec-free callees (`_A`, `_xp`, `get_D`, …) crosses it with `xa_node_span`: the callee's
`SFunc` run is related to the walk's state, the walk resumes at the return tag in the actual
returned state, and the remaining direct children are unchanged.

* `checkedM`: the certificate's entries are checked (`cert_checkM`);
* `xa_callee`: the crossing for any entry with an empty declared memory map, an exec-free
  closed entry set and an exec-free tree, from a stack whose top matches the entry's frame;
* `xa_A`: the instance for `_A` (entry 27, pc `0xa9`, frame `[.ret]`, one return word), whose
  entry set is `[27]`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune

theorem checkedM : Cert.CheckedM code cert mems true := Cert.checkedM_of_checkM cert_checkM

/-- **Crossing a certified exec-free callee.**  Entry `k` (pc `e.pc`, frame `e.frame`, return
arity `e.rets`, empty declared memory map) of an exec-free closed entry set `E`, entered with
its frame `S` above the caller's `base` and its return address `ρ`: the callee halts the frame
with no further child, or returns to `ρ` with `e.rets` words above `base` and the same remaining
children. -/
theorem xa_callee {k : Nat} {e : Entry} {f : SFunc} {E : List Nat}
    (hk : cert.entries[k]? = some e) (hf : cert.prog[k]? = some f)
    (hm : mems.getD k [] = []) (hE : ExecFreeSet cert.prog E = true)
    (hfree : f.execFreeIn E = true)
    {sevm : Sevm} {post d : Devm} {ρ : B256} {S base : List B256} {L : List Exec.Frame}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hstack : d.stack = S ++ base) (hframe : FrameMatches ρ e.frame S)
    (h : XAt sevm post e.pc d L) :
    (SFunc.Run cert.prog sevm d f (.halted post) ∧ L = []) ∨
      ∃ (d' : Devm) (S' : List B256),
        SFunc.Run cert.prog sevm d f (.returned d') ∧ XAt sevm post ρ.toNat d' L ∧
        d'.stack = S' ++ base ∧ S'.length = e.rets := by
  have hcheck := checkedM k e f hk hf
  rw [hm] at hcheck
  exact xa_node_span checkedM hE hcode hfork hcheck hfree hstack hframe (memMatches_nil _ _) h

/-- `_A`'s entry set: its tree makes no call and references no other entry. -/
def aEntries : List Nat := [27]

theorem a_entry : cert.entries[27]? = some ⟨0xa9, [.ret], 1⟩ := rfl

theorem a_prog : cert.prog[27]? = some t_00a9_c27 := rfl

theorem a_mems : mems.getD 27 [] = [] := by decide

theorem a_execFreeSet : ExecFreeSet cert.prog aEntries = true := by decide

theorem a_free : t_00a9_c27.execFreeIn aEntries = true := by decide

/-- **`_A` crossed from a walked state.**  A walk at `_A`'s entry (`0xa9`) with the return
address `ρ` on top of the caller's stack `base`: `_A` halts the frame with no further child,
or returns to `ρ` with one word (the amplification coefficient) above `base`, in the actual
returned state and with the same remaining children. -/
theorem xa_A {sevm : Sevm} {post d : Devm} {ρ : B256} {base : List B256}
    {L : List Exec.Frame} (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hstack : d.stack = ρ :: base) (h : XAt sevm post 0xa9 d L) :
    (SFunc.Run cert.prog sevm d t_00a9_c27 (.halted post) ∧ L = []) ∨
      ∃ (d' : Devm) (A : B256),
        SFunc.Run cert.prog sevm d t_00a9_c27 (.returned d') ∧ XAt sevm post ρ.toNat d' L ∧
        d'.stack = A :: base := by
  rcases xa_callee a_entry a_prog a_mems a_execFreeSet a_free hcode hfork
      (S := [ρ]) (by rw [hstack]; rfl) (List.Forall₂.cons rfl .nil) h with
    h | ⟨d', S', run, hx, hst, hlen⟩
  · exact .inl h
  · match S', hlen with
    | [A], _ => exact .inr ⟨d', A, run, hx, hst⟩

/-- `get_D_mem`'s entry. -/
theorem gdm_entry : cert.entries[29]? = some ⟨0x7b7, [.ret, .unk, .unk, .unk, .unk], 1⟩ :=
  rfl

theorem gdm_prog : cert.prog[29]? = some t_07b7_c29 := rfl

theorem gdm_mems : mems.getD 29 [] = [] := by decide

/-- **`get_D_mem` crossed from a walked state.**  A walk at `get_D_mem`'s entry (`0x7b7`)
with the return address `ρ`, the three balances and `amp` above the caller's stack `base`:
`get_D_mem` halts the frame with no further child, or returns to `ρ` with one word (the
invariant `D`) above `base`, in the actual returned state and with the same remaining
children.  The entry closure (`gdmEntries`, `Callee/GetDMem.lean`) covers the inner
`get_D` call. -/
theorem xa_getDMem {sevm : Sevm} {post d : Devm} {ρ b0 b1 b2 amp : B256} {base : List B256}
    {L : List Exec.Frame} (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hstack : d.stack = ρ :: b0 :: b1 :: b2 :: amp :: base)
    (h : XAt sevm post 0x7b7 d L) :
    (SFunc.Run cert.prog sevm d t_07b7_c29 (.halted post) ∧ L = []) ∨
      ∃ (d' : Devm) (v : B256),
        SFunc.Run cert.prog sevm d t_07b7_c29 (.returned d') ∧ XAt sevm post ρ.toNat d' L ∧
        d'.stack = v :: base := by
  rcases xa_callee gdm_entry gdm_prog gdm_mems gdm_execFreeSet gdm_free hcode hfork
      (S := [ρ, b0, b1, b2, amp]) (by rw [hstack]; rfl)
      (List.Forall₂.cons rfl (List.Forall₂.cons trivial (List.Forall₂.cons trivial
        (List.Forall₂.cons trivial (List.Forall₂.cons trivial List.Forall₂.nil))))) h with
    h | ⟨d', S', run, hx, hst, hlen⟩
  · exact .inl h
  · match S', hlen with
    | [v], _ => exact .inr ⟨d', v, run, hx, hst⟩

end Blanc.Lift.Curve3Pool
