import Blanc.Lift.InvWalkOps
import Blanc.Lift.InvWalkWorld

/-!
# Inverting successful synthetic runs: failing arms, calls, gotos and world steps

Companions to `InvWalk.lean`:

* `SFunc.noOk`, a decidable test for trees built only of straight-line steps and branches over
  `REVERT`/`undefined` terminals, with `SFunc.RunCutP.false_of_noOk`
  (a plain run is the cut run with nothing cut): such a tree has no successful run at all, so every `REVERT` arm
  of an inversion walk closes by `(by decide)`;
* `SFunc.noHalt` and the closed entry sets `NoHaltSet`, with `SFunc.RunP.not_halted` and
  `SFunc.RunP.not_halted_entry`: trees whose only terminals are `REVERT`, returns and
  `undefined` never halt;
* `ric_branchTo`/`ric_branchToCut` for conditional gotos, and `ric_call`/`ri_call` for internal
  calls (`callNext`), the converses of `rx_branchTo_*` and `rx_callRet`;
* the world steps `ri_sload` (successor over `afterSload`) and `ri_log1` (the entry appended by
  `addLog`), the converses of `rx_sload_sel` and `rx_log1`.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-! ## Trees with no successful run -/

/-! ## Trees that cannot halt -/

/-- A run of an entry in a `NoHaltSet` cannot halt. -/
theorem SFunc.RunP.not_halted_entry {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {S : List Nat} (hS : NoHaltSet fs S = true)
    {k : Nat} (hkS : k ∈ S) {g : SFunc} (hk : fs[k]? = some g)
    {sevm : Sevm} {devm : Devm} {D : Devm} {o : Outcome}
    (run : SFunc.RunP P fs sevm devm g o) (ho : o = .halted D) : False := by
  have closed : ∀ {k g}, k ∈ S → fs[k]? = some g →
      g.noHalt = true ∧ g.refs.all (· ∈ S) = true := by
    intro k g hk hget
    have h := (List.all_eq_true.mp hS) k hk
    rw [hget] at h
    simpa only [List.all_eq_true, decide_eq_true_eq, Bool.and_eq_true] using h
  have ht := closed hkS hk
  exact SFunc.RunP.not_halted hS ht.1 ht.2 run ho

/-! ## Gotos and calls of cut runs -/

section Control

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {G : Nat} {f g : SFunc} {r : Seg}

end Control

/-! ## Uncut runs

The segment statements are over `SFunc.Run`; `SFunc.Run.cut` moves one to the cut form with
nothing cut, where every `ric_*` lemma applies with `C = []`, and `SFunc.RunCut.uncut` moves
back. -/

/-! ## World steps -/

section World

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- `LOG1`, inverted: the successor's base carries the entry `rx_log1` appends, over the bytes
the window reads; memory is the window read's image. -/
theorem ri_log1 {i sz t : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (i :: sz :: t :: S) M G) (.reg (.log 1)) d) :
    ∃ G', d = St (b.addLog ⟨sevm.currentTarget, [t], (M.read i.toNat sz.toNat).1⟩) S
      (M.read i.toNat sz.toNat).2 G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rw [show (St b (i :: sz :: t :: S) M G).popToNat = .ok (i.toNat, St b (sz :: t :: S) M G)
    from rfl] at run
  simp only [Except.bind_ok] at run
  rw [show (St b (sz :: t :: S) M G).popToNat = .ok (sz.toNat, St b (t :: S) M G)
    from rfl] at run
  simp only [Except.bind_ok] at run
  rw [show (St b (t :: S) M G).popN ((1 : Fin 5) : Nat) = .ok ([t], St b S M G) from rfl] at run
  simp only [Except.bind_ok] at run
  rcases Except.bind_eq_ok run with ⟨s1, h1, h2⟩
  rcases Except.bind_eq_ok h2 with ⟨_, -, h3⟩
  cases h3
  have e1 := Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas h1)
  refine ⟨s1.gasLeft, ?_⟩
  rw [e1]
  rfl

end World

end Blanc.Lift
