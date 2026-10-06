import Blanc.Lift.StaticCall

/-!
# What a successful `CALL` step leaves

The mutable sibling of `StaticCallPost`: a successful `CALL` step from `St b (… :: S) M G`
leaves its flag on top of `S`; a set flag means the child message ran and the caller resumed,
so the output window is written with a prefix of the full returned data and the caller's own
output is unchanged. Nothing is said about the callee's storage effects: they are arbitrary
and are consumed elsewhere (for example by a turn fold over the child derivation).
-/

namespace Blanc.Lift

open Jaune AbstractStackSafety

/-- The caller-visible post state of a `CALL` step. -/
structure MutableCallPost (b d : Devm) (S : List B256) (M : Mem) (ii is oi os flag : B256) :
    Prop where
  stack : d.stack = flag :: S
  settled : flag ≠ 0 →
    d.memory = (M.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write oi.toNat
      (d.returnData.take os.toNat) ∧ d.output = b.output

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- **`CALL` to an arbitrary callee, inverted** to its caller-visible post state. -/
theorem ri_call_post {g c v ii is oi os : B256} {d : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    (h : Ninst.Run sevm (St b (g :: c :: v :: ii :: is :: oi :: os :: S) M G) (.exec .call) d) :
    ∃ flag, MutableCallPost b d S M ii is oi os flag := by
  have matched : Matches ((none :: none :: none :: none :: none :: none :: none :: S.map some) :
      Pattern) (St b (g :: c :: v :: ii :: is :: oi :: os :: S) M G).stack :=
    ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl,
      matches_some_map S⟩
  have transferred : Matches (none :: S.map some) d.stack := ninstTransfer_run hfork matched rfl h
  obtain ⟨flag, stack⟩ : ∃ flag, d.stack = flag :: S := by
    cases eq : d.stack with
    | nil => rw [eq] at transferred; exact transferred.elim
    | cons flag tail =>
      rw [eq] at transferred
      exact ⟨flag, by rw [matches_some_map_eq transferred.2]⟩
  refine ⟨flag, stack, ?_⟩
  intro nonzero
  have operands : (g :: c :: v :: ii :: is :: oi :: os :: S) <<+
      (St b (g :: c :: v :: ii :: is :: oi :: os :: S) M G).stack := by
    simpa only [List.append_nil, St.stack] using
      (pref_append (g :: c :: v :: ii :: is :: oi :: os :: S) [])
  rcases of_run_call_val_with_depth_frame operands h hfork with failed | entered
  · rw [stack] at failed
    exact absurd (pref_head_unique failed.1 (pref_append [flag] S)).symm nonzero
  · obtain ⟨parent, child, xl, dp, na, code, avail, pc, _, _, _, _, parentMemory, _,
      parentOutput, _, _, _, _, resume, _, returned, memory, _⟩ := entered
    refine ⟨?_, (Resume.call_output resume).trans parentOutput⟩
    rw [memory, parentMemory, returned]
    rfl

end Blanc.Lift
