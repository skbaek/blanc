import Batteries.Tactic.OpenPrivate
import Blanc.Lift.MemMap
import Jaune.StaticcallEffects

/-!
# Instruction capabilities for a STATICCALL lift step

The two fields are the existing node proof's checked stack-transfer and
combined frame/memory-map obligations. STATICCALL supplies both on every
fork from its original successful instruction run. The old lane delegates
to its existing proofs. This module proves no node recursion or full lift.
-/

namespace Blanc.Lift

open Jaune AbstractStackSafety
open private matches_six from Blanc.Lift.Transfer

/-- Check a restriction on external instruction families throughout a
synthetic tree. Internal certificate calls retain their separate references. -/
def SFunc.execsSatisfy (allowed : Xinst → Bool) : SFunc → Bool
  | .next (.exec x) f => allowed x && f.execsSatisfy allowed
  | .next _ f | .dest f | .branchTo f _ | .callNext _ f | .pcAt _ f =>
      f.execsSatisfy allowed
  | .branch f g => f.execsSatisfy allowed && g.execsSatisfy allowed
  | _ => true

/-- Admitting every external instruction admits every tree. -/
theorem SFunc.execsSatisfy_true (f : SFunc) : f.execsSatisfy (fun _ => true) = true := by
  induction f with
  | next n f ih => cases n <;> simp_all only [SFunc.execsSatisfy, Bool.true_and]
  | _ => simp_all only [SFunc.execsSatisfy, Bool.and_self]

/-- The original continuation retains the restriction of a next node. -/
theorem SFunc.execsSatisfy_next_tail {allowed : Xinst → Bool} {n : Ninst} {f : SFunc}
    (only : (SFunc.next n f).execsSatisfy allowed = true) : f.execsSatisfy allowed = true := by
  cases n <;> simp_all only [SFunc.execsSatisfy, Bool.and_eq_true]

/-- The two semantic obligations consumed by one checked lift step. -/
structure StepCapability (sevm : Sevm) (n : Ninst) : Prop where
  stack : ∀ {pre post : Devm} {input output : Pattern},
    Matches input pre.stack → ninstTransfer n input = some output →
    Ninst.Run sevm pre n post → Matches output post.stack
  memory : ∀ (b : Bool) {pre post : Devm} {a a' : List AVal}
      {μ : MemMap} {ρ : B256} {S S' base : List B256},
    FrameMatches ρ a S → pre.stack = S ++ base →
    MemMatches ρ μ pre.memory → Ninst.Run sevm pre n post →
    post.stack = S' ++ base → FrameMatches ρ a' S' →
    FrameMatches ρ (if b then memFold (memTop n a μ) a' else a') S' ∧
      MemMatches ρ (if b then absMem n a μ else []) post.memory

/-- The actual six operands yield the bounded reply write and agreement
outside the whole prepaid output window, including short or empty replies. -/
theorem staticcall_window_effects {sevm : Sevm} {pre post : Devm}
    {g t ii size oi os : B256} {rest : List B256}
    (stack : pre.stack = g :: t :: ii :: size :: oi :: os :: rest)
    (run : Ninst.Run sevm pre (.exec .staticcall) post) :
    (∃ flag, post.stack = flag :: rest) ∧
      ∃ bytes : Bytes, bytes.length ≤ os.toNat ∧
        post.memory = (pre.memory.extends
          [(ii.toNat, size.toNat), (oi.toNat, os.toNat)]).write oi.toNat bytes ∧
        Mem.AgreeOutside pre.memory post.memory oi.toNat (oi.toNat + os.toNat) := by
  obtain ⟨status, bytes, bounded, memory⟩ := Ninst.staticcall_run_effects stack run
  refine ⟨status, bytes, bounded, memory, ?_⟩
  rw [memory]
  exact (Mem.extends_agree _ _ _ _).trans
    ((Mem.write_agree _ _ _).mono (Nat.le_refl _) (Nat.add_le_add_left bounded _))

/-- A real STATICCALL's complete-stack Pattern and surviving map entries,
retaining the exact byte witness and original input/output extension. -/
theorem staticcall_lift_effects {sevm : Sevm} {pre post : Devm}
    {g t ii size oi os : B256} {rest : List B256}
    {tail : Pattern} {ρ : B256} {μ : MemMap}
    (stack : pre.stack = g :: t :: ii :: size :: oi :: os :: rest)
    (run : Ninst.Run sevm pre (.exec .staticcall) post)
    (tailMatches : Matches tail rest) (memoryMatches : MemMatches ρ μ pre.memory) :
    (∃ flag, post.stack = flag :: rest ∧ Matches (none :: tail) post.stack) ∧
      ∃ bytes : Bytes, bytes.length ≤ os.toNat ∧
        post.memory = (pre.memory.extends
          [(ii.toNat, size.toNat), (oi.toNat, os.toNat)]).write oi.toNat bytes ∧
        MemMatches ρ (memKill μ oi.toNat (oi.toNat + os.toNat)) post.memory := by
  obtain ⟨⟨flag, status⟩, bytes, bounded, memory, agreement⟩ := staticcall_window_effects stack run
  refine ⟨⟨flag, status, ?_⟩, bytes, bounded, memory, MemMatches.agree agreement memoryMatches⟩
  rw [status]
  exact tailMatches.push_any flag

private theorem staticcall_pattern {sevm : Sevm} {pre post : Devm}
    {input output : Pattern} (matched : Matches input pre.stack)
    (checked : ninstTransfer (.exec .staticcall) input = some output)
    (run : Ninst.Run sevm pre (.exec .staticcall) post) : Matches output post.stack := by
  match input, checked with
  | a :: b :: c :: d :: e :: f :: tail, checked =>
      simp only [ninstTransfer, staticcallTransfer, Option.some.injEq] at checked
      cases checked
      obtain ⟨g, t, ii, size, oi, os, rest, stack, tailMatches⟩ := matches_six matched
      obtain ⟨flag, status⟩ := (Ninst.staticcall_run_effects stack run).1
      rw [status]
      exact tailMatches.push_any flag

private theorem staticcall_absMem {sevm : Sevm} {pre post : Devm} {a : List AVal}
    {μ : MemMap} {ρ : B256} {S base : List B256}
    (frame : FrameMatches ρ a S) (stack : pre.stack = S ++ base)
    (memory : MemMatches ρ μ pre.memory) (run : Ninst.Run sevm pre (.exec .staticcall) post) :
    MemMatches ρ (absMem (.exec .staticcall) a μ) post.memory := by
  unfold absMem
  split
  · contradiction
  · contradiction
  · rcases frame with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨oi, _ | ⟨os, _⟩⟩⟩⟩⟩⟩
    simp only [AVal.Matches] at oi os
    subst oi os
    obtain ⟨_, _, _, _, agreement⟩ := staticcall_window_effects
      (by simpa only [List.cons_append] using stack) run
    exact MemMatches.agree agreement memory
  · change MemMatches ρ [] post.memory
    exact memMatches_nil _ _

/-- STATICCALL discharges both actual lift obligations on every fork. -/
theorem staticcall_capability (sevm : Sevm) : StepCapability sevm (.exec .staticcall) where
  stack := staticcall_pattern
  memory := by
    intro b pre post a a' μ ρ S S' base frame stack memory run _ frame'
    cases b with
    | false => exact ⟨frame', memMatches_nil _ _⟩
    | true =>
        exact ⟨frame', staticcall_absMem frame stack memory run⟩

/-- The original no-state-gas/non-exec lane reuses its existing semantic proofs. -/
theorem capability_of_lane {sevm : Sevm} {n : Ninst}
    (lane : sevm.benvStat.rules.stateGas = none ∨ ∀ x, n ≠ .exec x) : StepCapability sevm n where
  stack := ninstTransfer_run_lane lane
  memory := by
    intro b pre post a a' μ ρ S S' base frame stack memory run postStack frame'
    exact step_mem_sound_lane b lane frame stack memory run postStack frame'

/-- Add STATICCALL to the old lane without changing any other instruction's proof. -/
theorem capability_of_lane_or_staticcall {sevm : Sevm} {n : Ninst}
    (admitted : (sevm.benvStat.rules.stateGas = none ∨ ∀ x, n ≠ .exec x) ∨ n = .exec .staticcall) :
    StepCapability sevm n := by
  rcases admitted with lane | rfl
  · exact capability_of_lane lane
  · exact staticcall_capability sevm

/-- An admitted exec node uses its supplied law; non-exec nodes reuse the old lane. -/
theorem capability_of_next {sevm : Sevm} {allowed : Xinst → Bool} {n : Ninst} {f : SFunc}
    (steps : ∀ x, allowed x = true → StepCapability sevm (.exec x))
    (only : (SFunc.next n f).execsSatisfy allowed = true) : StepCapability sevm n := by
  cases n
  case exec x =>
    simp only [SFunc.execsSatisfy, Bool.and_eq_true] at only
    exact steps x only.1
  all_goals exact capability_of_lane (Or.inr (by intro x impossible; cases impossible))

end Blanc.Lift
