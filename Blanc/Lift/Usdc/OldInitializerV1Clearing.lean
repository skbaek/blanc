import Blanc.Lift.Usdc.ImplV1.Cert
import Blanc.Lift.Sound
import Blanc.Lift.RunPWalk
import Blanc.Lift.SolcStorageClear

/-!
# Actual V1 `initialize` zero-tail clearing

The actually reachable V1 zero-tail runs the legacy clearing loop: the helper
entry `t_2f0a_c42` (three-instruction prefix) reaches the clearing head
`t_2f10_c50`, whose store arm stages `.push [0x00]`, `.dup 1` (DUP2),
`.push [0x00]`, `.swap 0` (SWAP1), `.sstore`, and exits indirectly through the
shared return entry `t_2f2c_c51`. Every store in these runs is a literal zero
and no step executes an external instruction. The exact outcome remains the
actual one; no endpoint, seed, or completeness claim is made here.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift

/-- Every store in the actual V1 clearing head is a literal zero, and no step
executes an external instruction. The table entries are the actual `Cert`
entries at `50` (head) and `51` (shared return). -/
theorem v1Clear_zeroStores_noExec
    {R : Exec.Deriv} {sevm : Sevm} {pre : Devm} {out : Outcome}
    (run : SFunc.RunP (StepIn R) ImplV1.cert.prog sevm pre
      ImplV1.t_2f10_c50 out) :
    SFunc.RunP (fun s d n d' => StepIn R s d n d' ∧
      (n = .reg .sstore → ∀ key value rest, d.stack = key :: value :: rest → value = 0) ∧
      ∀ x, n ≠ .exec x)
      ImplV1.cert.prog sevm pre ImplV1.t_2f10_c50 out := by
  exact SolcStorageClear.legacyRunP_zeroStores_noExec
    (back := [0x2f, 0x10]) (exit := [0x2f, 0x28])
    (backBound := by decide) (exitBound := by decide) (k := 50) (j := 51)
    (fun step => StepIn.toRun step) rfl rfl (by decide) run

/-- The actual V1 helper entry keeps its three-instruction prefix
(`.push [0x2f, 0x2c]`, `.swap 1`, `.swap 0`) and the real loop/exit path,
with the same literal-zero/no-execution enrichment. -/
theorem v1ClearEntry_zeroStores_noExec
    {R : Exec.Deriv} {sevm : Sevm} {pre : Devm} {out : Outcome}
    (run : SFunc.RunP (StepIn R) ImplV1.cert.prog sevm pre
      ImplV1.t_2f0a_c42 out) :
    SFunc.RunP (fun s d n d' => StepIn R s d n d' ∧
      (n = .reg .sstore → ∀ key value rest, d.stack = key :: value :: rest → value = 0) ∧
      ∀ x, n ≠ .exec x)
      ImplV1.cert.prog sevm pre ImplV1.t_2f0a_c42 out := by
  unfold ImplV1.t_2f0a_c42 at run ⊢
  cases run with
  | dest burn run =>
    obtain ⟨m1, s1, run⟩ := rpw_next run
    obtain ⟨m2, s2, run⟩ := rpw_next run
    obtain ⟨m3, s3, run⟩ := rpw_next run
    have clear := v1Clear_zeroStores_noExec run
    refine SFunc.RunP.dest burn (SFunc.RunP.next
      ⟨s1, (by intro h; cases h), (by intro x h; cases h)⟩ (SFunc.RunP.next
      ⟨s2, (by intro h; cases h), (by intro x h; cases h)⟩ (SFunc.RunP.next
      ⟨s3, (by intro h; cases h), (by intro x h; cases h)⟩ clear)))

end Blanc.Lift.Usdc
