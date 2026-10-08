import Blanc.Lift.UniswapV2Pair.PermitSource
import Blanc.Lift.UniswapV2Pair.SyncWalk

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The certified raw pc-zero permit run supplies its recovery STATICCALL as a step of the
very same derivation. -/
theorem permit_raw_in {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xd505accf)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      (224 : B256) ≤ sevm.data.length.toB256 - 4 ∧ sevm.isStatic = false ∧
      sevm.benvStat.time ≤ permitDeadline sevm ∧
      ∃ (gw : B256) (callGas : Nat) (d : Devm) (out : Bytes) (G' : Nat),
        PermitRawCallP (Blanc.Lift.StepIn ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩)
          sevm b 0xd505accf gw callGas d out ∧
        post = permitPublicPost sevm b d out 0xd505accf G' := by
  obtain ⟨f, entry, run'⟩ := lift_sound_in cert_check codeEq fork run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  obtain ⟨value, size, _, guarded⟩ := syncGuards_inv run'
  obtain ⟨_, routed⟩ := permit_selector_invP Blanc.Lift.StepIn.toRun selector guarded
  obtain ⟨guard, nonstatic, timely, gw, callGas, d, out, G', call, eq⟩ :=
    permitEntry_invP Blanc.Lift.StepIn.toRun fork routed
  exact ⟨value, size, guard, nonstatic, timely, gw, callGas, d, out, G', call,
    Outcome.halted.inj eq⟩

end Blanc.Lift.UniswapV2Pair
