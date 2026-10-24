import Blanc.Lift.UniswapV2Pair.PermitSource
import Blanc.Lift.UniswapV2Pair.SyncWalk

namespace Blanc.Lift.UniswapV2Pair

open Jaune

theorem permit_raw_inH {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (stateGas : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none)
    (selector : Blanc.Sevm.selector sevm = 0xd505accf)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      (224 : B256) ≤ sevm.data.length.toB256 - 4 ∧ sevm.isStatic = false ∧
      sevm.benvStat.time ≤ permitDeadline sevm ∧
      ∃ (gw : B256) (callGas : Nat) (d : Devm) (out : Bytes) (G' : Nat),
        PermitRawCallPH (Blanc.Lift.StepIn ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩)
          sevm b 0xd505accf gw callGas d out ∧
        post = permitPublicPostH sevm b d out 0xd505accf G' := by
  obtain ⟨f, entry, run'⟩ := lift_sound_in_noStateGas cert_check codeEq stateGas run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  obtain ⟨value, size, _, guarded⟩ := syncGuards_inv run'
  obtain ⟨_, routed⟩ := permit_selector_invP Blanc.Lift.StepIn.toRun selector guarded
  obtain ⟨guard, nonstatic, timely, gw, callGas, d, out, G', call, eq⟩ :=
    permitEntry_invPH Blanc.Lift.StepIn.toRun stateGas bal routed
  exact ⟨value, size, guard, nonstatic, timely, gw, callGas, d, out, G', call,
    Outcome.halted.inj eq⟩


end Blanc.Lift.UniswapV2Pair
