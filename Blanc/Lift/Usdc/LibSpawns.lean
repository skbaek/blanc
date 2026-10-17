import Blanc.Lift.Usdc.Lib.Check
import Blanc.Lift.Usdc.Constants
import Blanc.Lift.StaticOnlyFrames
import Blanc.Lift.CallSiteChildren
import Blanc.Lift.CallChildren
import Blanc.Lift.Quiet
import Blanc.StaticStorage

/-!
# What the linked `SignatureChecker` library spawns (C2b, nested level)

`lib_children`: a frame running the library runtime `Lib.code` from pc `0` spawns only static
children called by its storage owner (the certificate executes no external instruction but
`STATICCALL`, `parentPrefix_exec_staticcall_of_cert`), and a successful frame leaves its storage
owner's storage unchanged: the whole certificate is quiet (`QuietSet`: no `SSTORE`, no `LOG`, the
only call `STATICCALL`), so the lifted run keeps every storage map (`SFunc.Run.world_of_quiet`).
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc

theorem lib_staticOnly : ∀ f ∈ Lib.cert.prog, f.execsSatisfy Xinst.isStaticcall = true := by
  decide +kernel

theorem lib_quiet : QuietSet Lib.cert.prog (List.range Lib.cert.length) = true := by
  decide +kernel

/-- The library calls out only by `STATICCALL` and leaves its storage owner's storage unchanged. -/
theorem lib_children {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (codeEq : sevm.code = Lib.code) (fork : CoveredFork sevm.benvStat.fork) :
    (∀ c ∈ Exec.childFrames run, c.sevm.isStatic = true ∧ c.sevm.caller = sevm.currentTarget) ∧
    ∀ post, out = .ok post →
      post.state.getStor sevm.currentTarget = pre.state.getStor sevm.currentTarget := by
  refine ⟨fun c member => ?_, fun post hout => ?_⟩
  · obtain ⟨N, f, rsm, pc', cevm, chain, step, enter, childEq⟩ :=
      Exec.childFrames_spawnedAt run (.refl _) c member
    obtain ⟨x, hat, hx, -⟩ := Evm.step_spawn_inv step
    have hsx : x = .staticcall := parentPrefix_exec_staticcall_of_cert Lib.cert_check lib_staticOnly
      (root := ⟨0, sevm, pre, out, run⟩) rfl codeEq fork chain hat
    subst hsx
    have sevmEq : N.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
    have hcaller : cevm.sta.caller = f.inner.caller := by
      obtain ⟨benv, -, rfl⟩ := Frame.enter_run_inv enter
      rfl
    rw [childEq]
    exact ⟨(Frame.enter_run_isStatic enter).trans (Xinst.step_staticcall_spawn_isStatic hx),
      hcaller.trans ((Xinst.step_staticcall_spawn_caller hx).trans (by rw [sevmEq]))⟩
  · subst hout
    obtain ⟨f, hf0, hrun⟩ := lift_sound Lib.cert_check codeEq fork run
    have hmem : (0 : Nat) ∈ List.range Lib.cert.length := by decide
    have hq := (List.all_eq_true.mp lib_quiet) 0 hmem
    rw [hf0] at hq
    simp only [Bool.and_eq_true] at hq
    exact congrFun (SFunc.Run.world_of_quiet lib_quiet fork hq.1 hq.2 hrun).1 sevm.currentTarget

end Blanc.Lift.Usdc
