import Blanc.Lift.Usdc.ProxyCreation.Effects
import Blanc.Lift.Usdc.ProxyCreation.Check
import Blanc.ExecutionStagedRootFacts

/-!
# The original proxy constructor at a raw history frame

A successful raw frame of a `ConfiguredHistoryTraceIn` running the registered
proxy creation code is, by `lift_sound_noStateGas` (entry facts from
`rawFrame_entryFacts`: pc zero, `stateGas = none`, empty stack and memory), a
run of the certificate's entry from the frame's own machine, so
`constructor_effects_of_run` and `constructor_row_preserved` apply to the
frame's raw result. Installation by `processCreateMessage` (touch, code
charge, code write) is not part of these statements.
-/

namespace Blanc.Lift.Usdc.ProxyCreation

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- The certificate's entry run from a fresh pc-zero frame on `stateGas = none`. -/
theorem constructor_run_of_exec {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (hcode : sevm.code = code)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (stack : pre.stack = []) (memory : pre.memory = Mem.empty) :
    SFunc.Run cert.prog sevm (St pre [] Mem.empty pre.gasLeft) t_0000_c0 (.halted post) := by
  obtain ⟨f, entry, body⟩ := lift_sound_noStateGas cert_check hcode hsg run
  have first : f = t_0000_c0 := by
    have : cert.prog[0]? = some t_0000_c0 := rfl
    exact Option.some.inj (entry.symm.trans this)
  rw [← St.self stack memory, ← first]
  exact body

/-- **Proxy constructor effects at a raw history frame.** A successful raw
frame running the registered creation code writes exactly the implementation
and admin slots of its target, returns the registered runtime window, and
leaves every other account's storage unchanged. -/
theorem constructor_effects_rawFrame
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    {R : Exec.Deriv} (member : R ∈ history.rawFrames) {post : Devm}
    (ok : R.exn = .ok post) (hcode : R.sevm.code = code) :
    post.getStor R.sevm.currentTarget =
      ((R.devm.getStor R.sevm.currentTarget).set implSlot initialImplementation).set
        adminSlot R.sevm.caller.toB256 ∧
    post.output = code.toList.sliceD 671 2186 0 ∧
    (∀ a, a ≠ R.sevm.currentTarget → post.getStor a = R.devm.getStor a) := by
  obtain ⟨pc, -, hsg, ⟨stack, memory⟩, -⟩ :=
    history.rawFrame_entryFacts capabilities R member
  rcases R with ⟨pc', sevm, pre, out, run⟩
  dsimp only at pc hsg stack memory ok hcode ⊢
  subst pc ok
  exact constructor_effects_of_run hcode (constructor_run_of_exec run hcode hsg stack memory)

/-- **A protected row survives the proxy constructor at a raw history
frame**: every target row other than the implementation and admin slots
keeps its entry value. -/
theorem constructor_row_preserved_rawFrame
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    {R : Exec.Deriv} (member : R ∈ history.rawFrames) {post : Devm}
    (ok : R.exn = .ok post) (hcode : R.sevm.code = code) {key : B256}
    (implementation : key ≠ implSlot) (admin : key ≠ adminSlot) :
    post.getStorVal R.sevm.currentTarget key = R.devm.getStorVal R.sevm.currentTarget key := by
  obtain ⟨pc, -, hsg, ⟨stack, memory⟩, -⟩ :=
    history.rawFrame_entryFacts capabilities R member
  rcases R with ⟨pc', sevm, pre, out, run⟩
  dsimp only at pc hsg stack memory ok hcode ⊢
  subst pc ok
  exact constructor_row_preserved hcode (constructor_run_of_exec run hcode hsg stack memory)
    implementation admin

end Blanc.Lift.Usdc.ProxyCreation
