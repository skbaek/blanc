import Blanc.Lift.Weth9.ClosedBlockData

/-!
Forward construction of the synthetic deposit block from its proved body.
All transaction and system processing remains in the `applyBody` premise,
which the connected WETH9 witness discharges before constructing its history.
-/

namespace Blanc.Lift.Weth9.ClosedInstance

open Jaune Blanc Blanc.BlockForward Blanc.ExecutionTrace

def depositChain (st post : Jaune.State) (bout : BlockOutput) : BlockChain :=
  ⟨appendBlock (checkpoint st).blocks (depositBlock st post bout), post, 1⟩

theorem input_lastHash (st : Jaune.State) :
    (input st).stat.blockHashes.getLast? = some (checkpointHeader st).hash := by
  rfl

theorem depositBlock_header {st post : Jaune.State} {bout : BlockOutput}
    (hgas : bout.blockGasUsed ≤ 1000000) :
    validateHeader Fork.bpo2.ruleSet (checkpoint st)
      (depositBlock st post bout).header = .ok () := by
  apply commitHeader_ok
  · rfl
  · change calculateBaseFeePerGas 1000000 1000000 500000 1 = .ok 1
    exact calculateBaseFeePerGas_unit (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact hgas
  · change ([] : Bytes).length ≤ 32
    decide +kernel
  · rfl
  · rfl

theorem depositBlock_transition {st post : Jaune.State} {bout : BlockOutput}
    (hgas : bout.blockGasUsed ≤ 1000000)
    (hbody : applyBody (input st) [Sum.inr depositTx] [] = .ok (post, bout)) :
    stateTransitionUsing config (checkpoint st) (depositBlock st post bout) =
      .ok (depositChain st post bout) := by
  have hbody' : applyBody
      (initBenv .bpo2 (checkpoint st) (depositBlock st post bout).header)
      (depositBlock st post bout).txs (depositBlock st post bout).wds = .ok (post, bout) := by
    change applyBody
      (initBenv .bpo2 (checkpoint st) (depositBlock st post bout).header)
      [Sum.inr depositTx] [] = .ok (post, bout)
    rw [depositBlock_input]
    exact hbody
  exact stateTransitionUsing_forward rfl (config_forkAt _) (by decide +kernel)
    (depositBlock_header hgas) rfl hbody' rfl rfl rfl rfl rfl rfl rfl rfl

theorem depositBlock_trace {st post : Jaune.State} {bout : BlockOutput}
    (hbound : SumNof st.bal)
    (hgas : bout.blockGasUsed ≤ 1000000)
    (hbody : applyBody (input st) [Sum.inr depositTx] [] = .ok (post, bout)) :
    Nonempty (ConfiguredBlockTrace config (checkpoint st) (depositChain st post bout)) := by
  exact configuredBlockTrace_forward hbound rfl (config_forkAt _) (by decide +kernel)
    (depositBlock_transition hgas hbody)

/-- One actual configured block yields a nonempty configured history. -/
def depositHistory {st post : Jaune.State} {bout : BlockOutput}
    (hcanon : st.Canonical)
    (trace : ConfiguredBlockTrace config (checkpoint st) (depositChain st post bout)) :
    ConfiguredHistoryTrace config (checkpoint st) (depositChain st post bout) :=
  .step (.refl config_valid (checkpoint_validContext hcanon) rfl) trace

theorem exists_depositHistory {st post : Jaune.State} {bout : BlockOutput}
    (hcanon : st.Canonical)
    (hbound : SumNof st.bal)
    (hgas : bout.blockGasUsed ≤ 1000000)
    (hbody : applyBody (input st) [Sum.inr depositTx] [] = .ok (post, bout)) :
    Nonempty (ConfiguredHistoryTrace config (checkpoint st) (depositChain st post bout)) := by
  obtain ⟨trace⟩ := depositBlock_trace hbound hgas hbody
  exact ⟨depositHistory hcanon trace⟩

end Blanc.Lift.Weth9.ClosedInstance
