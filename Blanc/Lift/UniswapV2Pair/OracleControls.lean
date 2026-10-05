import Blanc.Lift.UniswapV2Pair.PropertiesOracleLaw

/-!
# U5 statement control: the exact oracle law needs the `uint32` timestamp wrap

`OracleUpdate.LawfulNoWrap` is `OracleUpdate.Lawful` with one mutation: the elapsed time is the
plain difference `ts − last` instead of `(ts mod 2^32 − last) mod 2^32`; the accumulator
increments are unchanged.  `oracle_law_requires_timestamp_wrap` exhibits a reached typed-model
update (an actual successful `runTyped` `sync` from the initialized state at block timestamp
`2^32 + 1`) that the exact law `runTyped_oracle_law` admits and the mutant law refutes.

This is model-level evidence: a reached typed-model run, not an EVM execution witness.
-/

namespace Blanc.Lift.UniswapV2Pair.OracleControls

open Jaune

/-- The exact law with the `mod 2^32` wrap of the elapsed time removed. -/
def _root_.Blanc.Lift.UniswapV2Pair.OracleUpdate.LawfulNoWrap (u : OracleUpdate) : Prop :=
  u.elapsed = u.timestamp.toNat - u.oldTimestamp.toNat ∧
  u.increment0 =
    (if u.elapsed > 0 ∧ u.oldReserve0 ≠ 0 ∧ u.oldReserve1 ≠ 0 then
      (u.oldReserve1 * 2 ^ 112 / u.oldReserve0) * u.elapsed
    else 0) ∧
  u.increment1 =
    (if u.elapsed > 0 ∧ u.oldReserve0 ≠ 0 ∧ u.oldReserve1 ≠ 0 then
      (u.oldReserve0 * 2 ^ 112 / u.oldReserve1) * u.elapsed
    else 0)

def answer (value : B256) : ExternalResult :=
  { success := true, returndata := encodeWords [value], codeExists := true,
    recoveryOutput := 0 }

/-- The state actual factory initialization stores (`Creation/DeployInit.lean`). -/
def initialized : State := { State.empty 16 0 with token0 := 18, token1 := 19 }

/-- A block timestamp past the `uint32` range. -/
def wrapContext : Context :=
  { pair := 17, sender := 20, value := 0, timestamp := 4294967297,
    isStatic := false, invocation := [] }

def syncTranscript : Transcript :=
  .next (answer 1) .done (.next (answer 1) .done .done)

def wrapRun : RunResult := runTyped initialized wrapContext .sync syncTranscript

/-- **Control (U5).**  An actual successful typed `sync` at timestamp `2^32 + 1` records an update
that the exact law admits and the law without the `mod 2^32` wrap refutes. -/
theorem oracle_law_requires_timestamp_wrap :
    wrapRun.status = .success [] ∧
    ∃ u ∈ wrapRun.frame.current.updates, u.update.Lawful ∧ ¬ u.update.LawfulNoWrap := by
  refine ⟨rfl, ?_⟩
  obtain ⟨lawful, -⟩ := runTyped_oracle_law (st := initialized) (ctx := wrapContext)
    (entry := .sync) (transcript := syncTranscript)
  have stamps : wrapRun.frame.current.updates.map
      (fun u => (u.update.timestamp, u.update.oldTimestamp)) = [(4294967297, 0)] := by
    decide +kernel
  obtain ⟨u, member, eq⟩ := List.mem_map.mp (stamps ▸ List.mem_singleton_self _)
  have timestamp : u.update.timestamp = 4294967297 := (Prod.mk.inj eq).1
  have oldTimestamp : u.update.oldTimestamp = 0 := (Prod.mk.inj eq).2
  refine ⟨u, member, lawful u member, ?_⟩
  intro mutant
  have exact := (lawful u member).1
  rw [mutant.1, timestamp, oldTimestamp] at exact
  exact absurd exact (by decide)

end Blanc.Lift.UniswapV2Pair.OracleControls
