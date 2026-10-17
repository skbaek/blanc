import Blanc.Composition.UniswapV2PairWeth9CapstoneRaw
import Blanc.Lift.UniswapV2Pair.SwapPositionalSuffix
import Blanc.Lift.PrecompileAnswer

/-!
# The raw children of a successful `swap(0, b, to, "")` frame

From the Pair's physical decomposition of a successful swap (`SwapBalances`), with no `amount0Out`
and no callback data, every raw descendant of the root lies in the raw roots of the child entered
at the `token1.transfer` `CALL` (when `amount1Out ≠ 0`) or at one of the two `balanceOf`
`STATICCALL`s.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Capstone

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair

/-- `d` is a raw root of the child entered at the node of `step`. -/
def OccChild {root : Exec.Deriv} {x : Xinst} (step : CallOccurrenceStep root x)
    (d : Exec.Deriv) : Prop :=
  ∃ (frame : Jaune.Frame) (resume : Resume) (nextPc : Nat) (childEvm : Evm)
    (raw : Execution) (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw),
    Evm.step ⟨step.occurrence.node.pc, step.occurrence.node.sevm, step.occurrence.node.devm⟩ =
      .spawn frame resume nextPc ∧
    frame.enter = .run childEvm ∧ d ∈ Exec.rawFrameRoots child

theorem occChild_cases {root : Exec.Deriv} {x : Xinst} (step : CallOccurrenceStep root x) :
    ∀ d ∈ Exec.rawFrameDescendants step.occurrence.node.exc,
      d ∈ Exec.rawFrameDescendants step.returned.exc ∨ OccChild step d :=
  parentStep_rawFrameDescendants_cases step.edge

/-- **The raw children of a swap with no `amount0Out` and no callback.** -/
theorem swap_rawFrameDescendants {root : Exec.Deriv} {b : Devm}
    (r : SwapBalances root root.sevm b) (fork : CoveredFork root.sevm.benvStat.fork)
    (zero0 : swapAmount0Out root.sevm = 0) (noData : swapDataLength root.sevm = 0) :
    ∀ d ∈ Exec.rawFrameDescendants root.exc,
      (∃ actual : SwapTransferOccurrence root r.optional.transfers.first.next
          r.optional.transfers.first.world (swapRawLocalsStack root.sevm b)
          r.optional.transfers.first.memory r.optional.transfers.first.ptr
          (swapAmount1Out root.sevm) (swapRecipientWord root.sevm) (swapInitialToken1 root.sevm b)
          0x8e1 t_08e1_c4 [t_0257_c99],
        r.optional.transfers.second.next = actual.step.returned ∧ OccChild actual.step d) ∨
      OccChild r.first.step d ∨ OccChild r.second.step d := by
  intro d member
  -- the first transfer is skipped
  have firstNext : r.optional.transfers.first.next = root := by
    rcases r.optional.transfers.first.choice with ⟨-, h, -⟩ | ⟨-, nonzero, -⟩
    · exact h
    · exact (nonzero zero0).elim
  -- the callback is skipped
  have callbackNext : r.optional.callback.next = r.optional.transfers.second.next := by
    rcases r.optional.callback.choice with ⟨-, h, -⟩ | ⟨-, nonzero, -⟩
    · exact h
    · exact (nonzero noData).elim
  -- after the second query nothing is entered
  have tail : Exec.rawFrameDescendants r.second.step.returned.exc = [] :=
    deriv_rawFrameDescendants_nil _ (r.noExecTail fork)
  -- from the second query's node
  have fromSecond : ∀ e ∈ Exec.rawFrameDescendants r.first.step.returned.exc,
      OccChild r.second.step e := by
    intro e inner
    rw [execFreeUntil_rawFrameDescendants_eq r.second.gap] at inner
    rcases occChild_cases r.second.step e inner with later | here
    · rw [tail] at later; cases later
    · exact here
  have fromFirst : ∀ e ∈ Exec.rawFrameDescendants r.optional.transfers.second.next.exc,
      OccChild r.first.step e ∨ OccChild r.second.step e := by
    intro e inner
    rw [← callbackNext, execFreeUntil_rawFrameDescendants_eq r.first.gap] at inner
    rcases occChild_cases r.first.step e inner with later | here
    · exact Or.inr (fromSecond e later)
    · exact Or.inl here
  rcases r.optional.transfers.second.choice with ⟨-, h, -⟩ | ⟨actual, -, h, -⟩
  · rw [← firstNext, ← h] at member
    exact Or.inr (fromFirst d member)
  · rw [← firstNext, execFreeUntil_rawFrameDescendants_eq actual.gap] at member
    rcases occChild_cases actual.step d member with later | here
    · rw [← h] at later
      exact Or.inr (fromFirst d later)
    · exact Or.inl ⟨actual, h, here⟩

/-- A raw root of the child entered at a spawn of `Frame.ofCall msg` whose message settled
successfully as `cd` lies in a successful run of the entered message. -/
theorem occChild_of_spawn {root : Exec.Deriv} {x : Xinst} {step : CallOccurrenceStep root x}
    {msg : Msg} {resume : Resume} {nextPc : Nat} {xl : Xlot} {cd : Devm} {d : Exec.Deriv}
    (spawn : Evm.step ⟨step.occurrence.node.pc, step.occurrence.node.sevm,
      step.occurrence.node.devm⟩ = .spawn (Jaune.Frame.ofCall msg) resume nextPc)
    (filled : xl.Filled) (process : ProcessMessage msg xl (.ok cd))
    (clean : cd.error.isSome = false) (occ : OccChild step d) :
    ∃ benv, msg.benvAfterTransfer = .ok benv ∧
      ∃ child : Exec 0 (initSevm (msg.withBenv benv)) (initDevm (msg.withBenv benv)) (.ok cd),
        d ∈ Exec.rawFrameRoots child := by
  obtain ⟨frame, resume', nextPc', childEvm, raw, child, spawn', enter, mem⟩ := occ
  rcases Step.spawn.inj (spawn.symm.trans spawn') with ⟨rfl, -, -⟩
  have process' := process
  unfold ProcessMessage RunFrame at process'
  rw [enter] at process'
  obtain ⟨raw', slotEq, settled⟩ := process'
  subst slotEq
  obtain ⟨run'⟩ := filled
  have same := Exec.result_unique child run'
  subst same
  have ok := callFrame_settle_ok settled.symm clean
  subst ok
  obtain ⟨benv, after, rfl⟩ := Jaune.Frame.enter_run_inv enter
  exact ⟨benv, after, child, mem⟩

/-- What an entered call child is: a successful run of a message whose header the parent staged. -/
def CallChild (node : Exec.Deriv) (target : Adr) (data : Bytes) (value : B256)
    (returnData : Bytes) (d : Exec.Deriv) : Prop :=
  ∃ (m : Msg) (cd : Devm) (benv : Benv),
    m.currentTarget = target ∧ m.caller = node.sevm.currentTarget ∧ m.data = data ∧
    m.value = value ∧ m.benv.stat = node.sevm.benvStat ∧
    (getDelegatedCodeAddress (node.devm.getCode target) = none →
      m.code = node.devm.getCode target) ∧
    cd.output = returnData ∧ m.benvAfterTransfer = .ok benv ∧
    ∃ child : Exec 0 (initSevm (m.withBenv benv)) (initDevm (m.withBenv benv)) (.ok cd),
      d ∈ Exec.rawFrameRoots child

/-- **The child of an actual successful `STATICCALL` occurrence.** -/
theorem staticcall_occChild {root : Exec.Deriv} (step : CallOccurrenceStep root .staticcall)
    {g t ii is oi os : B256} {xs rest : List B256}
    (hp : (g :: t :: ii :: is :: oi :: os :: xs) <<+ step.occurrence.node.devm.stack)
    (flag : step.returned.devm.stack = 1 :: rest)
    (fork : CoveredFork step.occurrence.node.sevm.benvStat.fork) {d : Exec.Deriv}
    (occ : OccChild step d) :
    CallChild step.occurrence.node t.toAdr
      ((step.occurrence.node.devm.memory.read ii.toNat is.toNat).1) 0
      step.returned.devm.returnData d := by
  have stepRun := step.occurrence.stepRun
  rw [step.instruction, step.result] at stepRun
  rcases of_step_staticcall_val_with_depth_frame_cause hp step.occurrence.filled stepRun fork with
    ⟨failed, -⟩ | ⟨parent, cd, dp, na, code, avail, -, -, -, -, -, -, resolved, -, process, clean,
      -, -, returnData, -, -, spawn⟩
  · rw [flag] at failed
    exact absurd (pref_head_unique failed (pref_append [1] rest)) (by decide)
  · have decoded := step.occurrence.decoded
    rw [step.instruction] at decoded
    have spawn' := (Evm.step_next decoded).trans spawn
    obtain ⟨benv, after, child, mem⟩ :=
      occChild_of_spawn spawn' step.occurrence.filled process clean occ
    refine ⟨_, cd, benv, rfl, rfl, rfl, rfl, rfl, fun undelegated => ?_, returnData.symm,
      after, child, mem⟩
    rcases resolved with ⟨-, -, hc, -⟩ | ⟨e, hd, -⟩
    · exact hc
    · rw [undelegated] at hd; cases hd

/-- **The child of an actual successful `CALL` occurrence.** -/
theorem call_occChild {root : Exec.Deriv} (step : CallOccurrenceStep root .call)
    {g c v ii is oi os : B256} {xs rest : List B256}
    (hp : (g :: c :: v :: ii :: is :: oi :: os :: xs) <<+ step.occurrence.node.devm.stack)
    (flag : step.returned.devm.stack = 1 :: rest)
    (fork : CoveredFork step.occurrence.node.sevm.benvStat.fork) {d : Exec.Deriv}
    (occ : OccChild step d) :
    CallChild step.occurrence.node c.toAdr
      ((step.occurrence.node.devm.memory.read ii.toNat is.toNat).1) v
      step.returned.devm.returnData d := by
  have stepRun := step.occurrence.stepRun
  rw [step.instruction, step.result] at stepRun
  rcases of_step_call_val_with_depth_frame hp step.occurrence.filled stepRun fork with
    ⟨failed, -⟩ | ⟨parent, cd, dp, na, code, avail, -, -, -, -, -, -, resolved, -, process, clean,
      -, -, returnData, -, -, spawn⟩
  · rw [flag] at failed
    exact absurd (pref_head_unique failed (pref_append [1] rest)) (by decide)
  · have decoded := step.occurrence.decoded
    rw [step.instruction] at decoded
    have spawn' := (Evm.step_next decoded).trans spawn
    obtain ⟨benv, after, child, mem⟩ :=
      occChild_of_spawn spawn' step.occurrence.filled process clean occ
    refine ⟨_, cd, benv, rfl, rfl, rfl, rfl, rfl, fun undelegated => ?_, returnData.symm,
      after, child, mem⟩
    rcases resolved with ⟨-, -, hc, -⟩ | ⟨e, hd, -⟩
    · exact hc
    · rw [undelegated] at hd; cases hd

end Blanc.Composition.UniswapV2PairWeth9Capstone
