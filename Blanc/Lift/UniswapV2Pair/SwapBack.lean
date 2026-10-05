import Blanc.Lift.UniswapV2Pair.SwapUpdateWalk

/-! The swap body's back half, from the post-callback cut `t_09c3_c5` to the
body's return: both authentic balance queries in the same derivation, input
inference, the SafeMath `K` check, `_update`, the `Swap` log and the unlock. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The balance word a successful query decodes. -/
def swapBalanceWord (out : Bytes) : B256 := Bytes.toB256 (out.take 32)

/-- Everything the successful raw back half exposes, over the cut words. -/
def SwapBackRaw (D : Exec.Deriv) (sevm : Sevm) (d : Devm) (M : Mem) (p : B256)
    (w : SwapCutWords) (ρ : B256) (R : List B256) (o : Outcome) : Prop :=
  let R0 := w.reserve1 :: w.reserve0 :: w.dataLength :: w.dataOffset :: w.recipient ::
    w.amount1Out :: w.amount0Out :: ρ :: R
  ∃ (d0 d1 : Devm) (out0 out1 : Bytes),
    SwapBalanceCall D sevm d M p w.token0 (w.token1 :: w.token0 :: 0 :: 0 :: R0) d0 out0 ∧
    SwapBalanceCall D sevm d0 (swapBalanceReply M p sevm.currentTarget out0) p w.token1
      (w.token1 :: w.token0 :: 0 :: swapBalanceWord out0 :: R0) d1 out1 ∧
    let bal0 := swapBalanceWord out0
    let bal1 := swapBalanceWord out1
    let in0 := swapInWord bal0 w.reserve0 w.amount0Out
    let in1 := swapInWord bal1 w.reserve1 w.amount1Out
    (0 < in0 ∨ 0 < in1) ∧ SwapKFacts bal0 bal1 in0 in1 w.reserve0 w.reserve1 ∧
    bal0.toNat < 2 ^ 112 ∧ bal1.toNat < 2 ^ 112 ∧ sevm.isStatic = false ∧
    ∃ M' G', o = .returned (St (afterSstore sevm
      ((updateWorld sevm d1 w.reserve0 w.reserve1 bal0 bal1).addLog
        (swapEventLog sevm in0 in1 w.amount0Out w.amount1Out w.recipient)) 12 1) R M' G')

/-- **Raw back-half inversion.** A successful run of the actual body from the
post-callback cut returns exactly through both queries, the checked pricing,
`_update`, the `Swap` log and the unlock. -/
theorem swapBack_raw_inv {D : Exec.Deriv} {sevm : Sevm} {d : Devm} {R : List B256}
    {M : Mem} {G n : Nat} {p ρ : B256} {w : SwapCutWords} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St d (swapCutStack w ρ R) M G) t_09c3_c5 (.done o)) :
    SwapBackRaw D sevm d M p w ρ R o := by
  obtain ⟨d0, out0, _, call0, run⟩ := swapFirstBalance_inv fork mem lower width run
  have long0 : 32 ≤ out0.length := by
    obtain ⟨_, _, _, _, _, long, _⟩ := call0
    exact long
  have reply0 := swapBalanceReply_ptr (pair := sevm.currentTarget) out0 mem lower width
  obtain ⟨d1, out1, _, call1, run⟩ :=
    swapSecondBalance_inv fork mem lower width long0 run
  have long1 : 32 ≤ out1.length := by
    obtain ⟨_, _, _, _, _, long, _⟩ := call1
    exact long
  have reply1 := swapBalanceReply_ptr (pair := sevm.currentTarget) out1 reply0 lower width
  have cover := swapRequestSize_cover reply0
  have plain := SFunc.Run.cut ((SFunc.runP_iff_runCutP_nil.mpr run).mono StepIn.toRun)
  obtain ⟨guard, _, plain⟩ := swapInputs_inv
    (swapBalanceReply_word reply0.wf out1 long1) (reply1.read_self cover) plain
  obtain ⟨k, _, plain⟩ := swapK_inv plain
  obtain ⟨bound0, bound1, static, M', G', returned⟩ := swapTail_inv fork reply1 lower width plain
  exact ⟨d0, d1, out0, out1, call0, call1, guard, k, bound0, bound1, static, M', G', returned⟩

end Blanc.Lift.UniswapV2Pair
