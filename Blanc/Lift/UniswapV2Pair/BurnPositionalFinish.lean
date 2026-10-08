import Blanc.Lift.UniswapV2Pair.BurnPositionalFacts
import Blanc.Lift.UniswapV2Pair.BurnSuffixWalk
import Blanc.Lift.CursorQuietReturn

namespace Blanc.Lift.UniswapV2Pair
open Jaune

def BurnSevenCalls.finishInputMemory {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnSevenCalls root sevm b) : Mem :=
  burnBalanceReplyMemory
    (skimRequestMemory (burnBalanceReplyMemory r.five.finalRequestMemory r.five.finalPointer r.final0.out)
      r.five.finalPointer sevm.currentTarget) r.five.finalPointer r.final1.out

def BurnSevenCalls.finishWorld {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnSevenCalls root sevm b) : Devm :=
  burnSuffixPost sevm r.final1.call.returned.devm
    (burnInitialReserve0 sevm b) (burnInitialReserve1 sevm b)
    (Bytes.toB256 (r.final0.out.take 32)) (Bytes.toB256 (r.final1.out.take 32))
    (feeOnWord (Bytes.toB256 (r.five.four.three.fee.out.take 32)))
    (Sevm.dataWord sevm 4).toAdr.toB256
    (r.five.four.three.amount0 r.five.four.pricing) (r.five.four.three.amount1 r.five.four.pricing)

def BurnSevenCalls.finishMemory {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnSevenCalls root sevm b) : Mem :=
  burnSuffixMemory sevm r.final1.call.returned.devm r.finishInputMemory r.five.finalPointer
    (burnInitialReserve0 sevm b) (burnInitialReserve1 sevm b)
    (Bytes.toB256 (r.final0.out.take 32)) (Bytes.toB256 (r.final1.out.take 32))
    (r.five.four.three.amount0 r.five.four.pricing) (r.five.four.three.amount1 r.five.four.pricing)

/-- The retained final answer returns through this actual internal body and
the original ABI caller, fixing the complete successful output and raw post. -/
theorem BurnSevenCalls.finishRaw {root : Exec.Deriv} {sevm : Sevm} {b post : Devm}
    (r : BurnSevenCalls root sevm b) (success : root.exn = .ok post)
    (fork : CoveredFork sevm.benvStat.fork) :
    (Bytes.toB256 (r.final0.out.take 32)).toNat < 2 ^ 112 ∧
    (Bytes.toB256 (r.final1.out.take 32)).toNat < 2 ^ 112 ∧ sevm.isStatic = false ∧
    ∃ (N : Exec.Deriv) (next : Cursor) (gas : Nat),
      Exec.Deriv.ExecFreeUntil r.final1.call.returned N ∧ N.sevm = sevm ∧ N.exn = .ok post ∧
      CursorOK code cert N next ∧ next.f = t_053d_c83 ∧ next.K.map Cont.f = [] ∧
      N.devm = St r.finishWorld
        [r.five.four.three.amount1 r.five.four.pricing,
          r.five.four.three.amount0 r.five.four.pricing, 0x89afcb44] r.finishMemory gas ∧
      post.output = (r.five.four.three.amount0 r.five.four.pricing).toBytes ++
        (r.five.four.three.amount1 r.five.four.pricing).toBytes ∧
      (∀ a, post.getStor a = r.finishWorld.getStor a) ∧ post.logs = r.finishWorld.logs := by
  have reached := r.final1.call.sameFrame.snoc r.final1.call.edge
  have outcome : r.final1.call.returned.exn = .ok post :=
    (Blanc.Exec.Deriv.ParentPrefix.exn_eq reached).trans success
  have env : r.final1.call.returned.sevm = sevm :=
    (Blanc.Exec.Deriv.ParentPrefix.sevm_eq reached).trans
      ((Blanc.Exec.Deriv.ParentPrefix.sevm_eq r.five.second.sameFrame).symm.trans r.five.sevm_eq)
  have forkRet : CoveredFork r.final1.call.returned.sevm.benvStat.fork := by rw [env]; exact fork
  let cut := r.final1.decoded
  obtain ⟨N, next, span, nextEnv, nextOutcome, placed, tree, conts, run⟩ :=
    cut.placed.quietReturn cert_check (cut.exn_eq.trans outcome) (cut.sevm_eq ▸ forkRet)
      (E := [9,14,18,19,20,21,22,58,60,65,66]) (caller := t_053d_c83) (K := [])
      (by decide) (by decide) (by rw [cut.tree]; decide) (by rw [cut.tree]; decide)
      cut.continuations
  obtain ⟨initialGas, state⟩ := cut.state
  rw [cut.sevm_eq, cut.tree, state, env] at run
  have bounds := burnFinalPointer_bounds r.five.first_bound r.second_bound
  change 96 ≤ r.five.finalPointer.toNat ∧ r.five.finalPointer.toNat + 1024 < 2 ^ 256 at bounds
  obtain ⟨bound0, bound1, mutable, _, _, gas, _, returned, mem, covered⟩ :=
    burnSuffix_inv (fun step => step) fork r.final1.pointer bounds.1
      (by omega) (by decide : 14 ∉ [])
      (by simpa only [BurnFiveCalls.finalLocals, BurnThreeCalls.pricedLocals,
        burnPricedLocals, List.set, BurnSevenCalls.finishInputMemory] using
          SFunc.runP_iff_runCutP_nil.mp run)
  have full : N.devm = St r.finishWorld
      [r.five.four.three.amount1 r.five.four.pricing,
        r.five.four.three.amount0 r.five.four.pricing, 0x89afcb44] r.finishMemory gas := by
    exact Outcome.returned.inj (Seg.done.inj returned)
  have sameEnv : N.sevm = sevm := nextEnv.trans (cut.sevm_eq.trans env)
  have sameOutcome : N.exn = .ok post := nextOutcome.trans (cut.exn_eq.trans outcome)
  rcases placed.sourceRunReturn cert_check sameOutcome (by rw [sameEnv]; exact fork)
    with abi | resumed
  · rw [sameEnv, tree, full] at abi
    obtain ⟨_, d, terminal, _, output, stor, logs⟩ := burnAbi_return_inv
      (fun step => StepIn.toRun step) mem bounds.1 (by omega)
      (SFunc.runP_iff_runCutP_nil.mp abi)
    have same : post = d := Outcome.halted.inj (Seg.done.inj terminal)
    subst d
    exact ⟨bound0, bound1, mutable, N, next, gas, cut.free.trans span, sameEnv,
      sameOutcome, placed, tree, conts, full, output, stor, logs⟩
  · obtain ⟨continuation, tail, _, _, sameK, _, _, _, _⟩ := resumed
    rw [sameK, List.map_cons] at conts
    cases conts

end Blanc.Lift.UniswapV2Pair
