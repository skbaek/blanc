import Blanc.Lift.UniswapV2Pair.SwapCanonical
import Blanc.Lift.UniswapV2Pair.PropertiesSwap

/-!
# Swap controls: the uint112 guard (U4) at pc-zero altitude

The `_update` uint112 guard is load-bearing. On the model side, `swap_uint112_control` exhibits a
state where the observed balance `2^112` passes the SafeMath `K` check and the input inference,
yet the typed swap does not succeed: only the guard rejects it. On the bytecode side, every
successful raw swap run of the original bytes observes, through its actual post-callback
`balanceOf(pair)` STATICCALLs, balances strictly below `2^112`; so no successful raw run observes
`2^112` or more. The raw half is universal over successful raw runs (under the canonical frame's
premises); no concrete reverting raw execution is exhibited.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- **U4 uint112 guard control.** (Model) at the control state the observed balance `2^112`
passes the `K` check, and the typed swap over that observation does not succeed. (Bytecode)
every successful raw swap run's two actual post-callback balance STATICCALL steps (at the world
the callback left, to the cached `token0`/`token1`) reply with balance words below `2^112`. -/
theorem swap_bytecode_uint112_control {K : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b post : Devm} {G : Nat}
    (invocation : List Nat)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (freshOutput : b.output = [])
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (hashTInj : WriterInj (WriterExtend K
      (swapTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩)))
    (hashTApart : WriterApart (WriterExtend K
      (swapTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩)))
    (short : ∀ pre d, StepIn ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ sevm pre (.exec .call) d →
      d.returnData.length < 2 ^ 160) :
    (swapCheck (Nat.toB256 (2 ^ 112)) 10
        (swapInputs (Nat.toB256 (2 ^ 112)) 10 1 0 10 10).1
        (swapInputs (Nat.toB256 (2 ^ 112)) 10 1 0 10 10).2 10 10 = .ok () ∧
      (Nat.toB256 (2 ^ 112)).toNat = 2 ^ 112 ∧
      ¬((runTyped swapControlState swapControlContext (.swap 1 0 300 [])
        (swapCanonicalTranscript 1 0 (Nat.toB256 (2 ^ 112)) 10 [])).status = .success [])) ∧
    ∃ (d d0 d1 : Devm) (M M0 : Mem) (p : B256) (S0 S1 : List B256) (out0 out1 : Bytes),
      SwapBalanceCall ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ sevm d M p
        current.state.token0.toB256 S0 d0 out0 ∧
      SwapBalanceCall ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ sevm d0 M0 p
        current.state.token1.toB256 S1 d1 out1 ∧
      ¬(2 ^ 112 ≤ (swapBalanceWord out0).toNat) ∧ ¬(2 ^ 112 ≤ (swapBalanceWord out1).toNat) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, check, word, _, fails⟩ := swap_uint112_control
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, d, d0, d1, _, _, M, _, p, out0, out1, _, _, _, _, _, _,
    _, _, _, _, _, _, call0, call1, _, _, _, _, _, _, _, _, bound0, bound1, _⟩ :=
    swap_bytecode_exact_consumes invocation rep sem image installed freshOutput codeEq fork
      selector run hashTInj hashTApart short
  exact ⟨⟨check, word, fails⟩, d, d0, d1, M, _, p, _, _, out0, out1, call0, call1,
    Nat.not_le_of_lt bound0, Nat.not_le_of_lt bound1⟩

end Blanc.Lift.UniswapV2Pair
