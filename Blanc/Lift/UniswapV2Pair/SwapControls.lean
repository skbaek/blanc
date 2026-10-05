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
the callback left, to the masked cached token words in the Pair's storage slots 6 and 7) reply
with balance words below `2^112`. The bytecode half is a pure raw inversion of the pc-zero run:
it needs no storage representation, no HASH-T premise and no typed checkpoint, only the CALL
reply bound `short`. -/
theorem swap_bytecode_uint112_control {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (short : ∀ pre d, StepIn ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ sevm pre (.exec .call) d →
      d.returnData.length < 2 ^ 160) :
    (swapCheck (Nat.toB256 (2 ^ 112)) 10
        (swapInputs (Nat.toB256 (2 ^ 112)) 10 1 0 10 10).1
        (swapInputs (Nat.toB256 (2 ^ 112)) 10 1 0 10 10).2 10 10 = .ok () ∧
      (Nat.toB256 (2 ^ 112)).toNat = 2 ^ 112 ∧
      ¬((runTyped swapControlState swapControlContext (.swap 1 0 300 [])
        (swapCanonicalTranscript 1 0 (Nat.toB256 (2 ^ 112)) 10 [])).status = .success [])) ∧
    ∃ (d d0 d1 : Devm) (M M0 : Mem) (p t0 t1 : B256) (S0 S1 : List B256) (out0 out1 : Bytes),
      t0 = (0xffffffffffffffffffffffffffffffffffffffff &&& b.getStorVal sevm.currentTarget 6) ∧
      t1 = (0xffffffffffffffffffffffffffffffffffffffff &&& b.getStorVal sevm.currentTarget 7) ∧
      SwapBalanceCall ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ sevm d M p t0 S0 d0 out0 ∧
      SwapBalanceCall ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ sevm d0 M0 p t1 S1 d1 out1 ∧
      ¬(2 ^ 112 ≤ (swapBalanceWord out0).toNat) ∧ ¬(2 ^ 112 ≤ (swapBalanceWord out1).toNat) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, check, word, _, fails⟩ := swap_uint112_control
  refine ⟨⟨check, word, fails⟩, ?_⟩
  obtain ⟨f, entry, derived⟩ := lift_sound_in cert_check codeEq fork run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  obtain ⟨_, _, guards, _, calleePost, body, _⟩ := swapPc0_inv selector derived
  obtain ⟨_, _, _, gas0, run0⟩ := swapLockOutput_inv fork (SFunc.runP_iff_runCutP_nil.mp body)
  obtain ⟨_, _, _, _, gas1, run1⟩ := swapGuards_inv fork run0
  obtain ⟨b1, M1, p1, b2, M2, p2, n2, g2, _, _, ptr2, lower2, upper2, run2⟩ :=
    swapTransfers_inv fork getterInitMemory_ptr short run1
  obtain ⟨b3, M3, m3, g3, _, ptr3, run3⟩ :=
    swapCallback_inv fork ptr2 lower2 upper2 guards.length run2
  obtain ⟨d0, d1, out0, out1, call0, call1, _, _, bound0, bound1, _⟩ :=
    swapBack_raw_inv (w := ⟨_, _, _, _, _, _, _, _, _⟩) (ρ := _) (R := _) fork ptr3 lower2
      (by omega) run3
  have slot : ∀ k : B256, k ≠ 12 →
      (afterSload sevm (mintLockedWorld sevm b) 8).getStorVal sevm.currentTarget k =
        b.getStorVal sevm.currentTarget k := by
    intro k k12
    change ((afterSload sevm (mintLockedWorld sevm b) 8).getStor sevm.currentTarget).get k =
      (b.getStor sevm.currentTarget).get k
    rw [afterSload_getStor]
    unfold mintLockedWorld
    rw [afterSstore_getStor_self, afterSload_getStor, Stor.get_set_ne _ (Ne.symm k12)]
  have n6 : (6 : B256) ≠ 12 := by decide
  have n7 : (7 : B256) ≠ 12 := by decide
  exact ⟨_, d0, d1, _, _, _, _, _, _, _, out0, out1, by rw [slot 6 n6], by rw [slot 7 n7],
    call0, call1, Nat.not_le_of_lt bound0, Nat.not_le_of_lt bound1⟩

end Blanc.Lift.UniswapV2Pair
