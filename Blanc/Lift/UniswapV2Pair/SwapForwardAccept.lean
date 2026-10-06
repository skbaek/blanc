import Blanc.Lift.UniswapV2Pair.SwapForward
import Blanc.Lift.UniswapV2Pair.PropertiesSwap

/-!
# The swap back half's acceptance facts, from the model

`SwapBackForwardEnv` bundles the two post-callback `balanceOf(pair)` callees with the facts the bytes
check about their answers: the input guard, the SafeMath `K` facts and the `uint112` bounds, and the
non-static frame.  Those facts are the model's own acceptance conditions at the observed balances
(`SwapModelConditions`).  This module splits them off:

* `swapCheck_raw` — the converse of `swapCheck_source`: model acceptance of `swapCheck` at the source
  inputs gives the raw input guard and `SwapKFacts`;
* `SwapBackCalleeEnv` — the callee-only back environment (both `STATICCALL`s with their replies and
  returned gas, and the residual sentries of the update and unlock stores);
* `SwapBackCalleeEnv.toForward` — the forward environment, from the callee environment and the model's
  acceptance conditions at the actual answers.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- **Model acceptance of the `K` check gives the raw facts** (converse of `swapCheck_source`). -/
theorem swapCheck_raw {bal0 bal1 a0 a1 : B256} {r0 r1 : Nat}
    (bound0 : r0 < 2 ^ 112) (bound1 : r1 < 2 ^ 112)
    (out0 : a0.toNat < r0) (out1 : a1.toNat < r1)
    (positive : (swapInputs bal0 bal1 a0 a1 r0 r1).1 > 0 ∨ (swapInputs bal0 bal1 a0 a1 r0 r1).2 > 0)
    (checked : swapCheck bal0 bal1 (swapInputs bal0 bal1 a0 a1 r0 r1).1
      (swapInputs bal0 bal1 a0 a1 r0 r1).2 r0 r1 = .ok ()) :
    (0 < swapInWord bal0 (Nat.toB256 r0) a0 ∨ 0 < swapInWord bal1 (Nat.toB256 r1) a1) ∧
      SwapKFacts bal0 bal1 (swapInWord bal0 (Nat.toB256 r0) a0)
        (swapInWord bal1 (Nat.toB256 r1) a1) (Nat.toB256 r0) (Nat.toB256 r1) := by
  have in0 := swapInWord_source (balance := bal0) bound0 out0
  have in1 := swapInWord_source (balance := bal1) bound1 out1
  unfold swapInputs at positive checked
  dsimp only at positive checked
  rw [← in0, ← in1] at positive checked
  generalize swapInWord bal0 (Nat.toB256 r0) a0 = x0 at positive checked ⊢
  generalize swapInWord bal1 (Nat.toB256 r1) a1 = x1 at positive checked ⊢
  unfold swapCheck at checked
  rw [ite_eq_left positive] at checked
  by_cases f0 : bal0.toNat * 1000 < 2 ^ 256 ∧ x0.toNat * 3 < 2 ^ 256
  swap
  · rw [ite_eq_right f0] at checked; cases checked
  rw [ite_eq_left f0] at checked
  by_cases c0 : x0.toNat * 3 ≤ bal0.toNat * 1000
  swap
  · rw [ite_eq_right c0] at checked; cases checked
  rw [ite_eq_left c0] at checked
  by_cases f1 : bal1.toNat * 1000 < 2 ^ 256 ∧ x1.toNat * 3 < 2 ^ 256
  swap
  · rw [ite_eq_right f1] at checked; cases checked
  rw [ite_eq_left f1] at checked
  by_cases c1 : x1.toNat * 3 ≤ bal1.toNat * 1000
  swap
  · rw [ite_eq_right c1] at checked; cases checked
  rw [ite_eq_left c1] at checked
  by_cases adj : (bal0.toNat * 1000 - x0.toNat * 3) * (bal1.toNat * 1000 - x1.toNat * 3) < 2 ^ 256
  swap
  · rw [ite_eq_right adj] at checked; cases checked
  rw [ite_eq_left adj] at checked
  by_cases kk : r0 * r1 * 1000 ^ 2 ≤ (bal0.toNat * 1000 - x0.toNat * 3) *
      (bal1.toNat * 1000 - x1.toNat * 3)
  swap
  · rw [ite_eq_right kk] at checked; cases checked
  have e3 : ∀ x : B256, x.toNat * 3 < 2 ^ 256 → (x * 3).toNat = x.toNat * 3 := fun x h =>
    B256.toNat_mul_eq_of_nofm h
  have e1000 : ∀ x : B256, x.toNat * 1000 < 2 ^ 256 → (x * 1000).toNat = x.toNat * 1000 :=
    fun x h => B256.toNat_mul_eq_of_nofm h
  have le0 : x0 * 3 ≤ bal0 * 1000 := by
    rw [B256.le_iff_toNat_le_toNat, e3 x0 f0.2, e1000 bal0 f0.1]; exact c0
  have le1 : x1 * 3 ≤ bal1 * 1000 := by
    rw [B256.le_iff_toNat_le_toNat, e3 x1 f1.2, e1000 bal1 f1.1]; exact c1
  have s0 : (bal0 * 1000 - x0 * 3).toNat = bal0.toNat * 1000 - x0.toNat * 3 := by
    rw [B256.toNat_sub_eq_of_le _ _ le0, e3 x0 f0.2, e1000 bal0 f0.1]
  have s1 : (bal1 * 1000 - x1 * 3).toNat = bal1.toNat * 1000 - x1.toNat * 3 := by
    rw [B256.toNat_sub_eq_of_le _ _ le1, e3 x1 f1.2, e1000 bal1 f1.1]
  have h6 : (1000000 : B256).toNat = 1000000 := by decide
  have rNat0 : (Nat.toB256 r0).toNat = r0 := B256.toNat_toB256_of_lt (by omega)
  have rNat1 : (Nat.toB256 r1).toNat = r1 := B256.toNat_toB256_of_lt (by omega)
  have prodBound : r0 * r1 < 2 ^ 224 := by
    have := Nat.mul_lt_mul'' bound0 bound1
    simpa only [show 2 ^ 112 * 2 ^ 112 = 2 ^ 224 from by decide] using this
  have resProd : ((reserveMask112 &&& Nat.toB256 r0) * (Nat.toB256 r1 &&& reserveMask112) *
      1000000).toNat = r0 * r1 * 1000000 := by
    rw [swapMask_reserve bound0, B256.and_comm, swapMask_reserve bound1]
    have first : (Nat.toB256 r0 * Nat.toB256 r1).toNat = r0 * r1 := by
      rw [B256.toNat_mul_eq_of_nofm (by unfold B256.Nofm; rw [rNat0, rNat1]; omega), rNat0, rNat1]
    have fits : r0 * r1 * 1000000 < 2 ^ 256 :=
      lt_trans (Nat.mul_lt_mul_of_pos_right prodBound (by decide : 0 < 1000000)) (by decide)
    rw [B256.toNat_mul_eq_of_nofm (by unfold B256.Nofm; rw [first, h6]; exact fits), first, h6]
  refine ⟨?_, ⟨f0.2, f0.1, le0, f1.2, f1.1, le1, ?_, ?_⟩⟩
  · rw [B256.lt_iff_toNat_lt_toNat, B256.lt_iff_toNat_lt_toNat]
    exact positive
  · unfold B256.Nofm
    rw [s0, s1]
    exact adj
  · rw [B256.lt_iff_toNat_lt_toNat, resProd,
      B256.toNat_mul_eq_of_nofm (by unfold B256.Nofm; rw [s0, s1]; exact adj), s0, s1]
    rw [show (1000 : Nat) ^ 2 = 1000000 from rfl] at kk
    omega

/-- The callee-only back environment: the two post-callback `balanceOf(pair)` `STATICCALL`s with
their replies and returned gas, and the residual sentries of the update and unlock stores.  No fact
about the answers' values is a field. -/
structure SwapBackCalleeEnv (sevm : Sevm) (d : Devm) (M : Mem) (n : Nat) (p : B256)
    (w : SwapCutWords) (ρ : B256) (R : List B256) (G : Nat) where
  d0 : Devm
  d1 : Devm
  callGas0 : Nat
  callGas1 : Nat
  first : SwapBalanceEnv sevm d M p w.token0 (w.token1 :: w.token0 :: 0 :: 0 :: swapCutTail w ρ R)
    d0 callGas0 (callGas1 + 5 + swapRequestCharge d0 (swapRequestSize n p) p w.token1 83 + 21)
  second : SwapBalanceEnv sevm d0 (swapBalanceReply M p sevm.currentTarget d0.returnData) p
    w.token1 (w.token1 :: w.token0 :: 0 :: swapBalanceWord d0.returnData :: swapCutTail w ρ R) d1
    callGas1 (swapBackPostGas sevm d1 (swapRequestSize (swapRequestSize n p) p) p w
      (swapBalanceWord d0.returnData) (swapBalanceWord d1.returnData) G)
  sentries : SwapUpdateSentries sevm d1 (swapRequestSize (swapRequestSize n p) p) p w.reserve0
    w.reserve1 (swapBalanceWord d0.returnData) (swapBalanceWord d1.returnData)
    (swapEventRunGas G (swapSyncSize (swapRequestSize (swapRequestSize n p) p) p) p
      (swapUnlockCost sevm d1 w.reserve0 w.reserve1 (swapBalanceWord d0.returnData)
        (swapBalanceWord d1.returnData)
        (swapInWord (swapBalanceWord d0.returnData) w.reserve0 w.amount0Out)
        (swapInWord (swapBalanceWord d1.returnData) w.reserve1 w.amount1Out)
        w.amount0Out w.amount1Out w.recipient))
  unlock : gCallStipend < G + 26 + swapUnlockCost sevm d1 w.reserve0 w.reserve1
    (swapBalanceWord d0.returnData) (swapBalanceWord d1.returnData)
    (swapInWord (swapBalanceWord d0.returnData) w.reserve0 w.amount0Out)
    (swapInWord (swapBalanceWord d1.returnData) w.reserve1 w.amount1Out)
    w.amount0Out w.amount1Out w.recipient

/-- The forward back environment from the callee-only one and the answer-level acceptance facts. -/
def SwapBackCalleeEnv.toForward {sevm : Sevm} {d : Devm} {M : Mem} {n : Nat} {p : B256}
    {w : SwapCutWords} {ρ : B256} {R : List B256} {G : Nat}
    (env : SwapBackCalleeEnv sevm d M n p w ρ R G)
    (guard : 0 < swapInWord (swapBalanceWord env.d0.returnData) w.reserve0 w.amount0Out ∨
      0 < swapInWord (swapBalanceWord env.d1.returnData) w.reserve1 w.amount1Out)
    (k : SwapKFacts (swapBalanceWord env.d0.returnData) (swapBalanceWord env.d1.returnData)
      (swapInWord (swapBalanceWord env.d0.returnData) w.reserve0 w.amount0Out)
      (swapInWord (swapBalanceWord env.d1.returnData) w.reserve1 w.amount1Out) w.reserve0 w.reserve1)
    (bound0 : (swapBalanceWord env.d0.returnData).toNat < 2 ^ 112)
    (bound1 : (swapBalanceWord env.d1.returnData).toNat < 2 ^ 112)
    (static : sevm.isStatic = false) : SwapBackForwardEnv sevm d M n p w ρ R G :=
  { d0 := env.d0, d1 := env.d1, callGas0 := env.callGas0, callGas1 := env.callGas1,
    first := env.first, second := env.second, guard := guard, k := k, bound0 := bound0,
    bound1 := bound1, static := static, sentries := env.sentries, unlock := env.unlock }

/-- The back half's entry gas, from the callee environment (`SwapBackForwardEnv.gas`). -/
def SwapBackCalleeEnv.gas {sevm : Sevm} {d : Devm} {M : Mem} {n : Nat} {p : B256}
    {w : SwapCutWords} {ρ : B256} {R : List B256} {G : Nat}
    (env : SwapBackCalleeEnv sevm d M n p w ρ R G) : Nat :=
  env.callGas0 + 5 + swapRequestCharge d n p w.token0 72 + 16

/-- The back half's returned world, from the callee environment (`SwapBackForwardEnv.post`). -/
def SwapBackCalleeEnv.post {sevm : Sevm} {d : Devm} {M : Mem} {n : Nat} {p : B256}
    {w : SwapCutWords} {ρ : B256} {R : List B256} {G : Nat}
    (env : SwapBackCalleeEnv sevm d M n p w ρ R G) : Devm :=
  afterSstore sevm (swapLoggedWorld sevm env.d1 w.reserve0 w.reserve1
    (swapBalanceWord env.d0.returnData) (swapBalanceWord env.d1.returnData)
    (swapInWord (swapBalanceWord env.d0.returnData) w.reserve0 w.amount0Out)
    (swapInWord (swapBalanceWord env.d1.returnData) w.reserve1 w.amount1Out)
    w.amount0Out w.amount1Out w.recipient) 12 1

/-- The back half's returned memory, from the callee environment (`SwapBackForwardEnv.memory`). -/
def SwapBackCalleeEnv.memory {sevm : Sevm} {d : Devm} {M : Mem} {n : Nat} {p : B256}
    {w : SwapCutWords} {ρ : B256} {R : List B256} {G : Nat}
    (env : SwapBackCalleeEnv sevm d M n p w ρ R G) : Mem :=
  swapEventMemory (swapSyncMemory (swapBalanceReply (swapBalanceReply M p sevm.currentTarget
      env.d0.returnData) p sevm.currentTarget env.d1.returnData) p
      (updateFinalPackedWord sevm env.d1 w.reserve0 w.reserve1
        (swapBalanceWord env.d0.returnData) (swapBalanceWord env.d1.returnData)))
    p (swapInWord (swapBalanceWord env.d0.returnData) w.reserve0 w.amount0Out)
    (swapInWord (swapBalanceWord env.d1.returnData) w.reserve1 w.amount1Out)
    w.amount0Out w.amount1Out

/-- The model's acceptance at the actual answers gives the answer-level facts of the back half. -/
theorem SwapBackCalleeEnv.accepted {sevm : Sevm} {d : Devm} {M : Mem} {n : Nat} {p : B256}
    {ρ : B256} {R : List B256} {G : Nat} {st : State}
    (env : SwapBackCalleeEnv sevm d M n p (swapCutWords sevm st) ρ R G)
    (conditions : SwapModelConditions st (swapAmount0Out sevm) (swapAmount1Out sevm)
      (swapRecipient sevm) (swapBalanceWord env.d0.returnData) (swapBalanceWord env.d1.returnData))
    (static : sevm.isStatic = false) :
    ∃ back : SwapBackForwardEnv sevm d M n p (swapCutWords sevm st) ρ R G,
      back.gas = env.gas ∧ back.post = env.post ∧ back.memory = env.memory := by
  obtain ⟨_, _, out0, out1, _, _, bound0, bound1, positive, checked⟩ := conditions
  obtain ⟨guard, k⟩ := swapCheck_raw st.reserve0.isLt st.reserve1.isLt out0 out1 positive checked
  exact ⟨env.toForward guard k bound0 bound1 static, rfl, rfl, rfl⟩

end Blanc.Lift.UniswapV2Pair
