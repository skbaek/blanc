import Blanc.Lift.UniswapV2Pair.SwapForwardBalance
import Blanc.Lift.UniswapV2Pair.SwapBack

/-! The forward (gas-exact) back half of the swap body, from the post-callback join
`t_09c3_c5` (`SwapCut`) to the body's return: the mirror of `swapBack_raw_inv`. Both
`balanceOf` callees are forward-environment premises (`SwapBalanceEnv`, ENV class); every
other charge is a closed function of the actual worlds, memory sizes and words. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The gas the back half needs after the second balance callee returns: the ternaries and
input guard, the `K` check, `_update` at `p`, the `Swap` log, the unlock and the return, with
residual `G`. `d1` is the world the second callee returned and `n2` the allocation then. -/
def swapBackPostGas (sevm : Sevm) (d1 : Devm) (n2 : Nat) (p : B256) (w : SwapCutWords)
    (bal0 bal1 : B256) (G : Nat) : Nat :=
  swapEventRunGas G (swapSyncSize n2 p) p
      (swapUnlockCost sevm d1 w.reserve0 w.reserve1 bal0 bal1
        (swapInWord bal0 w.reserve0 w.amount0Out) (swapInWord bal1 w.reserve1 w.amount1Out)
        w.amount0Out w.amount1Out w.recipient) +
    swapUpdateCharge sevm d1 n2 p w.reserve0 w.reserve1 bal0 bal1 + 31 +
    swapKCharge bal1 (swapInWord bal1 w.reserve1 w.amount1Out) w.reserve1 +
    swapInputsCharge bal0 bal1 w.reserve0 w.reserve1 w.amount0Out w.amount1Out

/-- The cached words below the four balance slots at the join. -/
def swapCutTail (w : SwapCutWords) (ρ : B256) (R : List B256) : List B256 :=
  w.reserve1 :: w.reserve0 :: w.dataLength :: w.dataOffset :: w.recipient :: w.amount1Out ::
    w.amount0Out :: ρ :: R

/-- **Forward environment of the swap back half.** The two supplied `balanceOf(pair)` callees
(compiled `STATICCALL` steps from the actual staged states, with success, at least one word
of returndata and returned gas), and the primitive guards the successful path needs: the
input guard and SafeMath `K` facts over the observed balances, both uint112 bounds,
mutability, and the four SSTORE sentries. No successful suffix run is assumed. -/
structure SwapBackForwardEnv (sevm : Sevm) (d : Devm) (M : Mem) (n : Nat) (p : B256)
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
  guard : 0 < swapInWord (swapBalanceWord d0.returnData) w.reserve0 w.amount0Out ∨
    0 < swapInWord (swapBalanceWord d1.returnData) w.reserve1 w.amount1Out
  k : SwapKFacts (swapBalanceWord d0.returnData) (swapBalanceWord d1.returnData)
    (swapInWord (swapBalanceWord d0.returnData) w.reserve0 w.amount0Out)
    (swapInWord (swapBalanceWord d1.returnData) w.reserve1 w.amount1Out) w.reserve0 w.reserve1
  bound0 : (swapBalanceWord d0.returnData).toNat < 2 ^ 112
  bound1 : (swapBalanceWord d1.returnData).toNat < 2 ^ 112
  static : sevm.isStatic = false
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

/-- The exact gas the back half is entered with: the first callee's gas word plus the closed
staging charges. Everything after the first callee is charged inside `first.returnedGas`. -/
def SwapBackForwardEnv.gas {sevm : Sevm} {d : Devm} {M : Mem} {n : Nat} {p : B256}
    {w : SwapCutWords} {ρ : B256} {R : List B256} {G : Nat}
    (env : SwapBackForwardEnv sevm d M n p w ρ R G) : Nat :=
  env.callGas0 + 5 + swapRequestCharge d n p w.token0 72 + 16

/-- The world the back half returns: `_update` at the cached reserves and observed balances,
the `Swap` log, and the unlock store. -/
def SwapBackForwardEnv.post {sevm : Sevm} {d : Devm} {M : Mem} {n : Nat} {p : B256}
    {w : SwapCutWords} {ρ : B256} {R : List B256} {G : Nat}
    (env : SwapBackForwardEnv sevm d M n p w ρ R G) : Devm :=
  afterSstore sevm (swapLoggedWorld sevm env.d1 w.reserve0 w.reserve1
    (swapBalanceWord env.d0.returnData) (swapBalanceWord env.d1.returnData)
    (swapInWord (swapBalanceWord env.d0.returnData) w.reserve0 w.amount0Out)
    (swapInWord (swapBalanceWord env.d1.returnData) w.reserve1 w.amount1Out)
    w.amount0Out w.amount1Out w.recipient) 12 1

/-- The memory the back half returns. -/
def SwapBackForwardEnv.memory {sevm : Sevm} {d : Devm} {M : Mem} {n : Nat} {p : B256}
    {w : SwapCutWords} {ρ : B256} {R : List B256} {G : Nat}
    (env : SwapBackForwardEnv sevm d M n p w ρ R G) : Mem :=
  swapEventMemory (swapSyncMemory (swapBalanceReply (swapBalanceReply M p sevm.currentTarget
      env.d0.returnData) p sevm.currentTarget env.d1.returnData) p
      (updateFinalPackedWord sevm env.d1 w.reserve0 w.reserve1
        (swapBalanceWord env.d0.returnData) (swapBalanceWord env.d1.returnData)))
    p (swapInWord (swapBalanceWord env.d0.returnData) w.reserve0 w.amount0Out)
    (swapInWord (swapBalanceWord env.d1.returnData) w.reserve1 w.amount1Out)
    w.amount0Out w.amount1Out

/-- **Forward swap back half** (the mirror of `swapBack_raw_inv`). From the post-callback
join with the cut stack, the forward environment constructs the exact run of the actual
body to its return: both `balanceOf(pair)` queries at `p`, the ternaries and input guard, the
SafeMath `K` check, `_update` at `p`, the `Swap` log and the unlock. The entry gas is
`env.gas` and the residual is exactly `G`. -/
theorem swapBack_exact {sevm : Sevm} {d : Devm} {M : Mem} {n G : Nat} {p ρ : B256}
    {w : SwapCutWords} {R : List B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256) (room : R.length ≤ 980)
    (env : SwapBackForwardEnv sevm d M n p w ρ R G) :
    SFunc.RunExact cert.prog sevm (St d (swapCutStack w ρ R) M env.gas) t_09c3_c5
      (.returned (St env.post R env.memory G)) := by
  have reply0 := swapBalanceReply_ptr (pair := sevm.currentTarget) env.d0.returnData mem lower width
  have reply1 := swapBalanceReply_ptr (pair := sevm.currentTarget) env.d1.returnData reply0
    lower width
  refine swapFirstBalance_exact fork mem lower width
    (by simp only [List.length_cons]; omega) env.first ?_
  refine swapSecondBalance_exact fork mem lower width env.first.long
    (by simp only [List.length_cons]; omega) env.second ?_
  refine swapInputs_exact reply1 (swapRequestSize_cover reply0)
    (swapBalanceReply_word reply0.wf env.d1.returnData env.second.long) env.guard
    (by simp only [List.length_cons]; omega) ?_
  refine swapK_exact env.k (by simp only [List.length_cons]; omega) ?_
  exact swapTail_exact fork reply1 lower width env.static env.bound0 env.bound1 (by omega)
    env.sentries env.unlock

/-- **Source acceptance gives the raw guards** (forward dual of `swapCheck_source`): if the
source `swapCheck` accepts at the inputs `swapInputs` infers, then the actual input guard and
every SafeMath `K` fact hold over the actual ternary words. These are the `guard` and `k`
fields of `SwapBackForwardEnv` at the cut's cached reserves. -/
theorem swapRaw_of_check {bal0 bal1 a0 a1 : B256} {r0 r1 : Nat}
    (bound0 : r0 < 2 ^ 112) (bound1 : r1 < 2 ^ 112)
    (out0 : a0.toNat < r0) (out1 : a1.toNat < r1)
    (check : swapCheck bal0 bal1 (swapInputs bal0 bal1 a0 a1 r0 r1).1
      (swapInputs bal0 bal1 a0 a1 r0 r1).2 r0 r1 = .ok ()) :
    (0 < swapInWord bal0 (Nat.toB256 r0) a0 ∨ 0 < swapInWord bal1 (Nat.toB256 r1) a1) ∧
    SwapKFacts bal0 bal1 (swapInWord bal0 (Nat.toB256 r0) a0)
      (swapInWord bal1 (Nat.toB256 r1) a1) (Nat.toB256 r0) (Nat.toB256 r1) := by
  have in0 := swapInWord_source (balance := bal0) bound0 out0
  have in1 := swapInWord_source (balance := bal1) bound1 out1
  generalize swapInWord bal0 (Nat.toB256 r0) a0 = x0 at in0 ⊢
  generalize swapInWord bal1 (Nat.toB256 r1) a1 = x1 at in1 ⊢
  unfold swapCheck swapInputs at check
  dsimp only at check
  rw [← in0, ← in1] at check
  split at check
  case isFalse => cases check
  rename_i guard
  split at check
  case isFalse => cases check
  rename_i fit0
  split at check
  case isFalse => cases check
  rename_i cover0
  split at check
  case isFalse => cases check
  rename_i fit1
  split at check
  case isFalse => cases check
  rename_i cover1
  split at check
  case isFalse => cases check
  rename_i adjFit
  split at check
  case isFalse => cases check
  rename_i kNat
  have m0 : B256.Nofm x0 3 := fit0.2
  have b0 : B256.Nofm bal0 1000 := fit0.1
  have m1 : B256.Nofm x1 3 := fit1.2
  have b1 : B256.Nofm bal1 1000 := fit1.1
  have e0 : (x0 * 3).toNat = x0.toNat * 3 := B256.toNat_mul_eq_of_nofm m0
  have f0 : (bal0 * 1000).toNat = bal0.toNat * 1000 := B256.toNat_mul_eq_of_nofm b0
  have e1 : (x1 * 3).toNat = x1.toNat * 3 := B256.toNat_mul_eq_of_nofm m1
  have f1 : (bal1 * 1000).toNat = bal1.toNat * 1000 := B256.toNat_mul_eq_of_nofm b1
  have c0 : x0 * 3 ≤ bal0 * 1000 := by
    rw [B256.le_iff_toNat_le_toNat, e0, f0]
    exact cover0
  have c1 : x1 * 3 ≤ bal1 * 1000 := by
    rw [B256.le_iff_toNat_le_toNat, e1, f1]
    exact cover1
  have s0 : (bal0 * 1000 - x0 * 3).toNat = bal0.toNat * 1000 - x0.toNat * 3 := by
    rw [B256.toNat_sub_eq_of_le _ _ c0, e0, f0]
  have s1 : (bal1 * 1000 - x1 * 3).toNat = bal1.toNat * 1000 - x1.toNat * 3 := by
    rw [B256.toNat_sub_eq_of_le _ _ c1, e1, f1]
  have adj : B256.Nofm (bal0 * 1000 - x0 * 3) (bal1 * 1000 - x1 * 3) := by
    unfold B256.Nofm
    rw [s0, s1]
    exact adjFit
  have rNat0 : (Nat.toB256 r0).toNat = r0 := B256.toNat_toB256_of_lt (by omega)
  have rNat1 : (Nat.toB256 r1).toNat = r1 := B256.toNat_toB256_of_lt (by omega)
  obtain ⟨resMul, kMul⟩ := swapReserveProduct_nofm (Nat.toB256 r0) (Nat.toB256 r1)
  have resProd : ((reserveMask112 &&& Nat.toB256 r0) * (Nat.toB256 r1 &&& reserveMask112) *
      1000000).toNat = r0 * r1 * 1000000 := by
    rw [B256.toNat_mul_eq_of_nofm kMul, B256.toNat_mul_eq_of_nofm resMul, swapMask_reserve bound0,
      B256.and_comm, swapMask_reserve bound1, rNat0, rNat1,
      show (1000000 : B256).toNat = 1000000 from by decide]
  refine ⟨?_, m0, b0, c0, m1, b1, c1, adj, ?_⟩
  · rw [B256.lt_iff_toNat_lt_toNat, B256.lt_iff_toNat_lt_toNat]
    exact guard
  · rw [B256.lt_iff_toNat_lt_toNat, resProd, B256.toNat_mul_eq_of_nofm adj, s0, s1]
    rw [show (1000 : Nat) ^ 2 = 1000000 from rfl] at kNat
    omega

end Blanc.Lift.UniswapV2Pair
