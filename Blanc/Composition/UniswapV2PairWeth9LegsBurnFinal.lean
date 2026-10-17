import Blanc.Composition.UniswapV2PairWeth9LegsBurnRead

/-!
# The burn suffix's final WETH9 `balanceOf` legs (C4(b), U8b2)

`BurnBackForwardEnv.first`/`second` are the suffix's two final `balanceOf(pair)` queries, in the
swap's `SwapBalanceEnv` shape.  For the WETH9 side, `token0` (`burnWethFinal0`, staged over the
second transfer's result `d1`) or `token1` (`burnWethFinal1`, over the first final query's result
`e0`), the query is the generic read leg at the need the record's next segment fixes.  The legs are
stated over the suffix record's parameters with the earlier callees' results free.  Code-only.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair

section Final

variable (sevm : Sevm) (M : Mem) (p0 : B256) (w : BurnSuffixWords) (R : List B256)
  (d0 d1 : Devm)

/-- What the suffix needs left after its first final query: the second request's staging and the
second query's call gas (`BurnBackForwardEnv.first`'s `tailGas + 64`). -/
def burnFinal0Need (balanceGas1 : Nat) (e0 : Devm) : Nat :=
  balanceGas1 + 5 + swapRequestCharge e0
    (swapRequestSize (burnSuffixMem2 M p0 w d0 d1).size (burnSuffixPtr p0 d0 d1))
    (burnSuffixPtr p0 d0 d1) w.token1 83 + 21 + 64

/-- The memory the second final query is staged over (the first final reply written in). -/
def burnFinal1Mem (e0 : Devm) : Mem :=
  swapBalanceReply (burnSuffixMem2 M p0 w d0 d1) (burnSuffixPtr p0 d0 d1) sevm.currentTarget
    e0.returnData

/-- The words under the second final query's request words. -/
def burnFinal1Stack (e0 : Devm) : List B256 :=
  w.locals w.balance1 (Bytes.toB256 (e0.returnData.take 32)) R

/-- What the suffix needs left after its second final query: `_update`, the fee checkpoint, the
`Burn` log and the unlock (`BurnBackForwardEnv.second`'s `tailGas + 64`). -/
def burnFinal1Need (e0 : Devm) (G : Nat) (e1 : Devm) : Nat :=
  burnSuffixTailGas sevm M p0 w d0 d1 e0 e1 G + 64

end Final

/-- **The suffix's first final query when WETH9 is `token0`**: its result and the call gas WETH9's
code determines, given the second final query's call gas `balanceGas1`. -/
noncomputable def burnWethFinal0 (sevm : Sevm) (M : Mem) (p0 : B256) (w : BurnSuffixWords)
    (R : List B256) (d0 d1 : Devm) (balanceGas1 : Nat) : Devm × Nat :=
  wethReadLeg sevm d1 (w.locals w.balance1 w.balance0 R) (burnSuffixMem2 M p0 w d0 d1)
    (burnSuffixPtr p0 d0 d1) w.token0 (burnFinal0Need M p0 w d0 d1 balanceGas1)

/-- **The suffix's second final query when WETH9 is `token1`**, over the first final query's
result `e0`: its result and the call gas WETH9's code determines, given the suffix residual `G`. -/
noncomputable def burnWethFinal1 (sevm : Sevm) (M : Mem) (p0 : B256) (w : BurnSuffixWords)
    (R : List B256) (d0 d1 e0 : Devm) (G : Nat) : Devm × Nat :=
  wethReadLeg sevm e0 (burnFinal1Stack w R e0) (burnFinal1Mem sevm M p0 w d0 d1 e0)
    (burnSuffixPtr p0 d0 d1) w.token1 (burnFinal1Need sevm M p0 w d0 d1 e0 G)

theorem burnFinal0Need_gasFree (M : Mem) (p0 : B256) (w : BurnSuffixWords) (d0 d1 : Devm)
    (balanceGas1 : Nat) (e : Devm) (x : Nat) :
    burnFinal0Need M p0 w d0 d1 balanceGas1 (e.withGasLeft x) =
      burnFinal0Need M p0 w d0 d1 balanceGas1 e := rfl

/-- **The suffix's first final WETH9 read (WETH9 = token0), frame level.**  At the second transfer's
result world `d1`: WETH9's code at `token0` there, not a precompile, call depth left, a well-formed
memory, the pointer's width bound, stack room, the call gas a word, and room for WETH9's view.  Then
`burnWethFinal0` is the `BurnBackForwardEnv.first` record, and replies with the pair's WETH9 balance
at `d1`.  Code-only: nothing is assumed of the transfers' callees. -/
theorem burnWethFinal0_spec {sevm : Sevm} {M : Mem} {p0 : B256} {w : BurnSuffixWords}
    {R : List B256} {d0 d1 : Devm} {balanceGas1 : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (depth : sevm.depth ≠ 0)
    (wethCode : d1.state.getCode (swapTokenWord w.token0).toAdr = Weth9.code)
    (notPrecompile : sevm.benvStat.rules.isPrecomp (swapTokenWord w.token0).toAdr = false)
    (wf : Mem.Wf (burnSuffixMem2 M p0 w d0 d1))
    (width : (burnSuffixPtr p0 d0 d1).toNat + 260 < 2 ^ 256) (stackRoom : R.length < 1005)
    (fits : (burnWethFinal0 sevm M p0 w R d0 d1 balanceGas1).2 < 2 ^ 256)
    (room : balUsed sevm d1 (w.locals w.balance1 w.balance0 R) (burnSuffixMem2 M p0 w d0 d1)
        (burnSuffixPtr p0 d0 d1) w.token0 ≤
      except64th (burnFinal0Need M p0 w d0 d1 balanceGas1 (wethBalanceSkel sevm d1
          (w.locals w.balance1 w.balance0 R) (burnSuffixMem2 M p0 w d0 d1) (burnSuffixPtr p0 d0 d1)
          w.token0) +
        balUsed sevm d1 (w.locals w.balance1 w.balance0 R) (burnSuffixMem2 M p0 w d0 d1)
          (burnSuffixPtr p0 d0 d1) w.token0)) :
    SwapBalanceEnv sevm d1 (burnSuffixMem2 M p0 w d0 d1) (burnSuffixPtr p0 d0 d1) w.token0
      (w.locals w.balance1 w.balance0 R) (burnWethFinal0 sevm M p0 w R d0 d1 balanceGas1).1
      (burnWethFinal0 sevm M p0 w R d0 d1 balanceGas1).2
      (balanceGas1 + 5 + swapRequestCharge (burnWethFinal0 sevm M p0 w R d0 d1 balanceGas1).1
        (swapRequestSize (burnSuffixMem2 M p0 w d0 d1).size (burnSuffixPtr p0 d0 d1))
        (burnSuffixPtr p0 d0 d1) w.token1 83 + 21) ∧
    (burnWethFinal0 sevm M p0 w R d0 d1 balanceGas1).1.returnData =
      (d1.getStorVal (swapTokenWord w.token0).toAdr (Weth9.balSlot sevm.currentTarget)).toBytes := by
  obtain ⟨hrun, hstk, hret, hgas⟩ := wethReadLeg_spec (sevm := sevm) (B := d1)
    (S := w.locals w.balance1 w.balance0 R) (M := burnSuffixMem2 M p0 w d0 d1)
    (p := burnSuffixPtr p0 d0 d1) (t := w.token0) (need := burnFinal0Need M p0 w d0 d1 balanceGas1)
    (burnFinal0Need_gasFree M p0 w d0 d1 balanceGas1) fork wethCode depth notPrecompile
    (by simp only [BurnSuffixWords.locals, burnPricedLocals, List.length_cons]; omega) wf width
    fits room
  unfold burnWethFinal0
  exact ⟨⟨weth9_code_nonzero wethCode, hrun, hstk, by rw [hret]; exact toBytes_long _, hgas⟩, hret⟩

/-- The suffix's tail gas reads the second final query's result only off its gas-free columns. -/
theorem burnSuffixTailGas_withGasLeft (sevm : Sevm) (M : Mem) (p0 : B256) (w : BurnSuffixWords)
    (d0 d1 e0 e1 : Devm) (G x : Nat) :
    burnSuffixTailGas sevm M p0 w d0 d1 e0 (e1.withGasLeft x) G =
      burnSuffixTailGas sevm M p0 w d0 d1 e0 e1 G := by
  simp only [burnSuffixTailGas, burnSuffixUpdated, burnSuffixUnlockCost, burnKLastGas,
    burnKLastPost, burnKLastStorePost, burnEventPost, swapUpdateCharge, updateWorld,
    updateSyncPost, updatePackedPost, updateFinalPackedWord, updateOracleWorld, updateOracleActive,
    swapUpdLoad8, swapUpdStore8, swapUpdLoad9, swapUpdStore9, swapUpdLoad10, swapUpdStore10,
    swapUpdAcc0, updateAccumulatorPost, Devm.withGasLeft, afterSload_setMach, afterSstore_setMach,
    addLog_setMach', Devm.getStorVal_setMach, sstoreCost_setMach, sloadCost_setMach', ite_setMach]
  rfl

theorem burnFinal1Need_gasFree (sevm : Sevm) (M : Mem) (p0 : B256) (w : BurnSuffixWords)
    (d0 d1 e0 : Devm) (G : Nat) (e : Devm) (x : Nat) :
    burnFinal1Need sevm M p0 w d0 d1 e0 G (e.withGasLeft x) = burnFinal1Need sevm M p0 w d0 d1 e0 G e := by
  unfold burnFinal1Need
  rw [burnSuffixTailGas_withGasLeft]

/-- **The suffix's second final WETH9 read (WETH9 = token1), frame level.**  At the first final
query's result world `e0`: WETH9's code at `token1` there, not a precompile, call depth left, a
well-formed memory under the replies, the pointer's width bound, stack room, the call gas a word, and
room for WETH9's view.  Then `burnWethFinal1` is the `BurnBackForwardEnv.second` record, and replies
with the pair's WETH9 balance at `e0`.  Code-only. -/
theorem burnWethFinal1_spec {sevm : Sevm} {M : Mem} {p0 : B256} {w : BurnSuffixWords}
    {R : List B256} {d0 d1 e0 : Devm} {G : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (depth : sevm.depth ≠ 0)
    (wethCode : e0.state.getCode (swapTokenWord w.token1).toAdr = Weth9.code)
    (notPrecompile : sevm.benvStat.rules.isPrecomp (swapTokenWord w.token1).toAdr = false)
    (wf : Mem.Wf (burnSuffixMem2 M p0 w d0 d1))
    (width : (burnSuffixPtr p0 d0 d1).toNat + 260 < 2 ^ 256) (stackRoom : R.length < 1005)
    (fits : (burnWethFinal1 sevm M p0 w R d0 d1 e0 G).2 < 2 ^ 256)
    (room : balUsed sevm e0 (burnFinal1Stack w R e0) (burnFinal1Mem sevm M p0 w d0 d1 e0)
        (burnSuffixPtr p0 d0 d1) w.token1 ≤
      except64th (burnFinal1Need sevm M p0 w d0 d1 e0 G (wethBalanceSkel sevm e0
          (burnFinal1Stack w R e0) (burnFinal1Mem sevm M p0 w d0 d1 e0) (burnSuffixPtr p0 d0 d1)
          w.token1) +
        balUsed sevm e0 (burnFinal1Stack w R e0) (burnFinal1Mem sevm M p0 w d0 d1 e0)
          (burnSuffixPtr p0 d0 d1) w.token1)) :
    SwapBalanceEnv sevm e0
      (swapBalanceReply (burnSuffixMem2 M p0 w d0 d1) (burnSuffixPtr p0 d0 d1) sevm.currentTarget
        e0.returnData) (burnSuffixPtr p0 d0 d1) w.token1
      (w.locals w.balance1 (Bytes.toB256 (e0.returnData.take 32)) R)
      (burnWethFinal1 sevm M p0 w R d0 d1 e0 G).1 (burnWethFinal1 sevm M p0 w R d0 d1 e0 G).2
      (burnSuffixTailGas sevm M p0 w d0 d1 e0 (burnWethFinal1 sevm M p0 w R d0 d1 e0 G).1 G) ∧
    (burnWethFinal1 sevm M p0 w R d0 d1 e0 G).1.returnData =
      (e0.getStorVal (swapTokenWord w.token1).toAdr (Weth9.balSlot sevm.currentTarget)).toBytes := by
  obtain ⟨hrun, hstk, hret, hgas⟩ := wethReadLeg_spec (sevm := sevm) (B := e0)
    (S := burnFinal1Stack w R e0) (M := burnFinal1Mem sevm M p0 w d0 d1 e0)
    (p := burnSuffixPtr p0 d0 d1) (t := w.token1) (need := burnFinal1Need sevm M p0 w d0 d1 e0 G)
    (burnFinal1Need_gasFree sevm M p0 w d0 d1 e0 G) fork wethCode depth notPrecompile
    (by simp only [burnFinal1Stack, BurnSuffixWords.locals, burnPricedLocals, List.length_cons]; omega)
    (swapBalanceReply_wf wf) width fits room
  unfold burnWethFinal1
  exact ⟨⟨weth9_code_nonzero wethCode, hrun, hstk, by rw [hret]; exact toBytes_long _, hgas⟩, hret⟩

end Blanc.Composition.UniswapV2PairWeth9Joint
