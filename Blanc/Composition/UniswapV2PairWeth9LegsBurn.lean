import Blanc.Composition.UniswapV2PairWeth9LegsBurnRead

/-!
# The burn suffix's WETH9 `transfer` leg with WETH9 = token0 (C4(b), U8b2)

`burnWethLeg0` is Burn's first optimistic transfer (`BurnBackForwardEnv.transfer0`) when WETH9 is
`token0`: the WETH9 `transfer` `CALL` at the suffix's entry world, at the call gas the crossing
itself fixes.  WETH9 pays first, so no other token's leg precedes it.  The continuation's need (the
second transfer site's charge over its call gas, and `_safeTransfer`'s post-call charge) reads the
`CALL`'s result only off its reply, so it is computed on the gas-free skeleton.

The leg's one non-frame premise is `amount0 ≤` the pair's WETH9 balance at the transfer world.  The
history row feeds it from C3: C3's ghost at the `burnTransfer0` suspension bounds the initial
WETH9 answer by the booked balance, and `burnAmount_le_balance` bounds the priced amount by that
answer (from the model's pricing and LP-burn acceptance).
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair

/-! ## amount ≤ balance -/

/-- **The burn payment on each side is at most that side's answer.**  When the model prices a burn
of `liq` out of `supply` at the answers `b0`, `b1` and accepts the LP burn (`liq ≤ supply`), each
payment is at most its answer, in `Nat` and as the words the bytecode computes. -/
theorem burnAmount_le_balance {liq b0 b1 supply : B256} {a0 a1 : Nat}
    (priced : burnAmounts liq b0 b1 supply = .ok (a0, a1)) (lp : liq ≤ supply) :
    a0 ≤ b0.toNat ∧ a1 ≤ b1.toNat ∧ (liq * b0) / supply ≤ b0 ∧ (liq * b1) / supply ≤ b1 := by
  have lpN := B256.toNat_le_toNat lp
  unfold burnAmounts at priced
  by_cases m0 : liq.toNat * b0.toNat < 2 ^ 256
  · by_cases s0 : supply = 0
    · simp only [m0, s0, ↓reduceIte, reduceCtorEq] at priced
    · by_cases m1 : liq.toNat * b1.toNat < 2 ^ 256
      · simp only [m0, s0, m1, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at priced
        obtain ⟨e0, e1⟩ := priced
        have sp : 0 < supply.toNat := by
          rcases Nat.eq_zero_or_pos supply.toNat with h | h
          · exact absurd (B256.toNat_inj _ _ (h.trans B256.toNat_zero.symm)) s0
          · exact h
        have k0 : liq.toNat * b0.toNat / supply.toNat ≤ b0.toNat :=
          Nat.div_le_of_le_mul (Nat.mul_le_mul_right _ lpN)
        have k1 : liq.toNat * b1.toNat / supply.toNat ≤ b1.toNat :=
          Nat.div_le_of_le_mul (Nat.mul_le_mul_right _ lpN)
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [← e0]; exact k0
        · rw [← e1]; exact k1
        · rw [B256.le_iff_toNat_le_toNat, B256.toNat_div s0, B256.toNat_mul_eq_of_nofm m0]
          exact k0
        · rw [B256.le_iff_toNat_le_toNat, B256.toNat_div s0, B256.toNat_mul_eq_of_nofm m1]
          exact k1
      · simp only [m0, s0, m1, ↓reduceIte, reduceCtorEq] at priced
  · simp only [m0, ↓reduceIte, reduceCtorEq] at priced

/-! ## The transfer leg -/

section Leg

variable (sevm : Sevm) (b : Devm) (M : Mem) (p0 : B256) (w : BurnSuffixWords) (R : List B256)
  (callGas1 : Nat)

/-- The words under the suffix's transfer operands. -/
def burnLegStack : List B256 := w.locals w.balance1 w.balance0 R

/-- The gas-free skeleton of the WETH9 `transfer` CALL's result (token0 = WETH9). -/
def burnLeg0Skel : Devm :=
  wethTransferSkel sevm b (burnLegStack w R) M p0 w.amount0 w.recipient w.token0 0x1698

/-- The residual the record ties the first transfer to: the second transfer site's charge over its
call gas, read off the first transfer's result `d`. -/
def burnLeg0Next (d : Devm) : Nat :=
  callGas1 + safeTransferPreCharge (burnSuffixMem1 M p0 w d).size
    (swapMovedPointer p0 d.returnData) + 24

/-- What the suffix needs left after the WETH9 `transfer` CALL, read on the skeleton. -/
def burnLeg0Need : Nat :=
  burnLeg0Next M p0 w callGas1 (burnLeg0Skel sevm b M p0 w R) +
    safeTransferPostCharge M.size p0 (burnLeg0Skel sevm b M p0 w R).returnData

/-- WETH9's charge for the leg's child frame. -/
def burnLeg0Used : Nat :=
  xferUsed sevm b (burnLegStack w R) M p0 w.amount0 w.recipient w.token0 0x1698

/-- The `CALL`'s own charges: the token's access, the windows' expansion, WETH9's `transfer`. -/
def burnLeg0Charge : Nat :=
  xferAcc b w.token0 + xferExt b (burnLegStack w R) M p0 w.amount0 w.recipient w.token0 0x1698 +
    burnLeg0Used sevm b M p0 w R

end Leg

/-- **Burn's WETH9 `transfer` leg (token0 = WETH9)**: the `CALL` result and the `CALL` state's gas
that WETH9's deployed code determines at the suffix world `b`, given the second transfer's call gas
`callGas1`. -/
noncomputable def burnWethLeg0 (sevm : Sevm) (b : Devm) (M : Mem) (p0 : B256) (w : BurnSuffixWords)
    (R : List B256) (callGas1 : Nat) : Devm × Nat :=
  (wethTransferCall sevm b (burnLegStack w R) M p0 w.amount0 w.recipient w.token0 0x1698
      (burnLeg0Need sevm b M p0 w R callGas1 + burnLeg0Charge sevm b M p0 w R),
    burnLeg0Need sevm b M p0 w R callGas1 + burnLeg0Charge sevm b M p0 w R)

theorem burnLeg0Next_withGasLeft (M : Mem) (p0 : B256) (w : BurnSuffixWords) (callGas1 : Nat)
    (d : Devm) (x : Nat) :
    burnLeg0Next M p0 w callGas1 (d.withGasLeft x) = burnLeg0Next M p0 w callGas1 d := rfl

/-- **Burn's WETH9 `transfer` leg's spec, token0 = WETH9 (frame level).**  At the suffix's entry
world `b`: WETH9's code at `token0`, not a precompile, the frame mutable, call depth left, a
well-formed memory, the pointer's bounds, stack room, the pair's WETH9 balance covering `amount0`,
the leg's call gas a word, and room for WETH9's `transfer` under the 63/64 rule with its `SSTORE`
sentry.  Then `burnWethLeg0` is the transfer record `BurnBackForwardEnv.transfer0` asks for. -/
theorem burnWethLeg0_spec {sevm : Sevm} {b : Devm} {M : Mem} {p0 : B256} {w : BurnSuffixWords}
    {R : List B256} {callGas1 : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (nonstatic : sevm.isStatic = false)
    (depth : sevm.depth ≠ 0)
    (wethCode : b.state.getCode (swapTokenWord w.token0).toAdr = Weth9.code)
    (notPrecompile : sevm.benvStat.rules.isPrecomp (swapTokenWord w.token0).toAdr = false)
    (wf : Mem.Wf M) (lower : 128 ≤ p0.toNat) (width : p0.toNat + 164 < 2 ^ 256)
    (stackRoom : R.length < 1003)
    (balance : w.amount0 ≤
      b.getStorVal (swapTokenWord w.token0).toAdr (Weth9.balSlot sevm.currentTarget))
    (fits : (burnWethLeg0 sevm b M p0 w R callGas1).2 < 2 ^ 256)
    (room : burnLeg0Used sevm b M p0 w R + gCallStipend ≤
      except64th (burnLeg0Need sevm b M p0 w R callGas1 + burnLeg0Used sevm b M p0 w R)) :
    SwapTransferCallForward sevm b (w.locals w.balance1 w.balance0 R) M M.size p0
      w.amount0 w.recipient w.token0 0x1698 (burnWethLeg0 sevm b M p0 w R callGas1).2
      (callGas1 + safeTransferPreCharge
        (burnSuffixMem1 M p0 w (burnWethLeg0 sevm b M p0 w R callGas1).1).size
        (swapMovedPointer p0 (burnWethLeg0 sevm b M p0 w R callGas1).1.returnData) + 24)
      (burnWethLeg0 sevm b M p0 w R callGas1).1 := by
  have spec := wethTransferCall_spec (sevm := sevm) (W := b) (L := burnLegStack w R) (M := M)
    (p := p0) (amount := w.amount0) (toWord := w.recipient) (token := w.token0) (rho := 0x1698)
    (cg := burnLeg0Need sevm b M p0 w R callGas1 + burnLeg0Charge sevm b M p0 w R) fork
    wethCode nonstatic depth notPrecompile
    (by simp only [burnLegStack, BurnSuffixWords.locals, burnPricedLocals, List.length_cons]; omega)
    wf lower width balance fits
    (by unfold burnLeg0Charge; omega)
    (by
      have e : burnLeg0Need sevm b M p0 w R callGas1 + burnLeg0Charge sevm b M p0 w R -
          xferExt b (burnLegStack w R) M p0 w.amount0 w.recipient w.token0 0x1698 -
          xferAcc b w.token0 =
          burnLeg0Need sevm b M p0 w R callGas1 + burnLeg0Used sevm b M p0 w R := by
        unfold burnLeg0Charge; omega
      rw [e]
      exact room)
  obtain ⟨hrun, hstk, hret, hgas⟩ := spec
  have hskel : wethTransferCall sevm b (burnLegStack w R) M p0 w.amount0 w.recipient w.token0 0x1698
      (burnLeg0Need sevm b M p0 w R callGas1 + burnLeg0Charge sevm b M p0 w R) =
      (burnLeg0Skel sevm b M p0 w R).withGasLeft _ :=
    wethTransferCallAt_eq _ _ _ _ _ _ _ _ _ _ _ _ _
  have hret' : (burnWethLeg0 sevm b M p0 w R callGas1).1.returnData = B256.toBytes 1 := hret
  refine ⟨hrun, hstk, Or.inr (by rw [hret']; exact one_reply_accepted), ?_⟩
  change (wethTransferCall sevm b (burnLegStack w R) M p0 w.amount0 w.recipient w.token0 0x1698
      (burnLeg0Need sevm b M p0 w R callGas1 + burnLeg0Charge sevm b M p0 w R)).gasLeft =
    burnLeg0Next M p0 w callGas1 (wethTransferCall sevm b (burnLegStack w R) M p0 w.amount0
      w.recipient w.token0 0x1698
      (burnLeg0Need sevm b M p0 w R callGas1 + burnLeg0Charge sevm b M p0 w R)) +
    safeTransferPostCharge M.size p0
      (wethTransferCall sevm b (burnLegStack w R) M p0 w.amount0 w.recipient w.token0 0x1698
        (burnLeg0Need sevm b M p0 w R callGas1 + burnLeg0Charge sevm b M p0 w R)).returnData
  rw [hgas]
  conv => rhs; rw [hskel, burnLeg0Next_withGasLeft, withGasLeft_returnData]
  have hn : burnLeg0Need sevm b M p0 w R callGas1 =
      burnLeg0Next M p0 w callGas1 (burnLeg0Skel sevm b M p0 w R) +
        safeTransferPostCharge M.size p0 (burnLeg0Skel sevm b M p0 w R).returnData := rfl
  rw [← hn]
  unfold burnLeg0Charge burnLeg0Used
  omega

end Blanc.Composition.UniswapV2PairWeth9Joint
