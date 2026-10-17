import Blanc.Composition.UniswapV2PairWeth9LegsSwap0Read

/-!
# The swap's WETH9 `transfer` leg with WETH9 = token0 (C4(b), U8b1)

`swapWethLeg0` is the swap front half's first optimistic transfer (`SwapFrontForwardEnv.transfer0`)
when WETH9 is `token0`: the WETH9 `transfer` `CALL` at the swap's prefix world, at the call gas the
crossing itself fixes.  WETH9 pays first, so no other token's leg precedes it, and both outputs are
general.  As for `swapWethLeg1`, the continuation's need (the second transfer site's charge, the
callback branch's gas and `_safeTransfer`'s post-call charge) reads the `CALL`'s result only off its
gas-free columns, so it is computed on the gas-free skeleton.  The later legs (the second token's
transfer gas `cg1`, its result `d1`, the callback's `cgC` and the join gas `Gc`) are parameters.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair

section Leg0

variable (sevm : Sevm) (b : Devm) (st : UniswapV2Pair.State) (d1 : Devm) (cg1 cgC Gc : Nat)

/-- The gas-free skeleton of the WETH9 `transfer` CALL's result (token0 = WETH9). -/
def leg0Skel : Devm :=
  wethTransferSkel sevm (swapPrefixWorld sevm b) (swapLocalsStack sevm st) getterInitMemory 128
    (swapAmount0Out sevm) (swapRecipientWord sevm) st.token0.toB256 0x8d0

/-- The residual the record ties the first transfer to: the second transfer site's charge over the
callback branch's gas, read off the first transfer's result `d`. -/
def leg0Next (d : Devm) : Nat :=
  swapOptGas (swapOptMem getterInitMemory 128 (swapAmount0Out sevm) (swapRecipientWord sevm) d)
    (swapOptPtr 128 (swapAmount0Out sevm) d) (swapAmount1Out sevm) cg1
    (swapFrontCallbackGas sevm b d d1 cgC Gc)

/-- What the Pair needs left after the WETH9 `transfer` CALL, read on the skeleton. -/
def leg0Need : Nat :=
  leg0Next sevm b d1 cg1 cgC Gc (leg0Skel sevm b st) +
    safeTransferPostCharge getterInitMemory.size 128 (leg0Skel sevm b st).returnData

/-- WETH9's charge for the leg's child frame. -/
def leg0Used : Nat :=
  xferUsed sevm (swapPrefixWorld sevm b) (swapLocalsStack sevm st) getterInitMemory 128
    (swapAmount0Out sevm) (swapRecipientWord sevm) st.token0.toB256 0x8d0

/-- The `CALL`'s own charges: the token's access, the windows' expansion, WETH9's `transfer`. -/
def leg0Charge : Nat :=
  xferAcc (swapPrefixWorld sevm b) st.token0.toB256 +
    xferExt (swapPrefixWorld sevm b) (swapLocalsStack sevm st) getterInitMemory 128
      (swapAmount0Out sevm) (swapRecipientWord sevm) st.token0.toB256 0x8d0 +
    leg0Used sevm b st

end Leg0

/-- **The WETH9 `transfer` leg of the swap front half (token0 = WETH9)**: the `CALL` result and the
`CALL` state's gas that WETH9's deployed code determines, given the later legs' gas and result. -/
noncomputable def swapWethLeg0 (sevm : Sevm) (b : Devm) (st : UniswapV2Pair.State) (d1 : Devm)
    (cg1 cgC Gc : Nat) : Devm × Nat :=
  (wethTransferCall sevm (swapPrefixWorld sevm b) (swapLocalsStack sevm st) getterInitMemory 128
      (swapAmount0Out sevm) (swapRecipientWord sevm) st.token0.toB256 0x8d0
      (leg0Need sevm b st d1 cg1 cgC Gc + leg0Charge sevm b st),
    leg0Need sevm b st d1 cg1 cgC Gc + leg0Charge sevm b st)

/-- The callback branch's gas reads the first transfer's result only off its gas-free columns. -/
theorem swapFrontCallbackGas_withGasLeft0 (sevm : Sevm) (b d d1 : Devm) (cgC Gc x : Nat) :
    swapFrontCallbackGas sevm b (d.withGasLeft x) d1 cgC Gc = swapFrontCallbackGas sevm b d d1 cgC Gc := by
  unfold swapFrontCallbackGas swapFrontTransferWorld swapFrontTransferMem swapFrontPtr swapOptWorld
    swapOptMem swapOptPtr swapCallbackGas temporalAccountAccessCost
  by_cases h0 : swapAmount0Out sevm = 0 <;> by_cases h1 : swapAmount1Out sevm = 0 <;>
    simp only [h0, h1, ↓reduceIte, withGasLeft_accessedAddresses, withGasLeft_returnData]

theorem leg0Next_withGasLeft (sevm : Sevm) (b d1 : Devm) (cg1 cgC Gc : Nat) (d : Devm) (x : Nat) :
    leg0Next sevm b d1 cg1 cgC Gc (d.withGasLeft x) = leg0Next sevm b d1 cg1 cgC Gc d := by
  unfold leg0Next
  rw [swapFrontCallbackGas_withGasLeft0]
  rfl

/-- **The WETH9 `transfer` leg's spec, token0 = WETH9 (frame level).**  At the swap's prefix world,
for any outputs: WETH9's code at token0, token0 not a precompile, call depth left, the Pair's WETH9
balance covering `amount0Out`, the leg's call gas a word, and room for WETH9's `transfer` under the
63/64 rule with its `SSTORE` sentry.  Then `swapWethLeg0` is the transfer record
`SwapFrontForwardEnv.transfer0` asks for, at the residual its continuation fixes. -/
theorem swapWethLeg0_spec {sevm : Sevm} {b : Devm} {st : UniswapV2Pair.State} {d1 : Devm}
    {cg1 cgC Gc : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (nonstatic : sevm.isStatic = false)
    (depth : sevm.depth ≠ 0)
    (wethCode : (swapPrefixWorld sevm b).state.getCode st.token0 = Weth9.code)
    (notPrecompile : sevm.benvStat.rules.isPrecomp st.token0 = false)
    (balance : swapAmount0Out sevm ≤
      (swapPrefixWorld sevm b).getStorVal st.token0 (Weth9.balSlot sevm.currentTarget))
    (fits : (swapWethLeg0 sevm b st d1 cg1 cgC Gc).2 < 2 ^ 256)
    (room : leg0Used sevm b st + gCallStipend ≤
      except64th (leg0Need sevm b st d1 cg1 cgC Gc + leg0Used sevm b st)) :
    SwapTransferCallForward sevm (swapPrefixWorld sevm b)
      (swapLocalsStack sevm st) getterInitMemory getterInitMemory.size 128 (swapAmount0Out sevm)
      (swapRecipientWord sevm) st.token0.toB256 0x8d0 (swapWethLeg0 sevm b st d1 cg1 cgC Gc).2
      (swapOptGas (swapOptMem getterInitMemory 128 (swapAmount0Out sevm) (swapRecipientWord sevm)
          (swapWethLeg0 sevm b st d1 cg1 cgC Gc).1)
        (swapOptPtr 128 (swapAmount0Out sevm) (swapWethLeg0 sevm b st d1 cg1 cgC Gc).1)
        (swapAmount1Out sevm) cg1
        (swapFrontCallbackGas sevm b (swapWethLeg0 sevm b st d1 cg1 cgC Gc).1 d1 cgC Gc))
      (swapWethLeg0 sevm b st d1 cg1 cgC Gc).1 := by
  have spec := wethTransferCall_spec (sevm := sevm) (W := swapPrefixWorld sevm b)
    (L := swapLocalsStack sevm st) (M := getterInitMemory) (p := 128)
    (amount := swapAmount0Out sevm) (toWord := swapRecipientWord sevm) (token := st.token0.toB256)
    (rho := 0x8d0) (cg := leg0Need sevm b st d1 cg1 cgC Gc + leg0Charge sevm b st) fork
    (by rw [tokenMask_toAdr]; exact wethCode) nonstatic depth
    (by rw [tokenMask_toAdr]; exact notPrecompile)
    (by simp only [swapLocalsStack, swapBodyStack, List.length_cons, List.length_nil]; omega)
    getterInitMemory_ptr.wf (by decide) (by decide)
    (by rw [tokenMask_toAdr]; exact balance) fits
    (by unfold leg0Charge; omega)
    (by
      have e : leg0Need sevm b st d1 cg1 cgC Gc + leg0Charge sevm b st -
          xferExt (swapPrefixWorld sevm b) (swapLocalsStack sevm st) getterInitMemory 128
            (swapAmount0Out sevm) (swapRecipientWord sevm) st.token0.toB256 0x8d0 -
          xferAcc (swapPrefixWorld sevm b) st.token0.toB256 =
          leg0Need sevm b st d1 cg1 cgC Gc + leg0Used sevm b st := by
        unfold leg0Charge; omega
      rw [e]
      exact room)
  obtain ⟨hrun, hstk, hret, hgas⟩ := spec
  have hskel : wethTransferCall sevm (swapPrefixWorld sevm b) (swapLocalsStack sevm st)
      getterInitMemory 128 (swapAmount0Out sevm) (swapRecipientWord sevm) st.token0.toB256 0x8d0
      (leg0Need sevm b st d1 cg1 cgC Gc + leg0Charge sevm b st) =
      (leg0Skel sevm b st).withGasLeft _ :=
    wethTransferCallAt_eq _ _ _ _ _ _ _ _ _ _ _ _ _
  have hret' : (swapWethLeg0 sevm b st d1 cg1 cgC Gc).1.returnData = B256.toBytes 1 := hret
  refine ⟨hrun, hstk, Or.inr (by rw [hret']; exact one_reply_accepted), ?_⟩
  change (wethTransferCall sevm (swapPrefixWorld sevm b) (swapLocalsStack sevm st) getterInitMemory
      128 (swapAmount0Out sevm) (swapRecipientWord sevm) st.token0.toB256 0x8d0
      (leg0Need sevm b st d1 cg1 cgC Gc + leg0Charge sevm b st)).gasLeft =
    leg0Next sevm b d1 cg1 cgC Gc (wethTransferCall sevm (swapPrefixWorld sevm b)
      (swapLocalsStack sevm st) getterInitMemory 128 (swapAmount0Out sevm) (swapRecipientWord sevm)
      st.token0.toB256 0x8d0 (leg0Need sevm b st d1 cg1 cgC Gc + leg0Charge sevm b st)) +
    safeTransferPostCharge getterInitMemory.size 128
      (wethTransferCall sevm (swapPrefixWorld sevm b) (swapLocalsStack sevm st) getterInitMemory
        128 (swapAmount0Out sevm) (swapRecipientWord sevm) st.token0.toB256 0x8d0
        (leg0Need sevm b st d1 cg1 cgC Gc + leg0Charge sevm b st)).returnData
  rw [hgas]
  conv => rhs; rw [hskel, leg0Next_withGasLeft, withGasLeft_returnData]
  have hn : leg0Need sevm b st d1 cg1 cgC Gc = leg0Next sevm b d1 cg1 cgC Gc (leg0Skel sevm b st) +
      safeTransferPostCharge getterInitMemory.size 128 (leg0Skel sevm b st).returnData := rfl
  rw [← hn]
  unfold leg0Charge leg0Used
  omega

end Blanc.Composition.UniswapV2PairWeth9Joint
