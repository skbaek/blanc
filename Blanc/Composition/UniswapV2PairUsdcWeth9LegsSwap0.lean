import Blanc.Composition.UniswapV2PairUsdcWeth9LegsXfer
import Blanc.Composition.UniswapV2PairWeth9LegsSwap0

/-!
# The swap's USDC `transfer` leg (USDC = token0, WETH9 = token1; §10c, U9a)

`swapUsdcLeg0` is the swap front half's first optimistic transfer when USDC is `token0`: the USDC
`transfer` `CALL` at the swap's prefix world (`usdcTransferCall`), at the call gas the crossing
itself fixes.  As for `swapWethLeg0`, what the Pair needs after the `CALL` (the second transfer
site's charge, the callback branch's gas and `_safeTransfer`'s post-call charge) reads the `CALL`'s
result only off its gas-free columns, so it is computed on the gas-free skeleton `usdcLeg0Skel`.
The pins are one-directional: WETH9's leg reads `usdcLeg0Skel`, and this leg reads WETH9's leg
only through its skeleton (`usdcLeg1Skel`) and its call gas `cg1`.
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair Blanc.Lift.Usdc
  Blanc.Composition.UniswapV2PairWeth9Joint Blanc.Composition.UsdcLive Blanc.Composition.UsdcToken

section Leg0

variable (sevm : Sevm) (b : Devm) (st : UniswapV2Pair.State) (cg1 cgC Gc : Nat)

/-- The gas-free skeleton of the USDC `transfer` CALL's result at the swap front (proxy →
implementation `transfer` of `swapAmount0Out` to the recipient). -/
noncomputable def usdcLeg0Skel : Devm :=
  usdcTransferSkel sevm (swapPrefixWorld sevm b) (swapLocalsStack sevm st) getterInitMemory 128
    (swapAmount0Out sevm) (swapRecipientWord sevm) st.token0.toB256 0x8d0

/-- The gas-free skeleton of WETH9's `transfer` CALL after USDC's. -/
noncomputable abbrev usdcLeg1Skel : Devm := leg1Skel sevm b st (usdcLeg0Skel sevm b st)

/-- What the Pair needs left after the USDC `transfer` CALL, read on the skeletons. -/
noncomputable def usdcLeg0Need : Nat :=
  leg0Next sevm b (usdcLeg1Skel sevm b st) cg1 cgC Gc (usdcLeg0Skel sevm b st) +
    safeTransferPostCharge getterInitMemory.size 128 (usdcLeg0Skel sevm b st).returnData

/-- USDC's exact charge for the leg's child frame. -/
noncomputable def usdcLeg0Used : Nat :=
  usdcUsed sevm (swapPrefixWorld sevm b) (swapLocalsStack sevm st) getterInitMemory 128
    (swapAmount0Out sevm) (swapRecipientWord sevm) st.token0.toB256 0x8d0

/-- The gas USDC's child frame needs forwarded. -/
noncomputable def usdcLeg0Budget : Nat :=
  usdcBudget sevm (swapPrefixWorld sevm b) (swapLocalsStack sevm st) getterInitMemory 128
    (swapAmount0Out sevm) (swapRecipientWord sevm) st.token0.toB256 0x8d0

/-- The `CALL`'s own charges: the token's access, the windows' expansion, USDC's `transfer`. -/
noncomputable def usdcLeg0Charge : Nat :=
  xferAcc (swapPrefixWorld sevm b) st.token0.toB256 +
    xferExt (swapPrefixWorld sevm b) (swapLocalsStack sevm st) getterInitMemory 128
      (swapAmount0Out sevm) (swapRecipientWord sevm) st.token0.toB256 0x8d0 +
    usdcLeg0Used sevm b st

end Leg0

/-- **The USDC `transfer` leg of the swap front half (token0 = USDC)**: the `CALL` result and the
call gas USDC's code determines, given the gas the Pair needs after it (WETH9's leg gas `cg1`, the
callback's `cgC`, the callee's `Gc`). -/
noncomputable def swapUsdcLeg0 (sevm : Sevm) (b : Devm) (st : UniswapV2Pair.State)
    (cg1 cgC Gc : Nat) : Devm × Nat :=
  (usdcTransferCall sevm (swapPrefixWorld sevm b) (swapLocalsStack sevm st) getterInitMemory 128
      (swapAmount0Out sevm) (swapRecipientWord sevm) st.token0.toB256 0x8d0
      (usdcLeg0Need sevm b st cg1 cgC Gc + usdcLeg0Charge sevm b st),
    usdcLeg0Need sevm b st cg1 cgC Gc + usdcLeg0Charge sevm b st)

theorem swapRecipientWord_toAdr (sevm : Sevm) : (swapRecipientWord sevm).toAdr = swapRecipient sevm := by
  unfold swapRecipientWord swapRecipient
  rw [B256.and_comm, mask_toAdr]

/-- **The USDC `transfer` leg's spec, token0 = USDC (frame level).**  At the swap's prefix world,
for any outputs: USDC installed at token0 with its footprint invariant, token0 not a precompile, two
levels of call depth left, the Pair and the recipient tracked, the Pair not USDC's admin, the
transfer's ledger conditions and the Pair's USDC balance covering `amount0Out`, the leg's call gas
a word, and the child's budget under the 63/64 rule.  Then `swapUsdcLeg0` is the transfer record
the front half asks for, at the residual its continuation fixes with WETH9's leg result `d1`. -/
theorem swapUsdcLeg0_spec {sevm : Sevm} {b : Devm} {st : UniswapV2Pair.State} {cg1 cgC Gc : Nat}
    {U : Usdc.Key → Prop}
    (fork : CoveredFork sevm.benvStat.fork) (nonstatic : sevm.isStatic = false)
    (depth : 2 ≤ sevm.depth)
    (inst : UsdcInstalled st.token0 (swapPrefixWorld sevm b).state)
    (finv : FootInv U ((swapPrefixWorld sevm b).state.getStor st.token0))
    (notPrecompile : sevm.benvStat.rules.isPrecomp st.token0 = false)
    (kPair : U (.bal sevm.currentTarget)) (kTo : U (.bal (swapRecipient sevm)))
    (notAdmin : sevm.currentTarget ≠ adminOf (swapPrefixWorld sevm b).state st.token0)
    (ok : UsdcTransferOk (ledger U ((swapPrefixWorld sevm b).state.getStor st.token0))
      sevm.currentTarget (swapRecipient sevm) (swapAmount0Out sevm).toNat)
    (balance : (swapAmount0Out sevm).toNat ≤
      (ledger U ((swapPrefixWorld sevm b).state.getStor st.token0)).bal sevm.currentTarget)
    (fits : (swapUsdcLeg0 sevm b st cg1 cgC Gc).2 < 2 ^ 256)
    (room : usdcLeg0Budget sevm b st ≤
      except64th (usdcLeg0Need sevm b st cg1 cgC Gc + usdcLeg0Used sevm b st)) :
    SwapTransferCallForward sevm (swapPrefixWorld sevm b)
      (swapLocalsStack sevm st) getterInitMemory getterInitMemory.size 128 (swapAmount0Out sevm)
      (swapRecipientWord sevm) st.token0.toB256 0x8d0 (swapUsdcLeg0 sevm b st cg1 cgC Gc).2
      (swapOptGas (swapOptMem getterInitMemory 128 (swapAmount0Out sevm) (swapRecipientWord sevm)
          (swapUsdcLeg0 sevm b st cg1 cgC Gc).1)
        (swapOptPtr 128 (swapAmount0Out sevm) (swapUsdcLeg0 sevm b st cg1 cgC Gc).1)
        (swapAmount1Out sevm) cg1
        (swapFrontCallbackGas sevm b (swapUsdcLeg0 sevm b st cg1 cgC Gc).1
          (swapWethLeg1 sevm b st (usdcLeg0Skel sevm b st) cgC Gc).1 cgC Gc))
      (swapUsdcLeg0 sevm b st cg1 cgC Gc).1 := by
  rw [← tokenMask_toAdr st.token0] at inst finv notPrecompile notAdmin ok balance
  rw [← swapRecipientWord_toAdr] at kTo ok
  have spec := usdcTransferCall_spec (sevm := sevm) (W := swapPrefixWorld sevm b)
    (L := swapLocalsStack sevm st) (M := getterInitMemory) (p := 128)
    (amount := swapAmount0Out sevm) (toWord := swapRecipientWord sevm) (token := st.token0.toB256)
    (rho := 0x8d0) (cg := usdcLeg0Need sevm b st cg1 cgC Gc + usdcLeg0Charge sevm b st) (U := U)
    fork inst finv nonstatic depth notPrecompile
    (by simp only [swapLocalsStack, swapBodyStack, List.length_cons, List.length_nil]; omega)
    getterInitMemory_ptr.wf (by decide) (by decide) kPair kTo notAdmin ok balance fits
    (by unfold usdcLeg0Charge; omega)
    (by
      have e : usdcLeg0Need sevm b st cg1 cgC Gc + usdcLeg0Charge sevm b st -
          xferExt (swapPrefixWorld sevm b) (swapLocalsStack sevm st) getterInitMemory 128
            (swapAmount0Out sevm) (swapRecipientWord sevm) st.token0.toB256 0x8d0 -
          xferAcc (swapPrefixWorld sevm b) st.token0.toB256 =
          usdcLeg0Need sevm b st cg1 cgC Gc + usdcLeg0Used sevm b st := by
        unfold usdcLeg0Charge; omega
      rw [e]
      exact room)
  obtain ⟨hrun, hstk, hret, hgas⟩ := spec
  have hskel : usdcTransferCall sevm (swapPrefixWorld sevm b) (swapLocalsStack sevm st)
      getterInitMemory 128 (swapAmount0Out sevm) (swapRecipientWord sevm) st.token0.toB256 0x8d0
      (usdcLeg0Need sevm b st cg1 cgC Gc + usdcLeg0Charge sevm b st) =
      (usdcLeg0Skel sevm b st).withGasLeft _ :=
    usdcTransferCallAt_eq _ _ _ _ _ _ _ _ _ _ _ _ _
  have h1 : (swapWethLeg1 sevm b st (usdcLeg0Skel sevm b st) cgC Gc).1 =
      (usdcLeg1Skel sevm b st).withGasLeft _ :=
    wethTransferCallAt_eq _ _ _ _ _ _ _ _ _ _ _ _ _
  have hret' : (swapUsdcLeg0 sevm b st cg1 cgC Gc).1.returnData = B256.toBytes 1 := hret
  refine ⟨hrun, hstk, Or.inr (by rw [hret']; exact one_reply_accepted), ?_⟩
  rw [h1, swapFrontCallbackGas_withGasLeft]
  change (usdcTransferCall sevm (swapPrefixWorld sevm b) (swapLocalsStack sevm st) getterInitMemory
      128 (swapAmount0Out sevm) (swapRecipientWord sevm) st.token0.toB256 0x8d0
      (usdcLeg0Need sevm b st cg1 cgC Gc + usdcLeg0Charge sevm b st)).gasLeft =
    leg0Next sevm b (usdcLeg1Skel sevm b st) cg1 cgC Gc (usdcTransferCall sevm
      (swapPrefixWorld sevm b) (swapLocalsStack sevm st) getterInitMemory 128 (swapAmount0Out sevm)
      (swapRecipientWord sevm) st.token0.toB256 0x8d0
      (usdcLeg0Need sevm b st cg1 cgC Gc + usdcLeg0Charge sevm b st)) +
    safeTransferPostCharge getterInitMemory.size 128
      (usdcTransferCall sevm (swapPrefixWorld sevm b) (swapLocalsStack sevm st) getterInitMemory
        128 (swapAmount0Out sevm) (swapRecipientWord sevm) st.token0.toB256 0x8d0
        (usdcLeg0Need sevm b st cg1 cgC Gc + usdcLeg0Charge sevm b st)).returnData
  rw [hgas]
  conv => rhs; rw [hskel, leg0Next_withGasLeft, withGasLeft_returnData]
  have hn : usdcLeg0Need sevm b st cg1 cgC Gc =
      leg0Next sevm b (usdcLeg1Skel sevm b st) cg1 cgC Gc (usdcLeg0Skel sevm b st) +
      safeTransferPostCharge getterInitMemory.size 128 (usdcLeg0Skel sevm b st).returnData := rfl
  rw [← hn]
  unfold usdcLeg0Charge usdcLeg0Used
  omega

end Blanc.Composition.UniswapV2PairUsdcWeth9
