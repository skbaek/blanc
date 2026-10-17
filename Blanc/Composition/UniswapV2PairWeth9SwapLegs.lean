import Blanc.Composition.UniswapV2PairWeth9SwapLegsCall
import Blanc.AddressSlotProofs

/-!
# The swap's WETH9 legs (C4(b), WETH9 = token1): definitions and frame-level specs

`swapWethLeg1` and `swapWethRead1` (design Appendix A §9) are the WETH9 `transfer` CALL and the
post-callback WETH9 `balanceOf` STATICCALL of the Pair's swap, as WETH9's deployed code determines
them: each is the resumed parent of the actual crossing (`wethTransferCall`, …) at the call gas the
crossing itself fixes.

The call gas is a fixed point.  The record ties the CALL's residual gas to what the Pair's next
segment needs, and that need reads the CALL's result (the recipient's warmth, the reply); the CALL's
residual gas is the call gas less the access charge, the window's expansion and WETH9's own charge.
The result's gas-free columns do not depend on the call gas (`wethTransferCallAt_eq`), so the need
is computed on the gas-free skeleton and the call gas is that need plus the charges.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair

/-! ## The transfer leg -/

section Leg1

variable (sevm : Sevm) (b : Devm) (st : UniswapV2Pair.State) (d0 : Devm) (cgC Gc : Nat)

/-- The world at the WETH9 `transfer` site. -/
def leg1World : Devm := swapOptWorld (swapAmount0Out sevm) (swapPrefixWorld sevm b) d0

/-- The memory at the WETH9 `transfer` site. -/
def leg1Mem : Mem :=
  swapOptMem getterInitMemory 128 (swapAmount0Out sevm) (swapRecipientWord sevm) d0

/-- The free pointer at the WETH9 `transfer` site. -/
def leg1Ptr : B256 := swapOptPtr 128 (swapAmount0Out sevm) d0

/-- The gas-free skeleton of the WETH9 `transfer` CALL's result. -/
def leg1Skel : Devm :=
  wethTransferSkel sevm (leg1World sevm b d0) (swapLocalsStack sevm st) (leg1Mem sevm d0)
    (leg1Ptr sevm d0) (swapAmount1Out sevm) (swapRecipientWord sevm) st.token1.toB256 0x8e1

/-- What the Pair needs left after the WETH9 `transfer` CALL: the callback branch's gas and
`_safeTransfer`'s post-call charge, both read on the skeleton. -/
def leg1Need : Nat :=
  swapFrontCallbackGas sevm b d0 (leg1Skel sevm b st d0) cgC Gc +
    safeTransferPostCharge (leg1Mem sevm d0).size (leg1Ptr sevm d0) (leg1Skel sevm b st d0).returnData

/-- The `CALL`'s own charges: the token's access, the windows' expansion, WETH9's `transfer`. -/
def leg1Charge : Nat :=
  xferAcc (leg1World sevm b d0) st.token1.toB256 +
    xferExt (leg1World sevm b d0) (swapLocalsStack sevm st) (leg1Mem sevm d0) (leg1Ptr sevm d0)
      (swapAmount1Out sevm) (swapRecipientWord sevm) st.token1.toB256 0x8e1 +
    xferUsed sevm (leg1World sevm b d0) (swapLocalsStack sevm st) (leg1Mem sevm d0)
      (leg1Ptr sevm d0) (swapAmount1Out sevm) (swapRecipientWord sevm) st.token1.toB256 0x8e1

end Leg1

/-- The WETH9 `transfer` leg of the swap front half (token1 = WETH9): the `CALL` result and the
`CALL` state's gas that WETH9's deployed code determines.  Supplied by the C4(b) unit (world part
from `weth9_transfer_effect`, gas from `weth9_transfer_runExact`); no premise fixes it. -/
noncomputable def swapWethLeg1 (sevm : Sevm) (b : Devm) (st : UniswapV2Pair.State) (d0 : Devm)
    (cgC Gc : Nat) : Devm × Nat :=
  (wethTransferCall sevm (leg1World sevm b d0) (swapLocalsStack sevm st) (leg1Mem sevm d0)
      (leg1Ptr sevm d0) (swapAmount1Out sevm) (swapRecipientWord sevm) st.token1.toB256 0x8e1
      (leg1Need sevm b st d0 cgC Gc + leg1Charge sevm b st d0),
    leg1Need sevm b st d0 cgC Gc + leg1Charge sevm b st d0)

/-- WETH9's charge for the leg's child frame. -/
def leg1Used (sevm : Sevm) (b : Devm) (st : UniswapV2Pair.State) (d0 : Devm) : Nat :=
  xferUsed sevm (leg1World sevm b d0) (swapLocalsStack sevm st) (leg1Mem sevm d0)
    (leg1Ptr sevm d0) (swapAmount1Out sevm) (swapRecipientWord sevm) st.token1.toB256 0x8e1

section Leg1Facts

theorem withGasLeft_accessedAddresses (d : Devm) (x : Nat) :
    (d.withGasLeft x).accessedAddresses = d.accessedAddresses := rfl

theorem withGasLeft_returnData (d : Devm) (x : Nat) :
    (d.withGasLeft x).returnData = d.returnData := rfl

/-- The callback branch's gas reads the transfer's result only off the gas column. -/
theorem swapFrontCallbackGas_withGasLeft (sevm : Sevm) (b d0 d : Devm) (cgC Gc x : Nat) :
    swapFrontCallbackGas sevm b d0 (d.withGasLeft x) cgC Gc = swapFrontCallbackGas sevm b d0 d cgC Gc := by
  unfold swapFrontCallbackGas swapFrontTransferWorld swapFrontTransferMem swapFrontPtr swapOptWorld
    swapOptMem swapOptPtr swapCallbackGas temporalAccountAccessCost
  by_cases h : swapAmount1Out sevm = 0
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, withGasLeft_accessedAddresses, withGasLeft_returnData]

theorem tokenMask_toAdr (a : Adr) : (tokenMask a.toB256).toAdr = a := by
  unfold tokenMask
  rw [show (0xffffffffffffffffffffffffffffffffffffffff : B256) = ~~~ addressMask by decide,
    and_mask_word, toAdr_toB256, toAdr_toB256]

theorem one_reply_accepted :
    (32 ≤ (B256.toBytes 1).length ∧ Bytes.toB256 ((B256.toBytes 1).sliceD 0 32 0) ≠ 0) := by
  decide

end Leg1Facts

/-- **The WETH9 `transfer` leg's spec (frame level).**  At the swap's prefix world, with only
WETH9 (token1) paid out: WETH9's code at token1, token1 not a precompile, call depth left, the
Pair's WETH9 balance covering `amount1Out`, the leg's call gas a word, and room for WETH9's
`transfer` under the 63/64 rule with its `SSTORE` sentry.  Then `swapWethLeg1` is the transfer
record `SwapFrontForwardEnv.transfer1` asks for, at the callback branch's gas. -/
theorem swapWethLeg1_spec {sevm : Sevm} {b : Devm} {st : UniswapV2Pair.State} {d0 : Devm}
    {cgC Gc : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (nonstatic : sevm.isStatic = false)
    (depth : sevm.depth ≠ 0) (onlyWeth : swapAmount0Out sevm = 0)
    (wethCode : (swapPrefixWorld sevm b).state.getCode st.token1 = Weth9.code)
    (notPrecompile : sevm.benvStat.rules.isPrecomp st.token1 = false)
    (balance : swapAmount1Out sevm ≤
      (swapPrefixWorld sevm b).getStorVal st.token1 (Weth9.balSlot sevm.currentTarget))
    (fits : (swapWethLeg1 sevm b st d0 cgC Gc).2 < 2 ^ 256)
    (room : leg1Used sevm b st d0 + gCallStipend ≤
      except64th (leg1Need sevm b st d0 cgC Gc + leg1Used sevm b st d0)) :
    SwapTransferCallForward sevm (swapOptWorld (swapAmount0Out sevm) (swapPrefixWorld sevm b) d0)
      (swapLocalsStack sevm st)
      (swapOptMem getterInitMemory 128 (swapAmount0Out sevm) (swapRecipientWord sevm) d0)
      (swapOptMem getterInitMemory 128 (swapAmount0Out sevm) (swapRecipientWord sevm) d0).size
      (swapOptPtr 128 (swapAmount0Out sevm) d0) (swapAmount1Out sevm) (swapRecipientWord sevm)
      st.token1.toB256 0x8e1 (swapWethLeg1 sevm b st d0 cgC Gc).2
      (swapFrontCallbackGas sevm b d0 (swapWethLeg1 sevm b st d0 cgC Gc).1 cgC Gc)
      (swapWethLeg1 sevm b st d0 cgC Gc).1 := by
  show SwapTransferCallForward sevm (leg1World sevm b d0) (swapLocalsStack sevm st) (leg1Mem sevm d0)
    (leg1Mem sevm d0).size (leg1Ptr sevm d0) (swapAmount1Out sevm) (swapRecipientWord sevm)
    st.token1.toB256 0x8e1 (swapWethLeg1 sevm b st d0 cgC Gc).2
    (swapFrontCallbackGas sevm b d0 (swapWethLeg1 sevm b st d0 cgC Gc).1 cgC Gc)
    (swapWethLeg1 sevm b st d0 cgC Gc).1
  have hW : leg1World sevm b d0 = swapPrefixWorld sevm b := by
    unfold leg1World swapOptWorld
    rw [ite_eq_left onlyWeth]
  have hM : leg1Mem sevm d0 = getterInitMemory := by
    unfold leg1Mem swapOptMem
    rw [ite_eq_left onlyWeth]
  have hp : leg1Ptr sevm d0 = 128 := by
    unfold leg1Ptr swapOptPtr
    rw [ite_eq_left onlyWeth]
  have spec := wethTransferCall_spec (sevm := sevm) (W := leg1World sevm b d0)
    (L := swapLocalsStack sevm st) (M := leg1Mem sevm d0) (p := leg1Ptr sevm d0)
    (amount := swapAmount1Out sevm) (toWord := swapRecipientWord sevm) (token := st.token1.toB256)
    (rho := 0x8e1) (cg := leg1Need sevm b st d0 cgC Gc + leg1Charge sevm b st d0) fork
    (by rw [tokenMask_toAdr, hW]; exact wethCode) nonstatic depth
    (by rw [tokenMask_toAdr]; exact notPrecompile)
    (by simp only [swapLocalsStack, swapBodyStack, List.length_cons, List.length_nil]; omega)
    (by rw [hM]; exact getterInitMemory_ptr.wf) (by rw [hp]; decide) (by rw [hp]; decide)
    (by rw [tokenMask_toAdr, hW]; exact balance) fits
    (by unfold leg1Charge; omega)
    (by
      have e : leg1Need sevm b st d0 cgC Gc + leg1Charge sevm b st d0 -
          xferExt (leg1World sevm b d0) (swapLocalsStack sevm st) (leg1Mem sevm d0) (leg1Ptr sevm d0)
            (swapAmount1Out sevm) (swapRecipientWord sevm) st.token1.toB256 0x8e1 -
          xferAcc (leg1World sevm b d0) st.token1.toB256 =
          leg1Need sevm b st d0 cgC Gc + leg1Used sevm b st d0 := by
        unfold leg1Charge leg1Used; omega
      rw [e]
      exact room)
  obtain ⟨hrun, hstk, hret, hgas⟩ := spec
  have hskel : wethTransferCall sevm (leg1World sevm b d0) (swapLocalsStack sevm st)
      (leg1Mem sevm d0) (leg1Ptr sevm d0) (swapAmount1Out sevm) (swapRecipientWord sevm)
      st.token1.toB256 0x8e1 (leg1Need sevm b st d0 cgC Gc + leg1Charge sevm b st d0) =
      (leg1Skel sevm b st d0).withGasLeft _ :=
    wethTransferCallAt_eq _ _ _ _ _ _ _ _ _ _ _ _ _
  have hret' : (swapWethLeg1 sevm b st d0 cgC Gc).1.returnData = B256.toBytes 1 := hret
  refine ⟨hrun, hstk, Or.inr (by rw [hret']; exact one_reply_accepted), ?_⟩
  change (wethTransferCall sevm (leg1World sevm b d0) (swapLocalsStack sevm st) (leg1Mem sevm d0)
      (leg1Ptr sevm d0) (swapAmount1Out sevm) (swapRecipientWord sevm) st.token1.toB256 0x8e1
      (leg1Need sevm b st d0 cgC Gc + leg1Charge sevm b st d0)).gasLeft =
    swapFrontCallbackGas sevm b d0 (wethTransferCall sevm (leg1World sevm b d0)
      (swapLocalsStack sevm st) (leg1Mem sevm d0) (leg1Ptr sevm d0) (swapAmount1Out sevm)
      (swapRecipientWord sevm) st.token1.toB256 0x8e1
      (leg1Need sevm b st d0 cgC Gc + leg1Charge sevm b st d0)) cgC Gc +
    safeTransferPostCharge (leg1Mem sevm d0).size (leg1Ptr sevm d0)
      (wethTransferCall sevm (leg1World sevm b d0) (swapLocalsStack sevm st) (leg1Mem sevm d0)
        (leg1Ptr sevm d0) (swapAmount1Out sevm) (swapRecipientWord sevm) st.token1.toB256 0x8e1
        (leg1Need sevm b st d0 cgC Gc + leg1Charge sevm b st d0)).returnData
  rw [hgas]
  conv => rhs; rw [hskel, swapFrontCallbackGas_withGasLeft, withGasLeft_returnData]
  have hn : leg1Need sevm b st d0 cgC Gc = swapFrontCallbackGas sevm b d0 (leg1Skel sevm b st d0) cgC Gc +
      safeTransferPostCharge (leg1Mem sevm d0).size (leg1Ptr sevm d0)
        (leg1Skel sevm b st d0).returnData := rfl
  rw [← hn]
  unfold leg1Charge
  omega

end Blanc.Composition.UniswapV2PairWeth9Joint
