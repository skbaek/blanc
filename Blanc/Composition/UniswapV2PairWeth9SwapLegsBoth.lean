import Blanc.Composition.UniswapV2PairWeth9SwapLegs
import Blanc.Composition.UniswapV2PairWeth9XLegCall

/-!
# The swap's WETH9 transfer leg when both outputs are paid (WETH9 = token1)

With `amount0Out ≠ 0` the Pair first pays the other token `X = token0` (the record
`SwapFrontForwardEnv.transfer0`, an arbitrary callee record with result `d0`), then WETH9 at the world
`d0`.  `swapWethLeg1_spec_both` is `swapWethLeg1_spec` at that world (premises read at `d0`);
`swapWethLeg1_spec_afterX` discharges its WETH9 premises at `d0` from the prefix world through the
X-leg quiescence `xleg_call`: WETH9's code persists and the Pair's WETH9 balance slot does not drop
across X's transfer child.  Its premises are world facts at the swap's prefix world, the two tokens
distinct, and HASH-T over the keys X's child touches; none mentions WETH9's answers.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair
open Blanc.Composition.UniswapV2PairWeth9XLeg (xleg_call CallChildFresh wethRunKeys pairRunKeys)

/-- **The WETH9 `transfer` leg's spec after the other token's transfer (frame level).**  As
`swapWethLeg1_spec`, with both outputs nonzero: the WETH9 premises are read at the world `d0` the
token0 transfer left, and the staged memory and free pointer are the ones after that transfer. -/
theorem swapWethLeg1_spec_both {sevm : Sevm} {b : Devm} {st : UniswapV2Pair.State} {d0 : Devm}
    {cgC Gc : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (nonstatic : sevm.isStatic = false)
    (depth : sevm.depth ≠ 0) (both : swapAmount0Out sevm ≠ 0)
    (wethCode : d0.state.getCode st.token1 = Weth9.code)
    (notPrecompile : sevm.benvStat.rules.isPrecomp st.token1 = false)
    (wf : Mem.Wf (leg1Mem sevm d0)) (lower : 128 ≤ (leg1Ptr sevm d0).toNat)
    (width : (leg1Ptr sevm d0).toNat + 164 < 2 ^ 256)
    (balance : swapAmount1Out sevm ≤ d0.getStorVal st.token1 (Weth9.balSlot sevm.currentTarget))
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
  have hW : leg1World sevm b d0 = d0 := by
    unfold leg1World swapOptWorld
    rw [ite_eq_right both]
  have spec := wethTransferCall_spec (sevm := sevm) (W := leg1World sevm b d0)
    (L := swapLocalsStack sevm st) (M := leg1Mem sevm d0) (p := leg1Ptr sevm d0)
    (amount := swapAmount1Out sevm) (toWord := swapRecipientWord sevm) (token := st.token1.toB256)
    (rho := 0x8e1) (cg := leg1Need sevm b st d0 cgC Gc + leg1Charge sevm b st d0) fork
    (by rw [tokenMask_toAdr, hW]; exact wethCode) nonstatic depth
    (by rw [tokenMask_toAdr]; exact notPrecompile)
    (by simp only [swapLocalsStack, swapBodyStack, List.length_cons, List.length_nil]; omega)
    wf lower width
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

/-- The staged state of the swap's token0 `transfer` CALL, verbatim the record's `call` state. -/
def leg0CallState (sevm : Sevm) (b : Devm) (st : UniswapV2Pair.State) (cg0 : Nat) : Devm :=
  St (swapPrefixWorld sevm b) (cg0.toB256 ::
      (st.token0.toB256 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      0 :: (128 + 164) :: 68 :: (128 + 164) :: 0 :: (68 + (128 + 164)) ::
      (st.token0.toB256 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      96 :: 0 :: swapAmount0Out sevm :: swapRecipientWord sevm :: st.token0.toB256 :: 0x8d0 ::
      swapLocalsStack sevm st)
    (safeTransfer_dynamicCallMemory getterInitMemory 128 (swapAmount0Out sevm) (swapRecipientWord sevm))
    cg0

/-- **The WETH9 `transfer` leg after the other token's transfer, from the prefix world.**  Given the
token0 transfer record (`SwapFrontForwardEnv.transfer0`'s shape) with result `d0`, the facts at the
swap's prefix world (WETH9's code and footprint over `U` with the Pair tracked, the Pair's WETH9
allowances zero, the Pair runtime with a locked model state, the factory runtime at that state's
factory, `pair ≠ 0`, the ether supply a word, the Pair's WETH9 balance covering `amount1Out`), the two
tokens distinct and the Pair not WETH9, and HASH-T over the keys the token0 child touches (WETH9 frame
keys, Pair writer rows): `swapWethLeg1` is the record `SwapFrontForwardEnv.transfer1` asks for. -/
theorem swapWethLeg1_spec_afterX {sevm : Sevm} {b : Devm} {st : UniswapV2Pair.State} {d0 : Devm}
    {cgC Gc cg0 G0 : Nat} {U : Weth9.Key → Prop} {K : WriterKey → Prop} {stL : UniswapV2Pair.State}
    (fork : CoveredFork sevm.benvStat.fork) (nonstatic : sevm.isStatic = false)
    (depth : sevm.depth ≠ 0) (both : swapAmount0Out sevm ≠ 0)
    (env0 : SwapTransferCallForward sevm (swapPrefixWorld sevm b) (swapLocalsStack sevm st)
      getterInitMemory getterInitMemory.size 128 (swapAmount0Out sevm) (swapRecipientWord sevm)
      st.token0.toB256 0x8d0 cg0 G0 d0)
    (distinct : st.token0 ≠ st.token1) (apart : sevm.currentTarget ≠ st.token1)
    (wethCode : (swapPrefixWorld sevm b).state.getCode st.token1 = Weth9.code)
    (foot : Weth9.FootInv U ((swapPrefixWorld sevm b).state.getStor st.token1)
      ((swapPrefixWorld sevm b).state.bal st.token1))
    (tracked : U (.bal sevm.currentTarget))
    (zero : ∀ g, Weth9Token.weth9Book.allow
      (Weth9.ledger U ((swapPrefixWorld sevm b).state.getStor st.token1)) sevm.currentTarget g = 0)
    (pairCode : (swapPrefixWorld sevm b).state.getCode sevm.currentTarget = UniswapV2Pair.code)
    (rep : WriterRep K ((swapPrefixWorld sevm b).state.getStor sevm.currentTarget) stL)
    (locked : stL.unlocked ≠ 1)
    (factoryCode : (swapPrefixWorld sevm b).state.getCode stL.factory = UniswapV2Factory.code)
    (pairNonzero : sevm.currentTarget ≠ 0)
    (bound : sum (swapPrefixWorld sevm b).state.bal < 2 ^ 256)
    (balance : swapAmount1Out sevm ≤
      (swapPrefixWorld sevm b).getStorVal st.token1 (Weth9.balSlot sevm.currentTarget))
    (wethFresh : CallChildFresh sevm (leg0CallState sevm b st cg0)
      fun D => Weth9.KeysFresh U (wethRunKeys st.token1 D))
    (pairFresh : CallChildFresh sevm (leg0CallState sevm b st cg0)
      fun D => WriterFreshKeys K (pairRunKeys sevm.currentTarget D))
    (notPrecompile : sevm.benvStat.rules.isPrecomp st.token1 = false)
    (wf : Mem.Wf (leg1Mem sevm d0)) (lower : 128 ≤ (leg1Ptr sevm d0).toNat)
    (width : (leg1Ptr sevm d0).toNat + 164 < 2 ^ 256)
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
  have run0 : Ninst.RunCompiled sevm (leg0CallState sevm b st cg0) (.exec .call) d0 := env0.call
  have callee : ∀ g c v ii is oi os rest, (leg0CallState sevm b st cg0).stack =
      g :: c :: v :: ii :: is :: oi :: os :: rest → c.toAdr ≠ st.token1 := by
    intro g c v ii is oi os rest h
    have hc : c = st.token0.toB256 &&& 0xffffffffffffffffffffffffffffffffffffffff := by
      simp only [leg0CallState, St.stack, List.cons.injEq] at h
      exact h.2.1.symm
    rw [hc]
    have masked : (st.token0.toB256 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr =
        st.token0 := tokenMask_toAdr st.token0
    rw [masked]
    exact distinct
  have hstate : (leg0CallState sevm b st cg0).state = (swapPrefixWorld sevm b).state := by
    rw [leg0CallState, St, Devm.setMach_state]
  have wethCode' : (leg0CallState sevm b st cg0).getCode st.token1 = Weth9.code := by
    rw [leg0CallState, St, Devm.getCode_setMach]
    exact wethCode
  have pairCode' : (leg0CallState sevm b st cg0).getCode sevm.currentTarget = UniswapV2Pair.code := by
    rw [leg0CallState, St, Devm.getCode_setMach]
    exact pairCode
  have factoryCode' : (leg0CallState sevm b st cg0).getCode stL.factory = UniswapV2Factory.code := by
    rw [leg0CallState, St, Devm.getCode_setMach]
    exact factoryCode
  rw [← hstate] at foot zero rep bound
  obtain ⟨U', sub, codeD0, -, -, balLe, -⟩ := xleg_call (ca := st.token1)
    (pair := sevm.currentTarget) run0 fork rfl callee apart wethCode' foot zero pairCode' rep locked
    factoryCode' pairNonzero bound wethFresh pairFresh
  apply swapWethLeg1_spec_both fork nonstatic depth both codeD0 notPrecompile wf lower width _ fits
    room
  have h1 : Weth9Token.weth9Book.bal
      (Weth9.ledger U ((leg0CallState sevm b st cg0).state.getStor st.token1)) sevm.currentTarget =
      ((swapPrefixWorld sevm b).getStorVal st.token1 (Weth9.balSlot sevm.currentTarget)).toNat := by
    rw [hstate]
    show (Weth9.tracked U _ sevm.currentTarget).toNat = _
    rw [Weth9.tracked_self tracked]
    rfl
  have h2 : Weth9Token.weth9Book.bal (Weth9.ledger U' (d0.state.getStor st.token1))
      sevm.currentTarget = (d0.getStorVal st.token1 (Weth9.balSlot sevm.currentTarget)).toNat := by
    show (Weth9.tracked U' _ sevm.currentTarget).toNat = _
    rw [Weth9.tracked_self (sub _ tracked)]
    rfl
  rw [h1, h2] at balLe
  exact B256.le_iff_toNat_le_toNat.mpr (Nat.le_trans (B256.le_iff_toNat_le_toNat.mp balance) balLe)

end Blanc.Composition.UniswapV2PairWeth9Joint
