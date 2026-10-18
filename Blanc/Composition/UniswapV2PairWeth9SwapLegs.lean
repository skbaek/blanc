import Blanc.Composition.UniswapV2PairWeth9SwapLegsRead
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

/-! ## The read leg -/

section Read

variable (sevm : Sevm) (M : Mem) (n : Nat) (p : B256) (w : SwapCutWords) (ρ : B256) (R : List B256)
  (G : Nat) (d0 : Devm)

/-- The memory the WETH9 query is staged over (the first query's reply written in). -/
def readMem : Mem := swapBalanceReply M p sevm.currentTarget d0.returnData

/-- The words under the WETH9 query's operands. -/
def readStack : List B256 :=
  w.token1 :: w.token0 :: 0 :: swapBalanceWord d0.returnData :: swapCutTail w ρ R

/-- The gas-free skeleton of the WETH9 `balanceOf` STATICCALL's result. -/
def readSkel : Devm :=
  wethBalanceSkel sevm d0 (readStack w ρ R d0) (readMem sevm M p d0) p w.token1

/-- What the Pair needs left after the WETH9 query (the record's `tailGas + 64`), read on the
skeleton. -/
def readNeed : Nat :=
  swapBackPostGas sevm (readSkel sevm M p w ρ R d0) (swapRequestSize (swapRequestSize n p) p) p w
    (swapBalanceWord d0.returnData) (swapBalanceWord (readSkel sevm M p w ρ R d0).returnData) G + 64

/-- WETH9's charge for the query's child frame. -/
def readUsed : Nat := balUsed sevm d0 (readStack w ρ R d0) (readMem sevm M p d0) p w.token1

/-- The query's own charges: the token's (warm) access, the windows' expansion, WETH9's view. -/
def readCharge : Nat :=
  balAcc d0 w.token1 + balExt sevm d0 (readStack w ρ R d0) (readMem sevm M p d0) p w.token1 +
    readUsed sevm M p w ρ R d0

end Read

set_option linter.unusedVariables false in
/-- The WETH9 post-callback `balanceOf(pair)` `STATICCALL` (token1 = WETH9): its result and the call
gas WETH9's code determines.  (`d`, the join world, is part of the frozen signature; the query
is staged over the first query's result `d0`.) -/
noncomputable def swapWethRead1 (sevm : Sevm) (d : Devm) (M : Mem) (n : Nat) (p : B256)
    (w : SwapCutWords) (ρ : B256) (R : List B256) (G : Nat) (d0 : Devm) : Devm × Nat :=
  (wethBalanceCall sevm d0 (readStack w ρ R d0) (readMem sevm M p d0) p w.token1
      (readNeed sevm M n p w ρ R G d0 + readCharge sevm M p w ρ R d0),
    readNeed sevm M n p w ρ R G d0 + readCharge sevm M p w ρ R d0)

section ReadFacts

theorem sloadCost_setMach' (sevm : Sevm) (b : Devm) (m : Mach) (k : B256) :
    sloadCost sevm (b.setMach m) k = sloadCost sevm b k := rfl

theorem ite_setMach (c : Prop) [Decidable c] (a b : Devm) (m : Mach) :
    (if c then a.setMach m else b.setMach m) = (if c then a else b).setMach m := by
  split <;> rfl

/-- The Pair's post-query charges read the query's result only off the gas column. -/
theorem swapBackPostGas_withGasLeft (sevm : Sevm) (d : Devm) (x n2 : Nat) (p : B256)
    (w : SwapCutWords) (bal0 bal1 : B256) (G : Nat) :
    swapBackPostGas sevm (d.withGasLeft x) n2 p w bal0 bal1 G = swapBackPostGas sevm d n2 p w bal0 bal1 G := by
  simp only [swapBackPostGas, swapUnlockCost, swapUpdateCharge, swapLoggedWorld, updateWorld,
    updateSyncPost, updatePackedPost, updateFinalPackedWord, updateOracleWorld, updateOracleActive,
    swapUpdLoad8, swapUpdStore8, swapUpdLoad9, swapUpdStore9, swapUpdLoad10, swapUpdStore10,
    swapUpdAcc0, updateAccumulatorPost, Devm.withGasLeft, afterSload_setMach, afterSstore_setMach,
    addLog_setMach', Devm.getStorVal_setMach, sstoreCost_setMach, sloadCost_setMach', ite_setMach]
  rfl

theorem weth9_code_size_word : Weth9.code.size.toB256 ≠ 0 := by
  intro h
  have hlt : Weth9.code.size < 2 ^ 256 := by decide +kernel
  have := congrArg B256.toNat h
  rw [B256.toNat_toB256_of_lt hlt] at this
  exact Weth9.code_size_ne_zero this

theorem swapBalanceReply_wf {M : Mem} {p : B256} {pair : Adr} {out : Bytes} (wf : Mem.Wf M) :
    Mem.Wf (swapBalanceReply M p pair out) :=
  (Mem.Wf.extends _ ((wf.write _ _).write _ _)).write _ _

end ReadFacts

/-- **The WETH9 `balanceOf` read leg's spec (frame level).**  At the result world `d0` of the first
post-callback query, with WETH9's code at token1, token1 not a precompile, call depth left, the
pointer's width bound and a well-formed memory, the leg's call gas a word, and room for WETH9's view
under the 63/64 rule: `swapWethRead1` is the `SwapBalanceEnv` record the second query asks for.
Code-only: nothing is assumed of the callback subtree. -/
theorem swapWethRead1_spec {sevm : Sevm} {d : Devm} {M : Mem} {n : Nat} {p : B256}
    {w : SwapCutWords} {ρ : B256} {R : List B256} {G : Nat} {d0 : Devm}
    (fork : CoveredFork sevm.benvStat.fork) (depth : sevm.depth ≠ 0)
    (wethCode : d0.state.getCode (swapTokenWord w.token1).toAdr = Weth9.code)
    (notPrecompile : sevm.benvStat.rules.isPrecomp (swapTokenWord w.token1).toAdr = false)
    (wf : Mem.Wf M) (width : p.toNat + 260 < 2 ^ 256)
    (stackRoom : (swapCutTail w ρ R).length < 1014)
    (fits : (swapWethRead1 sevm d M n p w ρ R G d0).2 < 2 ^ 256)
    (room : readUsed sevm M p w ρ R d0 ≤
      except64th (readNeed sevm M n p w ρ R G d0 + readUsed sevm M p w ρ R d0)) :
    SwapBalanceEnv sevm d0 (swapBalanceReply M p sevm.currentTarget d0.returnData) p w.token1
      (w.token1 :: w.token0 :: 0 :: swapBalanceWord d0.returnData :: swapCutTail w ρ R)
      (swapWethRead1 sevm d M n p w ρ R G d0).1 (swapWethRead1 sevm d M n p w ρ R G d0).2
      (swapBackPostGas sevm (swapWethRead1 sevm d M n p w ρ R G d0).1
        (swapRequestSize (swapRequestSize n p) p) p w (swapBalanceWord d0.returnData)
        (swapBalanceWord (swapWethRead1 sevm d M n p w ρ R G d0).1.returnData) G) := by
  have spec := wethBalanceCall_spec (sevm := sevm) (B := d0) (S := readStack w ρ R d0)
    (M := readMem sevm M p d0) (p := p) (t := w.token1)
    (cg := readNeed sevm M n p w ρ R G d0 + readCharge sevm M p w ρ R d0) fork wethCode depth
    notPrecompile (by simp only [readStack, List.length_cons]; omega) (swapBalanceReply_wf wf) width
    fits (by unfold readCharge; omega)
    (by
      have e : readNeed sevm M n p w ρ R G d0 + readCharge sevm M p w ρ R d0 -
          balExt sevm d0 (readStack w ρ R d0) (readMem sevm M p d0) p w.token1 - balAcc d0 w.token1 =
          readNeed sevm M n p w ρ R G d0 + readUsed sevm M p w ρ R d0 := by
        unfold readCharge readUsed; omega
      rw [e]
      exact room)
  obtain ⟨hrun, hstk, hret, hgas⟩ := spec
  have hskel : wethBalanceCall sevm d0 (readStack w ρ R d0) (readMem sevm M p d0) p w.token1
      (readNeed sevm M n p w ρ R G d0 + readCharge sevm M p w ρ R d0) =
      (readSkel sevm M p w ρ R d0).withGasLeft _ :=
    wethBalanceCallAt_eq _ _ _ _ _ _ _ _ _ _
  refine ⟨?_, hrun, hstk, ?_, ?_⟩
  · change (d0.state.getCode (swapTokenWord w.token1).toAdr).size.toB256 ≠ 0
    rw [wethCode]
    exact weth9_code_size_word
  · change 32 ≤ (wethBalanceCall sevm d0 (readStack w ρ R d0) (readMem sevm M p d0) p w.token1
      (readNeed sevm M n p w ρ R G d0 + readCharge sevm M p w ρ R d0)).returnData.length
    rw [hret, B256.length_toBytes]
  · change (wethBalanceCall sevm d0 (readStack w ρ R d0) (readMem sevm M p d0) p w.token1
      (readNeed sevm M n p w ρ R G d0 + readCharge sevm M p w ρ R d0)).gasLeft =
      swapBackPostGas sevm (wethBalanceCall sevm d0 (readStack w ρ R d0) (readMem sevm M p d0) p
        w.token1 (readNeed sevm M n p w ρ R G d0 + readCharge sevm M p w ρ R d0))
        (swapRequestSize (swapRequestSize n p) p) p w (swapBalanceWord d0.returnData)
        (swapBalanceWord (wethBalanceCall sevm d0 (readStack w ρ R d0) (readMem sevm M p d0) p
          w.token1 (readNeed sevm M n p w ρ R G d0 + readCharge sevm M p w ρ R d0)).returnData) G + 64
    rw [hgas]
    conv => rhs; rw [hskel, swapBackPostGas_withGasLeft, withGasLeft_returnData]
    have hn : readNeed sevm M n p w ρ R G d0 = swapBackPostGas sevm (readSkel sevm M p w ρ R d0)
        (swapRequestSize (swapRequestSize n p) p) p w (swapBalanceWord d0.returnData)
        (swapBalanceWord (readSkel sevm M p w ρ R d0).returnData) G + 64 := rfl
    rw [← hn]
    unfold readCharge readUsed
    omega

end Blanc.Composition.UniswapV2PairWeth9Joint
