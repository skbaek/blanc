import Blanc.Composition.UniswapV2PairWeth9LegsBurn
import Blanc.Composition.UniswapV2PairWeth9XLegCall

/-!
# The burn suffix's WETH9 `transfer` leg with WETH9 = token1 (C4(b), U8e)

With WETH9 as `token1`, Burn pays the other token `X = token0` first (`BurnBackForwardEnv.transfer0`,
an arbitrary callee record with result `d0`), then WETH9 at the world `d0`
(`BurnBackForwardEnv.transfer1`).  `burnWethLeg1` is that second `CALL` as WETH9's deployed code
determines it, at the call gas the crossing itself fixes; `burnWethLeg1_spec` is its frame-level
spec with WETH9's premises read at `d0`.

`burnWethLeg1_spec_afterX` discharges the premises at `d0` from the suffix's entry world `b` through
the X-leg quiescence (`xleg_transfer`, a form of `xleg_call` for one `_safeTransfer` crossing):
WETH9's code persists and the Pair's WETH9 balance slot does not drop across X's transfer child, and
the staged memory after X's transfer is laid out by `swapFwdOpt_layout` from X's record.  Its premises
are world facts at `b`, the two tokens distinct, and HASH-T over the keys X's child touches; none
mentions WETH9's answers.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair
open Blanc.Composition.UniswapV2PairWeth9XLeg (xleg_call CallChildFresh wethRunKeys pairRunKeys)

/-! ## X-leg quiescence at one `_safeTransfer` crossing -/

/-- **WETH9 across the other token's `transfer` (X-leg quiescence at a `_safeTransfer` record).**
Given an optimistic-transfer record from a Pair frame to a token other than WETH9, and at the
record's world: WETH9's code and footprint over `U` with the Pair tracked, the Pair's WETH9
allowances zero, the Pair runtime with a locked model state over rows `K`, the factory runtime at
that state's factory, `pair ≠ 0`, the ether supply a word; and HASH-T over the keys the callee's run
touches.  Then WETH9's code persists to the record's result and the Pair's WETH9 balance word does
not drop. -/
theorem xleg_transfer {sevm : Sevm} {W d : Devm} {L : List B256} {M : Mem} {n : Nat}
    {p amount toWord token rho : B256} {callGas G : Nat} {weth : Adr} {U : Weth9.Key → Prop}
    {K : WriterKey → Prop} {stL : UniswapV2Pair.State}
    (fork : CoveredFork sevm.benvStat.fork)
    (env : SwapTransferCallForward sevm W L M n p amount toWord token rho callGas G d)
    (callee : (tokenMask token).toAdr ≠ weth) (apart : sevm.currentTarget ≠ weth)
    (wethCode : W.state.getCode weth = Weth9.code)
    (foot : Weth9.FootInv U (W.state.getStor weth) (W.state.bal weth))
    (tracked : U (.bal sevm.currentTarget))
    (zero : ∀ g, Weth9Token.weth9Book.allow (Weth9.ledger U (W.state.getStor weth))
      sevm.currentTarget g = 0)
    (pairCode : W.state.getCode sevm.currentTarget = UniswapV2Pair.code)
    (rep : WriterRep K (W.state.getStor sevm.currentTarget) stL) (locked : stL.unlocked ≠ 1)
    (factoryCode : W.state.getCode stL.factory = UniswapV2Factory.code)
    (pairNonzero : sevm.currentTarget ≠ 0) (bound : sum W.state.bal < 2 ^ 256)
    (wethFresh : CallChildFresh sevm (xferCallState W L M p amount toWord token rho callGas)
      fun D => Weth9.KeysFresh U (wethRunKeys weth D))
    (pairFresh : CallChildFresh sevm (xferCallState W L M p amount toWord token rho callGas)
      fun D => WriterFreshKeys K (pairRunKeys sevm.currentTarget D)) :
    d.state.getCode weth = Weth9.code ∧
      W.getStorVal weth (Weth9.balSlot sevm.currentTarget) ≤
        d.getStorVal weth (Weth9.balSlot sevm.currentTarget) := by
  have run : Ninst.RunCompiled sevm (xferCallState W L M p amount toWord token rho callGas)
      (.exec .call) d := env.call
  have callee' : ∀ g c v ii is oi os rest,
      (xferCallState W L M p amount toWord token rho callGas).stack =
        g :: c :: v :: ii :: is :: oi :: os :: rest → c.toAdr ≠ weth := by
    intro g c v ii is oi os rest h
    have hc : c = tokenMask token := by
      simp only [xferCallState, St, Devm.setMach_stack, List.cons.injEq] at h
      exact h.2.1.symm
    rw [hc]
    exact callee
  have hstate : (xferCallState W L M p amount toWord token rho callGas).state = W.state := by
    rw [xferCallState, St, Devm.setMach_state]
  have code' : ∀ a, (xferCallState W L M p amount toWord token rho callGas).getCode a =
      W.state.getCode a := by
    intro a
    rw [xferCallState, St, Devm.getCode_setMach]
    rfl
  rw [← hstate] at foot zero rep bound
  obtain ⟨U', sub, codeD, -, -, balLe, -⟩ := xleg_call (ca := weth) (pair := sevm.currentTarget)
    run fork rfl callee' apart (by rw [code']; exact wethCode) foot zero
    (by rw [code']; exact pairCode) rep locked (by rw [code']; exact factoryCode) pairNonzero bound
    wethFresh pairFresh
  refine ⟨codeD, ?_⟩
  have h1 : Weth9Token.weth9Book.bal
      (Weth9.ledger U ((xferCallState W L M p amount toWord token rho callGas).state.getStor weth))
      sevm.currentTarget = (W.getStorVal weth (Weth9.balSlot sevm.currentTarget)).toNat := by
    rw [hstate]
    show (Weth9.tracked U _ sevm.currentTarget).toNat = _
    rw [Weth9.tracked_self tracked]
    rfl
  have h2 : Weth9Token.weth9Book.bal (Weth9.ledger U' (d.state.getStor weth)) sevm.currentTarget =
      (d.getStorVal weth (Weth9.balSlot sevm.currentTarget)).toNat := by
    show (Weth9.tracked U' _ sevm.currentTarget).toNat = _
    rw [Weth9.tracked_self (sub _ tracked)]
    rfl
  rw [h1, h2] at balLe
  exact B256.le_iff_toNat_le_toNat.mpr balLe

/-! ## The transfer leg -/

/-- The memory the WETH9 `transfer` is staged over: X's transfer window and reply written in. -/
def burnLeg1Mem (M : Mem) (p0 : B256) (w : BurnSuffixWords) (d0 : Devm) : Mem :=
  burnSuffixMem1 M p0 w d0

/-- The pointer X's transfer moved. -/
def burnLeg1Ptr (p0 : B256) (d0 : Devm) : B256 := swapMovedPointer p0 d0.returnData

/-- The gas-free skeleton of the WETH9 `transfer` CALL's result (token1 = WETH9). -/
def burnLeg1Skel (sevm : Sevm) (d0 : Devm) (M : Mem) (p0 : B256) (w : BurnSuffixWords)
    (R : List B256) : Devm :=
  wethTransferSkel sevm d0 (burnLegStack w R) (burnLeg1Mem M p0 w d0) (burnLeg1Ptr p0 d0) w.amount1
    w.recipient w.token1 0x16a3

/-- The residual the record ties the second transfer to: the first final query's staging and call
gas, read off the transfer's result `d`. -/
def burnLeg1Next (M : Mem) (p0 : B256) (w : BurnSuffixWords) (d0 : Devm) (balanceGas0 : Nat)
    (d : Devm) : Nat :=
  balanceGas0 + 5 + swapRequestCharge d (burnSuffixMem2 M p0 w d0 d).size (burnSuffixPtr p0 d0 d)
    w.token0 72 + 16

/-- What the suffix needs left after the WETH9 `transfer` CALL, read on the skeleton. -/
def burnLeg1Need (sevm : Sevm) (d0 : Devm) (M : Mem) (p0 : B256) (w : BurnSuffixWords)
    (R : List B256) (balanceGas0 : Nat) : Nat :=
  burnLeg1Next M p0 w d0 balanceGas0 (burnLeg1Skel sevm d0 M p0 w R) +
    safeTransferPostCharge (burnLeg1Mem M p0 w d0).size (burnLeg1Ptr p0 d0)
      (burnLeg1Skel sevm d0 M p0 w R).returnData

/-- WETH9's charge for the leg's child frame. -/
def burnLeg1Used (sevm : Sevm) (d0 : Devm) (M : Mem) (p0 : B256) (w : BurnSuffixWords)
    (R : List B256) : Nat :=
  xferUsed sevm d0 (burnLegStack w R) (burnLeg1Mem M p0 w d0) (burnLeg1Ptr p0 d0) w.amount1
    w.recipient w.token1 0x16a3

/-- The `CALL`'s own charges: the token's access, the windows' expansion, WETH9's `transfer`. -/
def burnLeg1Charge (sevm : Sevm) (d0 : Devm) (M : Mem) (p0 : B256) (w : BurnSuffixWords)
    (R : List B256) : Nat :=
  xferAcc d0 w.token1 +
    xferExt d0 (burnLegStack w R) (burnLeg1Mem M p0 w d0) (burnLeg1Ptr p0 d0) w.amount1 w.recipient
      w.token1 0x16a3 +
    burnLeg1Used sevm d0 M p0 w R

/-- **Burn's WETH9 `transfer` leg (token1 = WETH9)**: the second transfer's `CALL` result and the
`CALL` state's gas that WETH9's deployed code determines at X's transfer result `d0`, given the first
final query's call gas `balanceGas0`. -/
noncomputable def burnWethLeg1 (sevm : Sevm) (d0 : Devm) (M : Mem) (p0 : B256)
    (w : BurnSuffixWords) (R : List B256) (balanceGas0 : Nat) : Devm × Nat :=
  (wethTransferCall sevm d0 (burnLegStack w R) (burnLeg1Mem M p0 w d0) (burnLeg1Ptr p0 d0) w.amount1
      w.recipient w.token1 0x16a3
      (burnLeg1Need sevm d0 M p0 w R balanceGas0 + burnLeg1Charge sevm d0 M p0 w R),
    burnLeg1Need sevm d0 M p0 w R balanceGas0 + burnLeg1Charge sevm d0 M p0 w R)

theorem burnLeg1Next_withGasLeft (M : Mem) (p0 : B256) (w : BurnSuffixWords) (d0 : Devm)
    (balanceGas0 : Nat) (d : Devm) (x : Nat) :
    burnLeg1Next M p0 w d0 balanceGas0 (d.withGasLeft x) = burnLeg1Next M p0 w d0 balanceGas0 d :=
  rfl

/-- **Burn's WETH9 `transfer` leg's spec, token1 = WETH9 (frame level).**  At X's transfer result
`d0`: WETH9's code at `token1`, not a precompile, the frame mutable, call depth left, the staged
memory well formed with the moved pointer's bounds, stack room, the pair's WETH9 balance covering
`amount1`, the leg's call gas a word, and room for WETH9's `transfer` under the 63/64 rule with its
`SSTORE` sentry.  Then `burnWethLeg1` is the transfer record `BurnBackForwardEnv.transfer1` asks
for. -/
theorem burnWethLeg1_spec {sevm : Sevm} {d0 : Devm} {M : Mem} {p0 : B256} {w : BurnSuffixWords}
    {R : List B256} {balanceGas0 : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (nonstatic : sevm.isStatic = false)
    (depth : sevm.depth ≠ 0)
    (wethCode : d0.state.getCode (swapTokenWord w.token1).toAdr = Weth9.code)
    (notPrecompile : sevm.benvStat.rules.isPrecomp (swapTokenWord w.token1).toAdr = false)
    (wf : Mem.Wf (burnSuffixMem1 M p0 w d0))
    (lower : 128 ≤ (swapMovedPointer p0 d0.returnData).toNat)
    (width : (swapMovedPointer p0 d0.returnData).toNat + 164 < 2 ^ 256)
    (stackRoom : R.length < 1003)
    (balance : w.amount1 ≤
      d0.getStorVal (swapTokenWord w.token1).toAdr (Weth9.balSlot sevm.currentTarget))
    (fits : (burnWethLeg1 sevm d0 M p0 w R balanceGas0).2 < 2 ^ 256)
    (room : burnLeg1Used sevm d0 M p0 w R + gCallStipend ≤
      except64th (burnLeg1Need sevm d0 M p0 w R balanceGas0 + burnLeg1Used sevm d0 M p0 w R)) :
    SwapTransferCallForward sevm d0 (w.locals w.balance1 w.balance0 R) (burnSuffixMem1 M p0 w d0)
      (burnSuffixMem1 M p0 w d0).size (swapMovedPointer p0 d0.returnData) w.amount1 w.recipient
      w.token1 0x16a3 (burnWethLeg1 sevm d0 M p0 w R balanceGas0).2
      (balanceGas0 + 5 + swapRequestCharge (burnWethLeg1 sevm d0 M p0 w R balanceGas0).1
        (burnSuffixMem2 M p0 w d0 (burnWethLeg1 sevm d0 M p0 w R balanceGas0).1).size
        (burnSuffixPtr p0 d0 (burnWethLeg1 sevm d0 M p0 w R balanceGas0).1) w.token0 72 + 16)
      (burnWethLeg1 sevm d0 M p0 w R balanceGas0).1 := by
  have spec := wethTransferCall_spec (sevm := sevm) (W := d0) (L := burnLegStack w R)
    (M := burnLeg1Mem M p0 w d0) (p := burnLeg1Ptr p0 d0) (amount := w.amount1)
    (toWord := w.recipient) (token := w.token1) (rho := 0x16a3)
    (cg := burnLeg1Need sevm d0 M p0 w R balanceGas0 + burnLeg1Charge sevm d0 M p0 w R) fork
    wethCode nonstatic depth notPrecompile
    (by simp only [burnLegStack, BurnSuffixWords.locals, burnPricedLocals, List.length_cons]; omega)
    wf lower width balance fits
    (by unfold burnLeg1Charge; omega)
    (by
      have e : burnLeg1Need sevm d0 M p0 w R balanceGas0 + burnLeg1Charge sevm d0 M p0 w R -
          xferExt d0 (burnLegStack w R) (burnLeg1Mem M p0 w d0) (burnLeg1Ptr p0 d0) w.amount1
            w.recipient w.token1 0x16a3 -
          xferAcc d0 w.token1 =
          burnLeg1Need sevm d0 M p0 w R balanceGas0 + burnLeg1Used sevm d0 M p0 w R := by
        unfold burnLeg1Charge; omega
      rw [e]
      exact room)
  obtain ⟨hrun, hstk, hret, hgas⟩ := spec
  have hskel : wethTransferCall sevm d0 (burnLegStack w R) (burnLeg1Mem M p0 w d0)
      (burnLeg1Ptr p0 d0) w.amount1 w.recipient w.token1 0x16a3
      (burnLeg1Need sevm d0 M p0 w R balanceGas0 + burnLeg1Charge sevm d0 M p0 w R) =
      (burnLeg1Skel sevm d0 M p0 w R).withGasLeft _ :=
    wethTransferCallAt_eq _ _ _ _ _ _ _ _ _ _ _ _ _
  have hret' : (burnWethLeg1 sevm d0 M p0 w R balanceGas0).1.returnData = B256.toBytes 1 := hret
  refine ⟨hrun, hstk, Or.inr (by rw [hret']; exact one_reply_accepted), ?_⟩
  change (wethTransferCall sevm d0 (burnLegStack w R) (burnLeg1Mem M p0 w d0) (burnLeg1Ptr p0 d0)
      w.amount1 w.recipient w.token1 0x16a3
      (burnLeg1Need sevm d0 M p0 w R balanceGas0 + burnLeg1Charge sevm d0 M p0 w R)).gasLeft =
    burnLeg1Next M p0 w d0 balanceGas0 (wethTransferCall sevm d0 (burnLegStack w R)
      (burnLeg1Mem M p0 w d0) (burnLeg1Ptr p0 d0) w.amount1 w.recipient w.token1 0x16a3
      (burnLeg1Need sevm d0 M p0 w R balanceGas0 + burnLeg1Charge sevm d0 M p0 w R)) +
    safeTransferPostCharge (burnLeg1Mem M p0 w d0).size (burnLeg1Ptr p0 d0)
      (wethTransferCall sevm d0 (burnLegStack w R) (burnLeg1Mem M p0 w d0) (burnLeg1Ptr p0 d0)
        w.amount1 w.recipient w.token1 0x16a3
        (burnLeg1Need sevm d0 M p0 w R balanceGas0 + burnLeg1Charge sevm d0 M p0 w R)).returnData
  rw [hgas]
  conv => rhs; rw [hskel, burnLeg1Next_withGasLeft, withGasLeft_returnData]
  have hn : burnLeg1Need sevm d0 M p0 w R balanceGas0 =
      burnLeg1Next M p0 w d0 balanceGas0 (burnLeg1Skel sevm d0 M p0 w R) +
        safeTransferPostCharge (burnLeg1Mem M p0 w d0).size (burnLeg1Ptr p0 d0)
          (burnLeg1Skel sevm d0 M p0 w R).returnData := rfl
  rw [← hn]
  unfold burnLeg1Charge burnLeg1Used
  omega

/-- **Burn's WETH9 `transfer` leg after the other token's transfer (token1 = WETH9).**  Given X's
transfer record (`BurnBackForwardEnv.transfer0`'s shape) with result `d0`, the suffix entry's memory
facts (as `burnBack_exact` takes them), and at the suffix's entry world `b`: WETH9's code and
footprint over `U` with the Pair tracked, the Pair's WETH9 allowances zero, the Pair runtime with a
locked model state, the factory runtime at that state's factory, `pair ≠ 0`, the ether supply a word,
and the Pair's WETH9 balance covering `amount1`; the two tokens distinct and the Pair not WETH9; and
HASH-T over the keys X's child touches.  Then `burnWethLeg1` is the record
`BurnBackForwardEnv.transfer1` asks for. -/
theorem burnWethLeg1_spec_afterX {sevm : Sevm} {b d0 : Devm} {M : Mem} {n0 : Nat} {p0 : B256}
    {w : BurnSuffixWords} {R : List B256} {callGas0 G0 balanceGas0 : Nat} {weth : Adr}
    {U : Weth9.Key → Prop} {K : WriterKey → Prop} {stL : UniswapV2Pair.State}
    (fork : CoveredFork sevm.benvStat.fork) (nonstatic : sevm.isStatic = false)
    (depth : sevm.depth ≠ 0)
    (env0 : SwapTransferCallForward sevm b (w.locals w.balance1 w.balance0 R) M M.size p0
      w.amount0 w.recipient w.token0 0x1698 callGas0 G0 d0)
    (mem : PtrMem p0 n0 M) (sentinel : memWord M 96 = 0) (lower : 128 ≤ p0.toNat)
    (upper : p0.toNat < 2 ^ 161) (nonzero0 : w.amount0 ≠ 0) (stackRoom : R.length ≤ 980)
    (token1 : (swapTokenWord w.token1).toAdr = weth)
    (distinct : (swapTokenWord w.token0).toAdr ≠ weth) (apart : sevm.currentTarget ≠ weth)
    (wethCode : b.state.getCode weth = Weth9.code)
    (foot : Weth9.FootInv U (b.state.getStor weth) (b.state.bal weth))
    (tracked : U (.bal sevm.currentTarget))
    (zero : ∀ g, Weth9Token.weth9Book.allow (Weth9.ledger U (b.state.getStor weth))
      sevm.currentTarget g = 0)
    (pairCode : b.state.getCode sevm.currentTarget = UniswapV2Pair.code)
    (rep : WriterRep K (b.state.getStor sevm.currentTarget) stL) (locked : stL.unlocked ≠ 1)
    (factoryCode : b.state.getCode stL.factory = UniswapV2Factory.code)
    (pairNonzero : sevm.currentTarget ≠ 0) (bound : sum b.state.bal < 2 ^ 256)
    (balance : w.amount1 ≤ b.getStorVal weth (Weth9.balSlot sevm.currentTarget))
    (wethFresh : CallChildFresh sevm
      (xferCallState b (w.locals w.balance1 w.balance0 R) M p0 w.amount0 w.recipient w.token0 0x1698
        callGas0) fun D => Weth9.KeysFresh U (wethRunKeys weth D))
    (pairFresh : CallChildFresh sevm
      (xferCallState b (w.locals w.balance1 w.balance0 R) M p0 w.amount0 w.recipient w.token0 0x1698
        callGas0) fun D => WriterFreshKeys K (pairRunKeys sevm.currentTarget D))
    (notPrecompile : sevm.benvStat.rules.isPrecomp weth = false)
    (fits : (burnWethLeg1 sevm d0 M p0 w R balanceGas0).2 < 2 ^ 256)
    (room : burnLeg1Used sevm d0 M p0 w R + gCallStipend ≤
      except64th (burnLeg1Need sevm d0 M p0 w R balanceGas0 + burnLeg1Used sevm d0 M p0 w R)) :
    SwapTransferCallForward sevm d0 (w.locals w.balance1 w.balance0 R) (burnSuffixMem1 M p0 w d0)
      (burnSuffixMem1 M p0 w d0).size (swapMovedPointer p0 d0.returnData) w.amount1 w.recipient
      w.token1 0x16a3 (burnWethLeg1 sevm d0 M p0 w R balanceGas0).2
      (balanceGas0 + 5 + swapRequestCharge (burnWethLeg1 sevm d0 M p0 w R balanceGas0).1
        (burnSuffixMem2 M p0 w d0 (burnWethLeg1 sevm d0 M p0 w R balanceGas0).1).size
        (burnSuffixPtr p0 d0 (burnWethLeg1 sevm d0 M p0 w R balanceGas0).1) w.token0 72 + 16)
      (burnWethLeg1 sevm d0 M p0 w R balanceGas0).1 := by
  obtain ⟨codeD0, balLe⟩ := xleg_transfer fork env0 distinct apart wethCode foot tracked zero
    pairCode rep locked factoryCode pairNonzero bound wethFresh pairFresh
  have roomL : (w.locals w.balance1 w.balance0 R).length ≤ 1000 := by
    simp only [BurnSuffixWords.locals, burnPricedLocals, List.length_cons]
    omega
  obtain ⟨⟨n1, mem1⟩, -, lower1, upper1, -⟩ :=
    swapFwdOpt_layout (k := 161) (a := w.amount0) (d := d0) fork roomL mem sentinel
      lower upper (by decide) (fun _ => env0)
  simp only [swapOptPtr, swapOptMem, nonzero0, ↓reduceIte] at mem1 lower1 upper1
  rw [← token1] at codeD0 balLe notPrecompile
  apply burnWethLeg1_spec fork nonstatic depth codeD0 notPrecompile mem1.wf lower1
    (by
      have : 2 ^ 161 + 2 ^ 161 + 164 < 2 ^ 256 := by decide
      omega)
    (by omega)
    (B256.le_iff_toNat_le_toNat.mpr (Nat.le_trans
      (B256.le_iff_toNat_le_toNat.mp (by rw [token1]; exact balance))
      (B256.le_iff_toNat_le_toNat.mp balLe)))
    fits room

end Blanc.Composition.UniswapV2PairWeth9Joint
