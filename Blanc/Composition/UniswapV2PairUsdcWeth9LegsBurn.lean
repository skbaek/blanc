import Blanc.Composition.UniswapV2PairUsdcWeth9LegsRead
import Blanc.Composition.UniswapV2PairUsdcWeth9LegsXferKeep
import Blanc.Composition.UniswapV2PairWeth9LegsBurn1
import Blanc.Composition.UniswapV2PairWeth9LegsBurnFinal

/-!
# Burn's three USDC legs (USDC = token0, WETH9 = token1; U9 freeze §3, U9d)

Each mirrors the WETH9 token0 leg (`burnWethRead0`, `burnWethLeg0`, `burnWethFinal0`) with U9a's
`usdcReadLeg` / `usdcTransferCall` and USDC's 63/64 need (`usdcBalNeed`, `usdcBudget`):

* `burnUsdcRead0` — Burn's first initial `balanceOf(pair)` query, given the second's call gas;
* `burnUsdcLeg0` — the suffix's first `transfer`, given the second transfer's call gas;
* `burnUsdcFinal0` — the suffix's first final query, given the second final query's call gas.

Each spec meets the generic Burn record (`BurnInitialCallee`'s first query, `BurnBackForwardEnv`'s
`transfer0` and `first`), with the reply as USDC's stored balance bits and, for the reads, the
result as its gas-free skeleton up to gas (what WETH9's pins read, A17).
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair Blanc.Lift.Usdc
  Blanc.Composition.UniswapV2PairWeth9Joint Blanc.Composition.UsdcLive Blanc.Composition.UsdcToken

/-- **Burn's first initial query, USDC = token0**, given the second initial query's call gas. -/
noncomputable def burnUsdcRead0 (sevm : Sevm) (b : Devm) (R : List B256) (callGas1 : Nat) :
    Devm × Nat :=
  usdcReadLeg sevm (burnRead0World sevm b) (burnRead0Stack sevm b R) getterInitMemory 128
    (burnT0 sevm b) (burnRead0Need sevm b callGas1)

/-- Its gas-free skeleton (what WETH9's second initial query and the fee caller's gas read). -/
noncomputable def burnUsdcRead0Skel (sevm : Sevm) (b : Devm) (R : List B256) : Devm :=
  usdcBalanceSkel sevm (burnRead0World sevm b) (burnRead0Stack sevm b R) getterInitMemory 128
    (burnT0 sevm b)

section BurnLeg

variable (sevm : Sevm) (b : Devm) (M : Mem) (p0 : B256) (w : BurnSuffixWords) (R : List B256)

/-- The gas-free skeleton of the USDC `transfer` CALL's result at the suffix (token0 = USDC). -/
noncomputable def burnUsdcLeg0Skel : Devm :=
  usdcTransferSkel sevm b (burnLegStack w R) M p0 w.amount0 w.recipient w.token0 0x1698

/-- What the suffix needs left after the USDC `transfer` CALL, read on the skeleton. -/
noncomputable def burnUsdcLeg0Need (callGas1 : Nat) : Nat :=
  burnLeg0Next M p0 w callGas1 (burnUsdcLeg0Skel sevm b M p0 w R) +
    safeTransferPostCharge M.size p0 (burnUsdcLeg0Skel sevm b M p0 w R).returnData

/-- USDC's exact charge for the leg's child frame (proxy and implementation). -/
noncomputable def burnUsdcLeg0Used : Nat :=
  usdcUsed sevm b (burnLegStack w R) M p0 w.amount0 w.recipient w.token0 0x1698

/-- The gas USDC's child frame needs forwarded (the 63/64 cut at the proxy's `DELEGATECALL`). -/
noncomputable def burnUsdcLeg0Budget : Nat :=
  usdcBudget sevm b (burnLegStack w R) M p0 w.amount0 w.recipient w.token0 0x1698

/-- The `CALL`'s own charges: the token's access, the windows' expansion, USDC's `transfer`. -/
noncomputable def burnUsdcLeg0Charge : Nat :=
  xferAcc b w.token0 + xferExt b (burnLegStack w R) M p0 w.amount0 w.recipient w.token0 0x1698 +
    burnUsdcLeg0Used sevm b M p0 w R

end BurnLeg

/-- **Burn's USDC `transfer` leg (token0 = USDC)** at the suffix world `b`, given the second
transfer's call gas `callGas1`. -/
noncomputable def burnUsdcLeg0 (sevm : Sevm) (b : Devm) (M : Mem) (p0 : B256) (w : BurnSuffixWords)
    (R : List B256) (callGas1 : Nat) : Devm × Nat :=
  (usdcTransferCall sevm b (burnLegStack w R) M p0 w.amount0 w.recipient w.token0 0x1698
      (burnUsdcLeg0Need sevm b M p0 w R callGas1 + burnUsdcLeg0Charge sevm b M p0 w R),
    burnUsdcLeg0Need sevm b M p0 w R callGas1 + burnUsdcLeg0Charge sevm b M p0 w R)

/-- **The suffix's first final query, USDC = token0**, at the second transfer's result `d1`,
given the second final query's call gas. -/
noncomputable def burnUsdcFinal0 (sevm : Sevm) (M : Mem) (p0 : B256) (w : BurnSuffixWords)
    (R : List B256) (d0 d1 : Devm) (balanceGas1 : Nat) : Devm × Nat :=
  usdcReadLeg sevm d1 (w.locals w.balance1 w.balance0 R) (burnSuffixMem2 M p0 w d0 d1)
    (burnSuffixPtr p0 d0 d1) w.token0 (burnFinal0Need M p0 w d0 d1 balanceGas1)

/-- Its gas-free skeleton (what WETH9's second final query reads). -/
noncomputable def burnUsdcFinal0Skel (sevm : Sevm) (M : Mem) (p0 : B256) (w : BurnSuffixWords)
    (R : List B256) (d0 d1 : Devm) : Devm :=
  usdcBalanceSkel sevm d1 (w.locals w.balance1 w.balance0 R) (burnSuffixMem2 M p0 w d0 d1)
    (burnSuffixPtr p0 d0 d1) w.token0

/-- A result that is a skeleton up to gas is that skeleton at its own gas. -/
theorem eq_withGasLeft_self {d s : Devm} {y : Nat} (h : d = s.withGasLeft y) :
    d = s.withGasLeft d.gasLeft := by
  rw [h]
  rfl

/-- The code-size word of an installed USDC proxy is nonzero. -/
theorem usdc_code_nonzero {d : Devm} {P : Adr} (inst : UsdcInstalled P d.state) :
    (d.getCode P).size.toB256 ≠ 0 := by
  rw [show d.getCode P = Proxy.code from code_of_at (d := d) inst.proxy]
  exact proxy_code_size_word

/-- **Burn's first initial USDC read (USDC = token0), frame level.**  USDC installed at the cached
`token0` in the world after the lock, reserve and token loads, not a precompile, two levels of call
depth left, the Pair not USDC's admin there, stack room, the call gas a word, and room for USDC's
view under the 63/64 rule: `burnUsdcRead0` meets `BurnInitialCallee`'s `code0`…`returnedGas0`,
replies with the Pair's USDC balance bits there, and is its skeleton up to gas. -/
theorem burnUsdcRead0_spec {sevm : Sevm} {b : Devm} {R : List B256} {callGas1 : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (depth : 2 ≤ sevm.depth)
    (inst : Usdc.UsdcInstalled (burnT0 sevm b).toAdr (burnRead0World sevm b).state)
    (notPrecompile : sevm.benvStat.rules.isPrecomp (burnT0 sevm b).toAdr = false)
    (notAdmin : sevm.currentTarget ≠ Usdc.adminOf (burnRead0World sevm b).state (burnT0 sevm b).toAdr)
    (stackRoom : R.length < 1009)
    (fits : (burnUsdcRead0 sevm b R callGas1).2 < 2 ^ 256)
    (room : usdcBalNeed sevm (burnRead0World sevm b) (burnRead0Stack sevm b R) getterInitMemory 128
        (burnT0 sevm b) ≤
      except64th (burnRead0Need sevm b callGas1 (burnUsdcRead0Skel sevm b R) +
        usdcBalUsed sevm (burnRead0World sevm b) (burnRead0Stack sevm b R) getterInitMemory 128
          (burnT0 sevm b))) :
    let d0 := (burnUsdcRead0 sevm b R callGas1).1
    let callGas0 := (burnUsdcRead0 sevm b R callGas1).2
    ((burnTokensWorld sevm (burnReservedWorld sevm b)).getCode (burnT0 sevm b).toAdr).size.toB256 ≠ 0 ∧
    Ninst.RunCompiled sevm
      (St (burnCall0World sevm b) (callGas0.toB256 :: burnT0 sevm b :: 128 :: 36 :: 128 :: 32 ::
        164 :: 0x70a08231 :: burnT0 sevm b :: 0 :: burnT1 sevm b :: burnT0 sevm b ::
        burnInitLocals sevm b R)
        (balanceRequestMemory getterInitMemory sevm.currentTarget) callGas0) (.exec .staticcall) d0 ∧
    d0.stack = 1 :: 164 :: 0x70a08231 :: burnT0 sevm b :: 0 :: burnT1 sevm b ::
      burnT0 sevm b :: burnInitLocals sevm b R ∧
    32 ≤ d0.returnData.length ∧
    d0.gasLeft = burnInitialGas1 sevm b d0 callGas1 + 64 ∧
    d0.returnData = (Nat.toB256 (Usdc.balanceBits (((burnRead0World sevm b).state.getStor
      (burnT0 sevm b).toAdr).get (Usdc.balSlot sevm.currentTarget)))).toBytes ∧
    d0 = (burnUsdcRead0Skel sevm b R).withGasLeft d0.gasLeft := by
  have ht := swapTokenWord_burnT0 sevm b
  have htok : balTok (burnT0 sevm b) = (burnT0 sevm b).toAdr := by unfold balTok; rw [ht]
  obtain ⟨hrun, hstk, hret, hgas⟩ := usdcReadLeg_spec (sevm := sevm) (B := burnRead0World sevm b)
    (S := burnRead0Stack sevm b R) (M := getterInitMemory) (p := 128) (t := burnT0 sevm b)
    (need := burnRead0Need sevm b callGas1) (burnRead0Need_gasFree sevm b callGas1) fork
    (by rw [htok]; exact inst) depth (by rw [htok]; exact notPrecompile)
    (by rw [htok]; exact notAdmin)
    (by simp only [burnRead0Stack, burnInitLocals, List.length_cons]; omega)
    getterInitMemory_ptr.wf (by decide) fits room
  rw [balCallState_128 _ ht] at hrun
  rw [htok] at hret
  dsimp only
  unfold burnUsdcRead0
  refine ⟨usdc_code_nonzero inst, hrun, ?_, by rw [hret, B256.length_toBytes], hgas, hret, ?_⟩
  · rw [hstk]
    unfold balRest
    rw [ht]
    rfl
  · unfold usdcReadLeg usdcBalanceCall
    exact eq_withGasLeft_self (usdcBalanceCallAt_eq _ _ _ _ _ _ _ _ _ _)

/-- **Burn's USDC `transfer` leg's spec, token0 = USDC (frame level).**  At the suffix's entry
world `b`: USDC installed at `token0` with its footprint facts (`FootCore`) over `U`, not a
precompile, the frame mutable, two levels of call depth left, the Pair and the recipient tracked,
the Pair not USDC's admin, the transfer's ledger conditions and the Pair's USDC balance covering
`amount0`, a well-formed memory with the pointer's bounds, stack room, the leg's call gas a word,
and the child's budget under the 63/64 rule.  Then `burnUsdcLeg0` is the transfer record
`BurnBackForwardEnv.transfer0` asks for. -/
theorem burnUsdcLeg0_spec {sevm : Sevm} {b : Devm} {M : Mem} {p0 : B256} {w : BurnSuffixWords}
    {R : List B256} {callGas1 : Nat} {U : Usdc.Key → Prop}
    (fork : CoveredFork sevm.benvStat.fork) (nonstatic : sevm.isStatic = false)
    (depth : 2 ≤ sevm.depth)
    (inst : Usdc.UsdcInstalled (swapTokenWord w.token0).toAdr b.state)
    (finv : FootCore U (b.state.getStor (swapTokenWord w.token0).toAdr))
    (notPrecompile : sevm.benvStat.rules.isPrecomp (swapTokenWord w.token0).toAdr = false)
    (kPair : U (.bal sevm.currentTarget)) (kTo : U (.bal w.recipient.toAdr))
    (notAdmin : sevm.currentTarget ≠ Usdc.adminOf b.state (swapTokenWord w.token0).toAdr)
    (ok : UsdcTransferOk (Usdc.ledger U (b.state.getStor (swapTokenWord w.token0).toAdr))
      sevm.currentTarget w.recipient.toAdr w.amount0.toNat)
    (balance : w.amount0.toNat ≤
      (Usdc.ledger U (b.state.getStor (swapTokenWord w.token0).toAdr)).bal sevm.currentTarget)
    (wf : Mem.Wf M) (lower : 128 ≤ p0.toNat) (width : p0.toNat + 164 < 2 ^ 256)
    (stackRoom : R.length < 1003)
    (fits : (burnUsdcLeg0 sevm b M p0 w R callGas1).2 < 2 ^ 256)
    (room : burnUsdcLeg0Budget sevm b M p0 w R ≤
      except64th (burnUsdcLeg0Need sevm b M p0 w R callGas1 + burnUsdcLeg0Used sevm b M p0 w R)) :
    SwapTransferCallForward sevm b (w.locals w.balance1 w.balance0 R) M M.size p0
      w.amount0 w.recipient w.token0 0x1698 (burnUsdcLeg0 sevm b M p0 w R callGas1).2
      (callGas1 + safeTransferPreCharge (burnSuffixMem1 M p0 w (burnUsdcLeg0 sevm b M p0 w R callGas1).1).size
        (swapMovedPointer p0 (burnUsdcLeg0 sevm b M p0 w R callGas1).1.returnData) + 24)
      (burnUsdcLeg0 sevm b M p0 w R callGas1).1 := by
  have spec := usdcTransferCall_spec (sevm := sevm) (W := b) (L := burnLegStack w R) (M := M)
    (p := p0) (amount := w.amount0) (toWord := w.recipient) (token := w.token0) (rho := 0x1698)
    (cg := burnUsdcLeg0Need sevm b M p0 w R callGas1 + burnUsdcLeg0Charge sevm b M p0 w R) (U := U)
    fork inst finv nonstatic depth notPrecompile
    (by simp only [burnLegStack, BurnSuffixWords.locals, burnPricedLocals, List.length_cons]; omega)
    wf lower width kPair kTo notAdmin ok balance fits
    (by unfold burnUsdcLeg0Charge; omega)
    (by
      have e : burnUsdcLeg0Need sevm b M p0 w R callGas1 + burnUsdcLeg0Charge sevm b M p0 w R -
          xferExt b (burnLegStack w R) M p0 w.amount0 w.recipient w.token0 0x1698 -
          xferAcc b w.token0 =
          burnUsdcLeg0Need sevm b M p0 w R callGas1 + burnUsdcLeg0Used sevm b M p0 w R := by
        unfold burnUsdcLeg0Charge; omega
      rw [e]
      exact room)
  obtain ⟨hrun, hstk, hret, hgas⟩ := spec
  have hskel : usdcTransferCall sevm b (burnLegStack w R) M p0 w.amount0 w.recipient w.token0 0x1698
      (burnUsdcLeg0Need sevm b M p0 w R callGas1 + burnUsdcLeg0Charge sevm b M p0 w R) =
      (burnUsdcLeg0Skel sevm b M p0 w R).withGasLeft _ :=
    usdcTransferCallAt_eq _ _ _ _ _ _ _ _ _ _ _ _ _
  have hret' : (burnUsdcLeg0 sevm b M p0 w R callGas1).1.returnData = B256.toBytes 1 := hret
  refine ⟨hrun, hstk, Or.inr (by rw [hret']; exact one_reply_accepted), ?_⟩
  change (usdcTransferCall sevm b (burnLegStack w R) M p0 w.amount0 w.recipient w.token0 0x1698
      (burnUsdcLeg0Need sevm b M p0 w R callGas1 + burnUsdcLeg0Charge sevm b M p0 w R)).gasLeft =
    burnLeg0Next M p0 w callGas1 (usdcTransferCall sevm b (burnLegStack w R) M p0 w.amount0
      w.recipient w.token0 0x1698
      (burnUsdcLeg0Need sevm b M p0 w R callGas1 + burnUsdcLeg0Charge sevm b M p0 w R)) +
    safeTransferPostCharge M.size p0
      (usdcTransferCall sevm b (burnLegStack w R) M p0 w.amount0 w.recipient w.token0 0x1698
        (burnUsdcLeg0Need sevm b M p0 w R callGas1 + burnUsdcLeg0Charge sevm b M p0 w R)).returnData
  rw [hgas]
  conv => rhs; rw [hskel, burnLeg0Next_withGasLeft, withGasLeft_returnData]
  have hn : burnUsdcLeg0Need sevm b M p0 w R callGas1 =
      burnLeg0Next M p0 w callGas1 (burnUsdcLeg0Skel sevm b M p0 w R) +
        safeTransferPostCharge M.size p0 (burnUsdcLeg0Skel sevm b M p0 w R).returnData := rfl
  rw [← hn]
  unfold burnUsdcLeg0Charge burnUsdcLeg0Used
  omega

/-- **The suffix's first final USDC read (USDC = token0), frame level.**  At the second transfer's
result world `d1`: USDC installed at `token0` there, not a precompile, two levels of call depth
left, the Pair not USDC's admin there, a well-formed memory, the pointer's width bound, stack room,
the call gas a word, and room for USDC's view.  Then `burnUsdcFinal0` is the
`BurnBackForwardEnv.first` record, replies with the Pair's USDC balance bits at `d1`, and is its
skeleton up to gas. -/
theorem burnUsdcFinal0_spec {sevm : Sevm} {M : Mem} {p0 : B256} {w : BurnSuffixWords}
    {R : List B256} {d0 d1 : Devm} {balanceGas1 : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (depth : 2 ≤ sevm.depth)
    (inst : Usdc.UsdcInstalled (swapTokenWord w.token0).toAdr d1.state)
    (notPrecompile : sevm.benvStat.rules.isPrecomp (swapTokenWord w.token0).toAdr = false)
    (notAdmin : sevm.currentTarget ≠ Usdc.adminOf d1.state (swapTokenWord w.token0).toAdr)
    (wf : Mem.Wf (burnSuffixMem2 M p0 w d0 d1))
    (width : (burnSuffixPtr p0 d0 d1).toNat + 260 < 2 ^ 256) (stackRoom : R.length < 1005)
    (fits : (burnUsdcFinal0 sevm M p0 w R d0 d1 balanceGas1).2 < 2 ^ 256)
    (room : usdcBalNeed sevm d1 (w.locals w.balance1 w.balance0 R) (burnSuffixMem2 M p0 w d0 d1)
        (burnSuffixPtr p0 d0 d1) w.token0 ≤
      except64th (burnFinal0Need M p0 w d0 d1 balanceGas1 (burnUsdcFinal0Skel sevm M p0 w R d0 d1) +
        usdcBalUsed sevm d1 (w.locals w.balance1 w.balance0 R) (burnSuffixMem2 M p0 w d0 d1)
          (burnSuffixPtr p0 d0 d1) w.token0)) :
    SwapBalanceEnv sevm d1 (burnSuffixMem2 M p0 w d0 d1) (burnSuffixPtr p0 d0 d1) w.token0
        (w.locals w.balance1 w.balance0 R) (burnUsdcFinal0 sevm M p0 w R d0 d1 balanceGas1).1
        (burnUsdcFinal0 sevm M p0 w R d0 d1 balanceGas1).2
        (balanceGas1 + 5 + swapRequestCharge (burnUsdcFinal0 sevm M p0 w R d0 d1 balanceGas1).1
          (swapRequestSize (burnSuffixMem2 M p0 w d0 d1).size (burnSuffixPtr p0 d0 d1))
          (burnSuffixPtr p0 d0 d1) w.token1 83 + 21) ∧
      (burnUsdcFinal0 sevm M p0 w R d0 d1 balanceGas1).1.returnData =
        (Nat.toB256 (Usdc.balanceBits ((d1.state.getStor (swapTokenWord w.token0).toAdr).get
          (Usdc.balSlot sevm.currentTarget)))).toBytes ∧
      (burnUsdcFinal0 sevm M p0 w R d0 d1 balanceGas1).1 =
        (burnUsdcFinal0Skel sevm M p0 w R d0 d1).withGasLeft
          (burnUsdcFinal0 sevm M p0 w R d0 d1 balanceGas1).1.gasLeft := by
  obtain ⟨hrun, hstk, hret, hgas⟩ := usdcReadLeg_spec (sevm := sevm) (B := d1)
    (S := w.locals w.balance1 w.balance0 R) (M := burnSuffixMem2 M p0 w d0 d1)
    (p := burnSuffixPtr p0 d0 d1) (t := w.token0) (need := burnFinal0Need M p0 w d0 d1 balanceGas1)
    (burnFinal0Need_gasFree M p0 w d0 d1 balanceGas1) fork inst depth notPrecompile notAdmin
    (by simp only [BurnSuffixWords.locals, burnPricedLocals, List.length_cons]; omega) wf width
    fits room
  unfold burnUsdcFinal0
  refine ⟨⟨usdc_code_nonzero inst, hrun, hstk, by rw [hret, B256.length_toBytes], hgas⟩, hret, ?_⟩
  unfold usdcReadLeg usdcBalanceCall
  exact eq_withGasLeft_self (usdcBalanceCallAt_eq _ _ _ _ _ _ _ _ _ _)

/-! ## The legs read the worlds they are staged over only off non-gas fields

The pins of `BurnEnvUW` read the earlier legs' results through their gas-free skeletons (A17); the
real results differ from the skeletons only in the gas column, so each leg over a real result is the
leg over the skeleton. -/

section GasFree

variable (sevm : Sevm) (B : Devm) (x : Nat) (S : List B256) (M : Mem) (p t : B256)

theorem usdcBalUsed_withGasLeft :
    usdcBalUsed sevm (B.withGasLeft x) S M p t = usdcBalUsed sevm B S M p t := by
  simp only [usdcBalUsed, bChildS, bChildB, balMsg_withGasLeft]

theorem usdcBalanceSkel_withGasLeft :
    usdcBalanceSkel sevm (B.withGasLeft x) S M p t = usdcBalanceSkel sevm B S M p t := by
  simp only [usdcBalanceSkel, bChildS, bChildB, balParent_withGasLeft, balMsg_withGasLeft]

theorem usdcBalanceCall_withGasLeft (cg : Nat) :
    usdcBalanceCall sevm (B.withGasLeft x) S M p t cg = usdcBalanceCall sevm B S M p t cg := by
  simp only [usdcBalanceCall, usdcBalanceCallAt, balSplit, bChildB, balParent_withGasLeft,
    balMsg_withGasLeft, balExt_withGasLeft, balAcc_withGasLeft, usdcBalUsed_withGasLeft]

theorem usdcReadLeg_withGasLeft (need : Devm → Nat) :
    usdcReadLeg sevm (B.withGasLeft x) S M p t need = usdcReadLeg sevm B S M p t need := by
  simp only [usdcReadLeg, usdcReadLegGas, usdcBalanceCall_withGasLeft, usdcBalanceSkel_withGasLeft,
    balAcc_withGasLeft, balExt_withGasLeft, usdcBalUsed_withGasLeft]

end GasFree

theorem burnUsdcFinal0_withGasLeft (sevm : Sevm) (M : Mem) (p0 : B256) (w : BurnSuffixWords)
    (R : List B256) (d0 d1 : Devm) (balanceGas1 x y : Nat) :
    burnUsdcFinal0 sevm M p0 w R (d0.withGasLeft x) (d1.withGasLeft y) balanceGas1 =
      burnUsdcFinal0 sevm M p0 w R d0 d1 balanceGas1 := by
  change usdcReadLeg sevm (d1.withGasLeft y) (w.locals w.balance1 w.balance0 R)
      (burnSuffixMem2 M p0 w d0 d1) (burnSuffixPtr p0 d0 d1) w.token0
      (burnFinal0Need M p0 w d0 d1 balanceGas1) = _
  rw [usdcReadLeg_withGasLeft]
  rfl

theorem burnUsdcFinal0Skel_withGasLeft (sevm : Sevm) (M : Mem) (p0 : B256) (w : BurnSuffixWords)
    (R : List B256) (d0 d1 : Devm) (x y : Nat) :
    burnUsdcFinal0Skel sevm M p0 w R (d0.withGasLeft x) (d1.withGasLeft y) =
      burnUsdcFinal0Skel sevm M p0 w R d0 d1 := by
  change usdcBalanceSkel sevm (d1.withGasLeft y) (w.locals w.balance1 w.balance0 R)
      (burnSuffixMem2 M p0 w d0 d1) (burnSuffixPtr p0 d0 d1) w.token0 = _
  rw [usdcBalanceSkel_withGasLeft]
  rfl

theorem burnWethRead1_withGasLeft (sevm : Sevm) (b d0 : Devm) (R : List B256) (T1 x : Nat) :
    burnWethRead1 sevm b (d0.withGasLeft x) R T1 = burnWethRead1 sevm b d0 R T1 := by
  change wethReadLeg sevm (d0.withGasLeft x) (burnRead1Stack sevm b R d0) (burnMem1 sevm d0) 128
    (burnT1 sevm b &&& burnAddrMask) (fun _ => T1 + 64) = _
  rw [wethReadLeg_withGasLeft]
  rfl

theorem burnWethLeg1_withGasLeft (sevm : Sevm) (d0 : Devm) (M : Mem) (p0 : B256)
    (w : BurnSuffixWords) (R : List B256) (balanceGas0 x : Nat) :
    burnWethLeg1 sevm (d0.withGasLeft x) M p0 w R balanceGas0 =
      burnWethLeg1 sevm d0 M p0 w R balanceGas0 := rfl

theorem burnWethFinal1_withGasLeft (sevm : Sevm) (M : Mem) (p0 : B256) (w : BurnSuffixWords)
    (R : List B256) (d0 d1 e0 : Devm) (G x y z : Nat) :
    burnWethFinal1 sevm M p0 w R (d0.withGasLeft x) (d1.withGasLeft y) (e0.withGasLeft z) G =
      burnWethFinal1 sevm M p0 w R d0 d1 e0 G := by
  change wethReadLeg sevm (e0.withGasLeft z) (burnFinal1Stack w R e0)
      (burnFinal1Mem sevm M p0 w d0 d1 e0) (burnSuffixPtr p0 d0 d1) w.token1
      (burnFinal1Need sevm M p0 w d0 d1 e0 G) = _
  rw [wethReadLeg_withGasLeft]
  rfl

/-! ## What the suffix's transfers keep

USDC's facts cross WETH9's `transfer` (an explicit post writing storage at WETH9 only), and its
installation crosses any world change that keeps the nonempty codes and the implementation slot. -/

/-- **WETH9's `transfer` CALL writes storage at the token only.** -/
theorem wethTransferCall_storOff (sevm : Sevm) (W : Devm) (L : List B256) (M : Mem)
    (p amount toWord token rho : B256) (cg : Nat) {a : Adr} (ha : a ≠ (tokenMask token).toAdr) :
    (wethTransferCall sevm W L M p amount toWord token rho cg).state.getStor a = W.state.getStor a := by
  generalize hs : initSevm (xferMsg sevm W L M p amount toWord token rho cg
    ((xferSplit W L M p amount toWord token rho cg).1 + xferExt W L M p amount toWord token rho)
    (xferSplit W L M p amount toWord token rho cg).2) = s
  have ht : s.currentTarget = (tokenMask token).toAdr := by
    rw [← hs]; unfold xferMsg; rw [callChildMsg_zero]; rfl
  have hb : (initDevm (xferMsg sevm W L M p amount toWord token rho cg
      ((xferSplit W L M p amount toWord token rho cg).1 + xferExt W L M p amount toWord token rho)
      (xferSplit W L M p amount toWord token rho cg).2)).state = W.state := by
    unfold xferMsg
    rw [callChildMsg_zero, vcsm_state]
    unfold xferParent xferWarm xferPopped
    rw [callSpawnParent_state, addAccessedAddress_setMach_state]
  have ne : s.currentTarget ≠ a := by rw [ht]; exact Ne.symm ha
  unfold wethTransferCall wethTransferCallAt
  rw [hs, (callChildPost_facts_zero _ _ _ (B256.toNat 0) rfl).2.2.2.1, weth9TransferPost_state, ← hb]
  change Devm.getStor (xferTailPost s (Weth9.pB1 s _ s.caller) s.caller (Sevm.dataWord s 4).toAdr
    (Sevm.dataWord s 36)) a = Devm.getStor _ a
  unfold xferTailPost
  simp only [addLog_getStor', afterSstore_getStor_ne _ _ _ _ _ ne, afterSload_getStor]

/-- **USDC stays installed** across a world change that keeps every nonempty code and the proxy's
implementation slot. -/
theorem usdcInstalled_of_codes {P : Adr} {w w' : Jaune.State} (inst : UsdcInstalled P w)
    (code : ∀ a, (w.getCode a).toList ≠ [] → w'.getCode a = w.getCode a)
    (slot : (w'.getStor P).get implSlot = (w.getStor P).get implSlot) : UsdcInstalled P w' := by
  have hp : w.getCode P = Proxy.code := Blanc.ExecutionTrace.bytes_eq_of_image inst.proxy
  have hi : w.getCode usdcImpl = Impl.code := Blanc.ExecutionTrace.bytes_eq_of_image inst.impl
  have hl : w.getCode usdcLib = Lib.code := Blanc.ExecutionTrace.bytes_eq_of_image inst.lib
  refine ⟨?_, ?_, ?_, by rw [slot]; exact inst.slot, inst.implApart, inst.libApart⟩
  · rw [code P (by rw [hp]; exact proxy_nonempty)]; exact inst.proxy
  · rw [code usdcImpl (by rw [hi]; exact implSem.ne_nil rfl)]; exact inst.impl
  · rw [code usdcLib (by rw [hl]; exact lib_toList_ne_nil)]; exact inst.lib

end Blanc.Composition.UniswapV2PairUsdcWeth9
