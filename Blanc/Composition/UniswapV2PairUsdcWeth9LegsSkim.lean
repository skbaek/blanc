import Blanc.Composition.UniswapV2PairUsdcWeth9LegsRead
import Blanc.Composition.UniswapV2PairUsdcWeth9LegsXferKeep
import Blanc.Composition.UniswapV2PairWeth9SkimEnvOne
import Jaune.DevmProjections

/-!
# Skim's USDC legs (USDC = token0, WETH9 = token1; U9e)

Skim queries and pays `token0` first.  With USDC as `token0` both are explicit runs of USDC's
deployed code: the first `balanceOf(pair)` query is U9a's read leg `usdcReadLeg` at the fixed
pointer `128` (`skimUsdcRead0`), and the first transfer is the USDC `transfer` `CALL`
`usdcTransferCall` over the query's result (`skimUsdcLeg0`).  Each is pinned by the gas the skim
needs after it, read on gas-free skeletons (`skimUsdcRead0Skel`, `skimUsdcLeg0Skel`), so WETH9's
later pins read USDC's results only through those skeletons (A17).
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair Blanc.Lift.Usdc
  Blanc.Composition.UniswapV2PairWeth9Joint Blanc.Composition.UsdcLive Blanc.Composition.UsdcToken

/-- **Skim's first `balanceOf(pair)` query with USDC as `token0`**, given the first transfer's call
gas. -/
noncomputable def skimUsdcRead0 (sevm : Sevm) (b : Devm) (callGasT0 : Nat) : Devm × Nat :=
  usdcReadLeg sevm (skimCachedWorld sevm b) (skimRead0Stack sevm b) getterInitMemory 128
    (skimToken0 sevm b) (skimRead0Need sevm callGasT0)

/-- Its gas-free skeleton. -/
noncomputable def skimUsdcRead0Skel (sevm : Sevm) (b : Devm) : Devm :=
  usdcBalanceSkel sevm (skimCachedWorld sevm b) (skimRead0Stack sevm b) getterInitMemory 128
    (skimToken0 sevm b)

section SkimLeg

variable (sevm : Sevm) (b qd0 : Devm) (callGasQ1 : Nat)

/-- The gas-free skeleton of skim's USDC `transfer` CALL's result, over the first query's result. -/
noncomputable def skimUsdcLeg0Skel : Devm :=
  usdcTransferSkel sevm qd0 (skimLegStack sevm b) (skimLegMem sevm qd0) 128
    (skimLegAmount sevm b qd0) (skimToWord sevm) (skimToken0 sevm b) 0x1a2b

noncomputable def skimUsdcLeg0Need : Nat :=
  skimLeg0Next sevm b qd0 callGasQ1 (skimUsdcLeg0Skel sevm b qd0) +
    safeTransferPostCharge (skimLegMem sevm qd0).size 128 (skimUsdcLeg0Skel sevm b qd0).returnData

noncomputable def skimUsdcLeg0Used : Nat :=
  usdcUsed sevm qd0 (skimLegStack sevm b) (skimLegMem sevm qd0) 128 (skimLegAmount sevm b qd0)
    (skimToWord sevm) (skimToken0 sevm b) 0x1a2b

noncomputable def skimUsdcLeg0Budget : Nat :=
  usdcBudget sevm qd0 (skimLegStack sevm b) (skimLegMem sevm qd0) 128 (skimLegAmount sevm b qd0)
    (skimToWord sevm) (skimToken0 sevm b) 0x1a2b

noncomputable def skimUsdcLeg0Charge : Nat :=
  xferAcc qd0 (skimToken0 sevm b) +
    xferExt qd0 (skimLegStack sevm b) (skimLegMem sevm qd0) 128 (skimLegAmount sevm b qd0)
      (skimToWord sevm) (skimToken0 sevm b) 0x1a2b +
    skimUsdcLeg0Used sevm b qd0

end SkimLeg

/-- **Skim's USDC `transfer` leg (token0 = USDC)**, over the first query's result `qd0`, given the
second query's call gas. -/
noncomputable def skimUsdcLeg0 (sevm : Sevm) (b qd0 : Devm) (callGasQ1 : Nat) : Devm × Nat :=
  (usdcTransferCall sevm qd0 (skimLegStack sevm b) (skimLegMem sevm qd0) 128
      (skimLegAmount sevm b qd0) (skimToWord sevm) (skimToken0 sevm b) 0x1a2b
      (skimUsdcLeg0Need sevm b qd0 callGasQ1 + skimUsdcLeg0Charge sevm b qd0),
    skimUsdcLeg0Need sevm b qd0 callGasQ1 + skimUsdcLeg0Charge sevm b qd0)

/-- **The first transfer's call gas**, fixed by USDC's code on the first query's skeleton, given
the second query's call gas (`skimLeg0Gas`'s analogue). -/
noncomputable def skimUsdcLeg0Gas (sevm : Sevm) (b : Devm) (callGasQ1 : Nat) : Nat :=
  (skimUsdcLeg0 sevm b (skimUsdcRead0Skel sevm b) callGasQ1).2

/-! ## Gas-freeness -/

/-- The query's result is its skeleton up to gas. -/
theorem skimUsdcRead0_skel (sevm : Sevm) (b : Devm) (callGasT0 : Nat) :
    ∃ x, (skimUsdcRead0 sevm b callGasT0).1 = (skimUsdcRead0Skel sevm b).withGasLeft x :=
  ⟨_, usdcBalanceCallAt_eq _ _ _ _ _ _ _ _ _ _⟩

/-- The transfer leg reads the query's result only off its non-gas fields. -/
theorem skimUsdcLeg0_withGasLeft (sevm : Sevm) (b d : Devm) (callGasQ1 x : Nat) :
    skimUsdcLeg0 sevm b (d.withGasLeft x) callGasQ1 = skimUsdcLeg0 sevm b d callGasQ1 := rfl

theorem skimUsdcLeg0Skel_withGasLeft (sevm : Sevm) (b d : Devm) (x : Nat) :
    skimUsdcLeg0Skel sevm b (d.withGasLeft x) = skimUsdcLeg0Skel sevm b d := rfl

/-- The transfer's result is its skeleton up to gas. -/
theorem skimUsdcLeg0_skel (sevm : Sevm) (b qd0 : Devm) (callGasQ1 : Nat) :
    ∃ x, (skimUsdcLeg0 sevm b qd0 callGasQ1).1 = (skimUsdcLeg0Skel sevm b qd0).withGasLeft x :=
  ⟨_, usdcTransferCallAt_eq _ _ _ _ _ _ _ _ _ _ _ _ _⟩

/-! ## The specs -/

theorem skimToken0_balTok (sevm : Sevm) (b : Devm) :
    balTok (skimToken0 sevm b) = (skimToken0 sevm b).toAdr := by
  unfold balTok skimToken0
  rw [swapTokenWord_adr]

/-- **Skim's first USDC query (token0 = USDC), frame level** (from `usdcReadLeg_spec`):
`SkimForwardEnv.code0` and `qenv0` at the pinned values, the reply, the skeleton form. -/
theorem skimUsdcRead0_spec {sevm : Sevm} {b : Devm} {callGasT0 : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (depth : 2 ≤ sevm.depth)
    (inst : Usdc.UsdcInstalled (skimToken0 sevm b).toAdr (skimCachedWorld sevm b).state)
    (notPrecompile : sevm.benvStat.rules.isPrecomp (skimToken0 sevm b).toAdr = false)
    (notAdmin : sevm.currentTarget ≠ Usdc.adminOf (skimCachedWorld sevm b).state (skimToken0 sevm b).toAdr)
    (fits : (skimUsdcRead0 sevm b callGasT0).2 < 2 ^ 256)
    (room : usdcBalNeed sevm (skimCachedWorld sevm b) (skimRead0Stack sevm b) getterInitMemory 128
        (skimToken0 sevm b) ≤
      except64th (skimRead0Need sevm callGasT0 (skimUsdcRead0Skel sevm b) +
        usdcBalUsed sevm (skimCachedWorld sevm b) (skimRead0Stack sevm b) getterInitMemory 128
          (skimToken0 sevm b))) :
    let qd0 := (skimUsdcRead0 sevm b callGasT0).1
    let callGasQ0 := (skimUsdcRead0 sevm b callGasT0).2
    (((skimCachedWorld sevm b).getCode (skimToken0 sevm b).toAdr).size.toB256) ≠ 0 ∧
    SkimQueryEnv sevm (temporalAccountAccessBase (skimCachedWorld sevm b) (skimToken0 sevm b).toAdr)
      (balanceRequestMemory getterInitMemory sevm.currentTarget) 128 (skimToken0 sevm b)
      (skimQuery0Stack sevm b) qd0 callGasQ0
      (((callGasT0 + safeTransferPreCharge (balanceReplyMemory getterInitMemory sevm.currentTarget
        qd0.returnData).size 128 + 12)) + 80) ∧
    qd0.returnData = (Nat.toB256 (Usdc.balanceBits (((skimCachedWorld sevm b).state.getStor
      (skimToken0 sevm b).toAdr).get (Usdc.balSlot sevm.currentTarget)))).toBytes ∧
    qd0 = (skimUsdcRead0Skel sevm b).withGasLeft qd0.gasLeft := by
  dsimp only
  have ht : swapTokenWord (skimToken0 sevm b) = skimToken0 sevm b := by
    unfold skimToken0
    rw [swapTokenWord_adr]
  rw [← skimToken0_balTok] at inst notPrecompile notAdmin
  obtain ⟨hrun, hstk, hret, hgas⟩ := usdcReadLeg_spec (sevm := sevm) (B := skimCachedWorld sevm b)
    (S := skimRead0Stack sevm b) (M := getterInitMemory) (p := 128) (t := skimToken0 sevm b)
    (need := skimRead0Need sevm callGasT0) (skimRead0Need_gasFree sevm callGasT0) fork inst depth
    notPrecompile notAdmin (by simp only [skimRead0Stack, List.length_cons, List.length_nil]; omega)
    getterInitMemory_ptr.wf (by decide) fits room
  rw [balCallState_128 _ ht] at hrun
  rw [skimToken0_balTok] at hret inst
  change (skimUsdcRead0 sevm b callGasT0).1.returnData = _ at hret
  change (skimUsdcRead0 sevm b callGasT0).1.stack = _ at hstk
  have hcode : (skimCachedWorld sevm b).state.getCode (skimToken0 sevm b).toAdr = Proxy.code :=
    code_of_at (d := skimCachedWorld sevm b) inst.proxy
  obtain ⟨x, hx⟩ := skimUsdcRead0_skel sevm b callGasT0
  refine ⟨?_, ⟨?_, hrun, ?_, by rw [hret, B256.length_toBytes], hgas⟩, hret, ?_⟩
  · change ((skimCachedWorld sevm b).state.getCode (skimToken0 sevm b).toAdr).size.toB256 ≠ 0
    rw [hcode]
    exact proxy_code_size_word
  · rw [temporalAccountAccessBase_getCode]
    change ((skimCachedWorld sevm b).state.getCode (skimToken0 sevm b).toAdr).size.toB256 ≠ 0
    rw [hcode]
    exact proxy_code_size_word
  · rw [hstk]
    unfold balRest
    rw [ht]
    rfl
  · rw [hx]
    rfl

/-- **Skim's USDC `transfer` leg's spec (token0 = USDC), frame level** (from
`usdcTransferCall_spec`, as `skimWethLeg0_spec`): `SkimForwardEnv.tenv0` at the pinned values.
`U` is the frame's universe (the history's, extended by the recipient's row). -/
theorem skimUsdcLeg0_spec {sevm : Sevm} {b qd0 : Devm} {callGasQ1 : Nat} {U : Usdc.Key → Prop}
    (fork : CoveredFork sevm.benvStat.fork) (nonstatic : sevm.isStatic = false)
    (depth : 2 ≤ sevm.depth)
    (inst : Usdc.UsdcInstalled (skimToken0 sevm b).toAdr qd0.state)
    (finv : FootCore U (qd0.state.getStor (skimToken0 sevm b).toAdr))
    (notPrecompile : sevm.benvStat.rules.isPrecomp (skimToken0 sevm b).toAdr = false)
    (kPair : U (.bal sevm.currentTarget)) (kTo : U (.bal (skimToWord sevm).toAdr))
    (notAdmin : sevm.currentTarget ≠ Usdc.adminOf qd0.state (skimToken0 sevm b).toAdr)
    (ok : UsdcTransferOk (Usdc.ledger U (qd0.state.getStor (skimToken0 sevm b).toAdr))
      sevm.currentTarget (skimToWord sevm).toAdr (skimLegAmount sevm b qd0).toNat)
    (balance : (skimLegAmount sevm b qd0).toNat ≤
      (Usdc.ledger U (qd0.state.getStor (skimToken0 sevm b).toAdr)).bal sevm.currentTarget)
    (fits : (skimUsdcLeg0 sevm b qd0 callGasQ1).2 < 2 ^ 256)
    (room : skimUsdcLeg0Budget sevm b qd0 ≤
      except64th (skimUsdcLeg0Need sevm b qd0 callGasQ1 + skimUsdcLeg0Used sevm b qd0)) :
    SwapTransferCallForward sevm qd0 (skimLegStack sevm b) (skimLegMem sevm qd0)
      (skimLegMem sevm qd0).size 128 (skimLegAmount sevm b qd0) (skimToWord sevm) (skimToken0 sevm b)
      0x1a2b (skimUsdcLeg0 sevm b qd0 callGasQ1).2
      (skimLeg0Next sevm b qd0 callGasQ1 (skimUsdcLeg0 sevm b qd0 callGasQ1).1)
      (skimUsdcLeg0 sevm b qd0 callGasQ1).1 := by
  rw [← skimToken0_mask] at inst finv notPrecompile notAdmin ok balance
  have spec := usdcTransferCall_spec (sevm := sevm) (W := qd0) (L := skimLegStack sevm b)
    (M := skimLegMem sevm qd0) (p := 128) (amount := skimLegAmount sevm b qd0)
    (toWord := skimToWord sevm) (token := skimToken0 sevm b) (rho := 0x1a2b)
    (cg := skimUsdcLeg0Need sevm b qd0 callGasQ1 + skimUsdcLeg0Charge sevm b qd0) (U := U)
    fork inst finv nonstatic depth notPrecompile
    (by simp only [skimLegStack, List.length_cons, List.length_nil]; omega)
    (burnMem1_wf sevm qd0) (by decide) (by decide) kPair kTo notAdmin ok balance fits
    (by unfold skimUsdcLeg0Charge; omega)
    (by
      have e : skimUsdcLeg0Need sevm b qd0 callGasQ1 + skimUsdcLeg0Charge sevm b qd0 -
          xferExt qd0 (skimLegStack sevm b) (skimLegMem sevm qd0) 128 (skimLegAmount sevm b qd0)
            (skimToWord sevm) (skimToken0 sevm b) 0x1a2b -
          xferAcc qd0 (skimToken0 sevm b) =
          skimUsdcLeg0Need sevm b qd0 callGasQ1 + skimUsdcLeg0Used sevm b qd0 := by
        unfold skimUsdcLeg0Charge; omega
      rw [e]
      exact room)
  obtain ⟨hrun, hstk, hret, hgas⟩ := spec
  have hskel : usdcTransferCall sevm qd0 (skimLegStack sevm b) (skimLegMem sevm qd0) 128
      (skimLegAmount sevm b qd0) (skimToWord sevm) (skimToken0 sevm b) 0x1a2b
      (skimUsdcLeg0Need sevm b qd0 callGasQ1 + skimUsdcLeg0Charge sevm b qd0) =
      (skimUsdcLeg0Skel sevm b qd0).withGasLeft _ :=
    usdcTransferCallAt_eq _ _ _ _ _ _ _ _ _ _ _ _ _
  have hret' : (skimUsdcLeg0 sevm b qd0 callGasQ1).1.returnData = B256.toBytes 1 := hret
  refine ⟨hrun, hstk, Or.inr (by rw [hret']; exact one_reply_accepted), ?_⟩
  change (usdcTransferCall sevm qd0 (skimLegStack sevm b) (skimLegMem sevm qd0) 128
      (skimLegAmount sevm b qd0) (skimToWord sevm) (skimToken0 sevm b) 0x1a2b
      (skimUsdcLeg0Need sevm b qd0 callGasQ1 + skimUsdcLeg0Charge sevm b qd0)).gasLeft =
    skimLeg0Next sevm b qd0 callGasQ1 (usdcTransferCall sevm qd0 (skimLegStack sevm b)
      (skimLegMem sevm qd0) 128 (skimLegAmount sevm b qd0) (skimToWord sevm) (skimToken0 sevm b)
      0x1a2b (skimUsdcLeg0Need sevm b qd0 callGasQ1 + skimUsdcLeg0Charge sevm b qd0)) +
    safeTransferPostCharge (skimLegMem sevm qd0).size 128
      (usdcTransferCall sevm qd0 (skimLegStack sevm b) (skimLegMem sevm qd0) 128
        (skimLegAmount sevm b qd0) (skimToWord sevm) (skimToken0 sevm b) 0x1a2b
        (skimUsdcLeg0Need sevm b qd0 callGasQ1 + skimUsdcLeg0Charge sevm b qd0)).returnData
  rw [hgas]
  conv => rhs; rw [hskel, skimLeg0Next_withGasLeft, Devm.withGasLeft_returnData]
  have hn : skimUsdcLeg0Need sevm b qd0 callGasQ1 =
      skimLeg0Next sevm b qd0 callGasQ1 (skimUsdcLeg0Skel sevm b qd0) +
        safeTransferPostCharge (skimLegMem sevm qd0).size 128
          (skimUsdcLeg0Skel sevm b qd0).returnData := rfl
  rw [← hn]
  unfold skimUsdcLeg0Charge skimUsdcLeg0Used
  omega

end Blanc.Composition.UniswapV2PairUsdcWeth9
