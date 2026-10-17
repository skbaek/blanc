import Blanc.Composition.UniswapV2PairUsdcWeth9LegsBalLive
import Blanc.Composition.UniswapV2PairUsdcWeth9LegsSwap0

/-!
# The swap's post-callback USDC `balanceOf` STATICCALL and read leg (§10c, U9a)

The USDC analogue of `wethBalanceCall`: the Pair's staged `balanceOf(pair)` `STATICCALL` (the
token-neutral `balCallState`, `balParent`, `balMsg`, `balExt`, `balAcc`, `balSplit`) into the USDC
proxy, whose child frame is the gas-exact proxy frame of `balanceOf` (`usdc_balance_frame`).
`usdcReadLeg` runs it at the call gas a caller's need fixes; `swapUsdcRead0` is the swap's first
post-callback query (USDC = token0), and `usdcRead0Skel` its gas-free skeleton, which WETH9's
second query reads.
-/

namespace Blanc.Composition.UsdcLive

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc Blanc.Lift.UniswapV2Pair
  Blanc.Composition.UniswapV2PairWeth9Joint

section Balance

variable (sevm : Sevm) (B : Devm) (S : List B256) (M : Mem) (p t : B256)

/-- The query's child environment (gas-free). -/
abbrev bChildS : Sevm := initSevm (balMsg sevm B S M p t 0 0 0)

/-- The query's child base (gas-free). -/
abbrev bChildB : Devm := initDevm (balMsg sevm B S M p t 0 0 0)

/-- USDC's exact charge for the child's `balanceOf` frame through the proxy. -/
noncomputable def usdcBalUsed : Nat := proxyBalCost (bChildS sevm B S M p t) (bChildB sevm B S M p t)

/-- The gas USDC's `balanceOf` child needs forwarded. -/
noncomputable def usdcBalNeed : Nat := usdcBalBudget (bChildS sevm B S M p t) (bChildB sevm B S M p t)

/-- The resumed parent at popped gas `g`, charge `k`, forwarded `f`, child gas left `r`. -/
noncomputable def usdcBalanceCallAt (g k f r : Nat) : Devm :=
  callChildPost (balParent sevm B S M p t g k)
    (proxyBalPost (initSevm (balMsg sevm B S M p t g k f)) (bChildB sevm B S M p t) r)
    p.toNat (32 : B256).toNat

/-- **The Pair's USDC `balanceOf` STATICCALL at call gas `cg`.** -/
noncomputable def usdcBalanceCall (cg : Nat) : Devm :=
  usdcBalanceCallAt sevm B S M p t cg ((balSplit sevm B S M p t cg).1 + balExt sevm B S M p t)
    (balSplit sevm B S M p t cg).2 ((balSplit sevm B S M p t cg).2 - usdcBalUsed sevm B S M p t)

/-- The gas-free skeleton. -/
noncomputable def usdcBalanceSkel : Devm :=
  callChildPost (balParent sevm B S M p t 0 0)
    (proxyBalPost (bChildS sevm B S M p t) (bChildB sevm B S M p t) 0) p.toNat (32 : B256).toNat

theorem usdcBalanceCallAt_eq (g k f r : Nat) :
    usdcBalanceCallAt sevm B S M p t g k f r =
      (usdcBalanceSkel sevm B S M p t).withGasLeft (g - k + r) := by
  unfold usdcBalanceCallAt usdcBalanceSkel
  rw [balMsg_sevm, proxyBalPost_gasField, balParent_eq, proxyBalPost_reframe _ _ r,
    callChildPost_withGasLeft]

end Balance

section BalanceSpec

variable {sevm : Sevm} {B : Devm} {S : List B256} {M : Mem} {p t : B256}

theorem usdc_bal_accessDelegation (cg : Nat) (hcode : B.state.getCode (balTok t) = Proxy.code) :
    accessDelegation (addAccessedAddress (balPopped sevm B S M p t cg) (balTok t)) (balTok t) =
      ⟨false, balTok t, B.state.getCode (balTok t), 0, balWarm sevm B S M p t cg⟩ := by
  unfold accessDelegation balWarm balPopped
  rw [addAccessedAddress_setMach_state, UniswapV2PairWeth9Joint.temporalAccountAccessBase_state]
  dsimp only
  rw [hcode, Blanc.Lift.Usdc.proxy_undelegated]

/-- **The Pair's USDC `balanceOf` STATICCALL at the call gas USDC's charge fixes.**  USDC installed
at the token, no precompile there, two levels of call depth left, the Pair not USDC's admin, a
well-formed request memory, and the child's budget after the 63/64 rule: the STATICCALL resumes
with the success flag, the Pair's USDC balance bits as the reply, and `cg` less the access charge,
the expansion and USDC's exact charge. -/
theorem usdcBalanceCall_spec {cg : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (inst : UsdcInstalled (balTok t) B.state)
    (hdepth : 2 ≤ sevm.depth) (hprec : sevm.benvStat.rules.isPrecomp (balTok t) = false)
    (notAdmin : sevm.currentTarget ≠ adminOf B.state (balTok t))
    (hroom : S.length < 1018) (wf : Mem.Wf M) (width : p.toNat + 260 < 2 ^ 256)
    (hgw : cg < 2 ^ 256)
    (hcharge : balAcc B t + balExt sevm B S M p t ≤ cg)
    (hfwd : usdcBalNeed sevm B S M p t ≤ except64th (cg - balExt sevm B S M p t - balAcc B t)) :
    Ninst.RunCompiled sevm (balCallState sevm B S M p t cg) (.exec .staticcall)
        (usdcBalanceCall sevm B S M p t cg) ∧
      (usdcBalanceCall sevm B S M p t cg).stack = 1 :: balRest S p t ∧
      (usdcBalanceCall sevm B S M p t cg).returnData =
        (Nat.toB256 (balanceBits ((B.state.getStor (balTok t)).get (balSlot sevm.currentTarget)))).toBytes ∧
      (usdcBalanceCall sevm B S M p t cg).gasLeft =
        cg - (balAcc B t + balExt sevm B S M p t + usdcBalUsed sevm B S M p t) := by
  have hbu : usdcBalUsed sevm B S M p t ≤ usdcBalNeed sevm B S M p t := by
    unfold usdcBalUsed usdcBalNeed usdcBalBudget; omega
  generalize hext : balExt sevm B S M p t = ext at hcharge hfwd ⊢
  generalize hacc : balAcc B t = acc at hcharge hfwd ⊢
  generalize hused : usdcBalUsed sevm B S M p t = used at hbu ⊢
  generalize hbud : usdcBalNeed sevm B S M p t = bud at hfwd hbu
  generalize hfw : except64th (cg - ext - acc) = fwd at hfwd
  have hfwle : fwd ≤ cg - ext - acc := by rw [← hfw]; unfold except64th; omega
  have hsplit : balSplit sevm B S M p t cg = ⟨fwd + acc, fwd⟩ := by
    unfold balSplit
    rw [hext, hacc]
    unfold calculateMsgCallGas
    simp only [show ¬ cg < acc + ext from by omega, ↓reduceIte, hfw]
    rw [Nat.min_eq_right (by omega), Nat.add_zero]
  -- the child
  have hdata := balMsg_data (sevm := sevm) (B := B) (S := S) (t := t) cg (fwd + acc + ext) fwd wf width
  obtain ⟨hw4, hlen⟩ := dataWord_oneWord (e := initSevm (balMsg sevm B S M p t cg (fwd + acc + ext) fwd))
    hdata
  have hsel := selector_eq_of_data_eq_abiSelectorBytes_append
    (sevm := initSevm (balMsg sevm B S M p t cg (fwd + acc + ext) fwd)) (selected := 0x70a08231)
    (by decide) hdata
  have hS := balMsg_sevm sevm B S M p t cg (fwd + acc + ext) fwd
  have hB := balMsg_devm sevm B S M p t cg (fwd + acc + ext) fwd
  have hstate : (bChildB sevm B S M p t).state = B.state := by
    show (initDevm (balMsg sevm B S M p t 0 0 0)).state = _
    show (balParent sevm B S M p t 0 0).state = _
    unfold balParent balWarm balPopped
    rw [callSpawnParent_state, addAccessedAddress_setMach_state, UniswapV2PairWeth9Joint.temporalAccountAccessBase_state]
  have hprox : B.state.getCode (balTok t) = Proxy.code := code_of_at (d := B) inst.proxy
  have frame := usdc_balance_frame (P := balTok t)
    (sevm := initSevm (balMsg sevm B S M p t cg (fwd + acc + ext) fwd))
    (pre := bChildB sevm B S M p t) (G := fwd) rfl (by rw [hstate]; rfl) (by rw [hstate]; exact inst)
    hfork rfl (by omega) (by omega) hsel (by rw [hstate]; exact notAdmin)
    (by
      have e : usdcBalBudget (initSevm (balMsg sevm B S M p t cg (fwd + acc + ext) fwd))
          (bChildB sevm B S M p t) = bud := by
        rw [← hbud, hS]
        unfold usdcBalNeed
        rw [usdcBalBudget_gasField]
      rw [e]; exact hfwd)
    (by omega) (by show sevm.depth - 1 ≠ 0; omega)
  have hcost : proxyBalCost (initSevm (balMsg sevm B S M p t cg (fwd + acc + ext) fwd))
      (bChildB sevm B S M p t) = used := by
    rw [← hused, hS, proxyBalCost_gasField]; rfl
  rw [hcost, ← hB] at frame
  obtain ⟨crun⟩ := frame
  have hexec := (exec_iff_exec_eq 0 _ _ _).mp ⟨crun⟩
  have hcross := Ninst.runCompiled_staticcall_child
    (devm := balCallState sevm B S M p t cg) (gw := cg.toB256) (tw := swapTokenWord t)
    (iiw := p) (isw := 36) (oiw := p) (osw := 32) (s := balRest S p t) (dp := false)
    (dadr := balTok t) (code := B.state.getCode (balTok t)) (dgc := 0)
    (d1 := balWarm sevm B S M p t cg) (ext := ext) (acc := acc) (mcc := fwd + acc) (mcs := fwd)
    (cpost := proxyBalPost (initSevm (balMsg sevm B S M p t cg (fwd + acc + ext) fwd))
      (bChildB sevm B S M p t) (fwd - used))
    hfork rfl ?ext ?del ?acc ?split ?gas (by omega) hprec ?room hexec
    (by rw [proxyBalPost_error]; rfl)
  case ext =>
    rw [← hext, balCallState_pop]
    exact setMach_extCost _ _ _ _ _ _ _
  case del =>
    rw [balCallState_pop]
    exact usdc_bal_accessDelegation cg hprox
  case acc => rw [← hacc]; rfl
  case split =>
    unfold balWarm balPopped
    rw [B256.toNat_toB256_of_lt hgw, addAccessedAddress_setMach_gasLeft, ← hsplit]
    unfold balSplit
    rw [hext, hacc]
  case gas =>
    unfold balWarm balPopped
    rw [addAccessedAddress_setMach_gasLeft]
    change fwd + acc + ext ≤ cg
    omega
  case room =>
    simp only [balRest, List.length_cons]
    omega
  have hd : usdcBalanceCall sevm B S M p t cg =
      callChildPost (callSpawnParent (balWarm sevm B S M p t cg) (fwd + acc + ext) p.toNat
        (36 : B256).toNat p.toNat (32 : B256).toNat)
        (proxyBalPost (initSevm (balMsg sevm B S M p t cg (fwd + acc + ext) fwd))
          (bChildB sevm B S M p t) (fwd - used))
        p.toNat (32 : B256).toNat := by
    unfold usdcBalanceCall usdcBalanceCallAt
    rw [hsplit, hext, hused]
    rfl
  rw [hd]
  refine ⟨hcross, ?_, ?_, ?_⟩
  · rw [callChildPost_stack, callSpawnParent_stack]
    unfold balWarm balPopped
    rw [addAccessedAddress_setMach_stack]
  · rw [callChildPost_returnData, proxyBalPost_output, balWord_eq (by omega) hw4]
    show (Nat.toB256 (balanceBits (((bChildB sevm B S M p t).state.getStor (balTok t)).get
      (balSlot sevm.currentTarget)))).toBytes = _
    rw [hstate]
  · rw [callChildPost_gasLeft, callSpawnParent_gasLeft, proxyBalPost_gasLeft]
    unfold balWarm balPopped
    rw [addAccessedAddress_setMach_gasLeft]
    change cg - (fwd + acc + ext) + (fwd - used) = cg - (acc + ext + used)
    omega

end BalanceSpec

/-! ## The read leg at a caller-fixed need -/

section ReadLeg

variable (sevm : Sevm) (B : Devm) (S : List B256) (M : Mem) (p t : B256) (need : Devm → Nat)

/-- The call gas of a USDC `balanceOf` query whose caller needs `need d` left after it. -/
noncomputable def usdcReadLegGas : Nat :=
  need (usdcBalanceSkel sevm B S M p t) + (balAcc B t + balExt sevm B S M p t + usdcBalUsed sevm B S M p t)

/-- **The USDC `balanceOf(pair)` `STATICCALL` at the call gas the caller's need fixes.** -/
noncomputable def usdcReadLeg : Devm × Nat :=
  (usdcBalanceCall sevm B S M p t (usdcReadLegGas sevm B S M p t need), usdcReadLegGas sevm B S M p t need)

end ReadLeg

/-- **Spec of the USDC read leg.** -/
theorem usdcReadLeg_spec {sevm : Sevm} {B : Devm} {S : List B256} {M : Mem} {p t : B256}
    {need : Devm → Nat} (gasFree : ∀ d x, need (d.withGasLeft x) = need d)
    (fork : CoveredFork sevm.benvStat.fork) (inst : UsdcInstalled (balTok t) B.state)
    (depth : 2 ≤ sevm.depth) (notPrecompile : sevm.benvStat.rules.isPrecomp (balTok t) = false)
    (notAdmin : sevm.currentTarget ≠ adminOf B.state (balTok t))
    (stackRoom : S.length < 1018) (wf : Mem.Wf M) (width : p.toNat + 260 < 2 ^ 256)
    (fits : (usdcReadLeg sevm B S M p t need).2 < 2 ^ 256)
    (room : usdcBalNeed sevm B S M p t ≤
      except64th (need (usdcBalanceSkel sevm B S M p t) + usdcBalUsed sevm B S M p t)) :
    Ninst.RunCompiled sevm (balCallState sevm B S M p t (usdcReadLeg sevm B S M p t need).2)
        (.exec .staticcall) (usdcReadLeg sevm B S M p t need).1 ∧
      (usdcReadLeg sevm B S M p t need).1.stack = 1 :: balRest S p t ∧
      (usdcReadLeg sevm B S M p t need).1.returnData =
        (Nat.toB256 (balanceBits ((B.state.getStor (balTok t)).get (balSlot sevm.currentTarget)))).toBytes ∧
      (usdcReadLeg sevm B S M p t need).1.gasLeft = need (usdcReadLeg sevm B S M p t need).1 := by
  have spec := usdcBalanceCall_spec (sevm := sevm) (B := B) (S := S) (M := M) (p := p) (t := t)
    (cg := usdcReadLegGas sevm B S M p t need) fork inst depth notPrecompile notAdmin stackRoom wf
    width fits (by unfold usdcReadLegGas; omega)
    (by
      have e : usdcReadLegGas sevm B S M p t need - balExt sevm B S M p t - balAcc B t =
          need (usdcBalanceSkel sevm B S M p t) + usdcBalUsed sevm B S M p t := by
        unfold usdcReadLegGas; omega
      rw [e]
      exact room)
  obtain ⟨hrun, hstk, hret, hgas⟩ := spec
  refine ⟨hrun, hstk, hret, ?_⟩
  have hskel : usdcBalanceCall sevm B S M p t (usdcReadLegGas sevm B S M p t need) =
      (usdcBalanceSkel sevm B S M p t).withGasLeft _ :=
    usdcBalanceCallAt_eq _ _ _ _ _ _ _ _ _ _
  change (usdcBalanceCall sevm B S M p t (usdcReadLegGas sevm B S M p t need)).gasLeft =
    need (usdcBalanceCall sevm B S M p t (usdcReadLegGas sevm B S M p t need))
  rw [hgas]
  conv => rhs; rw [hskel, gasFree]
  unfold usdcReadLegGas
  omega

theorem proxy_code_size_word : Proxy.code.size.toB256 ≠ 0 := by
  intro h
  have hlt : Proxy.code.size < 2 ^ 256 := by decide +kernel
  have hne : Proxy.code.size ≠ 0 := by decide +kernel
  have := congrArg B256.toNat h
  rw [B256.toNat_toB256_of_lt hlt] at this
  exact hne this

end Blanc.Composition.UsdcLive

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair Blanc.Lift.Usdc
  Blanc.Composition.UniswapV2PairWeth9Joint Blanc.Composition.UsdcLive

set_option linter.unusedVariables false in
/-- The gas-free skeleton of the USDC post-callback `balanceOf` result (the first query, staged
over the join world `d`). -/
noncomputable def usdcRead0Skel (sevm : Sevm) (d : Devm) (M : Mem) (n : Nat) (p : B256)
    (w : SwapCutWords) (ρ : B256) (R : List B256) : Devm :=
  usdcBalanceSkel sevm d (read0Stack w ρ R) M p w.token0

set_option linter.unusedVariables false in
/-- The USDC post-callback `balanceOf(pair)` STATICCALL (token0 = USDC), given the gas left for
WETH9's read (`callGas1`). -/
noncomputable def swapUsdcRead0 (sevm : Sevm) (d : Devm) (M : Mem) (n : Nat) (p : B256)
    (w : SwapCutWords) (ρ : B256) (R : List B256) (G callGas1 : Nat) : Devm × Nat :=
  usdcReadLeg sevm d (read0Stack w ρ R) M p w.token0 (read0Need n p w callGas1)

/-- **The swap's first USDC read leg (USDC = token0), frame level.**  At the post-callback join
world `d`: USDC installed at token0 there, not a precompile, two levels of call depth left, the Pair
not USDC's admin, a well-formed memory, the pointer's width bound, stack room, the call gas a word,
and the child's budget.  Then `swapUsdcRead0` is the first balance record, its reply is the Pair's
USDC balance bits at `d`, and its result is the skeleton up to gas. -/
theorem swapUsdcRead0_spec {sevm : Sevm} {d : Devm} {M : Mem} {n : Nat} {p : B256}
    {w : SwapCutWords} {ρ : B256} {R : List B256} {G callGas1 : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (depth : 2 ≤ sevm.depth)
    (inst : UsdcInstalled (swapTokenWord w.token0).toAdr d.state)
    (notPrecompile : sevm.benvStat.rules.isPrecomp (swapTokenWord w.token0).toAdr = false)
    (notAdmin : sevm.currentTarget ≠ adminOf d.state (swapTokenWord w.token0).toAdr)
    (wf : Mem.Wf M) (width : p.toNat + 260 < 2 ^ 256)
    (stackRoom : (swapCutTail w ρ R).length < 1014)
    (fits : (swapUsdcRead0 sevm d M n p w ρ R G callGas1).2 < 2 ^ 256)
    (room : usdcBalNeed sevm d (read0Stack w ρ R) M p w.token0 ≤
      except64th (read0Need n p w callGas1 (usdcRead0Skel sevm d M n p w ρ R) +
        usdcBalUsed sevm d (read0Stack w ρ R) M p w.token0)) :
    SwapBalanceEnv sevm d M p w.token0 (w.token1 :: w.token0 :: 0 :: 0 :: swapCutTail w ρ R)
      (swapUsdcRead0 sevm d M n p w ρ R G callGas1).1 (swapUsdcRead0 sevm d M n p w ρ R G callGas1).2
      (callGas1 + 5 + swapRequestCharge (swapUsdcRead0 sevm d M n p w ρ R G callGas1).1
        (swapRequestSize n p) p w.token1 83 + 21) ∧
    (swapUsdcRead0 sevm d M n p w ρ R G callGas1).1.returnData =
      (Nat.toB256 (balanceBits ((d.state.getStor (swapTokenWord w.token0).toAdr).get
        (balSlot sevm.currentTarget)))).toBytes ∧
    (swapUsdcRead0 sevm d M n p w ρ R G callGas1).1 =
      (usdcRead0Skel sevm d M n p w ρ R).withGasLeft
        (swapUsdcRead0 sevm d M n p w ρ R G callGas1).1.gasLeft := by
  obtain ⟨hrun, hstk, hret, hgas⟩ := usdcReadLeg_spec (sevm := sevm) (B := d)
    (S := read0Stack w ρ R) (M := M) (p := p) (t := w.token0) (need := read0Need n p w callGas1)
    (read0Need_gasFree n p w callGas1) fork inst depth notPrecompile notAdmin
    (by simp only [read0Stack, List.length_cons]; omega) wf width fits room
  have hcode : (d.getCode (swapTokenWord w.token0).toAdr).size.toB256 ≠ 0 := by
    change (d.state.getCode (swapTokenWord w.token0).toAdr).size.toB256 ≠ 0
    have hc : d.state.getCode (swapTokenWord w.token0).toAdr = Proxy.code :=
      code_of_at (d := d) inst.proxy
    rw [hc]
    exact proxy_code_size_word
  have hskel := usdcBalanceCallAt_eq sevm d (read0Stack w ρ R) M p w.token0
    (usdcReadLegGas sevm d (read0Stack w ρ R) M p w.token0 (read0Need n p w callGas1))
    ((balSplit sevm d (read0Stack w ρ R) M p w.token0 (usdcReadLegGas sevm d (read0Stack w ρ R) M p
      w.token0 (read0Need n p w callGas1))).1 + balExt sevm d (read0Stack w ρ R) M p w.token0)
    (balSplit sevm d (read0Stack w ρ R) M p w.token0 (usdcReadLegGas sevm d (read0Stack w ρ R) M p
      w.token0 (read0Need n p w callGas1))).2
    ((balSplit sevm d (read0Stack w ρ R) M p w.token0 (usdcReadLegGas sevm d (read0Stack w ρ R) M p
      w.token0 (read0Need n p w callGas1))).2 - usdcBalUsed sevm d (read0Stack w ρ R) M p w.token0)
  unfold swapUsdcRead0
  refine ⟨⟨hcode, hrun, hstk, by rw [hret, B256.length_toBytes], hgas⟩, hret, ?_⟩
  show usdcBalanceCall _ _ _ _ _ _ _ = _
  unfold usdcBalanceCall
  rw [hskel]
  rfl

end Blanc.Composition.UniswapV2PairUsdcWeth9
