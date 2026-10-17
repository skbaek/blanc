import Blanc.Composition.UniswapV2PairWeth9SwapLegs
import Blanc.Composition.UniswapV2PairWeth9Tx1
import Blanc.Lift.VyperNonreentrantDeployed.Token20.RunBalance

/-!
# The swap's post-callback `X.balanceOf(pair)` STATICCALL, as a function of the call gas

The closed instance's Pair has `token0 = X`, the synthetic Token20.  The first post-callback balance
query of its `swap` is a `STATICCALL` of `X.balanceOf(pair)`.  As for the WETH9 query
(`UniswapV2PairWeth9SwapLegsRead`), everything the `STATICCALL` leaves except its gas is fixed by the
world: `xBalanceCall … cg` is the resumed parent at call gas `cg`, built from Token20's
`balanceOf_runExact` exactly as the static crossing `Ninst.runCompiled_staticcall_child` builds it.
The staging (`balCallState`, `balExt`, `balAcc`, `balMsg`, …) is the token-neutral one of the WETH9
query.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Instance

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair Blanc.Composition.UniswapV2PairWeth9Joint
open Blanc.Lift.VyperNonreentrantDeployed.Token20 (balanceOfGas balanceOfPost balanceOf_runExact
  boHolder retPost)

section Balance

variable (sevm : Sevm) (B : Devm) (S : List B256) (M : Mem) (p t : B256)

/-- Token20's charge for the child's `balanceOf` frame. -/
def xBalUsed : Nat :=
  balanceOfGas (initSevm (balMsg sevm B S M p t 0 0 0)) (initDevm (balMsg sevm B S M p t 0 0 0))

/-- The resumed parent at popped gas `g`, charge `k`, forwarded `f`, child gas left `r`. -/
def xBalanceCallAt (g k f r : Nat) : Devm :=
  callChildPost (balParent sevm B S M p t g k)
    (balanceOfPost (initSevm (balMsg sevm B S M p t g k f)) (initDevm (balMsg sevm B S M p t g k f)) r)
    p.toNat (32 : B256).toNat

/-- **The swap's Token20 `balanceOf` STATICCALL at call gas `cg`.** -/
def xBalanceCall (cg : Nat) : Devm :=
  xBalanceCallAt sevm B S M p t cg ((balSplit sevm B S M p t cg).1 + balExt sevm B S M p t)
    (balSplit sevm B S M p t cg).2 ((balSplit sevm B S M p t cg).2 - xBalUsed sevm B S M p t)

/-- The gas-free skeleton. -/
def xBalanceSkel : Devm :=
  callChildPost (balParent sevm B S M p t 0 0)
    (balanceOfPost (initSevm (balMsg sevm B S M p t 0 0 0)) (initDevm (balMsg sevm B S M p t 0 0 0)) 0)
    p.toNat (32 : B256).toNat

end Balance

section Reframe

variable (s : Sevm) (f : Nat)

theorem retPost_setMach (b : Devm) (m : Mach) (S : List B256) (M : Mem) (G : Nat) (out : B256)
    (hsg : m.stateGas = b.stateGas) :
    retPost (b.setMach m) S M G out = retPost b S M G out := by
  unfold retPost St
  rw [Devm.setMach_setMach, Devm.stateGas_setMach, hsg]

theorem balanceOfPost_reframe (d : Devm) (f' r : Nat) :
    balanceOfPost { s with gas := f } (St d [] Mem.empty f') r = balanceOfPost s d r := by
  show retPost (afterSload s (St d [] Mem.empty f') (VyperNonreentrantDeployed.Token20.balSlot
      (boHolder s))) [Sevm.selector s] (Mem.empty.write 0 ((St d [] Mem.empty f').getStorVal
      s.currentTarget (VyperNonreentrantDeployed.Token20.balSlot (boHolder s))).toBytes) r
      ((St d [] Mem.empty f').getStorVal s.currentTarget
        (VyperNonreentrantDeployed.Token20.balSlot (boHolder s))) = _
  unfold St
  rw [afterSload_setMach, Devm.getStorVal_setMach]
  exact retPost_setMach _ _ _ _ _ _ (by rw [afterSload_stateGas])

theorem balanceOfGas_reframe (d : Devm) (f' : Nat) :
    balanceOfGas { s with gas := f } (St d [] Mem.empty f') = balanceOfGas s d := rfl

theorem retPost_gasLeft (b : Devm) (S : List B256) (M : Mem) (G G' : Nat) (out : B256) :
    retPost b S M G out = (retPost b S M G' out).withGasLeft G := rfl

end Reframe

section Skel

variable (sevm : Sevm) (B : Devm) (S : List B256) (M : Mem) (p t : B256)

end Skel

section Spec

variable {sevm : Sevm} {B : Devm} {S : List B256} {M : Mem} {p t : B256}

theorem xbal_accessDelegation (cg : Nat)
    (hcode : B.state.getCode (balTok t) = VyperNonreentrantDeployed.Token20.code) :
    accessDelegation (addAccessedAddress (balPopped sevm B S M p t cg) (balTok t)) (balTok t) =
      ⟨false, balTok t, B.state.getCode (balTok t), 0, balWarm sevm B S M p t cg⟩ := by
  unfold accessDelegation balWarm balPopped
  rw [addAccessedAddress_setMach_state, Lift.temporalAccountAccessBase_state]
  dsimp only
  rw [hcode, getDelegatedCodeAddress_token20]

/-- **The swap's Token20 `balanceOf` STATICCALL at the call gas Token20's charge fixes.**  Token20's
code at the token, no precompile there, call depth left, a well-formed request memory, and room
for the view after the 63/64 rule: the STATICCALL resumes with the success flag, the pair's balance
word as the reply, and `cg` less the access charge, the expansion and Token20's charge. -/
theorem xBalanceCall_spec {cg : Nat}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hcode : B.state.getCode (balTok t) = VyperNonreentrantDeployed.Token20.code)
    (hdepth : sevm.depth ≠ 0)
    (hprec : sevm.benvStat.rules.isPrecomp (balTok t) = false)
    (hroom : S.length < 1018) (wf : Mem.Wf M) (width : p.toNat + 260 < 2 ^ 256)
    (hgw : cg < 2 ^ 256)
    (hcharge : balAcc B t + balExt sevm B S M p t ≤ cg)
    (hfwd : xBalUsed sevm B S M p t ≤ except64th (cg - balExt sevm B S M p t - balAcc B t)) :
    Ninst.RunCompiled sevm (balCallState sevm B S M p t cg) (.exec .staticcall)
        (xBalanceCall sevm B S M p t cg) ∧
      (xBalanceCall sevm B S M p t cg).stack = 1 :: balRest S p t ∧
      (xBalanceCall sevm B S M p t cg).returnData =
        (B.getStorVal (balTok t)
          (VyperNonreentrantDeployed.Token20.balSlot sevm.currentTarget)).toBytes ∧
      (xBalanceCall sevm B S M p t cg).gasLeft =
        cg - (balAcc B t + balExt sevm B S M p t + xBalUsed sevm B S M p t) := by
  generalize hext : balExt sevm B S M p t = ext at hcharge hfwd ⊢
  generalize hacc : balAcc B t = acc at hcharge hfwd ⊢
  generalize hused : xBalUsed sevm B S M p t = used at hfwd ⊢
  generalize hfw : except64th (cg - ext - acc) = fwd at hfwd
  have hfwle : fwd ≤ cg - ext - acc := by rw [← hfw]; unfold except64th; omega
  have hsplit : balSplit sevm B S M p t cg = ⟨fwd + acc, fwd⟩ := by
    unfold balSplit
    rw [hext, hacc]
    unfold calculateMsgCallGas
    simp only [show ¬ cg < acc + ext from by omega, ↓reduceIte, hfw]
    rw [Nat.min_eq_right (by omega), Nat.add_zero]
  have hdata := balMsg_data (sevm := sevm) (B := B) (S := S) (t := t) cg (fwd + acc + ext) fwd wf width
  obtain ⟨hw4, -⟩ := dataWord_oneWord (e := initSevm (balMsg sevm B S M p t cg (fwd + acc + ext) fwd))
    hdata
  have hsel := selector_eq_of_data_eq_abiSelectorBytes_append
    (sevm := initSevm (balMsg sevm B S M p t cg (fwd + acc + ext) fwd)) (selected := 0x70a08231)
    (by decide) hdata
  have hUsed : balanceOfGas (initSevm (balMsg sevm B S M p t cg (fwd + acc + ext) fwd))
      (initDevm (balMsg sevm B S M p t cg (fwd + acc + ext) fwd)) = used := by
    rw [← hused, balMsg_sevm, balMsg_devm, balanceOfGas_reframe]
    rfl
  have hrun := balanceOf_runExact
    (sevm := initSevm (balMsg sevm B S M p t cg (fwd + acc + ext) fwd))
    (pre := initDevm (balMsg sevm B S M p t cg (fwd + acc + ext) fwd)) (G := fwd - used)
    hfork hsel rfl rfl
    (by
      rw [hUsed]
      change fwd = fwd - used + used
      omega)
  have hexec := (exec_iff_exec_eq 0 _ _ _).mp (lift_exact
    VyperNonreentrantDeployed.Token20.cert_check VyperNonreentrantDeployed.Token20.cert_jumpsOk
    (sevm := initSevm (balMsg sevm B S M p t cg (fwd + acc + ext) fwd)) hcode hfork hrun)
  have hcross := Ninst.runCompiled_staticcall_child
    (devm := balCallState sevm B S M p t cg) (gw := cg.toB256) (tw := swapTokenWord t)
    (iiw := p) (isw := 36) (oiw := p) (osw := 32) (s := balRest S p t) (dp := false)
    (dadr := balTok t) (code := B.state.getCode (balTok t)) (dgc := 0)
    (d1 := balWarm sevm B S M p t cg) (ext := ext) (acc := acc) (mcc := fwd + acc) (mcs := fwd)
    (cpost := balanceOfPost (initSevm (balMsg sevm B S M p t cg (fwd + acc + ext) fwd))
      (initDevm (balMsg sevm B S M p t cg (fwd + acc + ext) fwd)) (fwd - used))
    hfork rfl ?ext ?del ?acc ?split ?gas hdepth hprec ?room hexec ?err
  case ext =>
    rw [← hext, balCallState_pop]
    exact setMach_extCost _ _ _ _ _ _ _
  case del =>
    rw [balCallState_pop]
    exact xbal_accessDelegation cg hcode
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
  case err =>
    simp only [balanceOfPost, retPost, Devm.withOutput_error, Devm.memRead_error, St,
      Devm.setMach_error, afterSload_error]
    rfl
  have hd : xBalanceCall sevm B S M p t cg =
      callChildPost (callSpawnParent (balWarm sevm B S M p t cg) (fwd + acc + ext) p.toNat
        (36 : B256).toNat p.toNat (32 : B256).toNat)
        (balanceOfPost (initSevm (balMsg sevm B S M p t cg (fwd + acc + ext) fwd))
          (initDevm (balMsg sevm B S M p t cg (fwd + acc + ext) fwd)) (fwd - used))
        p.toNat (32 : B256).toNat := by
    unfold xBalanceCall xBalanceCallAt
    rw [hsplit, hext, hused]
    rfl
  rw [hd]
  refine ⟨hcross, ?_, ?_, ?_⟩
  · rw [callChildPost_stack, callSpawnParent_stack]
    unfold balWarm balPopped
    rw [addAccessedAddress_setMach_stack]
  · rw [callChildPost_returnData]
    simp only [balanceOfPost, retPost, Devm.withOutput_output]
    rw [boHolder, hw4, toAdr_toB256]
    unfold Devm.getStorVal Devm.getAcct
    change (((balParent sevm B S M p t cg (fwd + acc + ext)).state.get (balTok t)).stor.get
      (VyperNonreentrantDeployed.Token20.balSlot sevm.currentTarget)).toBytes = _
    unfold balParent balWarm balPopped
    rw [callSpawnParent_state, addAccessedAddress_setMach_state, Lift.temporalAccountAccessBase_state]
  · rw [callChildPost_gasLeft, callSpawnParent_gasLeft]
    change cg - (fwd + acc + ext) + (fwd - used) = cg - (acc + ext + used)
    omega

end Spec

end Blanc.Composition.UniswapV2PairWeth9Instance
