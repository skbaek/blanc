import Blanc.Composition.UniswapV2PairUsdcWeth9LegsBal
import Blanc.Composition.UniswapV2PairUsdcWeth9LegsCall

/-!
# The USDC `balanceOf` frame through the proxy, gas-exact (U9a)

The proxy prefix for selector `balanceOf`, its `DELEGATECALL` into the implementation's `balanceOf`
frame (`implBalW`), and the delegate tail, composed by `proxy_frame_run`; its charge reads no gas
field, and its result is fixed up to the gas left.
-/

namespace Blanc.Composition.UsdcLive

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc

theorem BalFacts.transport {s s' : Sevm} (f : BalFacts s) (hv : s'.value = s.value)
    (hd : s'.data = s.data) : BalFacts s' := by
  have hdw : Sevm.dataWord s' = Sevm.dataWord s := by
    funext i; unfold Sevm.dataWord; rw [hd]
  obtain ⟨f1, f2, f3, f4⟩ := f
  exact ⟨by rw [hv]; exact f1, by rw [hd]; exact f2, by rw [hd]; exact f3, by rw [hdw]; exact f4⟩

section Frame

variable (sevm : Sevm) (pre : Devm)

/-- The implementation `balanceOf` charge at the proxy's child (gas-free). -/
noncomputable abbrev childBalCost : Nat :=
  (implBalW (initSevm (dMsg sevm pre 0)) (initDevm (dMsg sevm pre 0))).1

/-- The word the implementation's `balanceOf` returns. -/
abbrev balWord : B256 := bWord (initSevm (dMsg sevm pre 0)) (initDevm (dMsg sevm pre 0))

/-- The gas at `_delegate`'s `DELEGATECALL` when `X` is left at the end. -/
noncomputable abbrev balY (X : Nat) : Nat :=
  X + tailW sevm pre (balWord sevm pre) + dAcc sevm pre + dExt sevm pre + childBalCost sevm pre

/-- **The exact charge of a USDC `balanceOf` frame through the proxy.** -/
noncomputable def proxyBalCost : Nat :=
  (proxyPreW sevm pre 0x70a08231).1 +
    (tailW sevm pre (balWord sevm pre) + dAcc sevm pre + dExt sevm pre + childBalCost sevm pre)

/-- The child's halting state in the frame with `X` left at the end. -/
noncomputable abbrev balChild (X : Nat) : Devm :=
  implBalPost (initSevm (dMsg sevm pre (balY sevm pre X))) (initDevm (dMsg sevm pre 0))
    (dFwd sevm pre (balY sevm pre X) - childBalCost sevm pre)

/-- The proxy frame of `balanceOf`'s halting state with `X` left. -/
noncomputable abbrev proxyBalPost (X : Nat) : Devm :=
  proxyPost sevm pre (balY sevm pre X) X (balChild sevm pre X) (balWord sevm pre)

end Frame

theorem implBalPost_gasLeft (s : Sevm) (b : Devm) (G : Nat) : (implBalPost s b G).gasLeft = G := rfl

theorem implBalPost_output (s : Sevm) (b : Devm) (G : Nat) :
    (implBalPost s b G).output = (bWord s b).toBytes := by
  unfold implBalPost; rw [Devm.withOutput_output]

theorem implBalPost_error (s : Sevm) (b : Devm) (G : Nat) : (implBalPost s b G).error = b.error := by
  unfold implBalPost
  rw [Devm.withOutput_error, Devm.memRead_error, St_error, afterSload_error]

/-- **The child `balanceOf` frame runs to its `RETURN`.** -/
theorem child_bal_exec {sevm : Sevm} {b : Devm} {Y : Nat} (fork : CoveredFork sevm.benvStat.fork)
    (hcode : (pBase sevm b).state.getCode (dI sevm b) = Impl.code)
    (facts : BalFacts (initSevm (dMsg sevm b Y))) (hfwd : childBalCost sevm b ≤ dFwd sevm b Y) :
    exec (initEvm (dMsg sevm b Y)) = .ok (implBalPost (initSevm (dMsg sevm b Y))
      (initDevm (dMsg sevm b 0)) (dFwd sevm b Y - childBalCost sevm b)) := by
  have hc : (implBalW (initSevm (dMsg sevm b Y)) (initDevm (dMsg sevm b 0))).1 =
      childBalCost sevm b := by
    rw [dMsg_sevm, implBalW_gas]
  have fork' : CoveredFork (initSevm (dMsg sevm b Y)).benvStat.fork := fork
  have run := (implBalW (initSevm (dMsg sevm b Y)) (initDevm (dMsg sevm b 0))).2 fork' facts
    (dFwd sevm b Y - childBalCost sevm b)
  rw [hc, Nat.sub_add_cancel hfwd, ← dMsg_devm] at run
  have hex := lift_exact Impl.cert_check Impl.jumps_ok hcode fork' ⟨_, rfl, run⟩
  exact (exec_iff_exec_eq _ _ _ _).mp hex

/-- **The USDC proxy frame of `balanceOf`, gas-exact.** -/
theorem proxy_bal_run {sevm : Sevm} {pre : Devm} {X : Nat} (fork : CoveredFork sevm.benvStat.fork)
    (depth : sevm.depth ≠ 0) (hlen : sevm.data.length < 2 ^ 256)
    (pf : ProxyFacts sevm pre 0x70a08231) (bf : BalFacts sevm)
    (hcode : (pBase sevm pre).state.getCode (dI sevm pre) = Impl.code)
    (hprec : sevm.benvStat.rules.isPrecomp (dI sevm pre) = false)
    (hfwd : childBalCost sevm pre ≤ dFwd sevm pre (balY sevm pre X))
    (hY : balY sevm pre X < 2 ^ 256) :
    SFunc.RunExact Proxy.cert.prog sevm (St pre [] Mem.empty (X + proxyBalCost sevm pre))
      Proxy.t_0000_c0 (.halted (proxyBalPost sevm pre X)) := by
  have hexec := child_bal_exec (sevm := sevm) (b := pre) (Y := balY sevm pre X) fork hcode
    (bf.transport rfl (dMsg_data sevm pre _ hlen)) hfwd
  have herr : (balChild sevm pre X).error = none := by
    rw [implBalPost_error]; rfl
  exact proxy_frame_run fork depth pf hcode hprec hY hfwd hexec herr
    (by rw [implBalPost_output]; rfl) (implBalPost_gasLeft _ _ _)

/-! ## The frame's charge and result read no gas field -/

theorem implBalPost_gasField (s : Sevm) (b : Devm) (f G : Nat) :
    implBalPost { s with gas := f } b G = implBalPost s b G := by
  simp only [implBalPost, implBalMem, bWord, bKey, bTo, UniswapV2PairWeth9Joint.afterSload_gasField,
    UniswapV2PairWeth9Joint.dataWord_gasField]

theorem implBalPost_reframe (s : Sevm) (b : Devm) (G : Nat) :
    implBalPost s b G = (implBalPost s b 0).withGasLeft G := by
  unfold implBalPost
  rw [St.memRead_snd, St.memRead_snd, St_reframe _ _ _ G, withOutput_withGasLeft]

theorem balY_gasField (s : Sevm) (pre : Devm) (f X : Nat) :
    balY { s with gas := f } pre X = balY s pre X := by
  exact congrArg (fun t => X + t + dAcc s pre + dExt s pre + childBalCost s pre)
    (dTailW_gas s f (dParent s pre 0) (pRest s pre) (dParent s pre 0).memory (balWord s pre))

theorem childBalCost_gasField (s : Sevm) (pre : Devm) (f : Nat) :
    childBalCost { s with gas := f } pre = childBalCost s pre := rfl

theorem proxyBalCost_gasField (s : Sevm) (pre : Devm) (f : Nat) :
    proxyBalCost { s with gas := f } pre = proxyBalCost s pre := by
  unfold proxyBalCost
  rw [proxyPreW_gas]
  exact congrArg _ (congrArg (· + _) (congrArg (· + _) (congrArg (· + _)
    (dTailW_gas s f _ _ _ _))))

theorem proxyBalPost_gasField (s : Sevm) (pre : Devm) (f X : Nat) :
    proxyBalPost { s with gas := f } pre X = proxyBalPost s pre X := by
  unfold proxyBalPost balChild
  rw [balY_gasField]
  rfl

theorem proxyBalPost_reframe (s : Sevm) (pre : Devm) (X : Nat) :
    proxyBalPost s pre X = (proxyBalPost s pre 0).withGasLeft X := by
  unfold proxyBalPost balChild proxyPost
  rw [dMsg_sevm s pre (balY s pre X), dMsg_sevm s pre (balY s pre 0), implBalPost_gasField,
    implBalPost_gasField, implBalPost_reframe _ _ (dFwd s pre (balY s pre X) - _),
    implBalPost_reframe _ _ (dFwd s pre (balY s pre 0) - _), dParent_reframe s pre (balY s pre X),
    dParent_reframe s pre (balY s pre 0), UniswapV2PairWeth9Joint.callChildPost_withGasLeft,
    UniswapV2PairWeth9Joint.callChildPost_withGasLeft, St_withGasLeft, St_withGasLeft,
    St.memRead_snd, St.memRead_snd, St_reframe _ _ _ X, withOutput_withGasLeft]
  simp only [implBalPost_gasField]
  rfl

end Blanc.Composition.UsdcLive
