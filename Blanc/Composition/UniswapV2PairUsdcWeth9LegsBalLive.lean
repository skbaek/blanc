import Blanc.Composition.UniswapV2PairUsdcWeth9LegsBalFrame

/-!
# The USDC `balanceOf` frame from natural conditions (U9a)

USDC installed, the `balanceOf` selector over a one-word argument, no value, a caller other than
the admin word, call depth left, and gas within `usdcBalBudget`: the proxy's code runs to `RETURN`
at the gas-exact charge `proxyBalCost` and returns the queried account's balance bits.
-/

namespace Blanc.Composition.UsdcLive

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc Blanc.Composition.UsdcToken

local notation "m20" => Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]
local notation "l255" => Bytes.toB256 [0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

/-- The gas a USDC `balanceOf` frame needs: its exact charge, plus what keeps the child's need
after the proxy's 63/64 cut. -/
noncomputable def usdcBalBudget (sevm : Sevm) (pre : Devm) : Nat :=
  proxyBalCost sevm pre + childBalCost sevm pre / 63 + 1

theorem usdcBalBudget_gasField (s : Sevm) (pre : Devm) (f : Nat) :
    usdcBalBudget { s with gas := f } pre = usdcBalBudget s pre := by
  unfold usdcBalBudget
  rw [proxyBalCost_gasField, childBalCost_gasField]

theorem args32_of_len {n : Nat} (h : 36 ≤ n) (hn : n < 2 ^ 256) :
    B256.ltCheck (Nat.toB256 n - Bytes.toB256 [4]) (Bytes.toB256 [32]) = 0 := by
  have h4 : (Bytes.toB256 [4]).toNat = 4 := by decide
  have le : Bytes.toB256 [4] ≤ Nat.toB256 n := by
    apply B256.not_lt.mp
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hn, h4]
    omega
  apply ltCheck_zero_of_le
  rw [B256.toNat_sub_eq_of_le _ _ le, B256.toNat_toB256_of_lt hn, h4]
  have h32 : (Bytes.toB256 [32]).toNat = 32 := by decide
  rw [h32]
  omega

/-- The proxy's branch facts for a `balanceOf` call by a caller other than the admin word. -/
theorem proxyFacts_bal {sevm : Sevm} {pre : Devm} (len : 4 ≤ sevm.data.length)
    (hlen : sevm.data.length < 2 ^ 256) (sel : Blanc.Sevm.selector sevm = 0x70a08231)
    (adm : sevm.caller ≠ ((Devm.getStor pre sevm.currentTarget).get adminSlot).toAdr) :
    ProxyFacts sevm pre 0x70a08231 := by
  refine ⟨short_of_len len hlen, (dispatchWord_eq_selector sevm).trans sel, by decide, by decide,
    by decide, by decide, by decide, ?_⟩
  apply eqCheck_ne
  rw [Blanc.ff20_and_word, Blanc.ff20_and_word, Jaune.toAdr_toB256, gsv, pKA_eq]
  intro e
  exact adm (Adr.toB256_inj e)

/-- **The USDC `balanceOf` frame, end to end.** -/
theorem usdc_balance_frame {P : Adr} {sevm : Sevm} {pre : Devm} {G : Nat}
    (htarget : sevm.currentTarget = P) (hcode : sevm.code = pre.state.getCode P)
    (inst : UsdcInstalled P pre.state) (fork : CoveredFork sevm.benvStat.fork)
    (hvalue : sevm.value = 0) (len : 36 ≤ sevm.data.length) (hlen : sevm.data.length < 2 ^ 256)
    (sel : Blanc.Sevm.selector sevm = 0x70a08231) (hadm : sevm.caller ≠ adminOf pre.state P)
    (hbud : usdcBalBudget sevm pre ≤ G) (hG : G < 2 ^ 256) (depth : sevm.depth ≠ 0) :
    Nonempty (Exec 0 sevm (St pre [] Mem.empty G)
      (.ok (proxyBalPost sevm pre (G - proxyBalCost sevm pre)))) := by
  subst htarget
  have pf := proxyFacts_bal (sevm := sevm) (pre := pre) (by omega) hlen sel hadm
  have bf : BalFacts sevm :=
    ⟨hvalue, short_of_len (by omega) hlen, args32_of_len len hlen, (selector_word sevm).trans sel⟩
  have hdI := dI_eq (sevm := sevm) (pre := pre) inst.slot
  have hcodeI : (pBase sevm pre).state.getCode (dI sevm pre) = Impl.code := by
    rw [pBase_state, hdI]; exact Blanc.ExecutionTrace.bytes_eq_of_image inst.impl
  have hprec : sevm.benvStat.rules.isPrecomp (dI sevm pre) = false := by
    rw [hdI]
    exact propext ⟨fun h => (impl_not_precompile fork h).elim, fun h => (Bool.false_ne_true h).elim⟩
  have hfwd : childBalCost sevm pre ≤ dFwd sevm pre (balY sevm pre (G - proxyBalCost sevm pre)) := by
    unfold usdcBalBudget at hbud
    unfold dFwd balY except64th
    omega
  have hY : balY sevm pre (G - proxyBalCost sevm pre) < 2 ^ 256 := by
    unfold usdcBalBudget at hbud
    unfold balY
    unfold proxyBalCost at hbud ⊢
    omega
  have run := proxy_bal_run fork depth hlen pf bf hcodeI hprec hfwd hY
  have hcodeP : sevm.code = Proxy.code := hcode.trans (code_of_at (d := pre) inst.proxy)
  have hle : proxyBalCost sevm pre ≤ G := by unfold usdcBalBudget at hbud; omega
  rw [Nat.sub_add_cancel hle] at run
  exact lift_exact Proxy.cert_check Proxy.jumps_ok hcodeP fork ⟨_, rfl, run⟩

theorem proxyBalPost_gasLeft (s : Sevm) (pre : Devm) (X : Nat) : (proxyBalPost s pre X).gasLeft = X :=
  proxyPost_gasLeft _ _ _ _ _ _

theorem proxyBalPost_output (s : Sevm) (pre : Devm) (X : Nat) :
    (proxyBalPost s pre X).output = (balWord s pre).toBytes :=
  proxyPost_output _ _ _ _ _ _

theorem proxyBalPost_error (s : Sevm) (pre : Devm) (X : Nat) :
    (proxyBalPost s pre X).error = pre.error := by
  unfold proxyBalPost proxyPost
  rw [Devm.withOutput_error, Devm.memRead_error, St_error]
  show (pBase s pre).error = _
  unfold pBase
  rw [afterSload_error, afterSload_error]

/-- The word `balanceOf(a)` returns is `a`'s balance bits at the proxy's storage. -/
theorem balWord_eq {sevm : Sevm} {pre : Devm} {a : Adr} (hlen : sevm.data.length < 2 ^ 256)
    (ha : Sevm.dataWord sevm 4 = a.toB256) :
    balWord sevm pre = Nat.toB256 (balanceBits ((Devm.getStor pre sevm.currentTarget).get (balSlot a))) := by
  have hd := dMsg_data sevm pre 0 hlen
  have hw : Sevm.dataWord (initSevm (dMsg sevm pre 0)) (Bytes.toB256 [4]) = a.toB256 := by
    unfold Sevm.dataWord; rw [hd]; exact ha
  show l255 &&& (initDevm (dMsg sevm pre 0)).getStorVal sevm.currentTarget
    (mapSlot (m20 &&& (m20 &&& Sevm.dataWord (initSevm (dMsg sevm pre 0)) (Bytes.toB256 [4])))
      (Bytes.toB256 [9])) = _
  rw [hw, Blanc.ff20_and_word a.toB256, Jaune.toAdr_toB256, Blanc.ff20_and_word a.toB256, Jaune.toAdr_toB256, gsv]
  have hs : Devm.getStor (initDevm (dMsg sevm pre 0)) sevm.currentTarget =
      Devm.getStor pre sevm.currentTarget := by
    show Devm.getStor (pBase sevm pre) _ = _
    rw [Blanc.afterSload_getStor, Blanc.afterSload_getStor]
  rw [hs, lit9]
  apply B256.toNat_inj
  rw [l255_and_toNat, B256.toNat_toB256_of_lt (by
    have := Nat.mod_lt ((Devm.getStor pre sevm.currentTarget).get (balSlot a)).toNat
      (Nat.two_pow_pos 255)
    unfold balanceBits; omega)]
  rfl

end Blanc.Composition.UsdcLive
