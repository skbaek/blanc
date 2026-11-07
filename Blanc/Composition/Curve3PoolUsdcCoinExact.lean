import Blanc.Lift.UsdcExact
import Blanc.Composition.Curve3PoolUsdc22Coin
import Blanc.Composition.Curve3PoolCoinFloorKit

/-!
# USDC's exact profiles at the pool's call sites, proxy over `FiatTokenV2_2`

`usdc22_coinPushExact`, `usdc22_coinPullExact`, `usdc22_coinBalExact`: the proxy's charges (`proxyPreG`, the
`DELEGATECALL`'s access and expansion, `tailG`) with the implementation's closed cost at the delegate's entry,
and the canonical post. The bounded theorems' runs and ledgers are reused; `exec` being a function identifies them
with the exact run.
-/

namespace Blanc.Composition.UsdcLive

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc Blanc.Lift.Curve3Pool
open Blanc.Composition.Curve3PoolCalleeLive
open Blanc.Lift.AccumulatedWalk
open Blanc.Composition.Curve3Pool3CrvInstance (CoinLeaves prec_false rawCallOk_one
  transferSel_abi transferFromSel_abi balanceOfSel_abi)
open Blanc.Composition.Curve3PoolCoinChild Blanc.Composition.Curve3PoolCoinExactKit

/-! ## The proxy around any implementation cost -/

/-- A message into the proxy's exact cost: its charges around the `DELEGATECALL`, and the implementation's cost
`impl` at the delegate's entry, normalized. -/
noncomputable def proxyG (w : B256) (impl : Sevm → Devm → Nat) (s : Sevm) (p : Devm) : Nat :=
  proxyPreG s p + (tailG s (dParent s p 0) (pRest s p) (dParent s p 0).memory w + dAcc s p + dExt s p +
    impl (initSevm (dMsg s p 0)) (initDevm (dMsg s p 0)))

/-- The proxy's canonical post around the implementation's canonical post. -/
noncomputable def proxyCanon (w : B256) (P : Sevm → Devm → Devm) (s : Sevm) (p : Devm) : Devm :=
  proxyPost s p 0 0 (P (initSevm (dMsg s p 0)) (initDevm (dMsg s p 0))) w

section Reframe

variable (s : Sevm) (p : Devm) (F : Nat)

theorem pBase_reframe : pBase {s with gas := F} (p.withGasLeft F) = (pBase s p).withGasLeft F := by
  simp only [pBase, afterSload_withStaticGas, afterSload_withGasLeft]

theorem pI_reframe : pI {s with gas := F} (p.withGasLeft F) = pI s p := by
  simp only [pI, afterSload_withStaticGas, afterSload_withGasLeft, getStorVal_withGasLeft]

theorem pRest_reframe : pRest {s with gas := F} (p.withGasLeft F) = pRest s p := by
  simp only [pRest, pI_reframe, dataWord_withStaticGas]

theorem St_withGasLeft (d : Devm) (S : List B256) (M : Mem) (G H : Nat) : St (d.withGasLeft H) S M G = St d S M G := rfl

theorem dPop_reframe (Y : Nat) : dPop {s with gas := F} (p.withGasLeft F) Y = dPop s p Y := by
  simp only [dPop, pBase_reframe, pRest_reframe, St_withGasLeft]

theorem dExt_reframe : dExt {s with gas := F} (p.withGasLeft F) = dExt s p := by
  simp only [dExt, dPop_reframe]

theorem dAcc_reframe : dAcc {s with gas := F} (p.withGasLeft F) = dAcc s p := by
  simp only [dAcc, dI, pI_reframe, pBase_reframe]
  rfl

theorem dParent_reframe (Y : Nat) : dParent {s with gas := F} (p.withGasLeft F) Y = dParent s p Y := by
  simp only [dParent, dWarm, dFwd, dI, pI_reframe, dPop_reframe, dExt_reframe, dAcc_reframe]

theorem dMsg_reframe (Y : Nat) : dMsg {s with gas := F} (p.withGasLeft F) Y = dMsg s p Y := by
  simp only [dMsg, dParent_reframe, dFwd, dI, pI_reframe, dExt_reframe, dAcc_reframe, pBase_reframe]
  rfl

theorem proxyPreG_reframe : proxyPreG {s with gas := F} (p.withGasLeft F) = proxyPreG s p := by
  simp only [proxyPreG, preExt, pBase_reframe, St_withGasLeft, afterSload_withStaticGas, afterSload_withGasLeft,
    sloadCost_withStaticGas, sloadCost_withGasLeft, getStorVal_withGasLeft, dataWord_withStaticGas]

theorem proxyG_reframe (w : B256) (impl : Sevm → Devm → Nat) :
    proxyG w impl {s with gas := F} (p.withGasLeft F) = proxyG w impl s p := by
  simp only [proxyG, proxyPreG_reframe, dParent_reframe, pRest_reframe, dAcc_reframe, dExt_reframe, dMsg_reframe, tailG]

theorem proxyPost_canon {Y X : Nat} {C C0 : Devm} (w : B256) (hC : Devm.EqModGas C C0) :
    Devm.EqModGas (proxyPost {s with gas := F} (p.withGasLeft F) Y X C w) (proxyPost s p 0 0 C0 w) := by
  have hP : Devm.EqModGas (callChildPost (dParent s p Y) C (Bytes.toB256 [0]).toNat (Bytes.toB256 [0]).toNat)
      (callChildPost (dParent s p 0) C0 (Bytes.toB256 [0]).toNat (Bytes.toB256 [0]).toNat) := by
    refine Devm.EqModGas.callChildPost ?_ hC _ _
    apply Devm.EqModGas.of_normalized_eq
    rfl
  have hM : (dParent s p Y).memory = (dParent s p 0).memory := rfl
  unfold proxyPost
  rw [dParent_reframe, pRest_reframe, hM]
  exact memRet_congr hP

end Reframe

/-! ## The proxy's run, exactly -/

theorem proxyPost_gasLeft' (s : Sevm) (p : Devm) (Y X : Nat) (C : Devm) (w : B256) :
    (proxyPost s p Y X C w).gasLeft = X := rfl

/-- **A message into the proxy runs at `proxyG`**, its child at `impl`, with a post named. -/
theorem proxy_execE {msg : Msg} {I : ByteArray} {s w : B256} (F Cu : Nat) (hCu : Cu ≤ F)
    {impl : Sevm → Devm → Nat} {C : Nat → Devm}
    (himpl : ∀ s p G', impl {s with gas := G'} (p.withGasLeft G') = impl s p)
    (hcode : (initSevm msg).code = Proxy.code) (fork : ShanghaiOnwards (initSevm msg).benvStat.fork)
    (hdepth : (initSevm msg).depth ≠ 0)
    (hr : ProxyReady (initSevm msg) (initDevm msg) I)
    (hshort : 4 ≤ (initSevm msg).data.length) (hlen : (initSevm msg).data.length ≤ 100)
    (hsel : Blanc.Sevm.selector (initSevm msg) = s)
    (n1 : B256.eqCheck (Bytes.toB256 [54, 89, 207, 230]) s = 0)
    (n2 : B256.eqCheck (Bytes.toB256 [79, 30, 242, 134]) s = 0)
    (n3 : B256.eqCheck (Bytes.toB256 [92, 96, 218, 27]) s = 0)
    (n4 : B256.eqCheck (Bytes.toB256 [143, 40, 57, 112]) s = 0)
    (n5 : B256.eqCheck (Bytes.toB256 [248, 81, 164, 64]) s = 0)
    (hgas : F + F / 63 + 8300 ≤ (initDevm msg).gasLeft) (hG : (initDevm msg).gasLeft < 2 ^ 256)
    (hchild : ∀ Y, F ≤ dFwd (initSevm msg) (initDevm msg) Y →
      impl (initSevm (dMsg (initSevm msg) (initDevm msg) Y)) (initDevm (dMsg (initSevm msg) (initDevm msg) Y)) ≤ Cu ∧
      exec (initEvm (dMsg (initSevm msg) (initDevm msg) Y)) = .ok (C Y) ∧ (C Y).error = none ∧
        (C Y).output = w.toBytes ∧
        (C Y).gasLeft = dFwd (initSevm msg) (initDevm msg) Y -
          impl (initSevm (dMsg (initSevm msg) (initDevm msg) Y)) (initDevm (dMsg (initSevm msg) (initDevm msg) Y))) :
    proxyG w impl (initSevm msg) (initDevm msg) ≤ Cu + 8300 ∧
    exec (initEvm msg) = .ok (proxyPost (initSevm msg) (initDevm msg)
      (frameYAt (initSevm msg) (initDevm msg) s)
      ((initDevm msg).gasLeft - proxyG w impl (initSevm msg) (initDevm msg))
      (C (frameYAt (initSevm msg) (initDevm msg) s)) w) := by
  have hlt : (initSevm msg).data.length < 2 ^ 256 := by omega
  have pf : ProxyFacts (initSevm msg) (initDevm msg) s :=
    proxyFacts_of_sel hshort hlt hsel n1 n2 n3 n4 n5 hr.admin
  have hs : (initDevm msg).stack = [] := rfl
  have hm : (initDevm msg).memory = Mem.empty := rfl
  have c0 := proxyPreW_le (initSevm msg) (initDevm msg) s hlen
  have he := dExt_le (initSevm msg) (initDevm msg) hlen
  have ha : dAcc (initSevm msg) (initDevm msg) ≤ 2600 := accessCost_le
  have ht : tailW (initSevm msg) (initDevm msg) w ≤ 100 := dTailW_le _ _ _ _ _ (dParent_size _ _ _).1 (dParent_size _ _ _).2
  have hfw : F ≤ dFwd (initSevm msg) (initDevm msg) (frameYAt (initSevm msg) (initDevm msg) s) := by
    unfold dFwd frameYAt except64th
    omega
  obtain ⟨hu, hexec, herr, hout, hgC⟩ := hchild _ hfw
  have hsame : impl (initSevm (dMsg (initSevm msg) (initDevm msg) (frameYAt (initSevm msg) (initDevm msg) s)))
      (initDevm (dMsg (initSevm msg) (initDevm msg) (frameYAt (initSevm msg) (initDevm msg) s))) =
      impl (initSevm (dMsg (initSevm msg) (initDevm msg) 0)) (initDevm (dMsg (initSevm msg) (initDevm msg) 0)) :=
    himpl (initSevm (dMsg (initSevm msg) (initDevm msg) 0)) (initDevm (dMsg (initSevm msg) (initDevm msg) 0))
      (dFwd (initSevm msg) (initDevm msg) (frameYAt (initSevm msg) (initDevm msg) s))
  rw [hsame] at hu hgC
  generalize hc : impl (initSevm (dMsg (initSevm msg) (initDevm msg) 0)) (initDevm (dMsg (initSevm msg) (initDevm msg) 0)) = u at hu hgC
  have hpi := pI_eq (initSevm msg) (initDevm msg)
  have hundel : getDelegatedCodeAddress ((pBase (initSevm msg) (initDevm msg)).state.getCode
      (dI (initSevm msg) (initDevm msg))) = none := by
    show getDelegatedCodeAddress ((pBase (initSevm msg) (initDevm msg)).getCode _) = none
    rw [afterSload_getCode, afterSload_getCode]
    unfold dI
    rw [hpi, hr.code]
    exact hr.undel
  have hprec : (initSevm msg).benvStat.rules.isPrecomp (dI (initSevm msg) (initDevm msg)) = false := by
    show (initSevm msg).benvStat.rules.isPrecomp (pI (initSevm msg) (initDevm msg)).toAdr = false
    rw [hpi]; exact hr.prec
  have hcost : proxyG w impl (initSevm msg) (initDevm msg) = (proxyPreW (initSevm msg) (initDevm msg) s).1 +
      (tailW (initSevm msg) (initDevm msg) w + dAcc (initSevm msg) (initDevm msg) +
        dExt (initSevm msg) (initDevm msg) + u) := by
    unfold proxyG tailW
    rw [hc, proxyPreW_eq, dTailW_eq]
  rw [hcost]
  refine ⟨by omega, ?_⟩
  have hYeq : (initDevm msg).gasLeft - ((proxyPreW (initSevm msg) (initDevm msg) s).1 +
      (tailW (initSevm msg) (initDevm msg) w + dAcc (initSevm msg) (initDevm msg) +
        dExt (initSevm msg) (initDevm msg) + u)) + tailW (initSevm msg) (initDevm msg) w +
        dAcc (initSevm msg) (initDevm msg) + dExt (initSevm msg) (initDevm msg) + u =
      frameYAt (initSevm msg) (initDevm msg) s := by
    unfold frameYAt
    omega
  generalize hXd : (initDevm msg).gasLeft - ((proxyPreW (initSevm msg) (initDevm msg) s).1 +
      (tailW (initSevm msg) (initDevm msg) w + dAcc (initSevm msg) (initDevm msg) +
        dExt (initSevm msg) (initDevm msg) + u)) = X at hYeq
  have run := proxy_frame_any (X := X) (cc := u) fork hdepth pf hundel hprec
    (by rw [hYeq]; unfold frameYAt; omega) (by rw [hYeq]; omega) (by rw [hYeq]; exact hexec) herr hout
    (by rw [hYeq]; exact hgC)
  rw [pre_eq_St hs hm (by omega)] at run
  rw [hYeq] at run
  exact (exec_iff_exec_eq 0 _ _ (.ok _)).mp
    (lift_exact Proxy.cert_check Proxy.jumps_ok hcode fork ⟨Proxy.t_0000_c0, rfl, run⟩)

/-- `proxyG` is bounded by its implementation's cost. -/
theorem proxyG_le {w : B256} {impl : Sevm → Devm → Nat} {s' : Sevm} {p : Devm} {Cu : Nat}
    (hlen : s'.data.length ≤ 100)
    (hCu : impl (initSevm (dMsg s' p 0)) (initDevm (dMsg s' p 0)) ≤ Cu) :
    proxyG w impl s' p ≤ Cu + 8300 := by
  have c0 := proxyPreW_le s' p 0 hlen
  rw [proxyPreW_eq] at c0
  have he := dExt_le s' p hlen
  have ha : dAcc s' p ≤ 2600 := accessCost_le
  have ht : tailG s' (dParent s' p 0) (pRest s' p) (dParent s' p 0).memory w ≤ 100 := by
    rw [← dTailW_eq]
    exact dTailW_le _ _ _ _ _ (dParent_size _ _ _).1 (dParent_size _ _ _).2
  unfold proxyG
  omega

/-- **A message into the proxy runs at `proxyG`**, above the floor `X0` its `DELEGATECALL` needs: what the retained
64th leaves the implementation must cover its cost and the store sentry. -/
theorem proxy_execF {msg : Msg} {I : ByteArray} {s w : B256} (X0 Cu : Nat) (hX0 : 2300 + (X0 + Cu) / 64 + 1 ≤ X0)
    {impl : Sevm → Devm → Nat} {C : Nat → Devm}
    (himpl : ∀ s p G', impl {s with gas := G'} (p.withGasLeft G') = impl s p)
    (hcode : (initSevm msg).code = Proxy.code) (fork : ShanghaiOnwards (initSevm msg).benvStat.fork)
    (hdepth : (initSevm msg).depth ≠ 0)
    (hr : ProxyReady (initSevm msg) (initDevm msg) I)
    (hshort : 4 ≤ (initSevm msg).data.length) (hlen : (initSevm msg).data.length ≤ 100)
    (hsel : Blanc.Sevm.selector (initSevm msg) = s)
    (n1 : B256.eqCheck (Bytes.toB256 [54, 89, 207, 230]) s = 0)
    (n2 : B256.eqCheck (Bytes.toB256 [79, 30, 242, 134]) s = 0)
    (n3 : B256.eqCheck (Bytes.toB256 [92, 96, 218, 27]) s = 0)
    (n4 : B256.eqCheck (Bytes.toB256 [143, 40, 57, 112]) s = 0)
    (n5 : B256.eqCheck (Bytes.toB256 [248, 81, 164, 64]) s = 0)
    (hCu : impl (initSevm (dMsg (initSevm msg) (initDevm msg) 0)) (initDevm (dMsg (initSevm msg) (initDevm msg) 0)) ≤ Cu)
    (hgas : proxyG w impl (initSevm msg) (initDevm msg) + X0 ≤ (initDevm msg).gasLeft)
    (hG : (initDevm msg).gasLeft < 2 ^ 256)
    (hchild : ∀ Y, impl (initSevm (dMsg (initSevm msg) (initDevm msg) Y)) (initDevm (dMsg (initSevm msg) (initDevm msg) Y)) + 2300 ≤
        dFwd (initSevm msg) (initDevm msg) Y →
      exec (initEvm (dMsg (initSevm msg) (initDevm msg) Y)) = .ok (C Y) ∧ (C Y).error = none ∧
        (C Y).output = w.toBytes ∧
        (C Y).gasLeft = dFwd (initSevm msg) (initDevm msg) Y -
          impl (initSevm (dMsg (initSevm msg) (initDevm msg) Y)) (initDevm (dMsg (initSevm msg) (initDevm msg) Y))) :
    exec (initEvm msg) = .ok (proxyPost (initSevm msg) (initDevm msg)
      (frameYAt (initSevm msg) (initDevm msg) s)
      ((initDevm msg).gasLeft - proxyG w impl (initSevm msg) (initDevm msg))
      (C (frameYAt (initSevm msg) (initDevm msg) s)) w) := by
  have hlt : (initSevm msg).data.length < 2 ^ 256 := by omega
  have pf : ProxyFacts (initSevm msg) (initDevm msg) s :=
    proxyFacts_of_sel hshort hlt hsel n1 n2 n3 n4 n5 hr.admin
  have hs : (initDevm msg).stack = [] := rfl
  have hm : (initDevm msg).memory = Mem.empty := rfl
  have hsame : impl (initSevm (dMsg (initSevm msg) (initDevm msg) (frameYAt (initSevm msg) (initDevm msg) s)))
      (initDevm (dMsg (initSevm msg) (initDevm msg) (frameYAt (initSevm msg) (initDevm msg) s))) =
      impl (initSevm (dMsg (initSevm msg) (initDevm msg) 0)) (initDevm (dMsg (initSevm msg) (initDevm msg) 0)) :=
    himpl (initSevm (dMsg (initSevm msg) (initDevm msg) 0)) (initDevm (dMsg (initSevm msg) (initDevm msg) 0))
      (dFwd (initSevm msg) (initDevm msg) (frameYAt (initSevm msg) (initDevm msg) s))
  have hcost : proxyG w impl (initSevm msg) (initDevm msg) = (proxyPreW (initSevm msg) (initDevm msg) s).1 +
      (tailW (initSevm msg) (initDevm msg) w + dAcc (initSevm msg) (initDevm msg) +
        dExt (initSevm msg) (initDevm msg) + impl (initSevm (dMsg (initSevm msg) (initDevm msg) 0)) (initDevm (dMsg (initSevm msg) (initDevm msg) 0))) := by
    unfold proxyG tailW
    rw [proxyPreW_eq, dTailW_eq]
  have hfw : impl (initSevm (dMsg (initSevm msg) (initDevm msg) 0)) (initDevm (dMsg (initSevm msg) (initDevm msg) 0)) + 2300 ≤
      dFwd (initSevm msg) (initDevm msg) (frameYAt (initSevm msg) (initDevm msg) s) := by
    rw [hcost] at hgas
    unfold dFwd frameYAt except64th
    omega
  obtain ⟨hexec, herr, hout, hgC⟩ := hchild _ (by rw [hsame]; exact hfw)
  rw [hsame] at hgC
  rw [hcost] at hgas ⊢
  generalize hc : impl (initSevm (dMsg (initSevm msg) (initDevm msg) 0)) (initDevm (dMsg (initSevm msg) (initDevm msg) 0)) = u at hgC hfw hgas ⊢
  have hpi := pI_eq (initSevm msg) (initDevm msg)
  have hundel : getDelegatedCodeAddress ((pBase (initSevm msg) (initDevm msg)).state.getCode
      (dI (initSevm msg) (initDevm msg))) = none := by
    show getDelegatedCodeAddress ((pBase (initSevm msg) (initDevm msg)).getCode _) = none
    rw [afterSload_getCode, afterSload_getCode]
    unfold dI
    rw [hpi, hr.code]
    exact hr.undel
  have hprec : (initSevm msg).benvStat.rules.isPrecomp (dI (initSevm msg) (initDevm msg)) = false := by
    show (initSevm msg).benvStat.rules.isPrecomp (pI (initSevm msg) (initDevm msg)).toAdr = false
    rw [hpi]; exact hr.prec
  have hYeq : (initDevm msg).gasLeft - ((proxyPreW (initSevm msg) (initDevm msg) s).1 +
      (tailW (initSevm msg) (initDevm msg) w + dAcc (initSevm msg) (initDevm msg) +
        dExt (initSevm msg) (initDevm msg) + u)) + tailW (initSevm msg) (initDevm msg) w +
        dAcc (initSevm msg) (initDevm msg) + dExt (initSevm msg) (initDevm msg) + u =
      frameYAt (initSevm msg) (initDevm msg) s := by
    unfold frameYAt
    omega
  generalize hXd : (initDevm msg).gasLeft - ((proxyPreW (initSevm msg) (initDevm msg) s).1 +
      (tailW (initSevm msg) (initDevm msg) w + dAcc (initSevm msg) (initDevm msg) +
        dExt (initSevm msg) (initDevm msg) + u)) = X at hYeq ⊢
  have run := proxy_frame_any (X := X) (cc := u) fork hdepth pf hundel hprec
    (by rw [hYeq]; unfold frameYAt; omega) (by rw [hYeq]; omega) (by rw [hYeq]; exact hexec) herr hout
    (by rw [hYeq]; exact hgC)
  rw [pre_eq_St hs hm (by omega)] at run
  rw [hYeq] at run
  exact (exec_iff_exec_eq 0 _ _ (.ok _)).mp
    (lift_exact Proxy.cert_check Proxy.jumps_ok hcode fork ⟨Proxy.t_0000_c0, rfl, run⟩)

/-! ## `FiatTokenV2_2`'s frames exactly, on messages -/

open Blanc.Composition.Curve3PoolUsdc22 (xferLaw pullLaw balLaw)

/-- V2_2's `transfer` as a message, exactly. -/
theorem implXfer_msgE {msg : Msg} {dst : Adr} {v : B256} (hcode : (initSevm msg).code = Impl.code)
    (fork : ShanghaiOnwards (initSevm msg).benvStat.fork) (static : (initSevm msg).isStatic = false)
    (hval : (initSevm msg).value = 0)
    (hd : (initSevm msg).data = abiSelectorBytes 0xa9059cbb ++ dst.toB256.toBytes ++ v.toBytes)
    (hF : 74300 ≤ (initDevm msg).gasLeft)
    (hf : MoveFits (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) (initSevm msg).caller dst v) :
    implXferG (initSevm msg) (initDevm msg) ≤ 72000 ∧
    exec (initEvm msg) = .ok (implXferPost (initSevm msg) (initDevm msg)
      ((initDevm msg).gasLeft - implXferG (initSevm msg) (initDevm msg))) ∧
    (implXferPost (initSevm msg) (initDevm msg)
      ((initDevm msg).gasLeft - implXferG (initSevm msg) (initDevm msg))).error = none ∧
    (implXferPost (initSevm msg) (initDevm msg)
      ((initDevm msg).gasLeft - implXferG (initSevm msg) (initDevm msg))).output = (1 : B256).toBytes := by
  obtain ⟨C, u, hexec, hu, L⟩ := xferLaw (msg := msg) (dst := dst) (v := v) hcode fork static hval hd hF hf
  have hsel : Blanc.Sevm.selector (initSevm msg) = 0xa9059cbb :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide) (by rw [hd, List.append_assoc])
  obtain ⟨w4, w36, hl⟩ := Blanc.Lift.dataWord_twoWords hd
  obtain ⟨hle, hrun⟩ := xfer_runE (dst := dst) (v := v) (pre := initDevm msg) fork static
    (guards_of hval hsel (by rw [hl]; decide) (by rw [hl]; decide))
    (by unfold xTo; rw [Blanc.Composition.Curve3PoolUsdc22.lit4', w4, word_ff20, toAdr_toB256])
    (by unfold xVal; rw [Blanc.Composition.Curve3PoolUsdc22.lit36', w36]) rfl rfl hF hf
  have hE := (exec_iff_exec_eq 0 _ _ (.ok _)).mp (lift_exact Impl.cert_check Impl.jumps_ok hcode fork hrun)
  have L' := lands_exact hexec hE (P := implXferPost (initSevm msg) (initDevm msg)
    ((initDevm msg).gasLeft - implXferG (initSevm msg) (initDevm msg))) rfl hu hle (by omega) L
  exact ⟨hle, hE, L'.keeps.error, L'.out⟩

/-- V2_2's `transfer` as a message, at the store sentry above its cost. -/
theorem implXfer_execF {msg : Msg} {dst : Adr} {v : B256} (hcode : (initSevm msg).code = Impl.code)
    (fork : ShanghaiOnwards (initSevm msg).benvStat.fork) (static : (initSevm msg).isStatic = false)
    (hval : (initSevm msg).value = 0)
    (hd : (initSevm msg).data = abiSelectorBytes 0xa9059cbb ++ dst.toB256.toBytes ++ v.toBytes)
    (hF : implXferG (initSevm msg) (initDevm msg) + 2300 ≤ (initDevm msg).gasLeft)
    (hf : MoveFits (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) (initSevm msg).caller dst v) :
    exec (initEvm msg) = .ok (implXferPost (initSevm msg) (initDevm msg)
      ((initDevm msg).gasLeft - implXferG (initSevm msg) (initDevm msg))) := by
  have hsel : Blanc.Sevm.selector (initSevm msg) = 0xa9059cbb :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide) (by rw [hd, List.append_assoc])
  obtain ⟨w4, w36, hl⟩ := Blanc.Lift.dataWord_twoWords hd
  exact (exec_iff_exec_eq 0 _ _ (.ok _)).mp (lift_exact Impl.cert_check Impl.jumps_ok hcode fork
    (xfer_runF (dst := dst) (v := v) (pre := initDevm msg) fork static
      (guards_of hval hsel (by rw [hl]; decide) (by rw [hl]; decide))
      (by unfold xTo; rw [Blanc.Composition.Curve3PoolUsdc22.lit4', w4, word_ff20, toAdr_toB256])
      (by unfold xVal; rw [Blanc.Composition.Curve3PoolUsdc22.lit36', w36]) rfl rfl hF hf))

/-- V2_2's `transferFrom` as a message, at the store sentry above its cost. -/
theorem implPull_execF {msg : Msg} {src dst : Adr} {v : B256} (hcode : (initSevm msg).code = Impl.code)
    (fork : ShanghaiOnwards (initSevm msg).benvStat.fork) (static : (initSevm msg).isStatic = false)
    (hval : (initSevm msg).value = 0)
    (hd : (initSevm msg).data = abiSelectorBytes 0x23b872dd ++ src.toB256.toBytes ++ dst.toB256.toBytes ++ v.toBytes)
    (hF : implPullG (initSevm msg) (initDevm msg) + 2300 ≤ (initDevm msg).gasLeft)
    (hf : PullFits (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) src (initSevm msg).caller dst v) :
    exec (initEvm msg) = .ok (implPullPost (initSevm msg) (initDevm msg)
      ((initDevm msg).gasLeft - implPullG (initSevm msg) (initDevm msg))) := by
  have hsel : Blanc.Sevm.selector (initSevm msg) = 0x23b872dd :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide)
      (by rw [hd, List.append_assoc, List.append_assoc])
  obtain ⟨w4, w36, w68⟩ := Blanc.Lift.Curve3Pool.cc_dataWord_threeWords hd
  have hl : (initSevm msg).data.length = 100 := by
    rw [hd]
    simp only [List.length_append, B256.length_toBytes, abiSelectorBytes_length]
  exact (exec_iff_exec_eq 0 _ _ (.ok _)).mp (lift_exact Impl.cert_check Impl.jumps_ok hcode fork
    (pull_runF (src := src) (dst := dst) (v := v) (pre := initDevm msg) fork static
      (guards_of hval hsel (by rw [hl]; decide) (by rw [hl]; decide))
      (by unfold pFrom; rw [Blanc.Composition.Curve3PoolUsdc22.lit4', w4, ff20_and_word, toAdr_toB256])
      (by unfold pTo; rw [Blanc.Composition.Curve3PoolUsdc22.lit4', show (4 : B256) + Bytes.toB256 [32] = 36 by decide, w36, ff20_and_word, toAdr_toB256])
      (by unfold pVal; rw [show Bytes.toB256 [64] + Bytes.toB256 [4] = 68 by decide, w68]) rfl rfl hF hf))

/-- V2_2's `transferFrom` as a message, exactly. -/
theorem implPull_msgE {msg : Msg} {src dst : Adr} {v : B256} (hcode : (initSevm msg).code = Impl.code)
    (fork : ShanghaiOnwards (initSevm msg).benvStat.fork) (static : (initSevm msg).isStatic = false)
    (hval : (initSevm msg).value = 0)
    (hd : (initSevm msg).data = abiSelectorBytes 0x23b872dd ++ src.toB256.toBytes ++ dst.toB256.toBytes ++ v.toBytes)
    (hF : 104300 ≤ (initDevm msg).gasLeft)
    (hf : PullFits (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) src (initSevm msg).caller dst v) :
    implPullG (initSevm msg) (initDevm msg) ≤ 102000 ∧
    exec (initEvm msg) = .ok (implPullPost (initSevm msg) (initDevm msg)
      ((initDevm msg).gasLeft - implPullG (initSevm msg) (initDevm msg))) ∧
    (implPullPost (initSevm msg) (initDevm msg)
      ((initDevm msg).gasLeft - implPullG (initSevm msg) (initDevm msg))).error = none ∧
    (implPullPost (initSevm msg) (initDevm msg)
      ((initDevm msg).gasLeft - implPullG (initSevm msg) (initDevm msg))).output = (1 : B256).toBytes := by
  obtain ⟨C, u, hexec, hu, L⟩ := pullLaw (msg := msg) (src := src) (dst := dst) (v := v) hcode fork static hval hd hF hf
  have hsel : Blanc.Sevm.selector (initSevm msg) = 0x23b872dd :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide)
      (by rw [hd, List.append_assoc, List.append_assoc])
  obtain ⟨w4, w36, w68⟩ := Blanc.Lift.Curve3Pool.cc_dataWord_threeWords hd
  have hl : (initSevm msg).data.length = 100 := by
    rw [hd]
    simp only [List.length_append, B256.length_toBytes, abiSelectorBytes_length]
  obtain ⟨hle, hrun⟩ := pull_runE (src := src) (dst := dst) (v := v) (pre := initDevm msg) fork static
    (guards_of hval hsel (by rw [hl]; decide) (by rw [hl]; decide))
    (by unfold pFrom; rw [Blanc.Composition.Curve3PoolUsdc22.lit4', w4, ff20_and_word, toAdr_toB256])
    (by unfold pTo; rw [Blanc.Composition.Curve3PoolUsdc22.lit4', show (4 : B256) + Bytes.toB256 [32] = 36 by decide, w36, ff20_and_word, toAdr_toB256])
    (by unfold pVal; rw [show Bytes.toB256 [64] + Bytes.toB256 [4] = 68 by decide, w68]) rfl rfl hF hf
  have hE := (exec_iff_exec_eq 0 _ _ (.ok _)).mp (lift_exact Impl.cert_check Impl.jumps_ok hcode fork hrun)
  have L' := lands_exact hexec hE (P := implPullPost (initSevm msg) (initDevm msg)
    ((initDevm msg).gasLeft - implPullG (initSevm msg) (initDevm msg))) rfl hu hle (by omega) L
  exact ⟨hle, hE, L'.keeps.error, L'.out⟩

/-! ## Through the proxy, exactly -/

/-- `transfer`'s post through the proxy. -/
noncomputable def xferProxyPost (s : Sevm) (p : Devm) (R : Nat) : Devm :=
  proxyPost s p (frameYAt s p 0xa9059cbb) R
    (implXferPost (initSevm (dMsg s p (frameYAt s p 0xa9059cbb))) (initDevm (dMsg s p (frameYAt s p 0xa9059cbb)))
      (dFwd s p (frameYAt s p 0xa9059cbb) - implXferG (initSevm (dMsg s p (frameYAt s p 0xa9059cbb)))
        (initDevm (dMsg s p (frameYAt s p 0xa9059cbb))))) 1

/-- `transferFrom`'s post through the proxy. -/
noncomputable def pullProxyPost (s : Sevm) (p : Devm) (R : Nat) : Devm :=
  proxyPost s p (frameYAt s p 0x23b872dd) R
    (implPullPost (initSevm (dMsg s p (frameYAt s p 0x23b872dd))) (initDevm (dMsg s p (frameYAt s p 0x23b872dd)))
      (dFwd s p (frameYAt s p 0x23b872dd) - implPullG (initSevm (dMsg s p (frameYAt s p 0x23b872dd)))
        (initDevm (dMsg s p (frameYAt s p 0x23b872dd))))) 1

/-- **`transfer`'s exact cost through the proxy.** -/
noncomputable abbrev xferG : Sevm → Devm → Nat := proxyG 1 implXferG

/-- **`transferFrom`'s exact cost through the proxy.** -/
noncomputable abbrev pullG : Sevm → Devm → Nat := proxyG 1 implPullG

theorem xferProxyPost_canon (s : Sevm) (p : Devm) (F R : Nat) :
    Devm.EqModGas (xferProxyPost {s with gas := F} (p.withGasLeft F) R)
      (proxyCanon 1 (fun s p => implXferPost s p 0) s p) := by
  unfold xferProxyPost proxyCanon
  refine proxyPost_canon s p F 1 ?_
  rw [dMsg_reframe]
  exact implXferPost_canon (initSevm (dMsg s p 0)) (initDevm (dMsg s p 0)) (dFwd s p _) _

theorem pullProxyPost_canon (s : Sevm) (p : Devm) (F R : Nat) :
    Devm.EqModGas (pullProxyPost {s with gas := F} (p.withGasLeft F) R)
      (proxyCanon 1 (fun s p => implPullPost s p 0) s p) := by
  unfold pullProxyPost proxyCanon
  refine proxyPost_canon s p F 1 ?_
  rw [dMsg_reframe]
  exact implPullPost_canon (initSevm (dMsg s p 0)) (initDevm (dMsg s p 0)) (dFwd s p _) _

/-- **`transfer` through the proxy, as a message, exactly.** -/
theorem proxyXfer_msgE {msg : Msg} {dst : Adr} {v : B256} (hcode : (initSevm msg).code = Proxy.code)
    (fork : ShanghaiOnwards (initSevm msg).benvStat.fork) (hdepth : (initSevm msg).depth ≠ 0)
    (static : (initSevm msg).isStatic = false) (hval : (initSevm msg).value = 0)
    (hr : ProxyReady (initSevm msg) (initDevm msg) Impl.code)
    (hd : (initSevm msg).data = abiSelectorBytes 0xa9059cbb ++ dst.toB256.toBytes ++ v.toBytes)
    (hgas : 74300 + 74300 / 63 + 8300 ≤ (initDevm msg).gasLeft) (hG : (initDevm msg).gasLeft < 2 ^ 256)
    (hfits : MoveFits (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) (initSevm msg).caller dst v) :
    xferG (initSevm msg) (initDevm msg) ≤ 80300 ∧
    exec (initEvm msg) = .ok (xferProxyPost (initSevm msg) (initDevm msg)
      ((initDevm msg).gasLeft - xferG (initSevm msg) (initDevm msg))) ∧
    FrameLands Proxy.cert.prog (initSevm msg) (initDevm msg) (xferProxyPost (initSevm msg) (initDevm msg)
        ((initDevm msg).gasLeft - xferG (initSevm msg) (initDevm msg))) (xferG (initSevm msg) (initDevm msg)) 1
      (creditStor (debitStor (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) (initSevm msg).caller v.toNat)
        dst v.toNat)
      ((getOrigAcct (initSevm msg) (initSevm msg).currentTarget).stor =
          Devm.getStor (initDevm msg) (initSevm msg).currentTarget ∧
        (initSevm msg).currentTarget ∉ (initDevm msg).createdAccounts ∧
        balSlot (initSevm msg).caller ≠ balSlot dst) := by
  have hsel : Blanc.Sevm.selector (initSevm msg) = 0xa9059cbb :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide) (by rw [hd, List.append_assoc])
  obtain ⟨-, -, hl⟩ := Blanc.Lift.dataWord_twoWords hd
  obtain ⟨hle, hE⟩ := proxy_execE (s := 0xa9059cbb) (w := 1) (impl := implXferG)
    (C := fun Y => implXferPost (initSevm (dMsg (initSevm msg) (initDevm msg) Y)) (initDevm (dMsg (initSevm msg) (initDevm msg) Y))
      (dFwd (initSevm msg) (initDevm msg) Y - implXferG (initSevm (dMsg (initSevm msg) (initDevm msg) Y)) (initDevm (dMsg (initSevm msg) (initDevm msg) Y))))
    74300 72000 (by decide) implXferG_reframe hcode fork hdepth hr (by omega) (by omega) hsel
    (by decide) (by decide) (by decide) (by decide) (by decide) hgas hG (fun Y hF => by
      obtain ⟨a1, a2, a3, a4⟩ := implXfer_msgE (msg := dMsg (initSevm msg) (initDevm msg) Y) (dst := dst) (v := v)
        (child_code hr) fork (child_static.trans static) hval
        (by rw [dMsg_data _ _ _ (by omega)]; exact hd) hF (by rw [dMsg_getStor]; exact hfits)
      exact ⟨a1, a2, a3, a4, rfl⟩)
  obtain ⟨post, used, hexec, hu, L⟩ := proxyXfer_msg (@xferLaw) (by decide) hcode fork hdepth static hval hr hd hgas hG hfits
  exact ⟨hle, hE, lands_exact hexec hE rfl hu hle (by omega) L⟩

/-- **`transferFrom` through the proxy, as a message, exactly.** -/
theorem proxyPull_msgE {msg : Msg} {src dst : Adr} {v : B256} (hcode : (initSevm msg).code = Proxy.code)
    (fork : ShanghaiOnwards (initSevm msg).benvStat.fork) (hdepth : (initSevm msg).depth ≠ 0)
    (static : (initSevm msg).isStatic = false) (hval : (initSevm msg).value = 0)
    (hr : ProxyReady (initSevm msg) (initDevm msg) Impl.code)
    (hd : (initSevm msg).data = abiSelectorBytes 0x23b872dd ++ src.toB256.toBytes ++ dst.toB256.toBytes ++ v.toBytes)
    (hgas : 104300 + 104300 / 63 + 8300 ≤ (initDevm msg).gasLeft) (hG : (initDevm msg).gasLeft < 2 ^ 256)
    (hfits : PullFits (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) src (initSevm msg).caller dst v) :
    pullG (initSevm msg) (initDevm msg) ≤ 110300 ∧
    exec (initEvm msg) = .ok (pullProxyPost (initSevm msg) (initDevm msg)
      ((initDevm msg).gasLeft - pullG (initSevm msg) (initDevm msg))) ∧
    FrameLands Proxy.cert.prog (initSevm msg) (initDevm msg) (pullProxyPost (initSevm msg) (initDevm msg)
        ((initDevm msg).gasLeft - pullG (initSevm msg) (initDevm msg))) (pullG (initSevm msg) (initDevm msg)) 1
      (pullStor (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) src (initSevm msg).caller dst v)
      ((getOrigAcct (initSevm msg) (initSevm msg).currentTarget).stor =
          Devm.getStor (initDevm msg) (initSevm msg).currentTarget ∧
        (initSevm msg).currentTarget ∉ (initDevm msg).createdAccounts ∧
        allowSlot src (initSevm msg).caller ≠ balSlot src ∧ allowSlot src (initSevm msg).caller ≠ balSlot dst ∧
        balSlot src ≠ balSlot dst) := by
  have hsel : Blanc.Sevm.selector (initSevm msg) = 0x23b872dd :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide)
      (by rw [hd, List.append_assoc, List.append_assoc])
  have hl : (initSevm msg).data.length = 100 := by
    rw [hd]
    simp only [List.length_append, B256.length_toBytes, abiSelectorBytes_length]
  obtain ⟨hle, hE⟩ := proxy_execE (s := 0x23b872dd) (w := 1) (impl := implPullG)
    (C := fun Y => implPullPost (initSevm (dMsg (initSevm msg) (initDevm msg) Y)) (initDevm (dMsg (initSevm msg) (initDevm msg) Y))
      (dFwd (initSevm msg) (initDevm msg) Y - implPullG (initSevm (dMsg (initSevm msg) (initDevm msg) Y)) (initDevm (dMsg (initSevm msg) (initDevm msg) Y))))
    104300 102000 (by decide) implPullG_reframe hcode fork hdepth hr (by omega) (by omega) hsel
    (by decide) (by decide) (by decide) (by decide) (by decide) hgas hG (fun Y hF => by
      obtain ⟨a1, a2, a3, a4⟩ := implPull_msgE (msg := dMsg (initSevm msg) (initDevm msg) Y) (src := src) (dst := dst) (v := v)
        (child_code hr) fork (child_static.trans static) hval
        (by rw [dMsg_data _ _ _ (by omega)]; exact hd) hF (by rw [dMsg_getStor]; exact hfits)
      exact ⟨a1, a2, a3, a4, rfl⟩)
  obtain ⟨post, used, hexec, hu, L⟩ := proxyPull_msg (@pullLaw) (by decide) hcode fork hdepth static hval hr hd hgas hG hfits
  exact ⟨hle, hE, lands_exact hexec hE rfl hu hle (by omega) L⟩

/-- **`transfer` through the proxy, at its floor.** -/
theorem proxyXfer_execF {msg : Msg} {dst : Adr} {v : B256} (hcode : (initSevm msg).code = Proxy.code)
    (fork : ShanghaiOnwards (initSevm msg).benvStat.fork) (hdepth : (initSevm msg).depth ≠ 0)
    (static : (initSevm msg).isStatic = false) (hval : (initSevm msg).value = 0)
    (hr : ProxyReady (initSevm msg) (initDevm msg) Impl.code)
    (hd : (initSevm msg).data = abiSelectorBytes 0xa9059cbb ++ dst.toB256.toBytes ++ v.toBytes)
    (hgas : xferG (initSevm msg) (initDevm msg) + 3370 ≤ (initDevm msg).gasLeft) (hG : (initDevm msg).gasLeft < 2 ^ 256)
    (hfits : MoveFits (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) (initSevm msg).caller dst v) :
    exec (initEvm msg) = .ok (xferProxyPost (initSevm msg) (initDevm msg)
      ((initDevm msg).gasLeft - xferG (initSevm msg) (initDevm msg))) := by
  have hsel : Blanc.Sevm.selector (initSevm msg) = 0xa9059cbb :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide) (by rw [hd, List.append_assoc])
  obtain ⟨-, -, hl⟩ := Blanc.Lift.dataWord_twoWords hd
  refine proxy_execF (s := 0xa9059cbb) (w := 1) (impl := implXferG)
    (C := fun Y => implXferPost (initSevm (dMsg (initSevm msg) (initDevm msg) Y)) (initDevm (dMsg (initSevm msg) (initDevm msg) Y))
      (dFwd (initSevm msg) (initDevm msg) Y - implXferG (initSevm (dMsg (initSevm msg) (initDevm msg) Y)) (initDevm (dMsg (initSevm msg) (initDevm msg) Y))))
    3370 65000 (by decide) implXferG_reframe hcode fork hdepth hr (by omega) (by omega) hsel
    (by decide) (by decide) (by decide) (by decide) (by decide) (implXferG_le _ _) hgas hG (fun Y hF => ?_)
  exact ⟨implXfer_execF (msg := dMsg (initSevm msg) (initDevm msg) Y) (dst := dst) (v := v)
      (child_code hr) fork (child_static.trans static) hval
      (by rw [dMsg_data _ _ _ (by omega)]; exact hd) hF (by rw [dMsg_getStor]; exact hfits),
    implXferPost_error _ _ _, (implXferPost_output _ _ _).trans (by decide), rfl⟩

/-- **`transferFrom` through the proxy, at its floor.** -/
theorem proxyPull_execF {msg : Msg} {src dst : Adr} {v : B256} (hcode : (initSevm msg).code = Proxy.code)
    (fork : ShanghaiOnwards (initSevm msg).benvStat.fork) (hdepth : (initSevm msg).depth ≠ 0)
    (static : (initSevm msg).isStatic = false) (hval : (initSevm msg).value = 0)
    (hr : ProxyReady (initSevm msg) (initDevm msg) Impl.code)
    (hd : (initSevm msg).data = abiSelectorBytes 0x23b872dd ++ src.toB256.toBytes ++ dst.toB256.toBytes ++ v.toBytes)
    (hgas : pullG (initSevm msg) (initDevm msg) + 4000 ≤ (initDevm msg).gasLeft) (hG : (initDevm msg).gasLeft < 2 ^ 256)
    (hfits : PullFits (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) src (initSevm msg).caller dst v) :
    exec (initEvm msg) = .ok (pullProxyPost (initSevm msg) (initDevm msg)
      ((initDevm msg).gasLeft - pullG (initSevm msg) (initDevm msg))) := by
  have hsel : Blanc.Sevm.selector (initSevm msg) = 0x23b872dd :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide)
      (by rw [hd, List.append_assoc, List.append_assoc])
  have hl : (initSevm msg).data.length = 100 := by
    rw [hd]
    simp only [List.length_append, B256.length_toBytes, abiSelectorBytes_length]
  refine proxy_execF (s := 0x23b872dd) (w := 1) (impl := implPullG)
    (C := fun Y => implPullPost (initSevm (dMsg (initSevm msg) (initDevm msg) Y)) (initDevm (dMsg (initSevm msg) (initDevm msg) Y))
      (dFwd (initSevm msg) (initDevm msg) Y - implPullG (initSevm (dMsg (initSevm msg) (initDevm msg) Y)) (initDevm (dMsg (initSevm msg) (initDevm msg) Y))))
    4000 102000 (by decide) implPullG_reframe hcode fork hdepth hr (by omega) (by omega) hsel
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by have h := pullW_le (initSevm (dMsg (initSevm msg) (initDevm msg) 0)) (initDevm (dMsg (initSevm msg) (initDevm msg) 0))
        rwa [pullW_eq] at h) hgas hG (fun Y hF => ?_)
  have hE : (implPullPost (initSevm (dMsg (initSevm msg) (initDevm msg) Y)) (initDevm (dMsg (initSevm msg) (initDevm msg) Y))
      (dFwd (initSevm msg) (initDevm msg) Y - implPullG (initSevm (dMsg (initSevm msg) (initDevm msg) Y)) (initDevm (dMsg (initSevm msg) (initDevm msg) Y)))).output = (1 : B256).toBytes := by
    show (okW).toBytes = _
    rw [okW_eq]
  have hX := implPull_execF (msg := dMsg (initSevm msg) (initDevm msg) Y) (src := src) (dst := dst) (v := v)
      (child_code hr) fork (child_static.trans static) hval
      (by rw [dMsg_data _ _ _ (by omega)]; exact hd) hF (by rw [dMsg_getStor]; exact hfits)
  obtain ⟨run⟩ := (exec_iff_exec_eq 0 _ _ _).mpr hX
  exact ⟨hX, (Exec.ok_error_eq run fork.rules_stateGas_none).trans rfl, hE, rfl⟩

/-! ## The pool's exact coin profiles -/

section Premises

variable {sevm : Sevm} {t amt : B256} {W W' : Devm → Prop} {U : Nat} {ii oi : B256}

/-- **The pool's `transfer(msg.sender, amt)` into USDC, exactly.** -/
theorem usdc22_coinPushExact (hfork : ShanghaiOnwards sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : 2 ≤ sevm.depth) (hprec : ¬ sevm.benvStat.rules.isPrecomp t.toAdr)
    (hne : t.toAdr ≠ sevm.currentTarget) (hU : 89000 ≤ U)
    (hii : ii.toNat + 0x44 ≤ 4096) (hoi : oi.toNat + 32 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Proxy.code ∧ ProxyAt sevm b t.toAdr Impl.code ∧
      MoveFits (b.getStor t.toAdr) sevm.currentTarget sevm.caller amt)
    (hW' : ∀ b d, W b → CoinLeaves t.toAdr
        (creditStor (debitStor (b.getStor t.toAdr) sevm.currentTarget amt.toNat) sevm.caller amt.toNat)
      ((getOrigAcct sevm t.toAdr).stor = b.getStor t.toAdr ∧ t.toAdr ∉ b.createdAccounts ∧
        balSlot sevm.currentTarget ≠ balSlot sevm.caller) b d → W' d) :
    MutableCallProfile sevm W W' t (transferSel ++ sevm.caller.toB256.toBytes ++ amt.toBytes) RawCallOk U ii
      0x44 oi (coinDebit xferG sevm t ii 0x44 oi)
      (coinNext (proxyCanon 1 (fun s p => implXferPost s p 0)) sevm t ii 0x44 oi) := by
  refine coinMutProfile (74300 + 74300 / 63 + 8300) 80300 xferG
    (proxyCanon 1 (fun s p => implXferPost s p 0)) (fun s p G' => proxyG_reframe s p G' 1 implXferG) hfork (by omega)
    (by rw [prec_false hprec]) (by omega) (by omega) (by decide)
    (by rw [show (0x44 : B256).toNat = 0x44 from rfl]; exact hii) hoi ?_
  intro b S M G hWb hG hin hfwd
  obtain ⟨hc, hp, hfits⟩ := hW b hWb
  have hgl : fwd b S M G t ii 0x44 oi 0x20 < 2 ^ 256 := by
    unfold fwd except64th; omega
  obtain ⟨hu, hexec, L⟩ := proxyXfer_msgE (msg := callMsg0 sevm b S M G t ii 0x44 oi 0x20)
    (dst := sevm.caller) (v := amt) hc hfork (by show sevm.depth - 1 ≠ 0; omega)
    (by rw [callMsg0_isStatic]; exact hstatic) rfl ⟨hp.undel, hp.code, hp.prec, hp.admin⟩
    (by rw [callMsg0_data, hin, transferSel_abi]) hfwd hgl hfits
  refine ⟨by rw [hc]; exact proxy_undelegated, hu, _, hexec, L.keeps.error, L.gas,
    xferProxyPost_canon (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))
      (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20)) _ _, ?_, ?_,
    L.keeps.other _ (Ne.symm hne), L.keeps.code 4, hW' b _ hWb (leaves_of_lands L (fun r => r))⟩
  · rw [L.out]; exact rawCallOk_one
  · rw [L.out]; decide +kernel

/-- **The pool's `transferFrom(msg.sender, self, amt)` into USDC, exactly.** -/
theorem usdc22_coinPullExact (hfork : ShanghaiOnwards sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : 2 ≤ sevm.depth) (hprec : ¬ sevm.benvStat.rules.isPrecomp t.toAdr)
    (hne : t.toAdr ≠ sevm.currentTarget) (hU : 120000 ≤ U)
    (hii : ii.toNat + 0x64 ≤ 4096) (hoi : oi.toNat + 32 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Proxy.code ∧ ProxyAt sevm b t.toAdr Impl.code ∧
      PullFits (b.getStor t.toAdr) sevm.caller sevm.currentTarget sevm.currentTarget amt)
    (hW' : ∀ b d, W b → CoinLeaves t.toAdr
        (pullStor (b.getStor t.toAdr) sevm.caller sevm.currentTarget sevm.currentTarget amt)
      ((getOrigAcct sevm t.toAdr).stor = b.getStor t.toAdr ∧ t.toAdr ∉ b.createdAccounts ∧
        allowSlot sevm.caller sevm.currentTarget ≠ balSlot sevm.caller ∧
        allowSlot sevm.caller sevm.currentTarget ≠ balSlot sevm.currentTarget ∧
        balSlot sevm.caller ≠ balSlot sevm.currentTarget) b d → W' d) :
    MutableCallProfile sevm W W' t
      (transferFromSel ++ sevm.caller.toB256.toBytes ++ sevm.currentTarget.toB256.toBytes ++ amt.toBytes)
      RawCallOk U ii 0x64 oi (coinDebit pullG sevm t ii 0x64 oi)
      (coinNext (proxyCanon 1 (fun s p => implPullPost s p 0)) sevm t ii 0x64 oi) := by
  refine coinMutProfile (104300 + 104300 / 63 + 8300) 110300 pullG
    (proxyCanon 1 (fun s p => implPullPost s p 0)) (fun s p G' => proxyG_reframe s p G' 1 implPullG) hfork (by omega)
    (by rw [prec_false hprec]) (by omega) (by omega) (by decide)
    (by rw [show (0x64 : B256).toNat = 0x64 from rfl]; exact hii) hoi ?_
  intro b S M G hWb hG hin hfwd
  obtain ⟨hc, hp, hfits⟩ := hW b hWb
  have hgl : fwd b S M G t ii 0x64 oi 0x20 < 2 ^ 256 := by
    unfold fwd except64th; omega
  obtain ⟨hu, hexec, L⟩ := proxyPull_msgE (msg := callMsg0 sevm b S M G t ii 0x64 oi 0x20)
    (src := sevm.caller) (dst := sevm.currentTarget) (v := amt) hc hfork (by show sevm.depth - 1 ≠ 0; omega)
    (by rw [callMsg0_isStatic]; exact hstatic) rfl ⟨hp.undel, hp.code, hp.prec, hp.admin⟩
    (by rw [callMsg0_data, hin, transferFromSel_abi]) hfwd hgl hfits
  refine ⟨by rw [hc]; exact proxy_undelegated, hu, _, hexec, L.keeps.error, L.gas,
    pullProxyPost_canon (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x64 oi 0x20))
      (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x64 oi 0x20)) _ _, ?_, ?_,
    L.keeps.other _ (Ne.symm hne), L.keeps.code 4, hW' b _ hWb (leaves_of_lands L (fun r => r))⟩
  · rw [L.out]; exact rawCallOk_one
  · rw [L.out]; decide +kernel

/-- **`transfer`'s exact profile through the proxy, at its floor.** -/
theorem usdc22_coinPushFloor {K : Nat} (hK : 3370 + (K + 73300) / 64 + 1 ≤ K)
    (hfork : ShanghaiOnwards sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : 2 ≤ sevm.depth) (hprec : ¬ sevm.benvStat.rules.isPrecomp t.toAdr)
    (hne : t.toAdr ≠ sevm.currentTarget) (hU : 89000 ≤ U) (hUw : U < 2 ^ 256) (hs : GasStable W')
    (hii : ii.toNat + 0x44 ≤ 4096) (hoi : oi.toNat + 32 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Proxy.code ∧ ProxyAt sevm b t.toAdr Impl.code ∧
      MoveFits (b.getStor t.toAdr) sevm.currentTarget sevm.caller amt)
    (hW' : ∀ b d, W b → CoinLeaves t.toAdr
        (creditStor (debitStor (b.getStor t.toAdr) sevm.currentTarget amt.toNat) sevm.caller amt.toNat)
      ((getOrigAcct sevm t.toAdr).stor = b.getStor t.toAdr ∧ t.toAdr ∉ b.createdAccounts ∧
        balSlot sevm.currentTarget ≠ balSlot sevm.caller) b d → W' d) :
    MutableFloorProfile sevm W W' t (transferSel ++ sevm.caller.toB256.toBytes ++ amt.toBytes) RawCallOk U K ii
      0x44 oi (coinDebit xferG sevm t ii 0x44 oi)
      (coinNext (proxyCanon 1 (fun s p => implXferPost s p 0)) sevm t ii 0x44 oi) := by
  refine coinMutFloor 3370 K 73300 xferG (proxyCanon 1 (fun s p => implXferPost s p 0))
    (fun s p G' => proxyG_reframe s p G' 1 implXferG) hfork (by omega) (by rw [prec_false hprec]) hK hUw hs
    (usdc22_coinPushExact hfork hstatic hdepth hprec hne hU hii hoi hW hW') (fun b S M _ hin => ?_) ?_
  · refine proxyG_le (by rw [callMsg0_data, hin]; simp only [List.length_append, B256.length_toBytes, transferSel_abi, abiSelectorBytes_length]; omega) ?_
    exact implXferG_le _ _
  intro b S M G hWb hG hin hfwd
  obtain ⟨hc, hp, hfits⟩ := hW b hWb
  have hgl : fwd b S M G t ii 0x44 oi 0x20 < 2 ^ 256 := by
    unfold fwd except64th; omega
  exact ⟨by rw [hc]; exact proxy_undelegated, _, proxyXfer_execF (msg := callMsg0 sevm b S M G t ii 0x44 oi 0x20)
    (dst := sevm.caller) (v := amt) hc hfork (by show sevm.depth - 1 ≠ 0; omega)
    (by rw [callMsg0_isStatic]; exact hstatic) rfl ⟨hp.undel, hp.code, hp.prec, hp.admin⟩
    (by rw [callMsg0_data, hin, transferSel_abi]) hfwd hgl hfits, rfl,
    xferProxyPost_canon (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))
      (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20)) _ _⟩

/-- **`transferFrom`'s exact profile through the proxy, at its floor.** -/
theorem usdc22_coinPullFloor {K : Nat} (hK : 4000 + (K + 110300) / 64 + 1 ≤ K)
    (hfork : ShanghaiOnwards sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : 2 ≤ sevm.depth) (hprec : ¬ sevm.benvStat.rules.isPrecomp t.toAdr)
    (hne : t.toAdr ≠ sevm.currentTarget) (hU : 120000 ≤ U) (hUw : U < 2 ^ 256) (hs : GasStable W')
    (hii : ii.toNat + 0x64 ≤ 4096) (hoi : oi.toNat + 32 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Proxy.code ∧ ProxyAt sevm b t.toAdr Impl.code ∧
      PullFits (b.getStor t.toAdr) sevm.caller sevm.currentTarget sevm.currentTarget amt)
    (hW' : ∀ b d, W b → CoinLeaves t.toAdr
        (pullStor (b.getStor t.toAdr) sevm.caller sevm.currentTarget sevm.currentTarget amt)
      ((getOrigAcct sevm t.toAdr).stor = b.getStor t.toAdr ∧ t.toAdr ∉ b.createdAccounts ∧
        allowSlot sevm.caller sevm.currentTarget ≠ balSlot sevm.caller ∧
        allowSlot sevm.caller sevm.currentTarget ≠ balSlot sevm.currentTarget ∧
        balSlot sevm.caller ≠ balSlot sevm.currentTarget) b d → W' d) :
    MutableFloorProfile sevm W W' t
      (transferFromSel ++ sevm.caller.toB256.toBytes ++ sevm.currentTarget.toB256.toBytes ++ amt.toBytes)
      RawCallOk U K ii 0x64 oi (coinDebit pullG sevm t ii 0x64 oi)
      (coinNext (proxyCanon 1 (fun s p => implPullPost s p 0)) sevm t ii 0x64 oi) := by
  refine coinMutFloor 4000 K 110300 pullG (proxyCanon 1 (fun s p => implPullPost s p 0))
    (fun s p G' => proxyG_reframe s p G' 1 implPullG) hfork (by omega) (by rw [prec_false hprec]) hK hUw hs
    (usdc22_coinPullExact hfork hstatic hdepth hprec hne hU hii hoi hW hW') (fun b S M _ hin => ?_) ?_
  · refine proxyG_le (by rw [callMsg0_data, hin]; simp only [List.length_append, B256.length_toBytes, transferFromSel_abi, abiSelectorBytes_length]; omega) ?_
    have h := pullW_le (initSevm (dMsg (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x64 oi 0x20))
      (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x64 oi 0x20)) 0))
      (initDevm (dMsg (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x64 oi 0x20))
      (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x64 oi 0x20)) 0))
    rw [pullW_eq] at h
    omega
  intro b S M G hWb hG hin hfwd
  obtain ⟨hc, hp, hfits⟩ := hW b hWb
  have hgl : fwd b S M G t ii 0x64 oi 0x20 < 2 ^ 256 := by
    unfold fwd except64th; omega
  exact ⟨by rw [hc]; exact proxy_undelegated, _, proxyPull_execF (msg := callMsg0 sevm b S M G t ii 0x64 oi 0x20)
    (src := sevm.caller) (dst := sevm.currentTarget) (v := amt) hc hfork (by show sevm.depth - 1 ≠ 0; omega)
    (by rw [callMsg0_isStatic]; exact hstatic) rfl ⟨hp.undel, hp.code, hp.prec, hp.admin⟩
    (by rw [callMsg0_data, hin, transferFromSel_abi]) hfwd hgl hfits, rfl,
    pullProxyPost_canon (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x64 oi 0x20))
      (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x64 oi 0x20)) _ _⟩

end Premises

end Blanc.Composition.UsdcLive
