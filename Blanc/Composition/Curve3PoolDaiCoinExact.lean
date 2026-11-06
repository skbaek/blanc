import Blanc.Lift.DaiExact
import Blanc.Composition.Curve3PoolDaiCoin
import Blanc.Composition.Curve3PoolCoinExactKit

/-!
# DAI's exact profiles at the pool's call sites

`dai_coinPushExact`, `dai_coinPullExact` and `dai_coinBalExact`: the bounded `dai_coin*OkAt` with the charge
closed (`xferG`, `pullG`, `balG`) and the successor canonical, as `MutableCallProfile` and
`StaticWordCallProfile`. The floors are the bounded theorems', from the same walks' bounds.
-/

namespace Blanc.Composition.Curve3PoolDai

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.Composition.Curve3PoolCalleeLive
open Blanc.Lift.AccumulatedWalk (FrameLands guards_of)
open Blanc.Composition.Curve3Pool3CrvInstance (CoinLeaves prec_false rawCallOk_one getCode_of_state
  getStor_of_state transferSel_abi transferFromSel_abi balanceOfSel_abi)
open Blanc.Composition.Curve3PoolCoinChild Blanc.Composition.Curve3PoolCoinExactKit
open Blanc.Lift.Dai

/-- `transfer` as a message, exactly. -/
theorem xfer_msgE {msg : Msg} {dst : Adr} {v : B256} (hcode : (initSevm msg).code = Dai.code)
    (fork : CoveredFork (initSevm msg).benvStat.fork) (static : (initSevm msg).isStatic = false)
    (hval : (initSevm msg).value = 0)
    (hd : (initSevm msg).data = abiSelectorBytes 0xa9059cbb ++ dst.toB256.toBytes ++ v.toBytes)
    (hgas : 58800 ≤ (initDevm msg).gasLeft)
    (hfits : MoveFits (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) (initSevm msg).caller dst v) :
    xferG (initSevm msg) (initDevm msg) ≤ 56500 ∧
    exec (initEvm msg) = .ok (xferPost (initSevm msg) (initDevm msg)
      ((initDevm msg).gasLeft - xferG (initSevm msg) (initDevm msg))) ∧
    FrameLands Dai.cert.prog (initSevm msg) (initDevm msg) (xferPost (initSevm msg) (initDevm msg)
        ((initDevm msg).gasLeft - xferG (initSevm msg) (initDevm msg))) (xferG (initSevm msg) (initDevm msg)) 1
      (moveStor (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) (initSevm msg).caller dst v)
      ((getOrigAcct (initSevm msg) (initSevm msg).currentTarget).stor =
          Devm.getStor (initDevm msg) (initSevm msg).currentTarget ∧
        (initSevm msg).currentTarget ∉ (initDevm msg).createdAccounts ∧
        balSlot (initSevm msg).caller ≠ balSlot dst) := by
  have hsel : Blanc.Sevm.selector (initSevm msg) = 0xa9059cbb :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide) (by rw [hd, List.append_assoc])
  obtain ⟨w4, w36, hl⟩ := Blanc.Lift.dataWord_twoWords hd
  obtain ⟨hu, L⟩ := xfer_landsE (dst := dst) (v := v) (pre := initDevm msg) fork static
    (guards_of hval hsel (by rw [hl]; decide) (by rw [hl]; decide))
    (by unfold xTo; rw [lit4, w4, ff20_and_word, toAdr_toB256])
    (by unfold xVal; rw [lit36, w36]) rfl rfl hgas hfits
  exact ⟨hu, (exec_iff_exec_eq 0 _ _ (.ok _)).mp (lift_exact Dai.cert_check Dai.jumps_ok hcode fork L.run), L⟩

/-- `transferFrom` as a message, exactly. -/
theorem pull_msgE {msg : Msg} {src dst : Adr} {v : B256} (hcode : (initSevm msg).code = Dai.code)
    (fork : CoveredFork (initSevm msg).benvStat.fork) (static : (initSevm msg).isStatic = false)
    (hval : (initSevm msg).value = 0)
    (hd : (initSevm msg).data = abiSelectorBytes 0x23b872dd ++ src.toB256.toBytes ++ dst.toB256.toBytes ++
      v.toBytes)
    (hgas : 90300 ≤ (initDevm msg).gasLeft)
    (hfits : PullFits (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) src (initSevm msg).caller
      dst v) :
    pullG (initSevm msg) (initDevm msg) ≤ 88000 ∧
    exec (initEvm msg) = .ok (pullPost (initSevm msg) (initDevm msg)
      ((initDevm msg).gasLeft - pullG (initSevm msg) (initDevm msg))) ∧
    FrameLands Dai.cert.prog (initSevm msg) (initDevm msg) (pullPost (initSevm msg) (initDevm msg)
        ((initDevm msg).gasLeft - pullG (initSevm msg) (initDevm msg))) (pullG (initSevm msg) (initDevm msg)) 1
      (moveStor (spendStor (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) src
        (initSevm msg).caller v) src dst v)
      (PullR (initSevm msg) (initDevm msg) src dst) := by
  have hsel : Blanc.Sevm.selector (initSevm msg) = 0x23b872dd :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide)
      (by rw [hd, List.append_assoc, List.append_assoc])
  obtain ⟨w4, w36, w68⟩ := Blanc.Lift.Curve3Pool.cc_dataWord_threeWords hd
  have hl : (initSevm msg).data.length = 100 := by
    rw [hd]
    simp only [List.length_append, B256.length_toBytes, abiSelectorBytes_length]
  obtain ⟨hu, L⟩ := pull_landsE (src := src) (dst := dst) (v := v) (pre := initDevm msg) fork static
    (guards_of hval hsel (by rw [hl]; decide) (by rw [hl]; decide))
    (by unfold pSrc; rw [lit4, w4, ff20_and_word, toAdr_toB256])
    (by unfold pTo; rw [lit36, w36, ff20_and_word, toAdr_toB256])
    (by unfold pVal; rw [lit36, show Bytes.toB256 [32] + (36 : B256) = 68 by decide, w68]) rfl rfl hgas hfits
  exact ⟨hu, (exec_iff_exec_eq 0 _ _ (.ok _)).mp (lift_exact Dai.cert_check Dai.jumps_ok hcode fork L.run), L⟩

/-- `balanceOf` as a message, exactly. -/
theorem bal_msgE {msg : Msg} {a : Adr} (hcode : (initSevm msg).code = Dai.code)
    (fork : CoveredFork (initSevm msg).benvStat.fork) (hval : (initSevm msg).value = 0)
    (hd : (initSevm msg).data = abiSelectorBytes 0x70a08231 ++ a.toB256.toBytes)
    (hgas : 5300 ≤ (initDevm msg).gasLeft) :
    balG (initSevm msg) (initDevm msg) ≤ 3000 ∧
    exec (initEvm msg) = .ok (balPost (initSevm msg) (initDevm msg)
      ((initDevm msg).gasLeft - balG (initSevm msg) (initDevm msg))) ∧
    FrameLands Dai.cert.prog (initSevm msg) (initDevm msg) (balPost (initSevm msg) (initDevm msg)
        ((initDevm msg).gasLeft - balG (initSevm msg) (initDevm msg))) (balG (initSevm msg) (initDevm msg))
      ((Devm.getStor (initDevm msg) (initSevm msg).currentTarget).get (balSlot a))
      (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) True := by
  have hsel : Blanc.Sevm.selector (initSevm msg) = 0x70a08231 :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide) hd
  have hl : (initSevm msg).data.length = 36 := by
    rw [hd]
    simp only [List.length_append, B256.length_toBytes, abiSelectorBytes_length]
  obtain ⟨hu, L⟩ := bal_landsE (a := a) (pre := initDevm msg) fork
    (guards_of hval hsel (by rw [hl]; decide) (by rw [hl]; decide))
    (by unfold bHolder; rw [lit4, Blanc.Lift.Curve3Pool.cc_dataWord_oneWord hd, ff20_and_word, toAdr_toB256])
    rfl rfl hgas
  exact ⟨hu, (exec_iff_exec_eq 0 _ _ (.ok _)).mp (lift_exact Dai.cert_check Dai.jumps_ok hcode fork L.run), L⟩

section Premises

variable {sevm : Sevm} {t amt : B256} {W W' : Devm → Prop} {U : Nat} {ii oi : B256}

/-- **The pool's `transfer(msg.sender, amt)` into DAI, exactly.** -/
theorem dai_coinPushExact (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hprec : ¬ sevm.benvStat.rules.isPrecomp t.toAdr)
    (hne : t.toAdr ≠ sevm.currentTarget) (hU : 63000 ≤ U)
    (hii : ii.toNat + 0x44 ≤ 4096) (hoi : oi.toNat + 32 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Dai.code ∧
      MoveFits (b.getStor t.toAdr) sevm.currentTarget sevm.caller amt)
    (hW' : ∀ b d, W b → CoinLeaves t.toAdr (moveStor (b.getStor t.toAdr) sevm.currentTarget sevm.caller amt)
      ((getOrigAcct sevm t.toAdr).stor = b.getStor t.toAdr ∧ t.toAdr ∉ b.createdAccounts ∧
        balSlot sevm.currentTarget ≠ balSlot sevm.caller) b d → W' d) :
    MutableCallProfile sevm W W' t (transferSel ++ sevm.caller.toB256.toBytes ++ amt.toBytes) RawCallOk U ii
      0x44 oi (coinDebit xferG sevm t ii 0x44 oi) (coinNext (fun s p => xferPost s p 0) sevm t ii 0x44 oi) := by
  refine coinMutProfile 58800 56500 xferG (fun s p => xferPost s p 0) xferG_reframe hfork hdepth
    (by rw [prec_false hprec]) (by omega) (by omega) (by decide)
    (by rw [show (0x44 : B256).toNat = 0x44 from rfl]; exact hii) hoi ?_
  intro b S M G hWb _ hin hfwd
  obtain ⟨hc, hfits⟩ := hW b hWb
  obtain ⟨hu, hexec, L⟩ := xfer_msgE (msg := callMsg0 sevm b S M G t ii 0x44 oi 0x20)
    (dst := sevm.caller) (v := amt) hc hfork
    (by rw [callMsg0_isStatic]; exact hstatic) rfl
    (by rw [callMsg0_data, hin, transferSel_abi]) hfwd hfits
  refine ⟨by rw [hc]; exact dai_undelegated, hu, _, hexec, L.keeps.error, L.gas,
    xferPost_canon (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))
      (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20)) _ _, ?_, ?_, L.keeps.other _ (Ne.symm hne), L.keeps.code 4,
    hW' b _ hWb (leaves_of_lands L (fun r => r))⟩
  · rw [L.out]; exact rawCallOk_one
  · rw [L.out]; decide +kernel

/-- **The pool's `transferFrom(msg.sender, self, amt)` into DAI, exactly.** -/
theorem dai_coinPullExact (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hprec : ¬ sevm.benvStat.rules.isPrecomp t.toAdr)
    (hne : t.toAdr ≠ sevm.currentTarget) (hU : 95000 ≤ U)
    (hii : ii.toNat + 0x64 ≤ 4096) (hoi : oi.toNat + 32 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Dai.code ∧
      PullFits (b.getStor t.toAdr) sevm.caller sevm.currentTarget sevm.currentTarget amt)
    (hW' : ∀ b d, W b → CoinLeaves t.toAdr
        (moveStor (spendStor (b.getStor t.toAdr) sevm.caller sevm.currentTarget amt)
          sevm.caller sevm.currentTarget amt)
      ((getOrigAcct sevm t.toAdr).stor = b.getStor t.toAdr ∧ t.toAdr ∉ b.createdAccounts ∧
        allowSlot sevm.caller sevm.currentTarget ≠ balSlot sevm.caller ∧
        allowSlot sevm.caller sevm.currentTarget ≠ balSlot sevm.currentTarget ∧
        balSlot sevm.caller ≠ balSlot sevm.currentTarget) b d → W' d) :
    MutableCallProfile sevm W W' t
      (transferFromSel ++ sevm.caller.toB256.toBytes ++ sevm.currentTarget.toB256.toBytes ++ amt.toBytes)
      RawCallOk U ii 0x64 oi (coinDebit pullG sevm t ii 0x64 oi)
      (coinNext (fun s p => pullPost s p 0) sevm t ii 0x64 oi) := by
  refine coinMutProfile 90300 88000 pullG (fun s p => pullPost s p 0) pullG_reframe hfork hdepth
    (by rw [prec_false hprec]) (by omega) (by omega) (by decide)
    (by rw [show (0x64 : B256).toNat = 0x64 from rfl]; exact hii) hoi ?_
  intro b S M G hWb _ hin hfwd
  obtain ⟨hc, hfits⟩ := hW b hWb
  obtain ⟨hu, hexec, L⟩ := pull_msgE (msg := callMsg0 sevm b S M G t ii 0x64 oi 0x20)
    (src := sevm.caller) (dst := sevm.currentTarget) (v := amt) hc hfork
    (by rw [callMsg0_isStatic]; exact hstatic) rfl
    (by rw [callMsg0_data, hin, transferFromSel_abi]) hfwd hfits
  refine ⟨by rw [hc]; exact dai_undelegated, hu, _, hexec, L.keeps.error, L.gas,
    pullPost_canon (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x64 oi 0x20))
      (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x64 oi 0x20)) _ _, ?_, ?_, L.keeps.other _ (Ne.symm hne), L.keeps.code 4,
    hW' b _ hWb (leaves_of_lands L (fun r => r))⟩
  · rw [L.out]; exact rawCallOk_one
  · rw [L.out]; decide +kernel

/-- **The pool's `balanceOf(self)` into DAI, exactly.** -/
theorem dai_coinBalExact {B : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hdepth : sevm.depth ≠ 0) (hprec : ¬ sevm.benvStat.rules.isPrecomp t.toAdr) (hU : 70000 ≤ U)
    (hii : ii.toNat + 0x24 ≤ 4096) (hoi : oi.toNat + 32 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Dai.code ∧
      (b.getStor t.toAdr).get (balSlot sevm.currentTarget) = B)
    (hW' : ∀ b d, W b → (∀ a, Devm.getStor d a = Devm.getStor b a) →
      (∀ a, d.getCode a = b.getCode a) → W' d) :
    StaticWordCallProfile sevm W W' t (balanceOfData sevm.currentTarget) B U ii 0x24 oi
      (coinStaticDebit balG sevm t ii 0x24 oi) (coinStaticNext (fun s p => balPost s p 0) sevm t ii 0x24 oi) := by
  refine coinStaticProfile 5300 3000 balG (fun s p => balPost s p 0) balG_reframe hfork hdepth
    (by rw [prec_false hprec]) (by omega) (by omega) (by decide)
    (by rw [show (0x24 : B256).toNat = 0x24 from rfl]; exact hii) hoi ?_
  intro b S M G hWb hin_ hin hfwd
  obtain ⟨hc, hB⟩ := hW b hWb
  obtain ⟨hu, hexec, L⟩ := bal_msgE (msg := staticMsg sevm b S M G t ii 0x24 oi 0x20)
    (a := sevm.currentTarget) hc hfork rfl
    (by rw [staticMsg_data, hin]; unfold balanceOfData; rw [balanceOfSel_abi]) hfwd
  have hst := callChildPost_state' (parent b S M G t ii 0x24 oi 0x20) (balPost (initSevm (staticMsg sevm b S M G t ii 0x24 oi 0x20)) (initDevm (staticMsg sevm b S M G t ii 0x24 oi 0x20)) ((initDevm (staticMsg sevm b S M G t ii 0x24 oi 0x20)).gasLeft - balG (initSevm (staticMsg sevm b S M G t ii 0x24 oi 0x20)) (initDevm (staticMsg sevm b S M G t ii 0x24 oi 0x20)))) oi.toNat (0x20 : B256).toNat
  refine ⟨by rw [hc]; exact dai_undelegated, hu, _, hexec, L.keeps.error, L.gas, balPost_canon (initSevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii 0x24 oi 0x20))
      (initDevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii 0x24 oi 0x20)) _ _,
    ?_, L.keeps.code 4, hW' b _ hWb (fun a => ?_) (fun a => ?_)⟩
  · rw [L.out, ← hB]; rfl
  · rw [getStor_of_state hst]
    by_cases ha : a = t.toAdr
    · subst ha; exact L.stor
    · exact L.keeps.other a ha
  · rw [getCode_of_state hst]; exact L.keeps.code a

end Premises

end Blanc.Composition.Curve3PoolDai
