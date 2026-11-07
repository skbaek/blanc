import Blanc.Lift.UsdtExact
import Blanc.Composition.Curve3PoolUsdtCoin
import Blanc.Composition.Curve3PoolCoinFloorKit

/-!
# USDT's exact profiles at the pool's call sites

`usdt_coinPushExact`, `usdt_coinPullExact` and `usdt_coinBalExact`: the bounded `usdt_coin*OkAt`, whose run,
ledger and keeps are reused unchanged, with the charge closed (`xferG`, `pullG`, `balG`) and the successor
canonical. The bounded law and the exact run start from one entry, and `exec` is a function, so they land in one
post; the two charges agree because both are below the gas given.
-/

namespace Blanc.Composition.Curve3PoolUsdt

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.Composition.Curve3PoolCalleeLive
open Blanc.Lift.AccumulatedWalk (FrameLands StopLands)
open Blanc.Composition.Curve3Pool3CrvInstance (CoinLeaves prec_false getCode_of_state
  getStor_of_state transferSel_abi transferFromSel_abi balanceOfSel_abi)
open Blanc.Composition.Curve3PoolCoinChild Blanc.Composition.Curve3PoolCoinExactKit
open Blanc.Lift.Usdt

/-- **`transfer` as a message, exactly.** -/
theorem xfer_msgE {msg : Msg} {dst : Adr} {v : B256} (hcode : (initSevm msg).code = Usdt.code)
    (fork : ShanghaiOnwards (initSevm msg).benvStat.fork) (static : (initSevm msg).isStatic = false)
    (hval : (initSevm msg).value = 0)
    (hd : (initSevm msg).data = abiSelectorBytes 0xa9059cbb ++ dst.toB256.toBytes ++ v.toBytes)
    (hgas : 100056 ≤ (initDevm msg).gasLeft)
    (hdep : NotDeprecated (Devm.getStor (initDevm msg) (initSevm msg).currentTarget))
    (hfits : XferFits (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) (initSevm msg).caller dst v) :
    xferG (initSevm msg) (initDevm msg) ≤ 97756 ∧
      exec (initEvm msg) = .ok (xferPost (initSevm msg) (initDevm msg)
        ((initDevm msg).gasLeft - xferG (initSevm msg) (initDevm msg))) ∧
      StopLands Usdt.cert.prog (initSevm msg) (initDevm msg) (xferPost (initSevm msg) (initDevm msg)
          ((initDevm msg).gasLeft - xferG (initSevm msg) (initDevm msg))) (xferG (initSevm msg) (initDevm msg))
        (moveStor (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) (initSevm msg).caller dst v
          (feeOf (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) v))
        ((getOrigAcct (initSevm msg) (initSevm msg).currentTarget).stor =
            Devm.getStor (initDevm msg) (initSevm msg).currentTarget ∧
          (initSevm msg).currentTarget ∉ (initDevm msg).createdAccounts ∧
          MoveApart (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) (initSevm msg).caller dst v
            (feeOf (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) v)) := by
  obtain ⟨post, used, hexec, hu, L⟩ := xfer_msg hcode fork static hval hd hgas hdep hfits
  have hsel : Blanc.Sevm.selector (initSevm msg) = 0xa9059cbb :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide) (by rw [hd, List.append_assoc])
  obtain ⟨w4, w36, hl⟩ := Blanc.Lift.dataWord_twoWords hd
  obtain ⟨hle, hrun⟩ := xfer_runE (dst := dst) (v := v) (pre := initDevm msg) fork static
    (lguards_of hval hsel (by rw [hl]; decide) (by rw [hl]; decide) (by rw [hl]; decide))
    (by unfold xTo; rw [lit4, w4, ff20_and_word, toAdr_toB256])
    (by unfold xVal; rw [lit36, w36]) rfl rfl hgas hdep hfits
  have hE := (exec_iff_exec_eq 0 _ _ (.ok _)).mp (lift_exact Usdt.cert_check Usdt.jumps_ok hcode fork hrun)
  exact ⟨hle, hE, stop_exact hexec hE (xferPost_gasLeft _ _ _) hu hle (by omega) L⟩

/-- What `transferFrom`'s calldata gives its frame. -/
theorem pull_facts {msg : Msg} {src dst : Adr} {v : B256} (hval : (initSevm msg).value = 0)
    (hd : (initSevm msg).data = abiSelectorBytes 0x23b872dd ++ src.toB256.toBytes ++ dst.toB256.toBytes ++
      v.toBytes) :
    LGuards (initSevm msg) 0x23b872dd (Bytes.toB256 [96]) ∧ pSrc (initSevm msg) = src.toB256 ∧
      pTo (initSevm msg) = dst.toB256 ∧ pVal (initSevm msg) = v := by
  have hsel : Blanc.Sevm.selector (initSevm msg) = 0x23b872dd :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide)
      (by rw [hd, List.append_assoc, List.append_assoc])
  obtain ⟨w4, w36, w68⟩ := Blanc.Lift.Curve3Pool.cc_dataWord_threeWords hd
  have hl : (initSevm msg).data.length = 100 := by
    rw [hd]
    simp only [List.length_append, B256.length_toBytes, abiSelectorBytes_length]
  exact ⟨lguards_of hval hsel (by rw [hl]; decide) (by rw [hl]; decide) (by rw [hl]; decide),
    by unfold pSrc; rw [lit4, w4, ff20_and_word, toAdr_toB256],
    by unfold pTo; rw [lit36, w36, ff20_and_word, toAdr_toB256],
    by unfold pVal; rw [lit36, show Bytes.toB256 [32] + (36 : B256) = 68 by decide, w68]⟩

/-- **`transferFrom` as a message, exactly.** -/
theorem pull_msgE {msg : Msg} {src dst : Adr} {v : B256} (hcode : (initSevm msg).code = Usdt.code)
    (fork : ShanghaiOnwards (initSevm msg).benvStat.fork) (static : (initSevm msg).isStatic = false)
    (hval : (initSevm msg).value = 0)
    (hd : (initSevm msg).data = abiSelectorBytes 0x23b872dd ++ src.toB256.toBytes ++ dst.toB256.toBytes ++
      v.toBytes)
    (hgas : 124480 ≤ (initDevm msg).gasLeft)
    (hdep : NotDeprecated (Devm.getStor (initDevm msg) (initSevm msg).currentTarget))
    (hfits : PullFits (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) src (initSevm msg).caller
      dst v) :
    pullG (initSevm msg) (initDevm msg) ≤ 122180 ∧
      exec (initEvm msg) = .ok (pullP (initSevm msg) (initDevm msg)
        ((initDevm msg).gasLeft - pullG (initSevm msg) (initDevm msg))) ∧
      StopLands Usdt.cert.prog (initSevm msg) (initDevm msg) (pullP (initSevm msg) (initDevm msg)
          ((initDevm msg).gasLeft - pullG (initSevm msg) (initDevm msg))) (pullG (initSevm msg) (initDevm msg))
        (moveStor (spendStor (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) src
          (initSevm msg).caller v) src dst v
          (feeOf (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) v))
        ((getOrigAcct (initSevm msg) (initSevm msg).currentTarget).stor =
            Devm.getStor (initDevm msg) (initSevm msg).currentTarget ∧
          (initSevm msg).currentTarget ∉ (initDevm msg).createdAccounts ∧
          PullApart (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) src (initSevm msg).caller dst v
            (feeOf (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) v)) := by
  obtain ⟨post, used, hexec, hu, L⟩ := pull_msg hcode fork static hval hd hgas hdep hfits
  obtain ⟨g, hs1, hs2, hs3⟩ := pull_facts hval hd
  obtain ⟨hle, hrun⟩ := pull_runE (src := src) (dst := dst) (v := v) (pre := initDevm msg) fork static g hs1 hs2 hs3
    rfl rfl hgas hdep hfits
  have hE := (exec_iff_exec_eq 0 _ _ (.ok _)).mp (lift_exact Usdt.cert_check Usdt.jumps_ok hcode fork hrun)
  exact ⟨hle, hE, stop_exact hexec hE (pullP_gasLeft _ _ _) hu hle (by omega) L⟩

/-- **`balanceOf` as a message, exactly.** -/
theorem bal_msgE {msg : Msg} {a : Adr} (hcode : (initSevm msg).code = Usdt.code)
    (fork : ShanghaiOnwards (initSevm msg).benvStat.fork) (hval : (initSevm msg).value = 0)
    (hd : (initSevm msg).data = abiSelectorBytes 0x70a08231 ++ a.toB256.toBytes)
    (hgas : 7331 ≤ (initDevm msg).gasLeft)
    (hdep : NotDeprecated (Devm.getStor (initDevm msg) (initSevm msg).currentTarget)) :
    balG (initSevm msg) (initDevm msg) ≤ 5031 ∧
      exec (initEvm msg) = .ok (balP (initSevm msg) (initDevm msg)
        ((initDevm msg).gasLeft - balG (initSevm msg) (initDevm msg))) ∧
      FrameLands Usdt.cert.prog (initSevm msg) (initDevm msg) (balP (initSevm msg) (initDevm msg)
          ((initDevm msg).gasLeft - balG (initSevm msg) (initDevm msg))) (balG (initSevm msg) (initDevm msg))
        ((Devm.getStor (initDevm msg) (initSevm msg).currentTarget).get (balSlot a))
        (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) True := by
  obtain ⟨post, used, hexec, hu, L⟩ := bal_msg hcode fork hval hd hgas hdep
  have hsel : Blanc.Sevm.selector (initSevm msg) = 0x70a08231 :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide) hd
  have hl : (initSevm msg).data.length = 36 := by
    rw [hd]
    simp only [List.length_append, B256.length_toBytes, abiSelectorBytes_length]
  obtain ⟨hle, hrun⟩ := bal_runE (pre := initDevm msg) fork
    (lguards_of hval hsel (by rw [hl]; decide) (by rw [hl]; decide) (by rw [hl]; decide)) rfl rfl hgas hdep
  have hE := (exec_iff_exec_eq 0 _ _ (.ok _)).mp (lift_exact Usdt.cert_check Usdt.jumps_ok hcode fork hrun)
  exact ⟨hle, hE, lands_exact hexec hE (balP_gasLeft _ _ _) hu hle (by omega) L⟩

/-- `transfer` as a message, at the store sentry above its cost. -/
theorem xfer_execF {msg : Msg} {dst : Adr} {v : B256} (hcode : (initSevm msg).code = Usdt.code)
    (fork : ShanghaiOnwards (initSevm msg).benvStat.fork) (static : (initSevm msg).isStatic = false)
    (hval : (initSevm msg).value = 0)
    (hd : (initSevm msg).data = abiSelectorBytes 0xa9059cbb ++ dst.toB256.toBytes ++ v.toBytes)
    (hgas : xferG (initSevm msg) (initDevm msg) + 2300 ≤ (initDevm msg).gasLeft)
    (hdep : NotDeprecated (Devm.getStor (initDevm msg) (initSevm msg).currentTarget))
    (hfits : XferFits (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) (initSevm msg).caller dst v) :
    exec (initEvm msg) = .ok (xferPost (initSevm msg) (initDevm msg)
      ((initDevm msg).gasLeft - xferG (initSevm msg) (initDevm msg))) := by
  have hsel : Blanc.Sevm.selector (initSevm msg) = 0xa9059cbb :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide) (by rw [hd, List.append_assoc])
  obtain ⟨w4, w36, hl⟩ := Blanc.Lift.dataWord_twoWords hd
  exact (exec_iff_exec_eq 0 _ _ (.ok _)).mp (lift_exact Usdt.cert_check Usdt.jumps_ok hcode fork
    (xfer_runF (dst := dst) (v := v) (pre := initDevm msg) fork static
      (lguards_of hval hsel (by rw [hl]; decide) (by rw [hl]; decide) (by rw [hl]; decide))
      (by unfold xTo; rw [lit4, w4, ff20_and_word, toAdr_toB256])
      (by unfold xVal; rw [lit36, w36]) rfl rfl hgas hdep hfits))

/-- `transferFrom` as a message, at the store sentry above its cost. -/
theorem pull_execF {msg : Msg} {src dst : Adr} {v : B256} (hcode : (initSevm msg).code = Usdt.code)
    (fork : ShanghaiOnwards (initSevm msg).benvStat.fork) (static : (initSevm msg).isStatic = false)
    (hval : (initSevm msg).value = 0)
    (hd : (initSevm msg).data = abiSelectorBytes 0x23b872dd ++ src.toB256.toBytes ++ dst.toB256.toBytes ++
      v.toBytes)
    (hgas : pullG (initSevm msg) (initDevm msg) + 2300 ≤ (initDevm msg).gasLeft)
    (hdep : NotDeprecated (Devm.getStor (initDevm msg) (initSevm msg).currentTarget))
    (hfits : PullFits (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) src (initSevm msg).caller
      dst v) :
    exec (initEvm msg) = .ok (pullP (initSevm msg) (initDevm msg)
      ((initDevm msg).gasLeft - pullG (initSevm msg) (initDevm msg))) := by
  obtain ⟨g, hs1, hs2, hs3⟩ := pull_facts hval hd
  exact (exec_iff_exec_eq 0 _ _ (.ok _)).mp (lift_exact Usdt.cert_check Usdt.jumps_ok hcode fork
    (pull_runF (src := src) (dst := dst) (v := v) (pre := initDevm msg) fork static g hs1 hs2 hs3
      rfl rfl hgas hdep hfits))

/-- `balanceOf` as a message, above its cost. -/
theorem bal_execF {msg : Msg} {a : Adr} (hcode : (initSevm msg).code = Usdt.code)
    (fork : ShanghaiOnwards (initSevm msg).benvStat.fork) (hval : (initSevm msg).value = 0)
    (hd : (initSevm msg).data = abiSelectorBytes 0x70a08231 ++ a.toB256.toBytes)
    (hgas : balG (initSevm msg) (initDevm msg) ≤ (initDevm msg).gasLeft)
    (hdep : NotDeprecated (Devm.getStor (initDevm msg) (initSevm msg).currentTarget)) :
    exec (initEvm msg) = .ok (balP (initSevm msg) (initDevm msg)
      ((initDevm msg).gasLeft - balG (initSevm msg) (initDevm msg))) := by
  have hsel : Blanc.Sevm.selector (initSevm msg) = 0x70a08231 :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide) hd
  have hl : (initSevm msg).data.length = 36 := by
    rw [hd]
    simp only [List.length_append, B256.length_toBytes, abiSelectorBytes_length]
  exact (exec_iff_exec_eq 0 _ _ (.ok _)).mp (lift_exact Usdt.cert_check Usdt.jumps_ok hcode fork
    (bal_runF (pre := initDevm msg) fork
      (lguards_of hval hsel (by rw [hl]; decide) (by rw [hl]; decide) (by rw [hl]; decide)) rfl rfl hgas hdep))

section Premises

variable {sevm : Sevm} {t amt : B256} {W W' : Devm → Prop} {U : Nat} {ii oi : B256}

/-- **The pool's `transfer(msg.sender, amt)` into USDT, exactly.** -/
theorem usdt_coinPushExact (hfork : ShanghaiOnwards sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hprec : ¬ sevm.benvStat.rules.isPrecomp t.toAdr)
    (hne : t.toAdr ≠ sevm.currentTarget) (hU : 104744 ≤ U)
    (hii : ii.toNat + 0x44 ≤ 4096) (hoi : oi.toNat + 32 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Usdt.code ∧ NotDeprecated (b.getStor t.toAdr) ∧
      XferFits (b.getStor t.toAdr) sevm.currentTarget sevm.caller amt)
    (hW' : ∀ b d, W b → CoinLeaves t.toAdr
        (moveStor (b.getStor t.toAdr) sevm.currentTarget sevm.caller amt (feeOf (b.getStor t.toAdr) amt))
      ((getOrigAcct sevm t.toAdr).stor = b.getStor t.toAdr ∧ t.toAdr ∉ b.createdAccounts ∧
        MoveApart (b.getStor t.toAdr) sevm.currentTarget sevm.caller amt (feeOf (b.getStor t.toAdr) amt)) b d → W' d) :
    MutableCallProfile sevm W W' t (transferSel ++ sevm.caller.toB256.toBytes ++ amt.toBytes) RawCallOk U ii
      0x44 oi (coinDebit xferG sevm t ii 0x44 oi) (coinNext (fun s p => xferPost s p 0) sevm t ii 0x44 oi) := by
  refine coinMutProfile 100056 97756 xferG (fun s p => xferPost s p 0) xferG_reframe hfork hdepth
    (by rw [prec_false hprec]) (by omega) (by omega) (by decide)
    (by rw [show (0x44 : B256).toNat = 0x44 from rfl]; exact hii) hoi ?_
  intro b S M G hWb _ hin hfwd
  obtain ⟨hc, hdep, hfits⟩ := hW b hWb
  obtain ⟨hu, hexec, L⟩ := xfer_msgE (msg := callMsg0 sevm b S M G t ii 0x44 oi 0x20)
    (dst := sevm.caller) (v := amt) hc hfork
    (by rw [callMsg0_isStatic]; exact hstatic) rfl
    (by rw [callMsg0_data, hin, transferSel_abi]) hfwd hdep hfits
  refine ⟨by rw [hc]; exact usdt_undelegated, hu, _, hexec, L.keeps.error, L.gas,
    xferPost_canon (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))
      (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20)) _ _, ?_, ?_,
    L.keeps.other _ (Ne.symm hne), L.keeps.code 4, hW' b _ hWb (leaves_of_stop L (fun r => r))⟩
  · rw [L.out]; exact rawCallOk_empty
  · rw [L.out]; decide

/-- **The pool's `transferFrom(msg.sender, self, amt)` into USDT, exactly.** -/
theorem usdt_coinPullExact (hfork : ShanghaiOnwards sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hprec : ¬ sevm.benvStat.rules.isPrecomp t.toAdr)
    (hne : t.toAdr ≠ sevm.currentTarget) (hU : 129555 ≤ U)
    (hii : ii.toNat + 0x64 ≤ 4096) (hoi : oi.toNat + 32 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Usdt.code ∧ NotDeprecated (b.getStor t.toAdr) ∧
      PullFits (b.getStor t.toAdr) sevm.caller sevm.currentTarget sevm.currentTarget amt)
    (hW' : ∀ b d, W b → CoinLeaves t.toAdr
        (moveStor (spendStor (b.getStor t.toAdr) sevm.caller sevm.currentTarget amt)
          sevm.caller sevm.currentTarget amt (feeOf (b.getStor t.toAdr) amt))
      ((getOrigAcct sevm t.toAdr).stor = b.getStor t.toAdr ∧ t.toAdr ∉ b.createdAccounts ∧
        PullApart (b.getStor t.toAdr) sevm.caller sevm.currentTarget sevm.currentTarget amt
          (feeOf (b.getStor t.toAdr) amt)) b d → W' d) :
    MutableCallProfile sevm W W' t
      (transferFromSel ++ sevm.caller.toB256.toBytes ++ sevm.currentTarget.toB256.toBytes ++ amt.toBytes)
      RawCallOk U ii 0x64 oi (coinDebit pullG sevm t ii 0x64 oi)
      (coinNext (fun s p => pullP s p 0) sevm t ii 0x64 oi) := by
  refine coinMutProfile 124480 122180 pullG (fun s p => pullP s p 0) pullG_reframe hfork hdepth
    (by rw [prec_false hprec]) (by omega) (by omega) (by decide)
    (by rw [show (0x64 : B256).toNat = 0x64 from rfl]; exact hii) hoi ?_
  intro b S M G hWb _ hin hfwd
  obtain ⟨hc, hdep, hfits⟩ := hW b hWb
  obtain ⟨hu, hexec, L⟩ := pull_msgE (msg := callMsg0 sevm b S M G t ii 0x64 oi 0x20)
    (src := sevm.caller) (dst := sevm.currentTarget) (v := amt) hc hfork
    (by rw [callMsg0_isStatic]; exact hstatic) rfl
    (by rw [callMsg0_data, hin, transferFromSel_abi]) hfwd hdep hfits
  refine ⟨by rw [hc]; exact usdt_undelegated, hu, _, hexec, L.keeps.error, L.gas,
    pullP_canon (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x64 oi 0x20))
      (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x64 oi 0x20)) _ _, ?_, ?_,
    L.keeps.other _ (Ne.symm hne), L.keeps.code 4, hW' b _ hWb (leaves_of_stop L (fun r => r))⟩
  · rw [L.out]; exact rawCallOk_empty
  · rw [L.out]; decide

/-- **The pool's `balanceOf(self)` into USDT, exactly.** -/
theorem usdt_coinBalExact {B : B256} (hfork : ShanghaiOnwards sevm.benvStat.fork)
    (hdepth : sevm.depth ≠ 0) (hprec : ¬ sevm.benvStat.rules.isPrecomp t.toAdr) (hU : 70000 ≤ U)
    (hii : ii.toNat + 0x24 ≤ 4096) (hoi : oi.toNat + 32 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Usdt.code ∧ NotDeprecated (b.getStor t.toAdr) ∧
      (b.getStor t.toAdr).get (balSlot sevm.currentTarget) = B)
    (hW' : ∀ b d, W b → (∀ a, Devm.getStor d a = Devm.getStor b a) →
      (∀ a, d.getCode a = b.getCode a) → W' d) :
    StaticWordCallProfile sevm W W' t (balanceOfData sevm.currentTarget) B U ii 0x24 oi
      (coinStaticDebit balG sevm t ii 0x24 oi) (coinStaticNext (fun s p => balP s p 0) sevm t ii 0x24 oi) := by
  refine coinStaticProfile 7331 5031 balG (fun s p => balP s p 0) balG_reframe hfork hdepth
    (by rw [prec_false hprec]) (by omega) (by omega) (by decide)
    (by rw [show (0x24 : B256).toNat = 0x24 from rfl]; exact hii) hoi ?_
  intro b S M G hWb _ hin hfwd
  obtain ⟨hc, hdep, hB⟩ := hW b hWb
  obtain ⟨hu, hexec, L⟩ := bal_msgE (msg := staticMsg sevm b S M G t ii 0x24 oi 0x20)
    (a := sevm.currentTarget) hc hfork rfl
    (by rw [staticMsg_data, hin]; unfold balanceOfData; rw [balanceOfSel_abi]) hfwd hdep
  have hst := callChildPost_state' (parent b S M G t ii 0x24 oi 0x20) (balP (initSevm (staticMsg sevm b S M G t ii 0x24 oi 0x20)) (initDevm (staticMsg sevm b S M G t ii 0x24 oi 0x20)) ((initDevm (staticMsg sevm b S M G t ii 0x24 oi 0x20)).gasLeft - balG (initSevm (staticMsg sevm b S M G t ii 0x24 oi 0x20)) (initDevm (staticMsg sevm b S M G t ii 0x24 oi 0x20)))) oi.toNat (0x20 : B256).toNat
  refine ⟨by rw [hc]; exact usdt_undelegated, hu, _, hexec, L.keeps.error, L.gas,
    balP_canon (initSevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii 0x24 oi 0x20))
      (initDevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii 0x24 oi 0x20)) _ _,
    ?_, L.keeps.code 4, hW' b _ hWb (fun a => ?_) (fun a => ?_)⟩
  · rw [L.out, ← hB]; rfl
  · rw [getStor_of_state hst]
    by_cases ha : a = t.toAdr
    · subst ha; exact L.stor
    · exact L.keeps.other a ha
  · rw [getCode_of_state hst]; exact L.keeps.code a

/-- **`transfer`'s exact profile at its floor.** -/
theorem usdt_coinPushFloor {K : Nat} (hK : 2300 + (K + 97756) / 64 + 1 ≤ K)
    (hfork : ShanghaiOnwards sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hprec : ¬ sevm.benvStat.rules.isPrecomp t.toAdr)
    (hne : t.toAdr ≠ sevm.currentTarget) (hU : 104744 ≤ U) (hUw : U < 2 ^ 256) (hs : GasStable W')
    (hii : ii.toNat + 0x44 ≤ 4096) (hoi : oi.toNat + 32 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Usdt.code ∧ NotDeprecated (b.getStor t.toAdr) ∧
      XferFits (b.getStor t.toAdr) sevm.currentTarget sevm.caller amt)
    (hW' : ∀ b d, W b → CoinLeaves t.toAdr
        (moveStor (b.getStor t.toAdr) sevm.currentTarget sevm.caller amt (feeOf (b.getStor t.toAdr) amt))
      ((getOrigAcct sevm t.toAdr).stor = b.getStor t.toAdr ∧ t.toAdr ∉ b.createdAccounts ∧
        MoveApart (b.getStor t.toAdr) sevm.currentTarget sevm.caller amt (feeOf (b.getStor t.toAdr) amt)) b d → W' d) :
    MutableFloorProfile sevm W W' t (transferSel ++ sevm.caller.toB256.toBytes ++ amt.toBytes) RawCallOk U K ii
      0x44 oi (coinDebit xferG sevm t ii 0x44 oi) (coinNext (fun s p => xferPost s p 0) sevm t ii 0x44 oi) := by
  refine coinMutFloor 2300 K 97756 xferG (fun s p => xferPost s p 0) xferG_reframe hfork hdepth (by rw [prec_false hprec]) hK hUw hs
    (usdt_coinPushExact hfork hstatic hdepth hprec hne hU hii hoi hW hW')
    (fun b S M _ _ => by
      have h := xferW_le (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))
        (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))
      rwa [xferW_eq] at h) ?_
  intro b S M G hWb _ hin hfwd
  obtain ⟨hc, hdep, hfits⟩ := hW b hWb
  exact ⟨by rw [hc]; exact usdt_undelegated, _, xfer_execF (msg := callMsg0 sevm b S M G t ii 0x44 oi 0x20)
    (dst := sevm.caller) (v := amt) hc hfork (by rw [callMsg0_isStatic]; exact hstatic) rfl
    (by rw [callMsg0_data, hin, transferSel_abi]) hfwd hdep hfits, xferPost_gasLeft _ _ _,
    xferPost_canon (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))
      (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20)) _ _⟩

/-- **`transferFrom`'s exact profile at its floor.** -/
theorem usdt_coinPullFloor {K : Nat} (hK : 2300 + (K + 122180) / 64 + 1 ≤ K)
    (hfork : ShanghaiOnwards sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hprec : ¬ sevm.benvStat.rules.isPrecomp t.toAdr)
    (hne : t.toAdr ≠ sevm.currentTarget) (hU : 129555 ≤ U) (hUw : U < 2 ^ 256) (hs : GasStable W')
    (hii : ii.toNat + 0x64 ≤ 4096) (hoi : oi.toNat + 32 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Usdt.code ∧ NotDeprecated (b.getStor t.toAdr) ∧
      PullFits (b.getStor t.toAdr) sevm.caller sevm.currentTarget sevm.currentTarget amt)
    (hW' : ∀ b d, W b → CoinLeaves t.toAdr
        (moveStor (spendStor (b.getStor t.toAdr) sevm.caller sevm.currentTarget amt)
          sevm.caller sevm.currentTarget amt (feeOf (b.getStor t.toAdr) amt))
      ((getOrigAcct sevm t.toAdr).stor = b.getStor t.toAdr ∧ t.toAdr ∉ b.createdAccounts ∧
        PullApart (b.getStor t.toAdr) sevm.caller sevm.currentTarget sevm.currentTarget amt
          (feeOf (b.getStor t.toAdr) amt)) b d → W' d) :
    MutableFloorProfile sevm W W' t
      (transferFromSel ++ sevm.caller.toB256.toBytes ++ sevm.currentTarget.toB256.toBytes ++ amt.toBytes)
      RawCallOk U K ii 0x64 oi (coinDebit pullG sevm t ii 0x64 oi)
      (coinNext (fun s p => pullP s p 0) sevm t ii 0x64 oi) := by
  refine coinMutFloor 2300 K 122180 pullG (fun s p => pullP s p 0) pullG_reframe hfork hdepth (by rw [prec_false hprec]) hK hUw hs
    (usdt_coinPullExact hfork hstatic hdepth hprec hne hU hii hoi hW hW')
    (fun b S M _ _ => by
      have h := pullW_le (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x64 oi 0x20))
        (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x64 oi 0x20))
      rwa [pullW_eq] at h) ?_
  intro b S M G hWb _ hin hfwd
  obtain ⟨hc, hdep, hfits⟩ := hW b hWb
  exact ⟨by rw [hc]; exact usdt_undelegated, _, pull_execF (msg := callMsg0 sevm b S M G t ii 0x64 oi 0x20)
    (src := sevm.caller) (dst := sevm.currentTarget) (v := amt) hc hfork
    (by rw [callMsg0_isStatic]; exact hstatic) rfl (by rw [callMsg0_data, hin, transferFromSel_abi]) hfwd hdep hfits,
    pullP_gasLeft _ _ _, pullP_canon (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x64 oi 0x20))
      (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x64 oi 0x20)) _ _⟩

/-- **`balanceOf`'s exact profile at its floor.** -/
theorem usdt_coinBalFloor {B : B256} {K : Nat} (hK : (K + 5031) / 64 + 1 ≤ K) (hfork : ShanghaiOnwards sevm.benvStat.fork)
    (hdepth : sevm.depth ≠ 0) (hprec : ¬ sevm.benvStat.rules.isPrecomp t.toAdr) (hU : 70000 ≤ U)
    (hUw : U < 2 ^ 256) (hs : GasStable W')
    (hii : ii.toNat + 0x24 ≤ 4096) (hoi : oi.toNat + 32 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Usdt.code ∧ NotDeprecated (b.getStor t.toAdr) ∧
      (b.getStor t.toAdr).get (balSlot sevm.currentTarget) = B)
    (hW' : ∀ b d, W b → (∀ a, Devm.getStor d a = Devm.getStor b a) →
      (∀ a, d.getCode a = b.getCode a) → W' d) :
    StaticWordFloorProfile sevm W W' t (balanceOfData sevm.currentTarget) B U K ii 0x24 oi
      (coinStaticDebit balG sevm t ii 0x24 oi) (coinStaticNext (fun s p => balP s p 0) sevm t ii 0x24 oi) := by
  refine coinStaticFloor 0 K 5031 balG (fun s p => balP s p 0) balG_reframe hfork hdepth (by rw [prec_false hprec])
    (by omega) hUw hs (usdt_coinBalExact hfork hdepth hprec hU hii hoi hW hW')
    (fun b S M _ _ => by
      have h := balW_le (initSevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii 0x24 oi 0x20))
        (initDevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii 0x24 oi 0x20))
      rwa [balW_eq] at h) ?_
  intro b S M G hWb _ hin hfwd
  obtain ⟨hc, hdep, -⟩ := hW b hWb
  exact ⟨by rw [hc]; exact usdt_undelegated, _, bal_execF (msg := staticMsg sevm b S M G t ii 0x24 oi 0x20)
    (a := sevm.currentTarget) hc hfork rfl
    (by rw [staticMsg_data, hin]; unfold balanceOfData; rw [balanceOfSel_abi]) hfwd hdep,
    balP_gasLeft _ _ _, balP_canon (initSevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii 0x24 oi 0x20))
      (initDevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii 0x24 oi 0x20)) _ _⟩

/-- The balance read's debit, in the frame's memory. -/
theorem usdt_balDebit_le (hii : ii.toNat + 0x24 ≤ 4096) (hoi : oi.toNat + 32 ≤ 4096) (b : Devm) (S : List B256) (M : Mem) :
    coinStaticDebit balG sevm t ii 0x24 oi b S M ≤ 8047 := by
  have he := ext_le (b := b.withGasLeft 0) (S := S) (M := M) (ii := ii) (is := 0x24) (oi := oi) (os := 0x20)
    (by rw [show (0x24 : B256).toNat = 0x24 from rfl]; exact hii)
    (by rw [show (0x20 : B256).toNat = 0x20 from rfl]; exact hoi)
  have ha := acc_le (b := b.withGasLeft 0) (t := t)
  have h := balW_le (initSevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii 0x24 oi 0x20))
    (initDevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii 0x24 oi 0x20))
  rw [balW_eq] at h
  unfold coinStaticDebit
  omega

end Premises

end Blanc.Composition.Curve3PoolUsdt
