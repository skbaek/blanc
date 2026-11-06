import Blanc.Lift.Usdc.V22Forward
import Blanc.Composition.Curve3PoolUsdcProxy

/-!
# The pool's coin premises, discharged by USDC's proxy over FiatTokenV2_2

`CoinPushOkAt`, `CoinPullOkAt` and `CoinBalOkAt` for a coin holding the proxy's certified runtime with
FiatTokenV2_2's certified runtime behind its implementation slot. The child of the pool's call site
is the proxy's actual run, whose child in turn is the implementation's (`V22Forward`, `proxy_msg`).
The proxy's `DELEGATECALL` spends one more call-depth level, so the pool's frame needs depth `2`.
-/

namespace Blanc.Composition.Curve3PoolUsdc22

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc Blanc.Lift.Curve3Pool
open Blanc.Composition.Curve3PoolCalleeLive Blanc.Composition.UsdcLive
open Blanc.Lift.AccumulatedWalk (FrameLands guards_of)
open Blanc.Composition.Curve3Pool3CrvInstance (CoinLeaves prec_false rawCallOk_one getCode_of_state
  getStor_of_state transferSel_abi transferFromSel_abi balanceOfSel_abi)
open Blanc.Composition.Curve3PoolCoinChild

theorem lit4' : Bytes.toB256 [4] = 4 := by decide
theorem lit36' : Bytes.toB256 [32] + Bytes.toB256 [4] = 36 := by decide

/-! ## The delegate child, read from its parent message -/

section Child

variable {msg : Msg} {Y : Nat}

theorem child_code (hr : ProxyReady (initSevm msg) (initDevm msg) Impl.code) :
    (initSevm (dMsg (initSevm msg) (initDevm msg) Y)).code = Impl.code := by
  show (pBase (initSevm msg) (initDevm msg)).getCode (pI (initSevm msg) (initDevm msg)).toAdr = _
  rw [afterSload_getCode, afterSload_getCode, pI_eq]
  exact hr.code

theorem child_static : (initSevm (dMsg (initSevm msg) (initDevm msg) Y)).isStatic =
    (initSevm msg).isStatic := by
  show (false || (initSevm msg).isStatic) = _
  rw [Bool.false_or]

end Child

/-- **`transfer` as a message.** -/
theorem xfer_msg {msg : Msg} {dst : Adr} {v : B256} (hcode : (initSevm msg).code = Proxy.code)
    (fork : CoveredFork (initSevm msg).benvStat.fork) (hdepth : (initSevm msg).depth ≠ 0)
    (static : (initSevm msg).isStatic = false) (hval : (initSevm msg).value = 0)
    (hr : ProxyReady (initSevm msg) (initDevm msg) Impl.code)
    (hd : (initSevm msg).data = abiSelectorBytes 0xa9059cbb ++ dst.toB256.toBytes ++ v.toBytes)
    (hgas : 83800 ≤ (initDevm msg).gasLeft) (hG : (initDevm msg).gasLeft < 2 ^ 256)
    (hfits : MoveFits (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) (initSevm msg).caller dst v) :
    ∃ post used, exec (initEvm msg) = .ok post ∧ used ≤ 80300 ∧
      FrameLands Proxy.cert.prog (initSevm msg) (initDevm msg) post used 1
        (creditStor (debitStor (Devm.getStor (initDevm msg) (initSevm msg).currentTarget)
          (initSevm msg).caller v.toNat) dst v.toNat)
        ((getOrigAcct (initSevm msg) (initSevm msg).currentTarget).stor =
            Devm.getStor (initDevm msg) (initSevm msg).currentTarget ∧
          (initSevm msg).currentTarget ∉ (initDevm msg).createdAccounts ∧
          balSlot (initSevm msg).caller ≠ balSlot dst) := by
  have hsel : Blanc.Sevm.selector (initSevm msg) = 0xa9059cbb :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide) (by rw [hd, List.append_assoc])
  obtain ⟨-, -, hl⟩ := Blanc.Lift.dataWord_twoWords hd
  refine proxy_msg (s := 0xa9059cbb) (prog := Impl.cert.prog) 74300 72000 (by decide) hcode fork hdepth hr (by omega) (by omega) hsel
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) hG ?_
    (fun r => r)
  intro Y hF
  have hd' : (initSevm (dMsg (initSevm msg) (initDevm msg) Y)).data = abiSelectorBytes 0xa9059cbb ++
      dst.toB256.toBytes ++ v.toBytes := by
    rw [dMsg_data _ _ _ (by omega)]; exact hd
  have hsel' : Blanc.Sevm.selector (initSevm (dMsg (initSevm msg) (initDevm msg) Y)) = 0xa9059cbb :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide) (by rw [hd', List.append_assoc])
  obtain ⟨w4, w36, hl'⟩ := Blanc.Lift.dataWord_twoWords hd'
  have fork' : CoveredFork (initSevm (dMsg (initSevm msg) (initDevm msg) Y)).benvStat.fork := fork
  obtain ⟨C, u, hu, L⟩ := Blanc.Composition.UsdcLive.xfer_lands (dst := dst) (v := v)
    (sevm := initSevm (dMsg (initSevm msg) (initDevm msg) Y))
    (pre := initDevm (dMsg (initSevm msg) (initDevm msg) Y)) fork' (child_static.trans static)
    (guards_of hval hsel' (by rw [hl']; decide) (by rw [hl']; decide))
    (by unfold xTo; rw [lit4', w4, word_ff20, toAdr_toB256])
    (by unfold xVal; rw [lit36', w36]) rfl rfl hF
    (by rw [dMsg_getStor]; exact hfits)
  rw [dMsg_getStor] at L
  exact ⟨C, u, (exec_iff_exec_eq 0 _ _ (.ok _)).mp (lift_exact Impl.cert_check Impl.jumps_ok
    (child_code hr) fork' L.run), hu, L.run, L.gas, L.out, L.keeps, L.stor,
    fun r => L.refund ⟨r.1, by rw [dMsg_created]; exact r.2.1, r.2.2⟩⟩

/-- **`transferFrom` as a message.** -/
theorem pull_msg {msg : Msg} {src dst : Adr} {v : B256} (hcode : (initSevm msg).code = Proxy.code)
    (fork : CoveredFork (initSevm msg).benvStat.fork) (hdepth : (initSevm msg).depth ≠ 0)
    (static : (initSevm msg).isStatic = false) (hval : (initSevm msg).value = 0)
    (hr : ProxyReady (initSevm msg) (initDevm msg) Impl.code)
    (hd : (initSevm msg).data = abiSelectorBytes 0x23b872dd ++ src.toB256.toBytes ++ dst.toB256.toBytes ++
      v.toBytes)
    (hgas : 114300 ≤ (initDevm msg).gasLeft) (hG : (initDevm msg).gasLeft < 2 ^ 256)
    (hfits : PullFits (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) src (initSevm msg).caller dst v) :
    ∃ post used, exec (initEvm msg) = .ok post ∧ used ≤ 110300 ∧
      FrameLands Proxy.cert.prog (initSevm msg) (initDevm msg) post used 1
        (pullStor (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) src (initSevm msg).caller dst v)
        ((getOrigAcct (initSevm msg) (initSevm msg).currentTarget).stor =
            Devm.getStor (initDevm msg) (initSevm msg).currentTarget ∧
          (initSevm msg).currentTarget ∉ (initDevm msg).createdAccounts ∧
          allowSlot src (initSevm msg).caller ≠ balSlot src ∧
          allowSlot src (initSevm msg).caller ≠ balSlot dst ∧ balSlot src ≠ balSlot dst) := by
  have hsel : Blanc.Sevm.selector (initSevm msg) = 0x23b872dd :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide)
      (by rw [hd, List.append_assoc, List.append_assoc])
  have hl : (initSevm msg).data.length = 100 := by
    rw [hd]
    simp only [List.length_append, B256.length_toBytes, abiSelectorBytes_length]
  refine proxy_msg (s := 0x23b872dd) (prog := Impl.cert.prog) 104300 102000 (by decide) hcode fork hdepth hr (by omega) (by omega) hsel
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) hG ?_
    (fun r => r)
  intro Y hF
  have hd' : (initSevm (dMsg (initSevm msg) (initDevm msg) Y)).data = abiSelectorBytes 0x23b872dd ++
      src.toB256.toBytes ++ dst.toB256.toBytes ++ v.toBytes := by
    rw [dMsg_data _ _ _ (by omega)]; exact hd
  have hsel' : Blanc.Sevm.selector (initSevm (dMsg (initSevm msg) (initDevm msg) Y)) = 0x23b872dd :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide)
      (by rw [hd', List.append_assoc, List.append_assoc])
  obtain ⟨w4, w36, w68⟩ := Blanc.Lift.Curve3Pool.cc_dataWord_threeWords hd'
  have hl' : (initSevm (dMsg (initSevm msg) (initDevm msg) Y)).data.length = 100 := by
    rw [hd']
    simp only [List.length_append, B256.length_toBytes, abiSelectorBytes_length]
  have fork' : CoveredFork (initSevm (dMsg (initSevm msg) (initDevm msg) Y)).benvStat.fork := fork
  obtain ⟨C, u, hu, L⟩ := Blanc.Composition.UsdcLive.pull_lands (src := src) (dst := dst) (v := v)
    (sevm := initSevm (dMsg (initSevm msg) (initDevm msg) Y))
    (pre := initDevm (dMsg (initSevm msg) (initDevm msg) Y)) fork' (child_static.trans static)
    (guards_of hval hsel' (by rw [hl']; decide) (by rw [hl']; decide))
    (by unfold pFrom; rw [lit4', w4, ff20_and_word, toAdr_toB256])
    (by unfold pTo; rw [lit4', show (4 : B256) + Bytes.toB256 [32] = 36 by decide, w36, ff20_and_word, toAdr_toB256])
    (by unfold pVal; rw [show Bytes.toB256 [64] + Bytes.toB256 [4] = 68 by decide, w68]) rfl rfl hF
    (by rw [dMsg_getStor]; exact hfits)
  rw [dMsg_getStor] at L
  exact ⟨C, u, (exec_iff_exec_eq 0 _ _ (.ok _)).mp (lift_exact Impl.cert_check Impl.jumps_ok
    (child_code hr) fork' L.run), hu, L.run, L.gas, L.out, L.keeps, L.stor,
    fun r => L.refund ⟨r.1, by rw [dMsg_created]; exact r.2.1, r.2.2⟩⟩

/-- **`balanceOf` as a message.** -/
theorem bal_msg {msg : Msg} {a : Adr} (hcode : (initSevm msg).code = Proxy.code)
    (fork : CoveredFork (initSevm msg).benvStat.fork) (hdepth : (initSevm msg).depth ≠ 0)
    (hval : (initSevm msg).value = 0)
    (hr : ProxyReady (initSevm msg) (initDevm msg) Impl.code)
    (hd : (initSevm msg).data = abiSelectorBytes 0x70a08231 ++ a.toB256.toBytes)
    (hgas : 14300 ≤ (initDevm msg).gasLeft) (hG : (initDevm msg).gasLeft < 2 ^ 256) :
    ∃ post used, exec (initEvm msg) = .ok post ∧ used ≤ 11800 ∧
      FrameLands Proxy.cert.prog (initSevm msg) (initDevm msg) post used
        (Nat.toB256 (balanceBits ((Devm.getStor (initDevm msg) (initSevm msg).currentTarget).get (balSlot a))))
        (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) True := by
  have hsel : Blanc.Sevm.selector (initSevm msg) = 0x70a08231 :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide) hd
  have hl : (initSevm msg).data.length = 36 := by
    rw [hd]
    simp only [List.length_append, B256.length_toBytes, abiSelectorBytes_length]
  refine proxy_msg (s := 0x70a08231) (prog := Impl.cert.prog) (R' := True) 5800 3500 (by decide) hcode fork hdepth hr (by omega) (by omega) hsel
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) hG ?_ (fun r => r)
  intro Y hF
  have hd' : (initSevm (dMsg (initSevm msg) (initDevm msg) Y)).data =
      abiSelectorBytes 0x70a08231 ++ a.toB256.toBytes := by
    rw [dMsg_data _ _ _ (by omega)]; exact hd
  have hsel' : Blanc.Sevm.selector (initSevm (dMsg (initSevm msg) (initDevm msg) Y)) = 0x70a08231 :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide) hd'
  have hl' : (initSevm (dMsg (initSevm msg) (initDevm msg) Y)).data.length = 36 := by
    rw [hd']
    simp only [List.length_append, B256.length_toBytes, abiSelectorBytes_length]
  have fork' : CoveredFork (initSevm (dMsg (initSevm msg) (initDevm msg) Y)).benvStat.fork := fork
  obtain ⟨C, u, hu, L⟩ := Blanc.Composition.UsdcLive.bal_lands (a := a)
    (sevm := initSevm (dMsg (initSevm msg) (initDevm msg) Y))
    (pre := initDevm (dMsg (initSevm msg) (initDevm msg) Y)) fork'
    (guards_of hval hsel' (by rw [hl']; decide) (by rw [hl']; decide))
    (by unfold bHolder; rw [lit4', Blanc.Lift.Curve3Pool.cc_dataWord_oneWord hd', ff20_and_word, toAdr_toB256])
    rfl rfl hF
  rw [dMsg_getStor] at L
  exact ⟨C, u, (exec_iff_exec_eq 0 _ _ (.ok _)).mp (lift_exact Impl.cert_check Impl.jumps_ok
    (child_code hr) fork' L.run), hu, L⟩

/-! ## The coin premises -/

section Premises

variable {sevm : Sevm} {t amt : B256} {W W' : Devm → Prop} {U : Nat} {ii oi : B256}

/-- **The pool's `transfer(msg.sender, amt)` into USDC over FiatTokenV2_2 succeeds**, at any window
inside the first 4 KiB and `U ≥ 89000`, at depth `2`, wherever the transfer fits the coin's ledger. -/
theorem usdc22_coinPushOkAt (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : 2 ≤ sevm.depth) (hprec : ¬ sevm.benvStat.rules.isPrecomp t.toAdr)
    (hne : t.toAdr ≠ sevm.currentTarget) (hU : 89000 ≤ U)
    (hii : ii.toNat + 0x44 ≤ 4096) (hoi : oi.toNat + 32 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Proxy.code ∧ ProxyAt sevm b t.toAdr Impl.code ∧
      MoveFits (b.getStor t.toAdr) sevm.currentTarget sevm.caller amt)
    (hW' : ∀ b d, W b → CoinLeaves t.toAdr
        (creditStor (debitStor (b.getStor t.toAdr) sevm.currentTarget amt.toNat) sevm.caller amt.toNat)
      ((getOrigAcct sevm t.toAdr).stor = b.getStor t.toAdr ∧ t.toAdr ∉ b.createdAccounts ∧
        balSlot sevm.currentTarget ≠ balSlot sevm.caller) b d → W' d) :
    CoinPushOkAt sevm W W' t amt U ii oi := by
  refine mutCallOkAt_of_childWith 83800 80300 hfork (by omega) (by rw [prec_false hprec]) (by omega) (by omega)
    (by rw [show (0x44 : B256).toNat = 0x44 from rfl]; exact hii) hoi ?_
  intro b S M G hWb hG hin hfwd
  obtain ⟨hc, hp, hfits⟩ := hW b hWb
  refine ⟨by rw [hc]; exact proxy_undelegated, ?_⟩
  have hgl : fwd b S M G t ii 0x44 oi 0x20 < 2 ^ 256 := by
    unfold fwd except64th; omega
  obtain ⟨cpost, used, hexec, hu, L⟩ := xfer_msg (msg := callMsg0 sevm b S M G t ii 0x44 oi 0x20)
    (dst := sevm.caller) (v := amt) hc hfork (by show sevm.depth - 1 ≠ 0; omega)
    (by rw [callMsg0_isStatic]; exact hstatic) rfl ⟨hp.undel, hp.code, hp.prec, hp.admin⟩
    (by rw [callMsg0_data, hin, transferSel_abi]) hfwd hgl hfits
  have hgas : cpost.gasLeft = fwd b S M G t ii 0x44 oi 0x20 - used := L.gas
  refine ⟨cpost, hexec, L.keeps.error, by omega, by omega, ?_, ?_, L.keeps.other _ (Ne.symm hne), L.keeps.code 4,
    hW' b _ hWb (leaves_of_lands L (fun r => r))⟩
  · rw [L.out]; exact rawCallOk_one
  · rw [L.out]; decide +kernel

/-- **The pool's `transferFrom(msg.sender, self, amt)` into USDC over FiatTokenV2_2 succeeds**, at any
window inside the first 4 KiB and `U ≥ 120000`, at depth `2`, wherever the pull fits the coin's ledger. -/
theorem usdc22_coinPullOkAt (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
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
    CoinPullOkAt sevm W W' t amt U ii oi := by
  refine mutCallOkAt_of_childWith 114300 110300 hfork (by omega) (by rw [prec_false hprec]) (by omega) (by omega)
    (by rw [show (0x64 : B256).toNat = 0x64 from rfl]; exact hii) hoi ?_
  intro b S M G hWb hG hin hfwd
  obtain ⟨hc, hp, hfits⟩ := hW b hWb
  refine ⟨by rw [hc]; exact proxy_undelegated, ?_⟩
  have hgl : fwd b S M G t ii 0x64 oi 0x20 < 2 ^ 256 := by
    unfold fwd except64th; omega
  obtain ⟨cpost, used, hexec, hu, L⟩ := pull_msg (msg := callMsg0 sevm b S M G t ii 0x64 oi 0x20)
    (src := sevm.caller) (dst := sevm.currentTarget) (v := amt) hc hfork (by show sevm.depth - 1 ≠ 0; omega)
    (by rw [callMsg0_isStatic]; exact hstatic) rfl ⟨hp.undel, hp.code, hp.prec, hp.admin⟩
    (by rw [callMsg0_data, hin, transferFromSel_abi]) hfwd hgl hfits
  have hgas : cpost.gasLeft = fwd b S M G t ii 0x64 oi 0x20 - used := L.gas
  refine ⟨cpost, hexec, L.keeps.error, by omega, by omega, ?_, ?_, L.keeps.other _ (Ne.symm hne), L.keeps.code 4,
    hW' b _ hWb (leaves_of_lands L (fun r => r))⟩
  · rw [L.out]; exact rawCallOk_one
  · rw [L.out]; decide +kernel

/-- **The pool's `balanceOf(self)` into USDC over FiatTokenV2_2 answers the coin's balance bits**, at
any window inside the first 4 KiB and `U ≥ 70000`, at depth `2`. -/
theorem usdc22_coinBalOkAt {B : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hdepth : 2 ≤ sevm.depth) (hprec : ¬ sevm.benvStat.rules.isPrecomp t.toAdr) (hU : 70000 ≤ U)
    (hii : ii.toNat + 0x24 ≤ 4096) (hoi : oi.toNat + 32 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Proxy.code ∧ ProxyAt sevm b t.toAdr Impl.code ∧
      Nat.toB256 (balanceBits ((b.getStor t.toAdr).get (balSlot sevm.currentTarget))) = B)
    (hW' : ∀ b d, W b → (∀ a, Devm.getStor d a = Devm.getStor b a) →
      (∀ a, d.getCode a = b.getCode a) → W' d) :
    CoinBalOkAt sevm W W' t B U ii oi := by
  refine staticWordOkAt_of_childWith 14300 11800 hfork (by omega) (by rw [prec_false hprec]) (by omega) (by decide) hU
    (by rw [show (0x24 : B256).toNat = 0x24 from rfl]; exact hii) hoi ?_
  intro b S M G hWb hG hin hfwd
  obtain ⟨hc, hp, hB⟩ := hW b hWb
  refine ⟨by rw [hc]; exact proxy_undelegated, ?_⟩
  have hgl : fwd b S M G t ii 0x24 oi 0x20 < 2 ^ 256 := by
    unfold fwd except64th; omega
  obtain ⟨cpost, used, hexec, hu, L⟩ := bal_msg (msg := staticMsg sevm b S M G t ii 0x24 oi 0x20)
    (a := sevm.currentTarget) hc hfork (by show sevm.depth - 1 ≠ 0; omega) rfl
    ⟨hp.undel, hp.code, hp.prec, hp.admin⟩
    (by rw [staticMsg_data, hin]; unfold balanceOfData; rw [balanceOfSel_abi]) hfwd hgl
  have hgas : cpost.gasLeft = fwd b S M G t ii 0x24 oi 0x20 - used := L.gas
  have hst := callChildPost_state' (parent b S M G t ii 0x24 oi 0x20) cpost oi.toNat (0x20 : B256).toNat
  refine ⟨cpost, hexec, L.keeps.error, by omega, by omega, ?_, L.keeps.code 4, hW' b _ hWb (fun a => ?_) (fun a => ?_)⟩
  · rw [L.out, ← hB]; rfl
  · rw [getStor_of_state hst]
    by_cases ha : a = t.toAdr
    · subst ha; exact L.stor
    · exact L.keeps.other a ha
  · rw [Blanc.Composition.Curve3Pool3CrvInstance.getCode_of_state hst]; exact L.keeps.code a

end Premises

end Blanc.Composition.Curve3PoolUsdc22
