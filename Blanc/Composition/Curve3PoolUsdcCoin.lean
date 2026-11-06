import Blanc.Composition.Curve3PoolUsdcProxy

/-!
# The pool's coin premises through USDC's proxy, for any implementation

`XferLaw`, `PullLaw`, `BalLaw`: what an implementation's code must do when entered with the pool's
calls. Given them, `usdc_coinPushOkAt`, `usdc_coinPullOkAt` and `usdc_coinBalOkAt` discharge the
pool's coin premises for an account holding the proxy's certified runtime with that implementation
behind its slot. The proxy's `DELEGATECALL` spends one more call-depth level, so the pool's frame needs
depth `2`.
-/

namespace Blanc.Composition.UsdcLive

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc Blanc.Lift.Curve3Pool
open Blanc.Composition.Curve3PoolCalleeLive
open Blanc.Lift.AccumulatedWalk (FrameLands)
open Blanc.Composition.Curve3Pool3CrvInstance (CoinLeaves prec_false rawCallOk_one
  transferSel_abi transferFromSel_abi balanceOfSel_abi)
open Blanc.Composition.Curve3PoolCoinChild

/-- **An implementation's `transfer` law**, on a message. -/
def XferLaw (I : ByteArray) (prog : List SFunc) (F Cu : Nat) (Fit : Stor → Adr → Adr → B256 → Prop)
    (mv : Stor → Adr → Adr → B256 → Stor) (Apart : Adr → Adr → Prop) : Prop :=
  ∀ {msg : Msg} {dst : Adr} {v : B256}, (initSevm msg).code = I → CoveredFork (initSevm msg).benvStat.fork →
    (initSevm msg).isStatic = false → (initSevm msg).value = 0 →
    (initSevm msg).data = abiSelectorBytes 0xa9059cbb ++ dst.toB256.toBytes ++ v.toBytes →
    F ≤ (initDevm msg).gasLeft →
    Fit (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) (initSevm msg).caller dst v →
    ∃ C u, exec (initEvm msg) = .ok C ∧ u ≤ Cu ∧ FrameLands prog (initSevm msg) (initDevm msg) C u 1
      (mv (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) (initSevm msg).caller dst v)
      ((getOrigAcct (initSevm msg) (initSevm msg).currentTarget).stor =
          Devm.getStor (initDevm msg) (initSevm msg).currentTarget ∧
        (initSevm msg).currentTarget ∉ (initDevm msg).createdAccounts ∧ Apart (initSevm msg).caller dst)

/-- **An implementation's `transferFrom` law**, on a message. -/
def PullLaw (I : ByteArray) (prog : List SFunc) (F Cu : Nat) (Fit : Stor → Adr → Adr → Adr → B256 → Prop)
    (mv : Stor → Adr → Adr → Adr → B256 → Stor) (Apart : Adr → Adr → Adr → Prop) : Prop :=
  ∀ {msg : Msg} {src dst : Adr} {v : B256}, (initSevm msg).code = I → CoveredFork (initSevm msg).benvStat.fork →
    (initSevm msg).isStatic = false → (initSevm msg).value = 0 →
    (initSevm msg).data = abiSelectorBytes 0x23b872dd ++ src.toB256.toBytes ++ dst.toB256.toBytes ++ v.toBytes →
    F ≤ (initDevm msg).gasLeft →
    Fit (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) src (initSevm msg).caller dst v →
    ∃ C u, exec (initEvm msg) = .ok C ∧ u ≤ Cu ∧ FrameLands prog (initSevm msg) (initDevm msg) C u 1
      (mv (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) src (initSevm msg).caller dst v)
      ((getOrigAcct (initSevm msg) (initSevm msg).currentTarget).stor =
          Devm.getStor (initDevm msg) (initSevm msg).currentTarget ∧
        (initSevm msg).currentTarget ∉ (initDevm msg).createdAccounts ∧ Apart src (initSevm msg).caller dst)

/-- **An implementation's `balanceOf` law**, on a message, static or not. -/
def BalLaw (I : ByteArray) (prog : List SFunc) (F Cu : Nat) (ans : Stor → Adr → B256) : Prop :=
  ∀ {msg : Msg} {a : Adr}, (initSevm msg).code = I → CoveredFork (initSevm msg).benvStat.fork →
    (initSevm msg).value = 0 → (initSevm msg).data = abiSelectorBytes 0x70a08231 ++ a.toB256.toBytes →
    F ≤ (initDevm msg).gasLeft →
    ∃ C u, exec (initEvm msg) = .ok C ∧ u ≤ Cu ∧ FrameLands prog (initSevm msg) (initDevm msg) C u
      (ans (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) a)
      (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) True

section Child

variable {msg : Msg} {I : ByteArray} {Y : Nat}

theorem child_code (hr : ProxyReady (initSevm msg) (initDevm msg) I) :
    (initSevm (dMsg (initSevm msg) (initDevm msg) Y)).code = I := by
  show (pBase (initSevm msg) (initDevm msg)).getCode (pI (initSevm msg) (initDevm msg)).toAdr = _
  rw [afterSload_getCode, afterSload_getCode, pI_eq]
  exact hr.code

theorem child_static : (initSevm (dMsg (initSevm msg) (initDevm msg) Y)).isStatic =
    (initSevm msg).isStatic := by
  show (false || (initSevm msg).isStatic) = _
  rw [Bool.false_or]

theorem child_refund {P : Prop} (r : (getOrigAcct (initSevm msg) (initSevm msg).currentTarget).stor =
      Devm.getStor (initDevm msg) (initSevm msg).currentTarget ∧
    (initSevm msg).currentTarget ∉ (initDevm msg).createdAccounts ∧ P) :
    (getOrigAcct (initSevm (dMsg (initSevm msg) (initDevm msg) Y))
        (initSevm (dMsg (initSevm msg) (initDevm msg) Y)).currentTarget).stor =
      Devm.getStor (initDevm msg) (initSevm msg).currentTarget ∧
    (initSevm (dMsg (initSevm msg) (initDevm msg) Y)).currentTarget ∉
        (initDevm (dMsg (initSevm msg) (initDevm msg) Y)).createdAccounts ∧ P :=
  ⟨r.1, by rw [dMsg_created]; exact r.2.1, r.2.2⟩

end Child

/-- **`transfer` as a message into the proxy.** -/
theorem proxyXfer_msg {I : ByteArray} {prog : List SFunc} {F Cu : Nat} {Fit : Stor → Adr → Adr → B256 → Prop}
    {mv : Stor → Adr → Adr → B256 → Stor} {Apart : Adr → Adr → Prop} (law : XferLaw I prog F Cu Fit mv Apart)
    (hCu : Cu ≤ F) {msg : Msg} {dst : Adr} {v : B256} (hcode : (initSevm msg).code = Proxy.code)
    (fork : CoveredFork (initSevm msg).benvStat.fork) (hdepth : (initSevm msg).depth ≠ 0)
    (static : (initSevm msg).isStatic = false) (hval : (initSevm msg).value = 0)
    (hr : ProxyReady (initSevm msg) (initDevm msg) I)
    (hd : (initSevm msg).data = abiSelectorBytes 0xa9059cbb ++ dst.toB256.toBytes ++ v.toBytes)
    (hgas : F + F / 63 + 8300 ≤ (initDevm msg).gasLeft) (hG : (initDevm msg).gasLeft < 2 ^ 256)
    (hfits : Fit (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) (initSevm msg).caller dst v) :
    ∃ post used, exec (initEvm msg) = .ok post ∧ used ≤ Cu + 8300 ∧
      FrameLands Proxy.cert.prog (initSevm msg) (initDevm msg) post used 1
        (mv (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) (initSevm msg).caller dst v)
        ((getOrigAcct (initSevm msg) (initSevm msg).currentTarget).stor =
            Devm.getStor (initDevm msg) (initSevm msg).currentTarget ∧
          (initSevm msg).currentTarget ∉ (initDevm msg).createdAccounts ∧ Apart (initSevm msg).caller dst) := by
  have hsel : Blanc.Sevm.selector (initSevm msg) = 0xa9059cbb :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide) (by rw [hd, List.append_assoc])
  obtain ⟨-, -, hl⟩ := Blanc.Lift.dataWord_twoWords hd
  refine proxy_msg (s := 0xa9059cbb) (prog := prog) F Cu hCu hcode fork hdepth hr (by omega) (by omega) hsel
    (by decide) (by decide) (by decide) (by decide) (by decide) hgas hG ?_ (fun r => r)
  intro Y hF
  obtain ⟨C, u, hexec, hu, L⟩ := law (msg := dMsg (initSevm msg) (initDevm msg) Y) (dst := dst) (v := v)
    (child_code hr) fork (child_static.trans static) hval
    (by rw [dMsg_data _ _ _ (by omega)]; exact hd) hF (by rw [dMsg_getStor]; exact hfits)
  rw [dMsg_getStor] at L
  exact ⟨C, u, hexec, hu, L.run, L.gas, L.out, L.keeps, L.stor, fun r => L.refund (child_refund r)⟩

/-- **`transferFrom` as a message into the proxy.** -/
theorem proxyPull_msg {I : ByteArray} {prog : List SFunc} {F Cu : Nat} {Fit : Stor → Adr → Adr → Adr → B256 → Prop}
    {mv : Stor → Adr → Adr → Adr → B256 → Stor} {Apart : Adr → Adr → Adr → Prop} (law : PullLaw I prog F Cu Fit mv Apart)
    (hCu : Cu ≤ F) {msg : Msg} {src dst : Adr} {v : B256} (hcode : (initSevm msg).code = Proxy.code)
    (fork : CoveredFork (initSevm msg).benvStat.fork) (hdepth : (initSevm msg).depth ≠ 0)
    (static : (initSevm msg).isStatic = false) (hval : (initSevm msg).value = 0)
    (hr : ProxyReady (initSevm msg) (initDevm msg) I)
    (hd : (initSevm msg).data = abiSelectorBytes 0x23b872dd ++ src.toB256.toBytes ++ dst.toB256.toBytes ++ v.toBytes)
    (hgas : F + F / 63 + 8300 ≤ (initDevm msg).gasLeft) (hG : (initDevm msg).gasLeft < 2 ^ 256)
    (hfits : Fit (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) src (initSevm msg).caller dst v) :
    ∃ post used, exec (initEvm msg) = .ok post ∧ used ≤ Cu + 8300 ∧
      FrameLands Proxy.cert.prog (initSevm msg) (initDevm msg) post used 1
        (mv (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) src (initSevm msg).caller dst v)
        ((getOrigAcct (initSevm msg) (initSevm msg).currentTarget).stor =
            Devm.getStor (initDevm msg) (initSevm msg).currentTarget ∧
          (initSevm msg).currentTarget ∉ (initDevm msg).createdAccounts ∧ Apart src (initSevm msg).caller dst) := by
  have hsel : Blanc.Sevm.selector (initSevm msg) = 0x23b872dd :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide)
      (by rw [hd, List.append_assoc, List.append_assoc])
  have hl : (initSevm msg).data.length = 100 := by
    rw [hd]
    simp only [List.length_append, B256.length_toBytes, abiSelectorBytes_length]
  refine proxy_msg (s := 0x23b872dd) (prog := prog) F Cu hCu hcode fork hdepth hr (by omega) (by omega) hsel
    (by decide) (by decide) (by decide) (by decide) (by decide) hgas hG ?_ (fun r => r)
  intro Y hF
  obtain ⟨C, u, hexec, hu, L⟩ := law (msg := dMsg (initSevm msg) (initDevm msg) Y) (src := src) (dst := dst) (v := v)
    (child_code hr) fork (child_static.trans static) hval
    (by rw [dMsg_data _ _ _ (by omega)]; exact hd) hF (by rw [dMsg_getStor]; exact hfits)
  rw [dMsg_getStor] at L
  exact ⟨C, u, hexec, hu, L.run, L.gas, L.out, L.keeps, L.stor, fun r => L.refund (child_refund r)⟩

/-- **`balanceOf` as a message into the proxy.** -/
theorem proxyBal_msg {I : ByteArray} {prog : List SFunc} {F Cu : Nat} {ans : Stor → Adr → B256}
    (law : BalLaw I prog F Cu ans) (hCu : Cu ≤ F) {msg : Msg} {a : Adr} (hcode : (initSevm msg).code = Proxy.code)
    (fork : CoveredFork (initSevm msg).benvStat.fork) (hdepth : (initSevm msg).depth ≠ 0)
    (hval : (initSevm msg).value = 0)
    (hr : ProxyReady (initSevm msg) (initDevm msg) I)
    (hd : (initSevm msg).data = abiSelectorBytes 0x70a08231 ++ a.toB256.toBytes)
    (hgas : F + F / 63 + 8300 ≤ (initDevm msg).gasLeft) (hG : (initDevm msg).gasLeft < 2 ^ 256) :
    ∃ post used, exec (initEvm msg) = .ok post ∧ used ≤ Cu + 8300 ∧
      FrameLands Proxy.cert.prog (initSevm msg) (initDevm msg) post used
        (ans (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) a)
        (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) True := by
  have hsel : Blanc.Sevm.selector (initSevm msg) = 0x70a08231 :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide) hd
  have hl : (initSevm msg).data.length = 36 := by
    rw [hd]
    simp only [List.length_append, B256.length_toBytes, abiSelectorBytes_length]
  refine proxy_msg (s := 0x70a08231) (prog := prog) (R' := True) F Cu hCu hcode fork hdepth hr (by omega) (by omega) hsel
    (by decide) (by decide) (by decide) (by decide) (by decide) hgas hG ?_ (fun r => r)
  intro Y hF
  obtain ⟨C, u, hexec, hu, L⟩ := law (msg := dMsg (initSevm msg) (initDevm msg) Y) (a := a)
    (child_code hr) fork hval (by rw [dMsg_data _ _ _ (by omega)]; exact hd) hF
  rw [dMsg_getStor] at L
  exact ⟨C, u, hexec, hu, L⟩

/-! ## The coin premises -/

section Premises

variable {sevm : Sevm} {t amt : B256} {W W' : Devm → Prop} {U : Nat} {ii oi : B256} {I : ByteArray}
  {prog : List SFunc} {F Cu : Nat}

/-- **The pool's `transfer(msg.sender, amt)` into USDC succeeds**, at any window inside the first 4 KiB,
at depth `2`, wherever the transfer fits the coin's ledger. -/
theorem usdc_coinPushOkAt {Fit : Stor → Adr → Adr → B256 → Prop} {mv : Stor → Adr → Adr → B256 → Stor}
    {Apart : Adr → Adr → Prop} (law : XferLaw I prog F Cu Fit mv Apart) (hCu : Cu ≤ F)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : 2 ≤ sevm.depth) (hprec : ¬ sevm.benvStat.rules.isPrecomp t.toAdr)
    (hne : t.toAdr ≠ sevm.currentTarget)
    (hU : (F + F / 63 + 8300) + (F + F / 63 + 8300) / 63 + 3100 ≤ U)
    (hii : ii.toNat + 0x44 ≤ 4096) (hoi : oi.toNat + 32 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Proxy.code ∧ ProxyAt sevm b t.toAdr I ∧
      Fit (b.getStor t.toAdr) sevm.currentTarget sevm.caller amt)
    (hW' : ∀ b d, W b → CoinLeaves t.toAdr (mv (b.getStor t.toAdr) sevm.currentTarget sevm.caller amt)
      ((getOrigAcct sevm t.toAdr).stor = b.getStor t.toAdr ∧ t.toAdr ∉ b.createdAccounts ∧
        Apart sevm.currentTarget sevm.caller) b d → W' d) :
    CoinPushOkAt sevm W W' t amt U ii oi := by
  refine mutCallOkAt_of_childWith (F + F / 63 + 8300) (Cu + 8300) hfork (by omega) (by rw [prec_false hprec]) hU
    (by omega) (by rw [show (0x44 : B256).toNat = 0x44 from rfl]; exact hii) hoi ?_
  intro b S M G hWb hG hin hfwd
  obtain ⟨hc, hp, hfits⟩ := hW b hWb
  refine ⟨by rw [hc]; exact proxy_undelegated, ?_⟩
  have hgl : fwd b S M G t ii 0x44 oi 0x20 < 2 ^ 256 := by
    unfold fwd except64th; omega
  obtain ⟨cpost, used, hexec, hu, L⟩ := proxyXfer_msg law hCu (msg := callMsg0 sevm b S M G t ii 0x44 oi 0x20)
    (dst := sevm.caller) (v := amt) hc hfork (by show sevm.depth - 1 ≠ 0; omega)
    (by rw [callMsg0_isStatic]; exact hstatic) rfl ⟨hp.undel, hp.code, hp.prec, hp.admin⟩
    (by rw [callMsg0_data, hin, transferSel_abi]) hfwd hgl hfits
  have hgas : cpost.gasLeft = fwd b S M G t ii 0x44 oi 0x20 - used := L.gas
  refine ⟨cpost, hexec, L.keeps.error, by omega, by omega, ?_, ?_, L.keeps.other _ (Ne.symm hne), L.keeps.code 4,
    hW' b _ hWb (leaves_of_lands L (fun r => r))⟩
  · rw [L.out]; exact rawCallOk_one
  · rw [L.out]; decide +kernel

/-- **The pool's `transferFrom(msg.sender, self, amt)` into USDC succeeds**, at any window inside the first
4 KiB, at depth `2`, wherever the pull fits the coin's ledger. -/
theorem usdc_coinPullOkAt {Fit : Stor → Adr → Adr → Adr → B256 → Prop} {mv : Stor → Adr → Adr → Adr → B256 → Stor}
    {Apart : Adr → Adr → Adr → Prop} (law : PullLaw I prog F Cu Fit mv Apart) (hCu : Cu ≤ F)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : 2 ≤ sevm.depth) (hprec : ¬ sevm.benvStat.rules.isPrecomp t.toAdr)
    (hne : t.toAdr ≠ sevm.currentTarget)
    (hU : (F + F / 63 + 8300) + (F + F / 63 + 8300) / 63 + 3100 ≤ U)
    (hii : ii.toNat + 0x64 ≤ 4096) (hoi : oi.toNat + 32 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Proxy.code ∧ ProxyAt sevm b t.toAdr I ∧
      Fit (b.getStor t.toAdr) sevm.caller sevm.currentTarget sevm.currentTarget amt)
    (hW' : ∀ b d, W b → CoinLeaves t.toAdr
        (mv (b.getStor t.toAdr) sevm.caller sevm.currentTarget sevm.currentTarget amt)
      ((getOrigAcct sevm t.toAdr).stor = b.getStor t.toAdr ∧ t.toAdr ∉ b.createdAccounts ∧
        Apart sevm.caller sevm.currentTarget sevm.currentTarget) b d → W' d) :
    CoinPullOkAt sevm W W' t amt U ii oi := by
  refine mutCallOkAt_of_childWith (F + F / 63 + 8300) (Cu + 8300) hfork (by omega) (by rw [prec_false hprec]) hU
    (by omega) (by rw [show (0x64 : B256).toNat = 0x64 from rfl]; exact hii) hoi ?_
  intro b S M G hWb hG hin hfwd
  obtain ⟨hc, hp, hfits⟩ := hW b hWb
  refine ⟨by rw [hc]; exact proxy_undelegated, ?_⟩
  have hgl : fwd b S M G t ii 0x64 oi 0x20 < 2 ^ 256 := by
    unfold fwd except64th; omega
  obtain ⟨cpost, used, hexec, hu, L⟩ := proxyPull_msg law hCu (msg := callMsg0 sevm b S M G t ii 0x64 oi 0x20)
    (src := sevm.caller) (dst := sevm.currentTarget) (v := amt) hc hfork (by show sevm.depth - 1 ≠ 0; omega)
    (by rw [callMsg0_isStatic]; exact hstatic) rfl ⟨hp.undel, hp.code, hp.prec, hp.admin⟩
    (by rw [callMsg0_data, hin, transferFromSel_abi]) hfwd hgl hfits
  have hgas : cpost.gasLeft = fwd b S M G t ii 0x64 oi 0x20 - used := L.gas
  refine ⟨cpost, hexec, L.keeps.error, by omega, by omega, ?_, ?_, L.keeps.other _ (Ne.symm hne), L.keeps.code 4,
    hW' b _ hWb (leaves_of_lands L (fun r => r))⟩
  · rw [L.out]; exact rawCallOk_one
  · rw [L.out]; decide +kernel

/-- **The pool's `balanceOf(self)` into USDC answers the coin's entry**, at any window inside the first
4 KiB, at depth `2`. -/
theorem usdc_coinBalOkAt {ans : Stor → Adr → B256} {B : B256} (law : BalLaw I prog F Cu ans) (hCu : Cu ≤ F)
    (hF : F + F / 63 + 8300 + (F + F / 63 + 8300) / 63 + 3100 ≤ U) (hCb : Cu + 8300 ≤ 60000)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hdepth : 2 ≤ sevm.depth) (hprec : ¬ sevm.benvStat.rules.isPrecomp t.toAdr) (hU : 70000 ≤ U)
    (hii : ii.toNat + 0x24 ≤ 4096) (hoi : oi.toNat + 32 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Proxy.code ∧ ProxyAt sevm b t.toAdr I ∧
      ans (b.getStor t.toAdr) sevm.currentTarget = B)
    (hW' : ∀ b d, W b → (∀ a, Devm.getStor d a = Devm.getStor b a) →
      (∀ a, d.getCode a = b.getCode a) → W' d) :
    CoinBalOkAt sevm W W' t B U ii oi := by
  refine staticWordOkAt_of_childWith (F + F / 63 + 8300) (Cu + 8300) hfork (by omega) (by rw [prec_false hprec]) hF hCb hU
    (by rw [show (0x24 : B256).toNat = 0x24 from rfl]; exact hii) hoi ?_
  intro b S M G hWb hG hin hfwd
  obtain ⟨hc, hp, hB⟩ := hW b hWb
  refine ⟨by rw [hc]; exact proxy_undelegated, ?_⟩
  have hgl : fwd b S M G t ii 0x24 oi 0x20 < 2 ^ 256 := by
    unfold fwd except64th; omega
  obtain ⟨cpost, used, hexec, hu, L⟩ := proxyBal_msg law hCu (msg := staticMsg sevm b S M G t ii 0x24 oi 0x20)
    (a := sevm.currentTarget) hc hfork (by show sevm.depth - 1 ≠ 0; omega) rfl
    ⟨hp.undel, hp.code, hp.prec, hp.admin⟩
    (by rw [staticMsg_data, hin]; unfold balanceOfData; rw [balanceOfSel_abi]) hfwd hgl
  have hgas : cpost.gasLeft = fwd b S M G t ii 0x24 oi 0x20 - used := L.gas
  have hst := callChildPost_state' (parent b S M G t ii 0x24 oi 0x20) cpost oi.toNat (0x20 : B256).toNat
  refine ⟨cpost, hexec, L.keeps.error, by omega, by omega, ?_, L.keeps.code 4, hW' b _ hWb (fun a => ?_) (fun a => ?_)⟩
  · rw [L.out, ← hB]; rfl
  · rw [Blanc.Composition.Curve3Pool3CrvInstance.getStor_of_state hst]
    by_cases ha : a = t.toAdr
    · subst ha; exact L.stor
    · exact L.keeps.other a ha
  · rw [Blanc.Composition.Curve3Pool3CrvInstance.getCode_of_state hst]; exact L.keeps.code a

end Premises

end Blanc.Composition.UsdcLive
