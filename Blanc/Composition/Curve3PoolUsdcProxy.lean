import Blanc.Lift.Usdc.ProxyLands
import Blanc.Composition.Curve3PoolCoinChild

/-!
# A USDC message, through the proxy

`proxy_msg`: a message into the proxy's code from a non-admin caller, with data of at most `100` bytes
under a selector that is no admin entry, runs and lands where the implementation child lands, at a
charge `8300` above the child's. The child is the delegate message of the proxy's own frame, at gas
above a floor; nothing here names an implementation.
-/

namespace Blanc.Composition.UsdcLive

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc
open Blanc.Lift.AccumulatedWalk
open Blanc.Composition.Curve3PoolCalleeLive (extCost_two_le)

/-- What a USDC account must hold at a frame's entry for the proxy to delegate to `I`. -/
structure ProxyReady (sevm : Sevm) (b : Devm) (I : ByteArray) : Prop where
  undel : getDelegatedCodeAddress I = none
  code : b.getCode ((b.getStorVal sevm.currentTarget pKI).toAdr) = I
  prec : sevm.benvStat.rules.isPrecomp (b.getStorVal sevm.currentTarget pKI).toAdr = false
  admin : sevm.caller ≠ (b.getStorVal sevm.currentTarget pKA).toAdr

theorem pI_eq (sevm : Sevm) (b : Devm) : pI sevm b = b.getStorVal sevm.currentTarget pKI := by
  unfold pI
  rw [gsv, afterSload_getStor, gsv]

theorem dExt_le (sevm : Sevm) (b : Devm) (hlen : sevm.data.length ≤ 100) : dExt sevm b ≤ 12 := by
  have h := extCost_two_le (dPop sevm b 0) (i1 := (Bytes.toB256 [0]).toNat)
    (s1 := (Nat.toB256 sevm.data.length).toNat) (i2 := (Bytes.toB256 [0]).toNat)
    (s2 := (Bytes.toB256 [0]).toNat) (B := 100)
    (by rw [B256.toNat_toB256_of_lt (by omega)]; exact Nat.le_trans (Nat.le_of_eq (Nat.zero_add _)) hlen)
    (by decide)
  have hc : calculateMemoryGasCost 100 = 12 := by decide
  rw [hc] at h
  exact h

/-- **A message into the proxy lands where its implementation child lands.** The child's law is
given at every delegate gas `Y` that forwards at least `F`. -/
theorem proxy_msg {msg : Msg} {I : ByteArray} {s w : B256} {σ' : Stor} {R R' : Prop} {prog : List SFunc}
    (F Cu : Nat) (hCu : Cu ≤ F)
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
      ∃ C u, exec (initEvm (dMsg (initSevm msg) (initDevm msg) Y)) = .ok C ∧ u ≤ Cu ∧
        FrameLands prog (initSevm (dMsg (initSevm msg) (initDevm msg) Y))
          (initDevm (dMsg (initSevm msg) (initDevm msg) Y)) C u w σ' R')
    (hR : R → R') :
    ∃ post used, exec (initEvm msg) = .ok post ∧ used ≤ Cu + 8300 ∧
      FrameLands Proxy.cert.prog (initSevm msg) (initDevm msg) post used w σ' R := by
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
  obtain ⟨C, u, hexec, hu, L⟩ := hchild _ hfw
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
  obtain ⟨post, P⟩ := proxy_lands (s := s) (u := u) (w := w) (σ' := σ') (R := R) fork hdepth pf hundel hprec hs hm hG
    (by omega) (by omega) hexec L.keeps.error L.out L.gas L.keeps
    (by
      have := L.stor
      exact this)
    (fun r => L.refund (hR r))
  exact ⟨post, _, (exec_iff_exec_eq 0 _ _ (.ok _)).mp (lift_exact Proxy.cert_check Proxy.jumps_ok hcode fork P.run),
    by omega, P⟩

/-- What a USDC account at `t` must hold in a call site's world `b` for its proxy to delegate to `I`
when the frame `sevm` calls it. -/
structure ProxyAt (sevm : Sevm) (b : Devm) (t : Adr) (I : ByteArray) : Prop where
  undel : getDelegatedCodeAddress I = none
  code : b.getCode ((b.getStorVal t pKI).toAdr) = I
  prec : sevm.benvStat.rules.isPrecomp (b.getStorVal t pKI).toAdr = false
  admin : sevm.currentTarget ≠ (b.getStorVal t pKA).toAdr

end Blanc.Composition.UsdcLive
