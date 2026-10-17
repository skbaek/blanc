import Blanc.Composition.UniswapV2PairUsdcWeth9LegsKit
import Blanc.Lift.Usdc.ProxyOk
import Blanc.Lift.Usdc.Impl.Contract
import Blanc.Composition.UniswapV2PairWeth9SwapLegsCall

/-!
# The USDC proxy frame, forward (U9a)

Gas-exact forward walks of the ZeppelinOS `AdminUpgradeabilityProxy` runtime (`Proxy.cert`) on the
fallback path a non-admin caller takes: the getters `_admin()` (entry 8) and `_implementation()`
(entry 14), `_willFallback()` (entry 22, `require(msg.sender != _admin())`), and the prefix of the
frame up to `_delegate`'s `DELEGATECALL`.
-/

namespace Blanc.Composition.UsdcLive

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc Proxy

local notation "m20" => Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

/-- The admin and implementation slot words as `_admin()`/`_implementation()` compute them. -/
abbrev pKA : B256 := Bytes.toB256 [1] * Bytes.toB256 [0x10, 0xd6, 0xa5, 0x4a, 0x47, 0x54, 0xc8, 0x86, 0x9d, 0x68, 0x86, 0xb5, 0xf5, 0xd7, 0xfb, 0xfa, 0x5b, 0x45, 0x22, 0x23, 0x7e, 0xa5, 0xc6, 0x0d, 0x11, 0xbc, 0x4e, 0x7a, 0x1f, 0xf9, 0x39, 0x0b]
abbrev pKI : B256 := Bytes.toB256 [1] * Bytes.toB256 [0x70, 0x50, 0xc9, 0xe0, 0xf4, 0xca, 0x76, 0x9c, 0x69, 0xbd, 0x3a, 0x8e, 0xf7, 0x40, 0xbc, 0x37, 0x93, 0x4f, 0x8e, 0x2c, 0x03, 0x6e, 0x5a, 0x72, 0x3f, 0xd8, 0xee, 0x04, 0x8e, 0xd3, 0xf8, 0xc3]

/-- **Entry 8, `_admin()`**: the admin word. -/
@[irreducible] noncomputable def p8W (sevm : Sevm) (b : Devm) (ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // CoveredFork sevm.benvStat.fork → S.length < 1000 → ∀ X,
      SFunc.RunExact cert.prog sevm (St b (ret :: S) M (X + c)) t_06a8_c8
        (.returned (St (afterSload sevm b pKA) (b.getStorVal sevm.currentTarget pKA :: S) M X))} :=
  ⟨_, fun fork room X => by xrun⟩

/-- **Entry 14, `_implementation()`**: the implementation word. -/
@[irreducible] noncomputable def p14W (sevm : Sevm) (b : Devm) (ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // CoveredFork sevm.benvStat.fork → S.length < 1000 → ∀ X,
      SFunc.RunExact cert.prog sevm (St b (ret :: S) M (X + c)) t_0651_c14
        (.returned (St (afterSload sevm b pKI) (b.getStorVal sevm.currentTarget pKI :: S) M X))} :=
  ⟨_, fun fork room X => by xrun⟩

/-- **Entry 31**: an empty internal function. -/
@[irreducible] noncomputable def p31W (sevm : Sevm) (b : Devm) (ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // ∀ X, SFunc.RunExact cert.prog sevm (St b (ret :: S) M (X + c)) t_0777_c31
        (.returned (St b S M X))} :=
  ⟨_, fun X => by xrun⟩

/-- **Entry 22, `_willFallback()`**: `require(msg.sender != _admin())`. -/
@[irreducible] noncomputable def p22W (sevm : Sevm) (b : Devm) (ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // CoveredFork sevm.benvStat.fork → S.length < 990 →
      B256.eqCheck (m20 &&& sevm.caller.toB256) (m20 &&& b.getStorVal sevm.currentTarget pKA) = 0 →
      ∀ X, SFunc.RunExact cert.prog sevm (St b (ret :: S) M (X + c)) t_0576_c22
        (.returned (St (afterSload sevm b pKA) S M X))} :=
  ⟨_, fun fork room hadm X => by
    xrun
    xcallM p8W 1 [] fork (by xroom)
    xrun
    xcallM p31W 1 []
    xrun⟩

/-- The proxy frame's branch facts on the fallback path. -/
structure ProxyFacts (sevm : Sevm) (b : Devm) (s : B256) : Prop where
  short : (Nat.toB256 sevm.data.length <? Bytes.toB256 [4]) = 0
  sel : (Bytes.toB256 [255, 255, 255, 255] &&& Sevm.dataWord sevm (Bytes.toB256 [0]) /
    Bytes.toB256 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) = s
  n1 : B256.eqCheck (Bytes.toB256 [54, 89, 207, 230]) s = 0
  n2 : B256.eqCheck (Bytes.toB256 [79, 30, 242, 134]) s = 0
  n3 : B256.eqCheck (Bytes.toB256 [92, 96, 218, 27]) s = 0
  n4 : B256.eqCheck (Bytes.toB256 [143, 40, 57, 112]) s = 0
  n5 : B256.eqCheck (Bytes.toB256 [248, 81, 164, 64]) s = 0
  adm : B256.eqCheck (m20 &&& sevm.caller.toB256) (m20 &&& b.getStorVal sevm.currentTarget pKA) = 0

/-- `_delegate`'s tail after its `DELEGATECALL`: copy the returndata out, return it on success. -/
def dRest : SFunc :=
  .next (.reg .returndatasize) (.next (.push [0x00] (by decide)) (.next (.reg (.dup 0))
    (.next (.reg .returndatacopy) (.next (.reg (.dup 0)) (.next (.push [0x00] (by decide))
      (.next (.reg (.dup 1)) (.next (.reg .eq) (.next (.push [0x06, 0xa3] (by decide))
        (.branch t_069f_c23 t_06a3_c23)))))))))

/-- The implementation word `_implementation()` reads (after `_admin()` warmed the admin slot). -/
abbrev pI (sevm : Sevm) (b : Devm) : B256 := (afterSload sevm b pKA).getStorVal sevm.currentTarget pKI

/-- The base at `_delegate`'s `DELEGATECALL`: both proxy slots read. -/
abbrev pBase (sevm : Sevm) (b : Devm) : Devm := afterSload sevm (afterSload sevm b pKA) pKI

/-- The memory at `_delegate`'s `DELEGATECALL`: the calldata copied to `0`. -/
abbrev pMem (sevm : Sevm) : Mem :=
  (Mem.empty.write 64 (Bytes.toB256 [128]).toBytes).write (Bytes.toB256 [0]).toNat
    (sevm.data.sliceD (Bytes.toB256 [0]).toNat (Nat.toB256 sevm.data.length).toNat 0)

/-- The words under `_delegate`'s `DELEGATECALL` operands. -/
abbrev pRest (sevm : Sevm) (b : Devm) : List B256 :=
  [pI sevm b, Bytes.toB256 [2, 17], Bytes.toB256 [0, 117],
    Bytes.toB256 [255, 255, 255, 255] &&& Sevm.dataWord sevm (Bytes.toB256 [0]) /
      Bytes.toB256 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- **The proxy frame up to `_delegate`'s `DELEGATECALL`** (a non-admin caller, a selector that is no
admin entry point), its charge synthesized. -/
@[irreducible] noncomputable def proxyPreW (sevm : Sevm) (b : Devm) (s : B256) :
    {c : Nat // CoveredFork sevm.benvStat.fork → ProxyFacts sevm b s → ∀ X o,
      SFunc.RunExact cert.prog sevm (St (pBase sevm b) (Nat.toB256 X :: pI sevm b :: Bytes.toB256 [0] ::
        Nat.toB256 sevm.data.length :: Bytes.toB256 [0] :: Bytes.toB256 [0] :: pRest sevm b) (pMem sevm) X)
        (.next (.exec .delegatecall) dRest) o →
      SFunc.RunExact cert.prog sevm (St b [] Mem.empty (X + c)) t_0000_c0 o} :=
  ⟨_, fun fork facts X o hk => by
    obtain ⟨short, sel, n1, n2, n3, n4, n5, adm⟩ := facts
    xrun
    xcallM p22W 1 [] fork (by xroom) adm
    xrun
    xcallM p14W 1 [] fork (by xroom)
    xrun
    exact rk0 hk⟩

/-! ## `_delegate`'s `DELEGATECALL`, as a function of the gas left -/

section Dlg

variable (sevm : Sevm) (b : Devm)

/-- The `DELEGATECALL` state with `Y` gas left (the `GAS` word is `Y`). -/
abbrev dSt (Y : Nat) : Devm :=
  St (pBase sevm b) (Nat.toB256 Y :: pI sevm b :: Bytes.toB256 [0] :: Nat.toB256 sevm.data.length ::
    Bytes.toB256 [0] :: Bytes.toB256 [0] :: pRest sevm b) (pMem sevm) Y

/-- The operands popped. -/
abbrev dPop (Y : Nat) : Devm := St (pBase sevm b) (pRest sevm b) (pMem sevm) Y

/-- The implementation address. -/
abbrev dI : Adr := (pI sevm b).toAdr

/-- The popped state with the implementation warmed. -/
abbrev dWarm (Y : Nat) : Devm := addAccessedAddress (dPop sevm b Y) (dI sevm b)

/-- The memory expansion of the input and output windows. -/
abbrev dExt : Nat :=
  (dPop sevm b 0).extCost [⟨(Bytes.toB256 [0]).toNat, (Nat.toB256 sevm.data.length).toNat⟩,
    ⟨(Bytes.toB256 [0]).toNat, (Bytes.toB256 [0]).toNat⟩]

/-- The implementation's access charge. -/
abbrev dAcc : Nat := accessCost (dI sevm b) (pBase sevm b).accessedAddresses + 0

/-- The gas the `DELEGATECALL` forwards with `Y` gas left. -/
abbrev dFwd (Y : Nat) : Nat := except64th (Y - dExt sevm b - dAcc sevm b)

/-- The parent the child returns to. -/
abbrev dParent (Y : Nat) : Devm :=
  callSpawnParent (dWarm sevm b Y) (dFwd sevm b Y + dAcc sevm b + dExt sevm b)
    (Bytes.toB256 [0]).toNat (Nat.toB256 sevm.data.length).toNat (Bytes.toB256 [0]).toNat
    (Bytes.toB256 [0]).toNat

/-- The child message: the implementation's code at the proxy's storage. -/
abbrev dMsg (Y : Nat) : Msg :=
  delegatecallSpawnMsg sevm (dParent sevm b Y) (dFwd sevm b Y) (dI sevm b)
    (Bytes.toB256 [0]).toNat (Nat.toB256 sevm.data.length).toNat
    ((pBase sevm b).state.getCode (dI sevm b)) false

end Dlg

theorem impl_undelegated : getDelegatedCodeAddress Blanc.Lift.Usdc.Impl.code = none := by
  decide +kernel

/-- **`_delegate`'s `DELEGATECALL` step**: with `Y < 2 ^ 256` gas left, the implementation's code at
`dI` (undelegated, no precompile) and a clean child run, the parent resumes in `callChildPost`. -/
theorem dlg_step {sevm : Sevm} {b cpost : Devm} {Y : Nat} (hfork : CoveredFork sevm.benvStat.fork)
    (hdepth : sevm.depth ≠ 0) (hY : Y < 2 ^ 256)
    (hcharge : dExt sevm b + dAcc sevm b ≤ Y)
    (hundel : getDelegatedCodeAddress ((pBase sevm b).state.getCode (dI sevm b)) = none)
    (hprec : sevm.benvStat.rules.isPrecomp (dI sevm b) = false)
    (hexec : exec (initEvm (dMsg sevm b Y)) = .ok cpost) (herr : cpost.error = none) :
    Ninst.RunCompiled sevm (dSt sevm b Y) (.exec .delegatecall)
      (callChildPost (dParent sevm b Y) cpost (Bytes.toB256 [0]).toNat (Bytes.toB256 [0]).toNat) := by
  have hsplit : calculateMsgCallGas 0 (Nat.toB256 Y).toNat (dWarm sevm b Y).gasLeft (dExt sevm b)
      (dAcc sevm b) = ⟨dFwd sevm b Y + dAcc sevm b, dFwd sevm b Y⟩ := by
    have hg : (dWarm sevm b Y).gasLeft = Y := rfl
    rw [hg, B256.toNat_toB256_of_lt hY]
    have hcA : accessCost (dI sevm b) (pBase sevm b).accessedAddresses + dExt sevm b ≤ Y := by
      simp only [dAcc, Nat.add_zero] at hcharge; omega
    have hle : except64th (Y - dExt sevm b - accessCost (dI sevm b) (pBase sevm b).accessedAddresses) ≤ Y := by
      unfold except64th; omega
    unfold calculateMsgCallGas
    rw [if_neg (by omega)]
    simp only [Nat.min_eq_right hle, ↓reduceIte, Nat.add_zero]
    rfl
  refine Ninst.runCompiled_delegatecall_child (d1 := dWarm sevm b Y) hfork rfl ?_ ?_ rfl hsplit
    ?_ hdepth hprec (by simp only [List.length_cons, List.length_nil]; omega) hexec herr
  · rfl
  · have hu : getDelegatedCodeAddress ((addAccessedAddress ((dSt sevm b Y).setMach
        ⟨pRest sevm b, (dSt sevm b Y).memory, (dSt sevm b Y).gasLeft, (dSt sevm b Y).stateGas⟩)
          (pI sevm b).toAdr).state.getCode (pI sevm b).toAdr) = none := hundel
    unfold accessDelegation
    simp only [hu]
    rfl
  · show dFwd sevm b Y + dAcc sevm b + dExt sevm b ≤ Y
    unfold dFwd except64th
    omega

/-- The memory the proxy returns from: the child's word copied to `0`. -/
abbrev dRetMem (M : Mem) (w : B256) : Mem := M.write (Bytes.toB256 [0]).toNat w.toBytes

/-- **`_delegate`'s tail after a successful `DELEGATECALL`** returning a word `w`: copy it out and
return it. -/
@[irreducible] noncomputable def dTailW (sevm : Sevm) (D : Devm) (R : List B256) (M : Mem) (w : B256) :
    {c : Nat // D.returnData = w.toBytes → M.size % 32 = 0 → 32 ≤ M.size → R.length < 1000 → ∀ G,
      SFunc.RunExact cert.prog sevm (St D (1 :: R) M (G + c)) dRest
        (.halted (((St D (1 :: 1 :: R) (dRetMem M w) G).memRead (Bytes.toB256 [0]).toNat
          (Nat.toB256 w.toBytes.length).toNat).2.withOutput w.toBytes))} :=
  ⟨_, fun hrd h32 hge room G => by
    have hext : ∀ (S : List B256) (g : Nat),
        (St D S M g).extCost [⟨(Bytes.toB256 [0]).toNat, (Nat.toB256 w.toBytes.length).toNat⟩] = 0 := by
      intro S g
      refine Devm.extCost_zero_of_le h32 ?_
      rw [B256.length_toBytes]
      exact hge
    unfold dRest
    apply rk; refine rx_returndatasize (by xroom) ?_
    rw [hrd]
    xrun
    apply rk
    refine rx_returndatacopyK (by rw [hrd, B256.length_toBytes]; decide) ?_
    rw [hrd]
    xrun
    xunfold
    apply rk; refine rx_returndatasize (by xroom) ?_
    xrun
    refine rk0 ?_
    rw [hrd]
    have hlen : (Nat.toB256 w.toBytes.length).toNat = 32 := by rw [B256.length_toBytes]; rfl
    have h0 : (Bytes.toB256 [0]).toNat = 0 := rfl
    rw [show w.toBytes.sliceD (Bytes.toB256 [0]).toNat (Nat.toB256 w.toBytes.length).toNat 0 =
      w.toBytes by rw [h0, hlen]; exact Bytes.sliceD_zero_length (B256.length_toBytes w)]
    refine rx_return ?_ ?_
    · rw [h0, hlen]
      exact Devm.extCost_zero_of_le (by rw [Mem.size_write_word_of_le rfl (by omega)]; exact h32)
        (by rw [Mem.size_write_word_of_le rfl (by omega)]; omega)
    · rw [h0, hlen, ← B256.length_toBytes w]
      exact Mem.read_write_zero' M w.toBytes
  ⟩

end Blanc.Composition.UsdcLive
