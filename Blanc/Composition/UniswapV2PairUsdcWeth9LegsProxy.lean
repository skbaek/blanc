import Blanc.Composition.UniswapV2PairUsdcWeth9LegsKit
import Blanc.Lift.Usdc.ProxyOk

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

noncomputable def proxyProbe (sevm : Sevm) (b : Devm) (s : B256) :
    {c : Nat // CoveredFork sevm.benvStat.fork → ProxyFacts sevm b s → ∀ X o,
      SFunc.RunExact cert.prog sevm (St b [] Mem.empty (X + c)) t_0000_c0 o} :=
  ⟨_, fun fork facts X o => by
    obtain ⟨short, sel, n1, n2, n3, n4, n5, adm⟩ := facts
    xrun
    xcallM p22W 1 [] fork (by xroom) adm
    xrun
    xcallM p14W 1 [] fork (by xroom)
    xrun
    trace_state
    sorry⟩

end Blanc.Composition.UsdcLive
