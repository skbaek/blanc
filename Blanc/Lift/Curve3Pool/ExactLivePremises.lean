import Blanc.Lift.ExactCallProfile
import Blanc.Lift.Curve3Pool.LivePremises

/-!
# Exact environmental profiles for the pool's call windows

These strengthen the existing bounded callee premises. Each selects a debit and canonical
successor before quantifying over input gas, and speaks only about one external call. Canonical
successors agree modulo gas, so returndata, warm sets and all later cost-relevant world columns
remain stable. The existing world chain, input windows and stack-room requirements are retained.

The projections keep all bounded-success clients available. These premises and the shared
continuation helpers do not yet establish the pool's exact whole-entry or history costs.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- A `STATICCALL` returning `A`, with a gas-independent debit and successor at this window. -/
def StaticWordExactAt (sevm : Sevm) (W W' : Devm → Prop) (t : B256) (data : Bytes) (A : B256)
    (U : Nat) (ii is oi : B256) : Prop :=
  ∃ debit next, StaticWordCallProfile sevm W W' t data A U ii is oi debit next

/-- A zero-value `CALL` passing `ok`, with a gas-independent debit and successor at this window. -/
def MutCallExactAt (sevm : Sevm) (W W' : Devm → Prop) (t : B256) (data : Bytes)
    (ok : Bytes → Prop) (U : Nat) (ii is oi : B256) : Prop :=
  ∃ debit next, MutableCallProfile sevm W W' t data ok U ii is oi debit next

/-- Forget exact accounting and canonical stability, preserving the existing static premise. -/
theorem StaticWordExactAt.bounded {sevm : Sevm} {W W' : Devm → Prop} {t : B256} {data : Bytes}
    {A : B256} {U : Nat} {ii is oi : B256}
    (h : StaticWordExactAt sevm W W' t data A U ii is oi) :
    StaticWordOkAt sevm W W' t data A U ii is oi := by
  obtain ⟨debit, next, hp⟩ := h
  intro b S M G hW hU hG hin hroom
  obtain ⟨hc, d, hrun, hgas, _, out, hpost, hlen, hlt, hA, hW', hid⟩ :=
    hp.sound b S M G ⟨hW, hU, hG, hin, hroom⟩
  exact ⟨d, out, hrun, hpost, hlen, hlt, hA, by omega, by omega, hW', hid⟩

/-- Forget exact accounting and canonical stability, preserving the existing mutable premise. -/
theorem MutCallExactAt.bounded {sevm : Sevm} {W W' : Devm → Prop} {t : B256} {data : Bytes}
    {ok : Bytes → Prop} {U : Nat} {ii is oi : B256}
    (h : MutCallExactAt sevm W W' t data ok U ii is oi) :
    MutCallOkAt sevm W W' t data ok U ii is oi := by
  obtain ⟨debit, next, hp⟩ := h
  intro b S M G hW hU hG hin hroom
  obtain ⟨hc, d, hrun, hgas, _, hpost, hok, hlt, hstor, hW', hid⟩ :=
    hp.sound b S M G ⟨hW, hU, hG, hin, hroom⟩
  exact ⟨d, hrun, hpost, hok, hlt, by omega, by omega, hstor, hW', hid⟩

/-- The exact profile of `token.totalSupply()` at one window. -/
abbrev SupplyExactAt (sevm : Sevm) (W W' : Devm → Prop) (t T : B256) (U : Nat) (ii oi : B256) :
    Prop :=
  StaticWordExactAt sevm W W' t totalSupplyData T U ii 4 oi

/-- The exact profile of `coin.balanceOf(self)` at one window. -/
abbrev CoinBalExactAt (sevm : Sevm) (W W' : Devm → Prop) (t B : B256) (U : Nat) (ii oi : B256) :
    Prop :=
  StaticWordExactAt sevm W W' t (balanceOfData sevm.currentTarget) B U ii 0x24 oi

/-- The exact profile of `coin.transfer(msg.sender, amt)` at one window. -/
abbrev CoinPushExactAt (sevm : Sevm) (W W' : Devm → Prop) (t amt : B256) (U : Nat)
    (ii oi : B256) : Prop :=
  MutCallExactAt sevm W W' t (transferSel ++ sevm.caller.toB256.toBytes ++ amt.toBytes) RawCallOk U
    ii 0x44 oi

/-- The exact profile of `coin.transferFrom(msg.sender, self, amt)` at one window. -/
abbrev CoinPullExactAt (sevm : Sevm) (W W' : Devm → Prop) (t amt : B256) (U : Nat)
    (ii oi : B256) : Prop :=
  MutCallExactAt sevm W W' t (transferFromSel ++ sevm.caller.toB256.toBytes ++
    sevm.currentTarget.toB256.toBytes ++ amt.toBytes) RawCallOk U ii 0x64 oi

/-- The exact profile of `token.burnFrom(msg.sender, amt)` at one window. -/
abbrev BurnExactAt (sevm : Sevm) (W W' : Devm → Prop) (t amt : B256) (U : Nat) (ii oi : B256) :
    Prop :=
  MutCallExactAt sevm W W' t (burnFromSel ++ sevm.caller.toB256.toBytes ++ amt.toBytes)
    (fun r => 32 ≤ r.length) U ii 0x44 oi

/-- The exact profile of `token.mint(msg.sender, amt)` at one window. -/
abbrev MintExactAt (sevm : Sevm) (W W' : Devm → Prop) (t amt : B256) (U : Nat) (ii oi : B256) :
    Prop :=
  MutCallExactAt sevm W W' t (mintSel ++ sevm.caller.toB256.toBytes ++ amt.toBytes)
    (fun r => 32 ≤ r.length) U ii 0x44 oi

/-- `remove_liquidity`'s exact supply window. -/
abbrev SupplyExact (sevm : Sevm) (W : Devm → Prop) (t T : B256) (U : Nat) : Prop :=
  SupplyExactAt sevm W W t T U 0x17c 0x1c0

end Blanc.Lift.Curve3Pool
