import Blanc.CommonCore

/-!
# The USDC pure model (FiatTokenV2_2 behind its proxy)

The ledger the FiatTokenV2_2 implementation keeps in the proxy's storage, as natural numbers and
flags (`Ledger`); the writer calls a committed implementation frame can ask (`Call`); and the effect
of one committed call (`Ledger.step`), with every guard that reads the ledger.  Nothing here mentions
an execution, a bytecode or a storage slot: `Blanc/Lift/Usdc/Decode.lean` reads a `Call` from a
message, `Blanc/Lift/Usdc/Slots.lean` places the ledger in storage.

Signature validity, deadlines and authorization time windows are not modelled: a committed frame
has passed them, and they read no ledger field.  Overflow checks are kept where the source has them
(SafeMath `add`/`sub`, the `2 ^ 255 - 1` credit cap of `_setBalance`); `_permitNonces[owner]++` is
unchecked in Solidity 0.6.12 and wraps.

## Correspondence (deployed source, Circle `stablecoin-evm` v2.2.0, byte-identical per C0 §2.2)

Paths are under `c0/source/impl/src/contracts/`.  Modifiers: `whenNotPaused` `v1/Pausable.sol:54`;
`notBlacklisted` `v1/Blacklistable.sol:50`, reading the packed word's top bit
(`v2/FiatTokenV2_2.sol:230-237`); `onlyMinters` `v1/FiatTokenV1.sol` (`minters[msg.sender]`);
`onlyMasterMinter`, `onlyOwner` `v1/Ownable.sol:73`, `onlyPauser` `v1/Pausable.sol:62`,
`onlyBlacklister` `v1/Blacklistable.sol:38`, `onlyRescuer` `v1.1/Rescuable.sol:43`.

| Call | Source | Model clause |
|---|---|---|
| `view` | the 24 view/pure selectors | `some l` |
| `transfer` | `v1/FiatTokenV1.sol` `transfer` → `_transfer` | not paused, caller and `dst` not frozen, `move caller dst v` |
| `transferFrom` | `v1/FiatTokenV1.sol` `transferFrom` | not paused, caller/`src`/`dst` not frozen, `v ≤ allow src caller`, `move`, then `allow src caller -= v` |
| `approve` | `v2/FiatTokenV2_2.sol:259-267` → `_approve` (`v1/FiatTokenV1.sol`) | not paused, `approve caller s v` (both nonzero) |
| `increaseAllowance` | `v2/FiatTokenV2_2.sol:287-295` → `v2/FiatTokenV2.sol:211-217` | not paused, SafeMath `add`, `approve` |
| `decreaseAllowance` | `v2/FiatTokenV2_2.sol:300-308` → `v2/FiatTokenV2.sol:225-238` | not paused, SafeMath `sub`, `approve` |
| `permit` (both) | `v2/FiatTokenV2_2.sol:95-103`, `:272-282` → `v2/EIP2612.sol:56-112` | not paused, `nonce o += 1` (wrapping), `approve o s v` |
| `transferWithAuthorization` (both) | `v2/FiatTokenV2_2.sol:116-134`, `v2/FiatTokenV2.sol:96-118` → `v2/EIP3009.sol:117-145` | not paused, `src`/`dst` not frozen, `authUsed src n` unset; mark it, `move src dst v` |
| `receiveWithAuthorization` (both) | `v2/FiatTokenV2_2.sol:149-167`, `v2/FiatTokenV2.sol:134-156` → `v2/EIP3009.sol:196-225` | as above and `dst = caller` (`:205`) |
| `cancelAuthorization` (both) | `v2/FiatTokenV2_2.sol:177-183`, `v2/FiatTokenV2.sol:167-175` → `v2/EIP3009.sol:252-268` | not paused, `authUsed a n` unset; mark it |
| `mint` | `v1/FiatTokenV1.sol` `mint` | not paused, minter, caller/`dst` not frozen, `dst ≠ 0`, `0 < v ≤ minterAllowance caller`, SafeMath `supply + v`, `setBalance dst`, `minterAllowance caller -= v` |
| `burn` | `v1/FiatTokenV1.sol` `burn` | not paused, minter, caller not frozen, `0 < v ≤ bal caller`, SafeMath `supply - v`, `setBalance caller` |
| `configureMinter` | `v1/FiatTokenV1.sol` `configureMinter` | not paused, master minter; `minter m`, `minterAllowance m := v` |
| `removeMinter` | `v1/FiatTokenV1.sol` `removeMinter` | master minter; `minter m := false`, `minterAllowance m := 0` |
| `updateMasterMinter` | `v1/FiatTokenV1.sol` `updateMasterMinter` | owner, `a ≠ 0` |
| `pause` / `unpause` | `v1/Pausable.sol:70-81` | pauser |
| `updatePauser` | `v1/Pausable.sol:87-94` | owner, `a ≠ 0` |
| `updateBlacklister` | `v1/Blacklistable.sol:89-96` | owner, `a ≠ 0` |
| `updateRescuer` | `v1.1/Rescuable.sol:66-73` | owner, `a ≠ 0` |
| `transferOwnership` | `v1/Ownable.sol:82-89` | owner, `a ≠ 0` |
| `blacklist` / `unBlacklist` | `v1/Blacklistable.sol:71-83` → `v2/FiatTokenV2_2.sol:196-203` | blacklister; the flag only (the balance bits are kept) |
| `rescueERC20` | `v1.1/Rescuable.sol:54-60` | rescuer; no ledger effect (the token `CALL` is another frame) |
| `initialize` | `v1/FiatTokenV1.sol` `initialize` | `none` (see below) |
| `initializeV2` | `v2/FiatTokenV2.sol:37-46` | `initialized ∧ version = 0`; `version := 1` |
| `initializeV2_1` | `v2/FiatTokenV2_1.sol:34-45` | `version = 1`; `move self L (bal self)` if positive, freeze `self`, `version := 2` |
| `initializeV2_2` | `v2/FiatTokenV2_2.sol:41-65` | `none` (see below) |

`initialize` and `initializeV2_2` write state from arguments the frozen `Call` constructors do not
carry (roles; the accounts to re-blacklist).  Their guards (`!initialized`, `version = 2`) fail at
every good ledger (`Ledger.Good`), and the model reverts them unconditionally: it is exact at good
ledgers and errs only towards revert elsewhere.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc

/-- The FiatTokenV2_2 ledger at the proxy's storage, as natural numbers and flags.  `bal` is the
low 255 bits of `balanceAndBlacklistStates`, `frozen` its top bit; `admin` is the proxy's admin word
(the proxy, not the implementation, reads it). -/
structure Ledger where
  bal : Adr → Nat
  frozen : Adr → Bool
  allow : Adr → Adr → Nat
  nonce : Adr → Nat
  authUsed : Adr → B256 → Bool
  paused : Bool
  owner : Adr
  pauser : Adr
  blacklister : Adr
  masterMinter : Adr
  rescuer : Adr
  minter : Adr → Bool
  minterAllowance : Adr → Nat
  supply : Nat
  initialized : Bool
  version : Nat
  admin : Adr

/-- What a committed implementation frame asks (C0 §5.1; both overloads of `permit`,
`transferWithAuthorization`, `receiveWithAuthorization`, `cancelAuthorization` decode to one
constructor each).  `view` is every selector that writes nothing. -/
inductive Call
  | view
  | transfer (dst : Adr) (v : Nat)
  | transferFrom (src dst : Adr) (v : Nat)
  | approve (spender : Adr) (v : Nat)
  | increaseAllowance (spender : Adr) (v : Nat)
  | decreaseAllowance (spender : Adr) (v : Nat)
  | permit (owner spender : Adr) (v : Nat)
  | transferWithAuthorization (src dst : Adr) (v : Nat) (nonce : B256)
  | receiveWithAuthorization (src dst : Adr) (v : Nat) (nonce : B256)
  | cancelAuthorization (authorizer : Adr) (nonce : B256)
  | mint (dst : Adr) (v : Nat)
  | burn (v : Nat)
  | configureMinter (m : Adr) (v : Nat)
  | removeMinter (m : Adr)
  | updateMasterMinter (a : Adr)
  | pause
  | unpause
  | updatePauser (a : Adr)
  | updateBlacklister (a : Adr)
  | updateRescuer (a : Adr)
  | transferOwnership (a : Adr)
  | blacklist (a : Adr)
  | unBlacklist (a : Adr)
  | rescueERC20 (token dst : Adr) (v : Nat)
  | initialize
  | initializeV2
  | initializeV2_1 (lostAndFound : Adr)
  | initializeV2_2

/-- Whose signature the code checks for a call: a permit's owner, an authorization's `from`, a
cancellation's authorizer; `none` for every other call. -/
def Call.signer : Call → Option Adr
  | .permit o _ _ => some o
  | .transferWithAuthorization src _ _ _ => some src
  | .receiveWithAuthorization src _ _ _ => some src
  | .cancelAuthorization a _ => some a
  | _ => none

namespace Ledger

/-- `balanceAndBlacklistStates[a] = x` with the flag clear: the balance bits become `x`. -/
def setBal (l : Ledger) (a : Adr) (x : Nat) : Ledger := { l with bal := Function.update l.bal a x }

/-- `_setBalance(a, x)` (`v2/FiatTokenV2_2.sol:214-225`): the credit cap and the blacklist check. -/
def setBalance (l : Ledger) (a : Adr) (x : Nat) : Option Ledger :=
  if 2 ^ 255 ≤ x ∨ l.frozen a = true then none else some (l.setBal a x)

/-- `allowed[o][s] = x`. -/
def setAllow (l : Ledger) (o s : Adr) (x : Nat) : Ledger :=
  { l with allow := fun p q => if p = o ∧ q = s then x else l.allow p q }

/-- `_approve(o, s, x)` (`v1/FiatTokenV1.sol`): both parties nonzero. -/
def approveOf (l : Ledger) (o s : Adr) (x : Nat) : Option Ledger :=
  if o = 0 ∨ s = 0 then none else some (l.setAllow o s x)

/-- The blacklist flag of `a` (`_setBlacklistState`, `v2/FiatTokenV2_2.sol:196-203`). -/
def setFrozen (l : Ledger) (a : Adr) (b : Bool) : Ledger :=
  { l with frozen := Function.update l.frozen a b }

/-- `_authorizationStates[a][n] = true`. -/
def useAuth (l : Ledger) (a : Adr) (n : B256) : Ledger :=
  { l with authUsed := fun p q => if p = a ∧ q = n then true else l.authUsed p q }

/-- `minterAllowed[m] = x`. -/
def setMinterAllowance (l : Ledger) (m : Adr) (x : Nat) : Ledger :=
  { l with minterAllowance := Function.update l.minterAllowance m x }

/-- `_permitNonces[o]++` (unchecked: it wraps at `2 ^ 256`). -/
def bumpNonce (l : Ledger) (o : Adr) : Ledger :=
  { l with nonce := Function.update l.nonce o ((l.nonce o + 1) % 2 ^ 256) }

/-- The guarded move of `transfer`/`transferFrom`'s balance part (`v ≤ bal src`, neither frozen,
`src ≠ 0`, `dst ≠ 0`, credit cap): `_transfer` (`v1/FiatTokenV1.sol`), whose two `_setBalance`
writes check the cap and the blacklist flag. -/
def move (l : Ledger) (src dst : Adr) (v : Nat) : Option Ledger :=
  if src = 0 ∨ dst = 0 ∨ l.bal src < v then none
  else (l.setBalance src (l.bal src - v)).bind fun l₁ => l₁.setBalance dst (l₁.bal dst + v)

/-- The effect of one committed call by `caller` at proxy `self`, with every guard that reads the
ledger (paused, frozen, balances, allowances, roles, minter allowance, `authUsed`,
`initialized`/`version`, the `2 ^ 255 - 1` credit cap); signature validity and time windows are not
modelled (a committed frame passed them).  `none` = the frame reverts.  The correspondence table is
in the module docstring. -/
def step (l : Ledger) (self caller : Adr) : Call → Option Ledger
  | .view => some l
  | .transfer dst v =>
      if l.paused = true ∨ l.frozen caller = true ∨ l.frozen dst = true then none
      else l.move caller dst v
  | .transferFrom src dst v =>
      if l.paused = true ∨ l.frozen caller = true ∨ l.frozen src = true ∨ l.frozen dst = true ∨
        l.allow src caller < v then none
      else (l.move src dst v).map fun l₁ => l₁.setAllow src caller (l₁.allow src caller - v)
  | .approve s v => if l.paused = true then none else l.approveOf caller s v
  | .increaseAllowance s v =>
      if l.paused = true ∨ 2 ^ 256 ≤ l.allow caller s + v then none
      else l.approveOf caller s (l.allow caller s + v)
  | .decreaseAllowance s v =>
      if l.paused = true ∨ l.allow caller s < v then none
      else l.approveOf caller s (l.allow caller s - v)
  | .permit o s v => if l.paused = true then none else (l.bumpNonce o).approveOf o s v
  | .transferWithAuthorization src dst v n =>
      if l.paused = true ∨ l.frozen src = true ∨ l.frozen dst = true ∨ l.authUsed src n = true
      then none else (l.useAuth src n).move src dst v
  | .receiveWithAuthorization src dst v n =>
      if l.paused = true ∨ l.frozen src = true ∨ l.frozen dst = true ∨ dst ≠ caller ∨
        l.authUsed src n = true then none
      else (l.useAuth src n).move src dst v
  | .cancelAuthorization a n =>
      if l.paused = true ∨ l.authUsed a n = true then none else some (l.useAuth a n)
  | .mint dst v =>
      if l.paused = true ∨ l.minter caller = false ∨ l.frozen caller = true ∨ l.frozen dst = true ∨
        dst = 0 ∨ v = 0 ∨ l.minterAllowance caller < v ∨ 2 ^ 256 ≤ l.supply + v then none
      else (Ledger.setBalance { l with supply := l.supply + v } dst (l.bal dst + v)).map fun l₁ =>
        l₁.setMinterAllowance caller (l₁.minterAllowance caller - v)
  | .burn v =>
      if l.paused = true ∨ l.minter caller = false ∨ l.frozen caller = true ∨ v = 0 ∨
        l.bal caller < v ∨ l.supply < v then none
      else Ledger.setBalance { l with supply := l.supply - v } caller (l.bal caller - v)
  | .configureMinter m v =>
      if l.paused = true ∨ caller ≠ l.masterMinter then none
      else some { l with minter := Function.update l.minter m true,
                         minterAllowance := Function.update l.minterAllowance m v }
  | .removeMinter m =>
      if caller ≠ l.masterMinter then none
      else some { l with minter := Function.update l.minter m false,
                         minterAllowance := Function.update l.minterAllowance m 0 }
  | .updateMasterMinter a =>
      if caller ≠ l.owner ∨ a = 0 then none else some { l with masterMinter := a }
  | .pause => if caller ≠ l.pauser then none else some { l with paused := true }
  | .unpause => if caller ≠ l.pauser then none else some { l with paused := false }
  | .updatePauser a => if caller ≠ l.owner ∨ a = 0 then none else some { l with pauser := a }
  | .updateBlacklister a =>
      if caller ≠ l.owner ∨ a = 0 then none else some { l with blacklister := a }
  | .updateRescuer a => if caller ≠ l.owner ∨ a = 0 then none else some { l with rescuer := a }
  | .transferOwnership a => if caller ≠ l.owner ∨ a = 0 then none else some { l with owner := a }
  | .blacklist a => if caller ≠ l.blacklister then none else some (l.setFrozen a true)
  | .unBlacklist a => if caller ≠ l.blacklister then none else some (l.setFrozen a false)
  | .rescueERC20 _ _ _ => if caller ≠ l.rescuer then none else some l
  | .«initialize» => none
  | .initializeV2 =>
      if l.initialized = true ∧ l.version = 0 then some { l with version := 1 } else none
  | .initializeV2_1 lostAndFound =>
      if l.version ≠ 1 then none
      else ((if 0 < l.bal self then l.move self lostAndFound (l.bal self) else some l)).map
        fun l₁ => { l₁.setFrozen self true with version := 2 }
  | .initializeV2_2 => none

/-- A good ledger: balances fit the packed word, the contract is initialized at version 3 (so every
`initialize*` reverts, in particular `initializeV2_1`'s move of the proxy's own balance). -/
structure Good (l : Ledger) : Prop where
  bal_lt : ∀ a, l.bal a < 2 ^ 255
  initialized : l.initialized = true
  version : l.version = 3

end Ledger

end Blanc.Lift.Usdc
