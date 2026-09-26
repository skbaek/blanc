-- Curve3Crv/Model.lean : the 3Crv LP token (CurveTokenV2.vy, Vyper 0.2.4) as pure functions.

import Blanc.LedgerUpdate

/-!
# The 3Crv token, modelled from its verified Vyper source

Source of truth: the Etherscan-verified source of
`0x6c3F90f043a72FA612cbac8115EE7e52BDe6E490` (= curvefi `CurveTokenV2.vy` at
`e96c8b72b8`, `# @version 0.2.4`).  One pure function per external function;
each returns `.ok (state', events, ret)` or `.error reason`.  The reason is for
reading only: every revert of this contract is `REVERT(0, 0)`, so callers can
observe only *that* a call reverted.

Conventions fixed by Vyper 0.2.4, recorded clause by clause in the Plans
correspondence table (`evidence/vyper-3crv-bytecode-v1/v3/correspondence.md`):

* every named function is non-payable (`msg.value ≠ 0` reverts first), and a
  selector miss, including calldata shorter than four bytes, reverts (`step`);
* arguments are ABI words; an `address` argument reverts unless it is
  `< 2^160` (checked in argument order, before the body);
* a `String[n]` argument reverts when its ABI length exceeds `n`; the model
  receives the decoded content;
* `uint256` `+=` reverts when the mathematical sum is `≥ 2^256`, `-=` when the
  subtrahend exceeds the minuend; statements run in source order, so a
  self-transfer debits and then credits the same row;
* `Curve(self.minter).owner()` is an external `STATICCALL`; its outcome is the
  input `Ctx.ownerOf` (`none` = the call failed or returned fewer than 32
  bytes; `some w` = the first returned word, compared *unclamped*, per
  GHSA-j2x6's absent return clamp in Vyper < 0.3.2).

Storage layout (for the later bytecode refinement): `name` 0, `symbol` 1,
`decimals` 2, `balanceOf` 3, `allowances` 4, `total_supply` 5, `minter` 6.
-/

namespace Blanc

open Jaune

namespace Curve3Crv

/-- Why a call reverted (not observable on chain). -/
inductive Error
  | nonpayable
  | selectorMiss
  | addressClamp
  | stringClamp
  | notMinter
  | ownerCallFailed
  | notOwner
  | zeroAddress
  | balanceUnderflow
  | balanceOverflow
  | allowanceUnderflow
  | supplyUnderflow
  | supplyOverflow
  | approveNonzero
  | decimalsBound
  | supplyMulOverflow
  deriving DecidableEq

/-- The two events of the source. -/
inductive Event
  | transfer (src dst : Adr) (value : B256)
  | approval (owner spender : Adr) (value : B256)

/-- The decoded return value. -/
inductive Ret
  | stop
  | bool (b : Bool)
  | word (w : B256)
  | string (bs : Bytes)

/-- Contract storage, one field per source variable. -/
structure State where
  name : Bytes
  symbol : Bytes
  decimals : B256
  balanceOf : Adr → B256
  allowances : Adr → Adr → B256
  totalSupply : B256
  minter : Adr

/-- The call environment: `msg.sender`, `msg.value`, and the outcome of
`owner()` staticcalled at a given address. -/
structure Ctx where
  sender : Adr
  value : B256
  ownerOf : Adr → Option B256

abbrev Out := State × List Event × Ret
abbrev Result := Except Error Out

/-- The external functions, in dispatcher order, plus the selector miss. -/
inductive Call
  | setMinter (minter : B256)
  | setName (name symbol : Bytes)
  | totalSupply
  | allowance (owner spender : B256)
  | transfer (dst value : B256)
  | transferFrom (src dst value : B256)
  | approve (spender value : B256)
  | mint (dst value : B256)
  | burnFrom (src value : B256)
  | name
  | symbol
  | decimals
  | balanceOf (holder : B256)
  | other

/-! ## Function bodies (after the non-payable guard) -/

def setMinter (ctx : Ctx) (minter : B256) (s : State) : Result :=
  if minter.toNat < 2 ^ 160 then
    if ctx.sender = s.minter then
      .ok ({ s with minter := minter.toAdr }, [], .stop)
    else .error .notMinter
  else .error .addressClamp

def setName (ctx : Ctx) (name symbol : Bytes) (s : State) : Result :=
  if name.length ≤ 64 then
    if symbol.length ≤ 32 then
      match ctx.ownerOf s.minter with
      | none => .error .ownerCallFailed
      | some w =>
        if w = ctx.sender.toB256 then
          .ok ({ s with name := name, symbol := symbol }, [], .stop)
        else .error .notOwner
    else .error .stringClamp
  else .error .stringClamp

def totalSupplyView (s : State) : Result :=
  .ok (s, [], .word s.totalSupply)

def allowanceView (owner spender : B256) (s : State) : Result :=
  if owner.toNat < 2 ^ 160 then
    if spender.toNat < 2 ^ 160 then
      .ok (s, [], .word (s.allowances owner.toAdr spender.toAdr))
    else .error .addressClamp
  else .error .addressClamp

def transfer (ctx : Ctx) (dst value : B256) (s : State) : Result :=
  if dst.toNat < 2 ^ 160 then
    if value ≤ s.balanceOf ctx.sender then
      if (ledgerDebit s.balanceOf ctx.sender value dst.toAdr).toNat + value.toNat
          < 2 ^ 256 then
        .ok ({ s with balanceOf :=
                (ledgerCredit (ledgerDebit s.balanceOf ctx.sender value) dst.toAdr value) },
             [.transfer ctx.sender dst.toAdr value], .bool true)
      else .error .balanceOverflow
    else .error .balanceUnderflow
  else .error .addressClamp

def transferFrom (ctx : Ctx) (src dst value : B256) (s : State) : Result :=
  if src.toNat < 2 ^ 160 then
    if dst.toNat < 2 ^ 160 then
      if value ≤ s.balanceOf src.toAdr then
        if (ledgerDebit s.balanceOf src.toAdr value dst.toAdr).toNat + value.toNat
            < 2 ^ 256 then
          if ctx.sender ≠ s.minter then
            if value ≤ s.allowances src.toAdr ctx.sender then
              .ok ({ s with
                      balanceOf := (ledgerCredit (ledgerDebit s.balanceOf src.toAdr value)
                        dst.toAdr value),
                      allowances := (Function.update s.allowances src.toAdr
                        (ledgerDebit (s.allowances src.toAdr) ctx.sender value)) },
                   [.transfer src.toAdr dst.toAdr value], .bool true)
            else .error .allowanceUnderflow
          else
            .ok ({ s with
                    balanceOf := (ledgerCredit (ledgerDebit s.balanceOf src.toAdr value)
                      dst.toAdr value) },
                 [.transfer src.toAdr dst.toAdr value], .bool true)
        else .error .balanceOverflow
      else .error .balanceUnderflow
    else .error .addressClamp
  else .error .addressClamp

def approve (ctx : Ctx) (spender value : B256) (s : State) : Result :=
  if spender.toNat < 2 ^ 160 then
    if value = 0 ∨ s.allowances ctx.sender spender.toAdr = 0 then
      .ok ({ s with allowances := (Function.update s.allowances ctx.sender
                (Function.update (s.allowances ctx.sender) spender.toAdr value)) },
           [.approval ctx.sender spender.toAdr value], .bool true)
    else .error .approveNonzero
  else .error .addressClamp

def mint (ctx : Ctx) (dst value : B256) (s : State) : Result :=
  if dst.toNat < 2 ^ 160 then
    if ctx.sender = s.minter then
      if dst ≠ 0 then
        if s.totalSupply.toNat + value.toNat < 2 ^ 256 then
          if (s.balanceOf dst.toAdr).toNat + value.toNat < 2 ^ 256 then
            .ok ({ s with totalSupply := s.totalSupply + value,
                          balanceOf := ledgerCredit s.balanceOf dst.toAdr value },
                 [.transfer 0 dst.toAdr value], .bool true)
          else .error .balanceOverflow
        else .error .supplyOverflow
      else .error .zeroAddress
    else .error .notMinter
  else .error .addressClamp

def burnFrom (ctx : Ctx) (src value : B256) (s : State) : Result :=
  if src.toNat < 2 ^ 160 then
    if ctx.sender = s.minter then
      if src ≠ 0 then
        if value ≤ s.totalSupply then
          if value ≤ s.balanceOf src.toAdr then
            .ok ({ s with totalSupply := s.totalSupply - value,
                          balanceOf := ledgerDebit s.balanceOf src.toAdr value },
                 [.transfer src.toAdr 0 value], .bool true)
          else .error .balanceUnderflow
        else .error .supplyUnderflow
      else .error .zeroAddress
    else .error .notMinter
  else .error .addressClamp

def nameView (s : State) : Result := .ok (s, [], .string s.name)

def symbolView (s : State) : Result := .ok (s, [], .string s.symbol)

def decimalsView (s : State) : Result := .ok (s, [], .word s.decimals)

def balanceOfView (holder : B256) (s : State) : Result :=
  if holder.toNat < 2 ^ 160 then
    .ok (s, [], .word (s.balanceOf holder.toAdr))
  else .error .addressClamp

/-- The body selected by a named call. -/
def body (ctx : Ctx) : Call → State → Result
  | .setMinter m, s => setMinter ctx m s
  | .setName n y, s => setName ctx n y s
  | .totalSupply, s => totalSupplyView s
  | .allowance o p, s => allowanceView o p s
  | .transfer d v, s => transfer ctx d v s
  | .transferFrom f d v, s => transferFrom ctx f d v s
  | .approve p v, s => approve ctx p v s
  | .mint d v, s => mint ctx d v s
  | .burnFrom f v, s => burnFrom ctx f v s
  | .name, s => nameView s
  | .symbol, s => symbolView s
  | .decimals, s => decimalsView s
  | .balanceOf h, s => balanceOfView h s
  | .other, _ => .error .selectorMiss

/-- One external call: a selector miss reverts, every named function is
non-payable. -/
def step (ctx : Ctx) (c : Call) (s : State) : Result :=
  match c with
  | .other => .error .selectorMiss
  | c => if ctx.value = 0 then body ctx c s else .error .nonpayable

/-- The constructor.  `10 ** _decimals` is guarded by `_decimals < 78` (the
largest power of ten below `2^256`), and `_supply * 10 ** _decimals` is a
checked product. -/
def init (ctx : Ctx) (name symbol : Bytes) (decimals supply : B256) :
    Except Error (State × List Event) :=
  if ctx.value = 0 then
    if decimals.toNat < 78 then
      if supply.toNat * 10 ^ decimals.toNat < 2 ^ 256 then
        .ok ({ name := name, symbol := symbol, decimals := decimals,
               balanceOf := (Function.update (fun _ => 0) ctx.sender
                 (Nat.toB256 (supply.toNat * 10 ^ decimals.toNat))),
               allowances := fun _ _ => 0,
               totalSupply := Nat.toB256 (supply.toNat * 10 ^ decimals.toNat),
               minter := ctx.sender },
             [.transfer 0 ctx.sender (Nat.toB256 (supply.toNat * 10 ^ decimals.toNat))])
      else .error .supplyMulOverflow
    else .error .decimalsBound
  else .error .nonpayable

end Curve3Crv

end Blanc
