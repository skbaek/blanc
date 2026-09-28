import Blanc.Lift.Curve3Crv.Layout
import Blanc.Lift.StaticCall

/-!
# What a 3Crv frame asks, and how the model's answer looks on chain

* `decodeCall sevm`: the model's `Call` the deployed dispatcher and argument decoders read from
  the calldata (a selector miss or calldata shorter than four bytes is `.other`; arguments are raw
  ABI words, the model applies the address clamps; a `String[n]` argument is the calldata bytes
  its length word names, `strArg`);
* `c3ctx sevm ow`: the model's context: `CALLER`, `CALLVALUE`, and the answer `ow` of
  `Curve(minter).owner()` (`OwnerAnswer` ties it to the frame's static call);
* `eventLog`, `retBytes`: the log entry of a model event and the return data of a model result;
* `callKeys`: the mapping keys a call reads or writes (for `Fresh`).
-/

namespace Blanc.Lift.Curve3Crv

open Jaune
open Blanc.Curve3Crv (Call Ctx Event Ret)

/-! ## Selectors (dispatcher order) -/

def selSetMinter : B256 := 0x1652e9fc
def selSetName : B256 := 0xe1430e06
def selTotalSupply : B256 := 0x18160ddd
def selAllowance : B256 := 0xdd62ed3e
def selTransfer : B256 := 0xa9059cbb
def selTransferFrom : B256 := 0x23b872dd
def selApprove : B256 := 0x095ea7b3
def selMint : B256 := 0x40c10f19
def selBurnFrom : B256 := 0x79cc6790
def selName : B256 := 0x06fdde03
def selSymbol : B256 := 0x95d89b41
def selDecimals : B256 := 0x313ce567
def selBalanceOf : B256 := 0x70a08231

/-- The `i`-th `String` argument: its ABI offset word plus 4 (wrapping, as the decoder adds) is
where its length word sits; the content is the calldata bytes after it. -/
def strArg (sevm : Sevm) (i : B256) : Bytes :=
  let s := Sevm.argWord sevm i + 4
  sevm.data.sliceD (s.toNat + 32) (Sevm.dataWord sevm s).toNat 0

/-- The call the deployed dispatcher selects. -/
def decodeCall (sevm : Sevm) : Call :=
  if sevm.data.length < 4 then .other else
  let sel := Sevm.selector sevm
  let a := Sevm.argWord sevm
  if sel = selSetMinter then .setMinter (a 0)
  else if sel = selSetName then .setName (strArg sevm 0) (strArg sevm 1)
  else if sel = selTotalSupply then .totalSupply
  else if sel = selAllowance then .allowance (a 0) (a 1)
  else if sel = selTransfer then .transfer (a 0) (a 1)
  else if sel = selTransferFrom then .transferFrom (a 0) (a 1) (a 2)
  else if sel = selApprove then .approve (a 0) (a 1)
  else if sel = selMint then .mint (a 0) (a 1)
  else if sel = selBurnFrom then .burnFrom (a 0) (a 1)
  else if sel = selName then .name
  else if sel = selSymbol then .symbol
  else if sel = selDecimals then .decimals
  else if sel = selBalanceOf then .balanceOf (a 0)
  else .other

/-- The model context of a frame, with `ow` the owner answer. -/
def c3ctx (sevm : Sevm) (ow : Option B256) : Ctx :=
  ⟨sevm.caller, sevm.value, fun _ => ow⟩

/-- `owner()`'s calldata. -/
def ownerCalldata : Bytes := [0x8d, 0xa5, 0xcb, 0x5b]

/-- The frame's static call to `m` for `owner()` succeeded and returned at least a word starting
with `w` (over the world of `b`, the frame's world when it calls). -/
def OwnerAnswer (sevm : Sevm) (b : Devm) (m : Adr) (w : B256) : Prop :=
  ∃ out, StaticAnswered sevm b m ownerCalldata out ∧ 32 ≤ out.length ∧
    Bytes.toB256 (out.take 32) = w

/-! ## Events and return data -/

def transferTopic : B256 := 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef
def approvalTopic : B256 := 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925

/-- The `LOG3` entry of a model event. -/
def eventLog (target : Adr) : Event → Log
  | .transfer src dst v => ⟨target, [transferTopic, src.toB256, dst.toB256], v.toBytes⟩
  | .approval o p v => ⟨target, [approvalTopic, o.toB256, p.toB256], v.toBytes⟩

/-- The ABI encoding of a returned string: head `0x20`, length, bytes, zero padding. -/
def abiString (bs : Bytes) : Bytes :=
  (32 : B256).toBytes ++ (Nat.toB256 bs.length).toBytes ++ bs ++
    List.replicate (ceil32 bs.length - bs.length) 0

/-- The return data of a model result at fresh frame entry: `STOP` returns no bytes. -/
def RetOut (out : Bytes) : Ret → Prop
  | .stop => out = []
  | .bool b => out = (if b then (1 : B256) else 0).toBytes
  | .word w => out = w.toBytes
  | .string bs => out = abiString bs

/-- The exact output relation over an arbitrary base machine. Jaune's `STOP`
preserves its enclosing output field; the other results overwrite it. -/
def RetOutFrom (initial out : Bytes) : Ret → Prop
  | .stop => out = initial
  | .bool b => RetOut out (.bool b)
  | .word w => RetOut out (.word w)
  | .string bs => RetOut out (.string bs)

theorem RetOutFrom.of_empty {initial out : Bytes} {ret : Ret}
    (h : RetOutFrom initial out ret) (hempty : initial = []) : RetOut out ret := by
  cases ret <;> simpa only [RetOutFrom, RetOut, hempty] using h

/-! ## Keys and writers -/

/-- The mapping keys a call reads or writes. -/
def callKeys (sender : Adr) : Call → List Key
  | .allowance o p => [.allow o.toAdr p.toAdr]
  | .transfer d _ => [.bal sender, .bal d.toAdr]
  | .transferFrom f d _ => [.bal f.toAdr, .bal d.toAdr, .allow f.toAdr sender]
  | .approve p _ => [.allow sender p.toAdr]
  | .mint d _ => [.bal d.toAdr]
  | .burnFrom f _ => [.bal f.toAdr]
  | .balanceOf h => [.bal h.toAdr]
  | _ => []

/-- The calls that may write storage or log. -/
def IsWriter : Call → Prop
  | .setMinter _ | .setName _ _ | .transfer _ _ | .transferFrom _ _ _ | .approve _ _ | .mint _ _
  | .burnFrom _ _ => True
  | _ => False

end Blanc.Lift.Curve3Crv
