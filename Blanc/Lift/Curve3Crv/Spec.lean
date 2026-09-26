import Blanc.Lift.Curve3Crv.Decode
import Blanc.Lift.Curve3Crv.Prog
import Blanc.Lift.Vyper
import Blanc.Lift.Exact

/-!
# The deployed functions over raw storage, and the segment interface

The walks of the design (`Safe*.lean`, `Body*.lean`, `ViewBodies.lean`) never mention the
model.  Each function's effect is stated here once, over the contract's raw storage words, in the
order-free form `raw… sevm stor : Option Raw` (`none`: some guard of the bytes fails; `some (st',
logs, out)`: the new storage, the appended log entries, the return data, `none` for `STOP`).
The pure refinement lemmas (`Refine.lean`) relate each to the model's `step` under `VyInv`.

* `Lands sevm b post r`: a body run from base `b` ended in `post` exactly as `r` says;
* `BodyLive sevm b f r`: the gas-exact liveness form: for some cost `c`, every gas `G` above
  the `SSTORE` sentry runs `f` to a halt that `Lands`, leaving exactly `G`;
* `bodies`, `sels`: the thirteen function bodies inside the dispatcher (entry 0) and their
  selectors, in dispatcher order.
-/

namespace Blanc.Lift.Curve3Crv

open Jaune

/-- New storage, appended log entries, return data (`none` for `STOP`). -/
abbrev Raw := Stor × List Log × Option Bytes

/-- `n` words of `src` stored at `base`, `base + 1`, …: the Vyper string copy loop. -/
def vyCopyStore (stor : Stor) (base : B256) (src : Bytes) (n : Nat) : Stor :=
  (List.range n).foldl
    (fun st i => st.set (base + Nat.toB256 i) (Bytes.toB256 (src.sliceD (32 * i) 32 0))) stor

/-- The string a storage holds at `base` (length word, then up to `n` data words). -/
def vyStrOf (stor : Stor) (base : B256) (n : Nat) : Bytes :=
  (vyStrWords stor base n).take (stor.get base).toNat

section Raw

variable (sevm : Sevm) (stor : Stor)

local notation "arg" => Sevm.argWord sevm

def rawSetMinter : Option Raw :=
  if sevm.value = 0 ∧ (arg 0).toNat < 2 ^ 160 ∧ stor.get vyMinterSlot = sevm.caller.toB256 then
    some (stor.set vyMinterSlot (arg 0), [], none)
  else none

/-- `set_name`, with `ow` the word the owner call answered (`none`: it failed or was short). -/
def rawSetName (ow : Option B256) : Option Raw :=
  let s0 := arg 0 + 4
  let s1 := arg 1 + 4
  let L0 := (Sevm.dataWord sevm s0).toNat
  let L1 := (Sevm.dataWord sevm s1).toNat
  if sevm.value = 0 ∧ L0 ≤ 64 ∧ L1 ≤ 32 ∧ ow = some sevm.caller.toB256 then
    some (vyCopyStore (vyCopyStore stor vyNameBase (sevm.data.sliceD s0.toNat 96 0)
      (min 3 ((32 + L0) / 32 + 1))) vySymbolBase (sevm.data.sliceD s1.toNat 64 0)
      (min 2 ((32 + L1) / 32 + 1)), [], none)
  else none

def rawTransfer : Option Raw :=
  let d := arg 0
  let v := arg 1
  let s1 := vyBalSlot sevm.caller
  let x := stor.get s1
  let st1 := stor.set s1 (x - v)
  let y := st1.get (mapSlot 3 d)
  if sevm.value = 0 ∧ d.toNat < 2 ^ 160 ∧ v ≤ x ∧ y.toNat + v.toNat < 2 ^ 256 then
    some (st1.set (mapSlot 3 d) (y + v),
      [⟨sevm.currentTarget, [transferTopic, sevm.caller.toB256, d], v.toBytes⟩],
      some (1 : B256).toBytes)
  else none

def rawTransferFrom : Option Raw :=
  let f := arg 0
  let d := arg 1
  let v := arg 2
  let x := stor.get (mapSlot 3 f)
  let st1 := stor.set (mapSlot 3 f) (x - v)
  let y := st1.get (mapSlot 3 d)
  let st2 := st1.set (mapSlot 3 d) (y + v)
  let s3 := mapSlot (mapSlot 4 f) sevm.caller.toB256
  let z := st2.get s3
  let spend := st2.get vyMinterSlot ≠ sevm.caller.toB256
  if sevm.value = 0 ∧ f.toNat < 2 ^ 160 ∧ d.toNat < 2 ^ 160 ∧ v ≤ x ∧
      y.toNat + v.toNat < 2 ^ 256 ∧ (spend → v ≤ z) then
    some (if spend then st2.set s3 (z - v) else st2,
      [⟨sevm.currentTarget, [transferTopic, f, d], v.toBytes⟩], some (1 : B256).toBytes)
  else none

def rawApprove : Option Raw :=
  let p := arg 0
  let v := arg 1
  let s := mapSlot (mapSlot 4 sevm.caller.toB256) p
  if sevm.value = 0 ∧ p.toNat < 2 ^ 160 ∧ (v = 0 ∨ stor.get s = 0) then
    some (stor.set s v, [⟨sevm.currentTarget, [approvalTopic, sevm.caller.toB256, p], v.toBytes⟩],
      some (1 : B256).toBytes)
  else none

def rawMint : Option Raw :=
  let d := arg 0
  let v := arg 1
  let sup := stor.get vySupplySlot
  let st1 := stor.set vySupplySlot (sup + v)
  let y := st1.get (mapSlot 3 d)
  if sevm.value = 0 ∧ d.toNat < 2 ^ 160 ∧ stor.get vyMinterSlot = sevm.caller.toB256 ∧ d ≠ 0 ∧
      sup.toNat + v.toNat < 2 ^ 256 ∧ y.toNat + v.toNat < 2 ^ 256 then
    some (st1.set (mapSlot 3 d) (y + v), [⟨sevm.currentTarget, [transferTopic, 0, d], v.toBytes⟩],
      some (1 : B256).toBytes)
  else none

def rawBurnFrom : Option Raw :=
  let f := arg 0
  let v := arg 1
  let sup := stor.get vySupplySlot
  let st1 := stor.set vySupplySlot (sup - v)
  let y := st1.get (mapSlot 3 f)
  if sevm.value = 0 ∧ f.toNat < 2 ^ 160 ∧ stor.get vyMinterSlot = sevm.caller.toB256 ∧ f ≠ 0 ∧
      v ≤ sup ∧ v ≤ y then
    some (st1.set (mapSlot 3 f) (y - v), [⟨sevm.currentTarget, [transferTopic, f, 0], v.toBytes⟩],
      some (1 : B256).toBytes)
  else none

/-! Views: storage and logs kept, the return data read off the storage. -/

def rawTotalSupply : Option Raw :=
  if sevm.value = 0 then some (stor, [], some (stor.get vySupplySlot).toBytes) else none

def rawDecimals : Option Raw :=
  if sevm.value = 0 then some (stor, [], some (stor.get vyDecimalsSlot).toBytes) else none

def rawBalanceOf : Option Raw :=
  if sevm.value = 0 ∧ (arg 0).toNat < 2 ^ 160 then
    some (stor, [], some (stor.get (mapSlot 3 (arg 0))).toBytes)
  else none

def rawAllowance : Option Raw :=
  if sevm.value = 0 ∧ (arg 0).toNat < 2 ^ 160 ∧ (arg 1).toNat < 2 ^ 160 then
    some (stor, [], some (stor.get (mapSlot (mapSlot 4 (arg 0)) (arg 1))).toBytes)
  else none

/-- `name()`: the stored string, when its length word is within `String[64]`. -/
def rawName : Option Raw :=
  if sevm.value = 0 ∧ (stor.get vyNameBase).toNat ≤ 64 then
    some (stor, [], some (abiString (vyStrOf stor vyNameBase 2)))
  else none

def rawSymbol : Option Raw :=
  if sevm.value = 0 ∧ (stor.get vySymbolBase).toNat ≤ 32 then
    some (stor, [], some (abiString (vyStrOf stor vySymbolBase 1)))
  else none

end Raw

/-! ## The segment interface -/

/-- A body run from base `b` ended in `post` as `r` says. -/
structure Lands (sevm : Sevm) (b post : Devm) (r : Raw) : Prop where
  stor : Devm.getStor post sevm.currentTarget = r.1
  other : ∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor b a
  logs : post.logs = b.logs ++ r.2.1
  output : ∀ o, r.2.2 = some o → post.output = o

/-- The frame state at a body's entry: the base, empty stack, the prologue's memory. -/
def entrySt (sevm : Sevm) (b : Devm) (G : Nat) : Devm :=
  St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G

/-- **The liveness form of a body**: for some cost `c`, every gas `G` above the `SSTORE`
sentry runs `f` from the body's entry to a halt that `Lands` as `r`, with exactly `G` left. -/
def BodyLive (sevm : Sevm) (b : Devm) (f : SFunc) (r : Raw) : Prop :=
  ∃ c, ∀ G, gCallStipend < G → ∃ post,
    SFunc.RunExact prog sevm (entrySt sevm b (G + c)) f (.halted post) ∧ post.gasLeft = G ∧
      Lands sevm b post r

/-- The thirteen bodies inside the dispatcher (entry 0), in dispatcher order. -/
def bodies : List SFunc :=
  [t_00b0_c0, t_00f1_c0, t_0240_c0, t_0267_c0, t_02ce_c0, t_0390_c0, t_04ab_c0, t_056e_c0,
    t_0644_c0, t_0716_c0, t_07ca_c0, t_087e_c0, t_08a5_c0]

/-- Their selectors. -/
def sels : List B256 :=
  [selSetMinter, selSetName, selTotalSupply, selAllowance, selTransfer, selTransferFrom,
    selApprove, selMint, selBurnFrom, selName, selSymbol, selDecimals, selBalanceOf]

/-- The dispatcher's gas up to body `k`: the size test and prologue (100), then 28 per test and
1 per `JUMPDEST` of a missed test. -/
def dispatchGas (k : Nat) : Nat := 128 + 29 * k

end Blanc.Lift.Curve3Crv
