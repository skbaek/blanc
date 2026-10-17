import Blanc.Lift.Curve3Pool.Decode
import Blanc.Lift.CallerProvenance
import Blanc.Lift.VyperRawCall

/-!
# What a 3pool frame observes, and what it calls

The model (`Model.lean`) takes the coins' and 3Crv's answers as an input `Env`. This file ties
an `Env` to one actual frame derivation `D : Exec.Deriv` of the pool (`EnvOf D e`), names the
external calls the frame actually makes (`CallsOf D`) and the encoding the model's `calls` list
implies for them (`encodeCall`), and states the per-child environmental premise of the walk
architecture (`PoolCallsKeep D`, decision `curve3pool-walk-architecture-20261017`).

## The answers (`EnvOf`)

Every answer is read off the frame's **direct, settlement-committed children**
(`Exec.childFrames D.exc`, in execution order), each matched by its target and calldata:

* `time` is `D.sevm.benvStat.time` (`TIMESTAMP`); `caller` is the `CALLER` word; `value` is
  `CALLVALUE`;
* `balPre`/`balPost` of coin `k`: replies of children at `coins[k]` with calldata exactly
  `balanceOf(self)`, at least 32 bytes long (`RETURNDATASIZE > 31`, the runtime's assert), read
  as their first word; `balPost`'s child comes after `balPre`'s;
* `pullOk`/`pushOk` of coin `k`: a child at `coins[k]` whose calldata starts with the
  `transferFrom` / `transfer` selector returned data satisfying `RawCallOk` (the `raw_call`
  tail: empty, or its first `min(len, 32)` bytes are not all zero; the call flag is nonzero
  because the child is committed);
* `supply`: the reply of a child at `token` with calldata exactly `totalSupply()`, at least 32
  bytes, first word;
* `mintOk`/`burnOk`: a child at `token` whose calldata starts with the `mint` / `burnFrom`
  selector returned at least 32 bytes (the bool is discarded by the runtime, U0 review R2).

Coin and token addresses are the words stored at the frame's entry (`coinSlot k`, `tokenSlot`;
they never change after the constructor).

Each clause constrains a *positive* answer only (`some w`, `true`): the step function reverts
on `none`/`false` wherever it uses them, so a refinement statement `∃ e, EnvOf D e ∧ step s e c
= some o` pins exactly the answers the step reads. A clause is also met when the target runs no
code frame (`framed D t = false`: an undelegated precompile); such a call is
answered by Jaune's precompile semantics and leaves no child, so no coin code stands behind the
answer and none is claimed.

## The calls (`CallsOf`)

`CallsOf D` lists the non-static committed children as `(target, calldata, value)`. In a
non-static frame these are exactly the successful `CALL`s that enter a code frame; `STATICCALL`
children are static, and calls to the identity precompile (Vyper's `concat`) leave no child.
`modelCalls D calls` is the model's list, encoded at the frame's pool, coin and token addresses
and filtered to targets that run a code frame.

## The premise (`PoolCallsKeep`)

Each direct child leaves the pool's storage, read slot by slot, as it found it. This is the
environmental form of "the coins and 3Crv make no state-changing callback into the pool"; it is
per child, so U8 can discharge the 3Crv children from 3Crv's own theorems.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune

/-! ## Byte encodings -/

/-- A number as a 32-byte ABI word. -/
def word (n : Nat) : Bytes := (Nat.toB256 n).toBytes

/-- The address a stored or model number names (the low 160 bits of its word). -/
def adrOf (n : Nat) : Adr := (Nat.toB256 n).toAdr

def transferFromSel : Bytes := [0x23, 0xb8, 0x72, 0xdd]
def transferSel : Bytes := [0xa9, 0x05, 0x9c, 0xbb]
def mintSel : Bytes := [0x40, 0xc1, 0x0f, 0x19]
def burnFromSel : Bytes := [0x79, 0xcc, 0x67, 0x90]
def balanceOfSel : Bytes := [0x70, 0xa0, 0x82, 0x31]
def totalSupplySel : Bytes := [0x18, 0x16, 0x0d, 0xdd]

/-- `balanceOf(self)`'s calldata. -/
def balanceOfData (self : Adr) : Bytes := balanceOfSel ++ self.toB256.toBytes

/-- `totalSupply()`'s calldata. -/
def totalSupplyData : Bytes := totalSupplySel

/-- The first word of returned data, as a number. -/
def answerWord (out : Bytes) : Nat := (Bytes.toB256 (out.take 32)).toNat

/-! ## The frame's parties -/

/-- The pool's storage at the frame's entry. -/
def entryStor (D : Exec.Deriv) : Stor := D.devm.getStor D.sevm.currentTarget

/-- `coins[k]` at the frame's entry. -/
def coinAdr (D : Exec.Deriv) (k : Fin 3) : Adr := ((entryStor D).get (coinSlot k)).toAdr

/-- `token` (3Crv) at the frame's entry. -/
def tokenAdr (D : Exec.Deriv) : Adr := ((entryStor D).get tokenSlot).toAdr

/-- A call from the frame to `t` enters a code frame: `t` is not a precompile, or it carries an
EIP-7702 delegation (by its code at the frame's entry). A delegated call disables precompiles
(Jaune's `callMsg … disablePrecompiles`), so it always runs a code frame, the delegate's code,
even when the delegate is a precompile address; a call to an undelegated precompile is
answered by the precompile and leaves no child. -/
def framed (D : Exec.Deriv) (t : Adr) : Bool :=
  !decide (D.sevm.benvStat.rules.isPrecomp t) ||
    (getDelegatedCodeAddress (D.devm.getCode t)).isSome

/-- The frame's direct, settlement-committed children, in order. -/
def children (D : Exec.Deriv) : List Exec.Frame := Exec.childFrames D.exc

/-- Child `n` of the frame ran at `t` with calldata `input` and replied with at least a word
reading `w`. -/
def ReplyAt (D : Exec.Deriv) (n : Nat) (t : Adr) (input : Bytes) (w : Nat) : Prop :=
  ∃ c, (children D)[n]? = some c ∧ c.sevm.currentTarget = t ∧ c.sevm.data = input ∧
    32 ≤ c.post.output.length ∧ answerWord c.post.output = w

/-- Some child of the frame ran at `t` with calldata starting with `sel` and returned data
satisfying `ok`. -/
def CalledWith (D : Exec.Deriv) (t : Adr) (sel : Bytes) (ok : Bytes → Prop) : Prop :=
  ∃ c ∈ children D, c.sevm.currentTarget = t ∧ c.sevm.data.take 4 = sel ∧ ok c.post.output

/-- Coin `k`'s answers in `o` are its replies in the frame `D`. -/
structure CoinObsOf (D : Exec.Deriv) (k : Fin 3) (o : CoinObs) : Prop where
  balPre : ∀ w, o.balPre = some w → framed D (coinAdr D k) = false ∨
    ∃ n, ReplyAt D n (coinAdr D k) (balanceOfData D.sevm.currentTarget) w
  balPost : ∀ w', o.balPost = some w' → framed D (coinAdr D k) = false ∨
    ∃ w n m, o.balPre = some w ∧ n < m ∧
      ReplyAt D n (coinAdr D k) (balanceOfData D.sevm.currentTarget) w ∧
      ReplyAt D m (coinAdr D k) (balanceOfData D.sevm.currentTarget) w'
  pullOk : o.pullOk = true → framed D (coinAdr D k) = false ∨
    CalledWith D (coinAdr D k) transferFromSel RawCallOk
  pushOk : o.pushOk = true → framed D (coinAdr D k) = false ∨
    CalledWith D (coinAdr D k) transferSel RawCallOk

/-- **The frame's environment**: `e` is what the frame `D` observed (see the module note). -/
structure EnvOf (D : Exec.Deriv) (e : Env) : Prop where
  time : e.time = D.sevm.benvStat.time.toNat
  caller : e.caller = D.sevm.caller.toB256.toNat
  value : e.value = D.sevm.value.toNat
  coin : ∀ k, CoinObsOf D k (e.coin k)
  supply : ∀ T, e.supply = some T → framed D (tokenAdr D) = false ∨
    ∃ n, ReplyAt D n (tokenAdr D) totalSupplyData T
  mintOk : e.mintOk = true → framed D (tokenAdr D) = false ∨
    CalledWith D (tokenAdr D) mintSel (fun out => 32 ≤ out.length)
  burnOk : e.burnOk = true → framed D (tokenAdr D) = false ∨
    CalledWith D (tokenAdr D) burnFromSel (fun out => 32 ≤ out.length)

/-! ## The calls -/

/-- One external call: target, calldata, value. -/
structure CallReq where
  target : Adr
  input : Bytes
  value : B256

/-- **The frame's state-changing calls**: its non-static committed children, in order. -/
def CallsOf (D : Exec.Deriv) : List CallReq :=
  (children D).filterMap fun c =>
    if c.sevm.isStatic then none else some ⟨c.sevm.currentTarget, c.sevm.data, c.sevm.value⟩

/-- The call a model `ExtCall` is, from the pool at `pool` whose coins are at `coin` and whose
token is at `token`: the ABI calldata Vyper builds (`concat(method_id, convert(…, bytes32)…)`
for the `raw_call` transfers, the interface encoding for `mint`/`burnFrom`), value `0`. -/
def encodeCall (pool : Adr) (coin : Fin 3 → Adr) (token : Adr) : ExtCall → CallReq
  | .pull i src amt => ⟨coin i, transferFromSel ++ word src ++ pool.toB256.toBytes ++ word amt, 0⟩
  | .push i dst amt => ⟨coin i, transferSel ++ word dst ++ word amt, 0⟩
  | .mint dst amt => ⟨token, mintSel ++ word dst ++ word amt, 0⟩
  | .burn src amt => ⟨token, burnFromSel ++ word src ++ word amt, 0⟩

/-- The calls the model's list implies for the frame `D`: encoded at the frame's pool, coins and
token, and kept when the target enters a code frame. -/
def modelCalls (D : Exec.Deriv) (calls : List ExtCall) : List CallReq :=
  (calls.map (encodeCall D.sevm.currentTarget (coinAdr D) (tokenAdr D))).filter
    fun r => framed D r.target

/-! ## The per-child premise -/

/-- **Every direct child leaves the pool's storage as it found it**, slot by slot. -/
def PoolCallsKeep (D : Exec.Deriv) : Prop :=
  ∀ c ∈ children D, ∀ x,
    (c.post.getStor D.sevm.currentTarget).get x = (c.pre.getStor D.sevm.currentTarget).get x

/-! ## Facts -/

/-- At the frame's entry the stored coin and token words name the addresses `encodeCall` uses. -/
theorem coinAdr_eq {D : Exec.Deriv} {s : State} (h : Abstracts (entryStor D) s) (k : Fin 3) :
    coinAdr D k = adrOf (s.coins.get k) := by
  rw [coinAdr, adrOf, ← h.coins k, Jaune.toB256_toNat]

theorem tokenAdr_eq {D : Exec.Deriv} {s : State} (h : Abstracts (entryStor D) s) :
    tokenAdr D = adrOf s.token := by
  rw [tokenAdr, adrOf, ← h.token, Jaune.toB256_toNat]

/-- The frame's coin and token addresses are the model state's, read as addresses. -/
theorem encodeCall_entry {D : Exec.Deriv} {s : State} (h : Abstracts (entryStor D) s) :
    encodeCall D.sevm.currentTarget (coinAdr D) (tokenAdr D) =
      encodeCall D.sevm.currentTarget (fun k => adrOf (s.coins.get k)) (adrOf s.token) := by
  have hc : coinAdr D = fun k => adrOf (s.coins.get k) := funext (coinAdr_eq h)
  rw [hc, tokenAdr_eq h]

/-- When every party of the frame enters a code frame, the model's calls are all kept. -/
theorem modelCalls_of_framed {D : Exec.Deriv} {calls : List ExtCall}
    (h : ∀ r ∈ calls.map (encodeCall D.sevm.currentTarget (coinAdr D) (tokenAdr D)),
      framed D r.target = true) :
    modelCalls D calls = calls.map (encodeCall D.sevm.currentTarget (coinAdr D) (tokenAdr D)) :=
  List.filter_eq_self.mpr h

end Blanc.Lift.Curve3Pool
