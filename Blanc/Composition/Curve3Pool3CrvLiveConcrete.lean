import Blanc.Composition.Curve3Pool3CrvLiveWitness
import Blanc.Composition.Curve3Pool3CrvWorld

/-!
# The concrete entry machine of the liveness instances

One concrete entry machine for calls into the pool, built from `P0` (the U9(b) synthetic world)
with the trader's `600` 3Crv LP tokens and coins 1 and 2 funded for the pulls, and its plain facts
for any calldata: 3Crv's entry facts `C3Entry` at supply `6000` (`c3Entry_of`) and the three
`Token20` coins' `T20Coins` (`coins_of`), each by kernel evaluation through the state equations.
The end-to-end liveness instances with real selectors and model-pinned amounts are built on this
machine in `Curve3Pool3CrvLiveEndEntry` and the `Curve3Pool3CrvLiveEnd*` modules.
-/

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.Composition.Curve3PoolCalleeLive
open Blanc.Composition.Curve3Pool3CrvJoint

/-! ## Concrete entry states

The entry world is `P0` (U9(b)'s synthetic world) with three changes that make the calls fit at
positive amounts: the trader holds `600` 3Crv LP tokens (`cC3Stor`), and coins 1 and 2 give the
trader a `1000` balance and a `1000` allowance to the pool (`cCoinStor`).  Coin 0 already gives
the trader `1000` and an allowance of `100`.  The pool's storage is `poolStor` (balances
`1000, 2000, 3000`), 3Crv's supply is `T = 6000`, and the minter is the pool.  The entry machine
is `initSevm`/`initDevm` of the message `cMsg`; only its calldata varies per entry. -/

section Concrete

open Blanc.Composition.Curve3Pool3CrvJoint
open VyperNonreentrantDeployed.Token20 (balSlot allowSlot)

/-- 3Crv's storage with the trader holding `600` LP tokens (the holder's row is unchanged). -/
def cC3Stor : Stor := c3Stor.set (mapSlot 3 trader.toB256) 600

/-- A coin's ledger with the trader holding `1000` and approving the pool for `1000`. -/
def cCoinStor (σ : Stor) : Stor :=
  (σ.set (balSlot trader) 1000).set (allowSlot trader poolAddr) 1000

/-- The concrete entry world. -/
def cState : Jaune.State :=
  ((P0.set c3crvAddr { c3crvAcct with stor := cC3Stor }).set coin1Addr
    (coinAcct (cCoinStor coin1Stor))).set coin2Addr (coinAcct (cCoinStor coin2Stor))

/-- The concrete block environment: BPO2, chain `1`. -/
def cBenvStat : BenvStat :=
  { fork := .bpo2, chainId := 1, origState := cState, blockGasLimit := 900000,
    blockHashes := [], coinbase := 0, number := 0, baseFeePerGas := 1, time := 1,
    prevRandao := 0, excessBlobGas := 0, parentBeaconBlockRoot := 0 }

/-- The concrete block environment: the entry world. -/
def cBenv : Benv :=
  { state := cState, createdAccounts := .emptyWithCapacity, stat := cBenvStat }

/-- The concrete transaction environment: the trader is the origin. -/
def cTenv : Tenv :=
  { transientStorage := ∅,
    stat := { origin := trader, gasPrice := 1, gas := 900000,
              accessListAddresses := .emptyWithCapacity,
              accessListStorageKeys := .emptyWithCapacity,
              blobVersionedHashes := [], auths := [], indexInBlock := none, txHash := none } }

/-- The message of a call from the trader to the pool with calldata `data`. -/
def cMsg (data : Bytes) : Msg :=
  { benv := cBenv, tenv := cTenv, caller := trader, target := some poolAddr,
    currentTarget := poolAddr, gas := 878400, value := 0, data := data,
    codeAddress := some poolAddr, code := Blanc.Lift.Curve3Pool.code, depth := 1,
    shouldTransferValue := false, isStatic := false, accessedAddresses := .emptyWithCapacity,
    accessedStorageKeys := .emptyWithCapacity, disablePrecompiles := false }

/-- The entry machine of a call with calldata `d`. -/
abbrev cSevm (d : Bytes) : Sevm := initSevm (cMsg d)
/-- The entry devm of a call with calldata `d`. -/
abbrev cPre (d : Bytes) : Devm := initDevm (cMsg d)

/-! ### Lookups, not code evaluation

The code facts go through the state equations (`cState.get a` at each address), so the byte arrays
of 3Crv and `Token20` are never evaluated. -/

theorem cState_get_c3 : cState.get c3crvAddr = { c3crvAcct with stor := cC3Stor } := by
  unfold cState
  rw [State.get_set_ne _ (by decide +kernel), State.get_set_ne _ (by decide +kernel),
    State.get_set_self]

theorem cState_code_c3 : cState.getCode c3crvAddr = Curve3Crv.code :=
  congrArg Acct.code cState_get_c3

theorem cState_get_coin0 : cState.get coin0Addr = coinAcct coin0Stor := by
  unfold cState
  rw [State.get_set_ne _ (by decide +kernel), State.get_set_ne _ (by decide +kernel),
    State.get_set_ne _ (by decide +kernel), p0_coin0]

theorem cState_get_coin1 : cState.get coin1Addr = coinAcct (cCoinStor coin1Stor) := by
  unfold cState
  rw [State.get_set_ne _ (by decide +kernel), State.get_set_self]

theorem cState_get_coin2 : cState.get coin2Addr = coinAcct (cCoinStor coin2Stor) := by
  unfold cState
  rw [State.get_set_self]

theorem cState_code_coin0 : cState.getCode coin0Addr = VyperNonreentrantDeployed.Token20.code :=
  congrArg Acct.code cState_get_coin0

theorem cState_code_coin1 : cState.getCode coin1Addr = VyperNonreentrantDeployed.Token20.code :=
  congrArg Acct.code cState_get_coin1

theorem cState_code_coin2 : cState.getCode coin2Addr = VyperNonreentrantDeployed.Token20.code :=
  congrArg Acct.code cState_get_coin2

/-- The three coins' addresses. -/
def coinAdr : Fin 3 → Adr
  | 0 => coin0Addr
  | 1 => coin1Addr
  | 2 => coin2Addr

theorem cState_code_coin (k : Fin 3) : cState.getCode (coinAdr k) = VyperNonreentrantDeployed.Token20.code := by
  fin_cases k
  · exact cState_code_coin0
  · exact cState_code_coin1
  · exact cState_code_coin2

theorem cPre_getCode (d : Bytes) (a : Adr) : (cPre d).getCode a = cState.getCode a := rfl

theorem cSevm_target (d : Bytes) : (cSevm d).currentTarget = poolAddr := rfl

theorem cSevm_benv (d : Bytes) : (cSevm d).benvStat = cBenvStat := rfl

theorem cPre_getStor (d : Bytes) (a : Adr) : (cPre d).getStor a = cState.getStor a := rfl

/-- The pool's token is 3Crv (the pool's storage is the state's, whatever the calldata). -/
theorem cPre_tok (d : Bytes) : tokOf (cSevm d) (cPre d) = c3crvAddr := by
  have h : tokOf (cSevm d) (cPre d) = ((cState.getStor poolAddr).get tokenSlot).toAdr := rfl
  rw [h]
  decide +kernel

/-- The pool's coins are `coinAdr`. -/
theorem cPre_coin (d : Bytes) (k : Fin 3) : coinOf (cSevm d) (cPre d) k = coinAdr k := by
  have h : coinOf (cSevm d) (cPre d) k = ((cState.getStor poolAddr).get (coinSlot k)).toAdr := rfl
  rw [h]
  fin_cases k <;> decide +kernel

/-- 3Crv at the entry: its code, supply `6000`, the token is not the pool, and no precompile. -/
theorem c3Entry_of (d : Bytes) : C3Entry (cSevm d) (cPre d) 6000 :=
  ⟨by rw [cPre_getCode, cPre_tok]; exact cState_code_c3,
    by rw [cPre_getStor, cPre_tok]; decide +kernel,
    by rw [cPre_tok, cSevm_target]; decide +kernel,
    by rw [cPre_tok, cSevm_benv]; decide +kernel⟩

/-- The three coins at the entry: `Token20`'s code, not a precompile, not the pool nor 3Crv,
pairwise distinct. -/
theorem coins_of (d : Bytes) : T20Coins (cSevm d) (cPre d) :=
  ⟨fun k => by rw [cPre_getCode, cPre_coin]; exact cState_code_coin k,
    fun k => by rw [cPre_coin, cSevm_benv]; fin_cases k <;> decide +kernel,
    fun k => by rw [cPre_coin, cSevm_target]; fin_cases k <;> decide +kernel,
    fun k => by rw [cPre_coin, cPre_tok]; fin_cases k <;> decide +kernel,
    fun j k h => by
      rw [cPre_coin, cPre_coin]
      revert h
      fin_cases j <;> fin_cases k <;> decide +kernel⟩

end Concrete

end Blanc.Composition.Curve3Pool3CrvInstance
