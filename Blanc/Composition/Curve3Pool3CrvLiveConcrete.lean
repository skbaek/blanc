import Blanc.Composition.Curve3Pool3CrvLiveWitness
import Blanc.Composition.Curve3Pool3CrvWorld

/-!
# The liveness premises at a concrete entry machine

`Curve3Pool3CrvLiveWitness`'s `<entry>_premises_satisfiable` theorems are conditional. Here each
theorem's callee premises — and only the callee premises — are instantiated at one concrete entry
machine (built from `P0`, the U9(b) synthetic world, with the trader's `600` 3Crv LP tokens and
coins 1 and 2 funded for the pulls) at chosen positive amounts: the plain facts are discharged by
kernel evaluation, and the callee premises follow from the conditional theorem. The model step
(`hstep`) at the concrete entry is not discharged here, so agreement of the chosen amounts with
the model's outputs is not proved, and the composed `_live_entry` forms are not instantiated.
-/

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.Composition.Curve3PoolCalleeLive
open Blanc.Composition.Curve3Pool3CrvJoint

/-! ## Concrete entry states

The four `_premises_satisfiable` theorems above are conditional. Here each is instantiated at one
concrete entry machine built from `P0` (U9(b)'s synthetic world) with three changes that make the
calls fit at positive amounts: the trader holds `600` 3Crv LP tokens (`cC3Stor`), and coins 1
and 2 give the trader a `1000` balance and a `1000` allowance to the pool (`cCoinStor`).  Coin
0 already gives the trader `1000` and an allowance of `100`.  The pool's storage is `poolStor`
(balances `1000, 2000, 3000`), 3Crv's supply is `T = 6000`, and the minter is the pool.  The entry
machine is `initSevm`/`initDevm` of the message `cMsg`; only its calldata varies per entry. -/

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


/-- The `remove_liquidity` calldata: burn `600`. -/
def rlData : Bytes := abiSelectorBytes 0 ++ (600 : B256).toBytes
/-- The `add_liquidity` calldata: pulls `100, 200, 300`, minimum mint `1000`. -/
def alData : Bytes := abiSelectorBytes 0 ++ (100 : B256).toBytes ++ (200 : B256).toBytes ++
  (300 : B256).toBytes ++ (1000 : B256).toBytes
/-- The `remove_liquidity_imbalance` calldata: amounts `100, 200, 300`, maximum burn `600`. -/
def rliData : Bytes := abiSelectorBytes 0 ++ (100 : B256).toBytes ++ (200 : B256).toBytes ++
  (300 : B256).toBytes ++ (600 : B256).toBytes
/-- The `remove_liquidity_one_coin` calldata: burn `600`. -/
def ocData : Bytes := abiSelectorBytes 0 ++ (600 : B256).toBytes

/-- The entry machine of a call with calldata `d`. -/
abbrev cSevm (d : Bytes) : Sevm := initSevm (cMsg d)
/-- The entry devm of a call with calldata `d`. -/
abbrev cPre (d : Bytes) : Devm := initDevm (cMsg d)

abbrev rlSevm : Sevm := cSevm rlData
abbrev rlPre : Devm := cPre rlData
abbrev alSevm : Sevm := cSevm alData
abbrev alPre : Devm := cPre alData
abbrev rliSevm : Sevm := cSevm rliData
abbrev rliPre : Devm := cPre rliData
abbrev ocSevm : Sevm := cSevm ocData
abbrev ocPre : Devm := cPre ocData

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

theorem rl_amt : rlAmt rlSevm = 600 := by decide +kernel

theorem al_amts : alAmt alSevm 0 = 100 ∧ alAmt alSevm 1 = 200 ∧ alAmt alSevm 2 = 300 := by
  decide +kernel

theorem rli_amts : rliAmt rliSevm 0 = 100 ∧ rliAmt rliSevm 1 = 200 ∧ rliAmt rliSevm 2 = 300 := by
  decide +kernel

theorem oc_amt : ocAmt ocSevm = 600 := by decide +kernel

/-- **`remove_liquidity`'s callee premises hold at the concrete entry** (`T = 6000`, burn
`600`, pushes `100, 200, 300`): the conditional theorem, its plain facts kernel-checked. Only
the callee premises; the model step is not discharged and the `_live_entry` form is not
instantiated. -/
theorem removeLiquidity_premises_satisfiable_concrete :
    0 < (rlAmt rlSevm).toNat ∧
    (∀ k, k ≤ 3 → WClosed rlSevm (rlWorld rlSevm rlPre k)) ∧ rlWorld rlSevm rlPre 0 rlPre ∧
      SupplyOk rlSevm (rlWorld rlSevm rlPre 0) ((rlPre.getStor rlSevm.currentTarget).get tokenSlot) 6000
        80000 ∧
      (∀ k : Fin 3, CoinPushOkAt rlSevm (rlWorld rlSevm rlPre k) (rlWorld rlSevm rlPre (k + 1))
        ((rlPre.getStor rlSevm.currentTarget).get (coinSlot k))
        (balAt (rlPre.getStor rlSevm.currentTarget) k * rlAmt rlSevm / 6000) 80000 0x520 0x5c0) ∧
      BurnOkTo rlSevm (rlWorld rlSevm rlPre 3) (rlWorld rlSevm rlPre 4)
        ((rlPre.getStor rlSevm.currentTarget).get tokenSlot) (rlAmt rlSevm) 80000 := by
  have hc3 := c3Entry_of rlData
  have hcoins := coins_of rlData
  refine ⟨by rw [rl_amt]; decide +kernel, removeLiquidity_premises_satisfiable (sevm := rlSevm)
    (pre := rlPre) (T := 6000) (by decide +kernel) rfl (by decide +kernel) hc3 hcoins ?_ ?_⟩
  · unfold BurnFits; decide +kernel
  · unfold T20MoveFits; decide +kernel


/-- **`add_liquidity`'s callee premises hold at the concrete entry** (`T = 6000`, mint `1000`,
pulls `100, 200, 300`): the conditional theorem, its plain facts kernel-checked. Only the callee
premises; the model step is not discharged and the `_live_entry` form is not instantiated. -/
theorem addLiquidity_premises_satisfiable_concrete :
    0 < (alAmt alSevm 0).toNat ∧ 0 < (alAmt alSevm 1).toNat ∧ 0 < (alAmt alSevm 2).toNat ∧
    (∀ k, k ≤ 4 → WClosed alSevm (alWorld alSevm alPre 1000 k)) ∧ alWorld alSevm alPre 1000 0 alPre ∧
      SupplyOkAt alSevm (alWorld alSevm alPre 1000 0) (alWorld alSevm alPre 1000 0)
        ((alPre.getStor alSevm.currentTarget).get tokenSlot) 6000 80000 0x27c 0x2c0 ∧
      (∀ k : Fin 3, k ≠ feeIndex → alAmt alSevm k.val ≠ 0 →
        CoinPullOkAt alSevm (alWorld alSevm alPre 1000 k) (alWorld alSevm alPre 1000 (k + 1))
          ((alPre.getStor alSevm.currentTarget).get (coinSlot k)) (alAmt alSevm k.val) 80000 0x760
          0x820) ∧
      (∀ k : Fin 3, alAmt alSevm k.val = 0 → ∀ b, alWorld alSevm alPre 1000 k b →
        alWorld alSevm alPre 1000 (k + 1) b) ∧
      (alAmt alSevm 2 ≠ 0 →
        CoinBalOkAt alSevm (alWorld alSevm alPre 1000 2) (alWorld alSevm alPre 1000 2)
          ((alPre.getStor alSevm.currentTarget).get (coinSlot 2))
          ((alPre.getStor (coinOf alSevm alPre 2)).get
            (VyperNonreentrantDeployed.Token20.balSlot alSevm.currentTarget)) 80000 0x53c 0x5a0 ∧
        CoinPullOkAt alSevm (alWorld alSevm alPre 1000 2) (alWorld alSevm alPre 1000 3)
          ((alPre.getStor alSevm.currentTarget).get (coinSlot 2)) (alAmt alSevm 2) 80000 0x760 0x820 ∧
        CoinBalOkAt alSevm (alWorld alSevm alPre 1000 3) (alWorld alSevm alPre 1000 3)
          ((alPre.getStor alSevm.currentTarget).get (coinSlot 2))
          ((alFeeStor alSevm alPre).get (VyperNonreentrantDeployed.Token20.balSlot alSevm.currentTarget))
          80000 0x87c 0x8e0) ∧
      MintOkAt alSevm (alWorld alSevm alPre 1000 3) (alWorld alSevm alPre 1000 4)
        ((alPre.getStor alSevm.currentTarget).get tokenSlot) 1000 80000 0xc7c 0xd00 := by
  have hc3 := c3Entry_of alData
  have hcoins := coins_of alData
  refine ⟨by rw [al_amts.1]; decide +kernel, by rw [al_amts.2.1]; decide +kernel, by rw [al_amts.2.2]; decide +kernel,
    addLiquidity_premises_satisfiable (sevm := alSevm) (pre := alPre) (T := 6000) (m := 1000)
      (by decide +kernel) rfl (by decide +kernel) hc3 hcoins ?_ ?_⟩
  · unfold MintFits; decide +kernel
  · unfold T20PullFits t20Allow T20MoveFits; decide +kernel


/-- **`remove_liquidity_imbalance`'s callee premises hold at the concrete entry** (`T = 6000`,
burn `600`, pushes `100, 200, 300`): the conditional theorem, its plain facts kernel-checked.
Only the callee premises; the model step is not discharged and the `_live_entry` form is not
instantiated. -/
theorem removeLiquidityImbalance_premises_satisfiable_concrete :
    0 < (rliAmt rliSevm 0).toNat ∧ 0 < (rliAmt rliSevm 1).toNat ∧ 0 < (rliAmt rliSevm 2).toNat ∧
    (∀ j, j ≤ 4 → WClosed rliSevm (rliWorld rliSevm rliPre 600 j)) ∧ rliWorld rliSevm rliPre 600 0 rliPre ∧
      SupplyOkAt rliSevm (rliWorld rliSevm rliPre 600 0) (rliWorld rliSevm rliPre 600 0)
        ((rliPre.getStor rliSevm.currentTarget).get tokenSlot) 6000 80000 0x17c 0x1c0 ∧
      BurnOkAt rliSevm (rliWorld rliSevm rliPre 600 0) (rliWorld rliSevm rliPre 600 1)
        ((rliPre.getStor rliSevm.currentTarget).get tokenSlot) 600 80000 0x85c 0x8e0 ∧
      (∀ k : Fin 3, rliAmt rliSevm k.val ≠ 0 →
        CoinPushOkAt rliSevm (rliWorld rliSevm rliPre 600 (k + 1)) (rliWorld rliSevm rliPre 600 (k + 2))
          ((rliPre.getStor rliSevm.currentTarget).get (coinSlot k)) (rliAmt rliSevm k.val) 80000 0xaa0
          0xb40) ∧
      (∀ k : Fin 3, rliAmt rliSevm k.val = 0 → ∀ b, rliWorld rliSevm rliPre 600 (k + 1) b →
        rliWorld rliSevm rliPre 600 (k + 2) b) := by
  have hc3 := c3Entry_of rliData
  have hcoins := coins_of rliData
  refine ⟨by rw [rli_amts.1]; decide +kernel, by rw [rli_amts.2.1]; decide +kernel, by rw [rli_amts.2.2]; decide +kernel,
    removeLiquidityImbalance_premises_satisfiable (sevm := rliSevm) (pre := rliPre) (T := 6000)
      (m := 600) (by decide +kernel) rfl (by decide +kernel) hc3 hcoins ?_ ?_⟩
  · unfold BurnFits; decide +kernel
  · unfold T20MoveFits; decide +kernel


/-- **`remove_liquidity_one_coin`'s callee premises hold at the concrete entry** (`T = 6000`,
burn `600`, coin `0` pushes `100`): the conditional theorem, its plain facts kernel-checked. Only
the callee premises; the model step is not discharged and the `_live_entry` form is not
instantiated. -/
theorem removeLiquidityOneCoin_premises_satisfiable_concrete :
    0 < (ocAmt ocSevm).toNat ∧
    WClosed ocSevm (ocWorld ocSevm ocPre (Devm.getStor ocPre (tokOf ocSevm ocPre)) 0) ∧
      WClosed ocSevm (ocWorld ocSevm ocPre (burnStor (Devm.getStor ocPre (tokOf ocSevm ocPre))
        ocSevm.caller.toB256 (ocAmt ocSevm)) 0) ∧
      ocWorld ocSevm ocPre (Devm.getStor ocPre (tokOf ocSevm ocPre)) 0 ocPre ∧
      SupplyOkAt ocSevm (ocWorld ocSevm ocPre (Devm.getStor ocPre (tokOf ocSevm ocPre)) 0)
        (ocWorld ocSevm ocPre (Devm.getStor ocPre (tokOf ocSevm ocPre)) 0)
        ((ocPre.getStor ocSevm.currentTarget).get tokenSlot) 6000 80000 0x2bc 0x300 ∧
      BurnOkAt ocSevm (ocWorld ocSevm ocPre (Devm.getStor ocPre (tokOf ocSevm ocPre)) 0)
        (ocWorld ocSevm ocPre (burnStor (Devm.getStor ocPre (tokOf ocSevm ocPre)) ocSevm.caller.toB256
          (ocAmt ocSevm)) 0)
        ((ocPre.getStor ocSevm.currentTarget).get tokenSlot) (ocAmt ocSevm) 80000 0x31c 0x3a0 ∧
      WClosed ocSevm (fun _ => True) ∧
      CoinPushOkAt ocSevm (ocWorld ocSevm ocPre (burnStor (Devm.getStor ocPre (tokOf ocSevm ocPre))
          ocSevm.caller.toB256 (ocAmt ocSevm)) 0) (fun _ => True)
        ((ocPre.getStor ocSevm.currentTarget).get (coinSlot 0)) 100 80000 0x540 0x5e0 := by
  have hc3 := c3Entry_of ocData
  have hcoin0 : coinOf ocSevm ocPre 0 = coin0Addr := by rw [cPre_coin]; rfl
  refine ⟨by rw [oc_amt]; decide +kernel, removeLiquidityOneCoin_premises_satisfiable (sevm := ocSevm)
    (pre := ocPre) (T := 6000) (v := 100) (i := 0) (by decide +kernel) rfl (by decide +kernel) hc3
    (by rw [cPre_getCode, hcoin0]; exact cState_code_coin0) (by rw [hcoin0]; decide +kernel)
    (by rw [hcoin0]; decide +kernel) (by rw [hcoin0]; decide +kernel) ?_ ?_⟩
  · unfold BurnFits; decide +kernel
  · unfold T20MoveFits; decide +kernel


end Concrete

end Blanc.Composition.Curve3Pool3CrvInstance
