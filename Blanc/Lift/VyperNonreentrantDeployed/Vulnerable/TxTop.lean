import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Attacker2.Check
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.WitnessCerts
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
import Blanc.Lift.WitnessChild
import Blanc.Lift.Exact

/-!
V- as an admitted transaction (O10, best effort), stage 2 (outer frame): the tx-level
dispatcher attacker `A'` (`Attacker2`, registry id `vminus-attacker2`), entered from a
transaction-shaped message under **real** EIP-2929 pre-warming (`prepareMessage`, not the
message-level witness's empty accessed sets), reaches its `CALL` into the pool proxy `P`
with `remove_liquidity(200, [0, 0], A')` calldata and value 0.

This is deliberately self-contained: it does not (yet) wire this frame to the deep chain
(`Vulnerable.SubtreeRun`/`Frame4Chunks`), whose gas and accessed-set literals were all taken
from a message-level trace with empty accessed sets, and would need to be regenerated from a
trace with the real `E`/`A'`/precompile pre-warming (Plans `reports/vminus-tx-v1.md`
diagnosis). What this module gives: `prepareMessage` really does succeed for the chosen
type-2, zero-fee, zero-value transaction from the EOA `E`; `Frame.ofCall` on the resulting
message enters `A'`'s certificate; and the certificate's own dispatcher branch (proved by
running the interpreter over the *registered* `Attacker2` certificate, not by hand-picking a
branch) reaches the intended `CALL`, with the calldata and value the entry chain actually
produces -- via the generic `callPrep`/`callPrep_spec`, not any V--specific lemma.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop

open Jaune Blanc.Lift Blanc.Lift.Witness
open Blanc.Lift.VyperNonreentrantDeployed
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1

/-! ### Addresses -/

/-- The EOA sender `E` of the vminus-tx-v1 witness: nonce 0, no code, no balance (the
transaction's fees and value are both zero, so none is needed). -/
def eAddress : Adr := 0xeeee0000000000000000000000000000000000e0

/-- The tx-level dispatcher attacker `A'` (the address baked into `Attacker2.code`'s own
`receiver` literals; a byte list, not a hand-typed hex string -- see
`scripts/lift/certificates.json`'s `vminus-attacker2` provenance for the 19-byte address
that this replaced). -/
def a2Address : Adr := 0xaaaa0000000000000000000000000000a2a2a2a2

/-! ### The pre-state -/

/-- The pre-state's accounts without storage: the proxy, the implementation and the honest
token exactly as in the message-level witness (`Vulnerable.Frame1`), `A'` holding the
registered `Attacker2` certificate's bytes, and `E` (an EOA, nonce 0, no code). -/
def acctsTx : List (Adr × Acct) :=
  [(proxyAddress, ⟨1, (1000 : Nat).toB256, .empty, proxyCode⟩),
   (implementationAddress, ⟨1, 0, .empty, code⟩),
   (a2Address, ⟨1, 0, .empty, Attacker2.code⟩),
   (tokenAddress, ⟨1, 0, .empty, tokenCode⟩),
   (eAddress, ⟨0, 0, .empty, .empty⟩)]

def worldTx_base : State := stateFoldAcct default acctsTx

theorem storOf_worldTx_base (a : Adr) (k : B256) : storOf worldTx_base a k = 0 :=
  storOf_stateFoldAcct acctsTx a k

def acsTx0 : AcctShadow := acctShadowOf acctsTx

theorem acctAgree_worldTx_base : AcctAgree worldTx_base acsTx0 :=
  acctAgree_stateFoldAcct acctsTx

/-- Concrete storage writes of the pre-state: the pool's, exactly as in the message-level
witness, and the token's `balanceOf[P] = 1000`. -/
def poolWritesTx : List ((Adr × B256) × B256) :=
  poolStorage.map (fun (k, v) => ((proxyAddress, k.toB256), v.toB256)) ++
    [((tokenAddress, proxyAddress.toNat.toB256), (1000 : Nat).toB256)]

def worldTx : State := stateFoldStor worldTx_base poolWritesTx

theorem acctAgree_worldTx : AcctAgree worldTx acsTx0 :=
  acctAgree_stateFoldStor poolWritesTx acctAgree_worldTx_base

/-! ### The transaction -/

/-- The dispatcher selector the tx's calldata carries: `A'`'s "start" branch. -/
def START : Bytes := [0x12, 0x34, 0x56, 0x78]

/-- `remove_liquidity(200, [0, 0], A')`: `Vulnerable.Frame1.removeCalldata` with the
receiver `A'` instead of the message-level witness's old attacker. -/
def removeCalldata2 : Bytes :=
  [0x3e, 0xb1, 0x71, 0x9f] ++ word 200 ++ word 0 ++ word 0 ++ word a2Address.toNat

/-- A type-2 (EIP-1559), zero-fee, zero-value transaction from `E` to `A'`: `chainId = 0`,
`maxPriorityFee = maxFee = 0` (legal since `baseFeePerGas = 0`), empty access list, nonce 0
(matching `E`'s nonce), 30,000,000 gas, calldata `START`. -/
def tx0 : Tx :=
  { nonce := 0, gas := 30000000, value := 0, data := START, v := 0, r := [], s := [],
    type := .two (0 : UInt64) 0 0 (some a2Address) [] }

def benvStatTx : BenvStat :=
  { fork := .prague, chainId := 0, origState := worldTx, blockGasLimit := 30000000,
    blockHashes := [], coinbase := 0, number := 0, baseFeePerGas := 0, time := 0,
    prevRandao := 0, excessBlobGas := 0, parentBeaconBlockRoot := 0 }

def benv0 : Benv :=
  { state := worldTx, createdAccounts := .emptyWithCapacity, stat := benvStatTx }

def tenvStat0 : TenvStat :=
  { origin := eAddress, gasPrice := 0, gas := 30000000, stateGasReservoir := 0,
    accessListAddresses := .emptyWithCapacity, accessListStorageKeys := .emptyWithCapacity,
    blobVersionedHashes := [], auths := [], indexInBlock := some 0, txHash := none }

def tenv0 : Tenv := { transientStorage := default, stat := tenvStat0 }

/-! ### `prepareMessage` really succeeds, with the real EIP-2929 warm set -/

/-- The message `prepareMessage` produces for `tx0` over `benv0`/`tenv0`. -/
def msg0tx : Msg :=
  match prepareMessage benv0 tenv0 tx0 with
  | .ok m => m
  | .error _ => default

theorem msg0tx_eq : prepareMessage benv0 tenv0 tx0 = .ok msg0tx := by kernel_rfl

/-- `prepareMessage`'s pre-warmed set at entry is exactly the 17 Prague precompiles plus
`E` (the origin) and `A'` (the target) -- not the empty set the message-level witness used.
This is the one fact that makes this an honest transaction-shaped entry. -/
theorem msg0tx_adrs_eq : msg0tx.accessedAddresses =
    (Std.HashSet.emptyWithCapacity : AdrSet).insertMany
      (praguePrecompiles ++ [eAddress, a2Address]) := by kernel_rfl

theorem msg0tx_adrs : ∀ a, a ∈ msg0tx.accessedAddresses ↔
    a ∈ (praguePrecompiles ++ [eAddress, a2Address]) := by
  intro a
  rw [msg0tx_adrs_eq, Std.HashSet.mem_insertMany_list]
  simp

theorem msg0tx_keys_empty : msg0tx.accessedStorageKeys = (Std.HashSet.emptyWithCapacity : KeySet) := by
  kernel_rfl

theorem msg0tx_facts : (msg0tx.caller, msg0tx.currentTarget, msg0tx.code, msg0tx.data,
    msg0tx.value, msg0tx.depth, msg0tx.benv.stat.fork) =
    (eAddress, a2Address, Attacker2.code, START, 0, 1024, .prague) := by kernel_rfl

/-! ### The frame enters -/

def f0tx : Frame := Frame.ofCall msg0tx

def e0tx : Evm := match frameEnterS f0tx acsTx0 with | .run e => e | .done _ => default

theorem e0tx_eq : frameEnterS f0tx acsTx0 = .run e0tx := by kernel_rfl

/-- The real `Frame.enter` (what `Exec`/`processMessage` actually use) agrees with the
shadow-based, kernel-cheap `frameEnterS` once the account shadow agrees with the world --
exactly the bridge the message-level witness's `f0_enter` uses. -/
theorem f0tx_enter : f0tx.enter = .run e0tx := by
  rw [frame_enter_eq_B, frameEnterB_eq_S (acs := acsTx0) acctAgree_worldTx]; exact e0tx_eq

theorem e0tx_facts : (e0tx.pc, e0tx.sta.code, e0tx.sta.data, e0tx.sta.benvStat.fork) =
    (0, Attacker2.code, START, .prague) := by kernel_rfl

theorem e0tx_meta : ∃ benv, benvAfterTransferS msg0tx acsTx0 = .ok benv ∧
    e0tx = initEvm (msg0tx.withBenv benv) := frameEnterS_run e0tx_eq

theorem e0tx_adrs : ∀ a, a ∈ e0tx.dyna.accessedAddresses ↔
    a ∈ (praguePrecompiles ++ [eAddress, a2Address]) := by
  obtain ⟨benv, -, he⟩ := e0tx_meta
  intro a
  show a ∈ e0tx.dyna.accessedAddresses ↔ _
  rw [he]
  show a ∈ msg0tx.accessedAddresses ↔ _
  exact msg0tx_adrs a

theorem e0tx_keys : ∀ x, x ∈ e0tx.dyna.accessedStorageKeys ↔ x ∈ ([] : List (Adr × B256)) := by
  obtain ⟨benv, -, he⟩ := e0tx_meta
  intro x
  show x ∈ e0tx.dyna.accessedStorageKeys ↔ _
  rw [he]
  show x ∈ msg0tx.accessedStorageKeys ↔ _
  rw [msg0tx_keys_empty]
  simp

theorem e0tx_stor : ∀ a k, storOf e0tx.dyna.state a k = storOf worldTx a k := by
  obtain ⟨benv, hb, he⟩ := e0tx_meta
  have hbB : benvAfterTransferB msg0tx = .ok benv := by
    rw [benvAfterTransfer_eq_S acctAgree_worldTx]; exact hb
  intro a k
  show storOf e0tx.dyna.state a k = _
  rw [he]
  show storOf benv.state a k = _
  rw [benvAfterTransferB_stor hbB]
  rfl

/-- The account shadow after the (zero) value transfer of the top-level message. -/
def acsTx1 : AcctShadow := acsTransfer msg0tx acsTx0

theorem acctAgree_acsTx1 : AcctAgree e0tx.dyna.state acsTx1 := by
  obtain ⟨benv, hb, he⟩ := e0tx_meta
  show AcctAgree e0tx.dyna.state _
  rw [he]
  exact acctAgree_transfer acctAgree_worldTx hb

/-! ### The certificate run, to the intended `CALL` -/

abbrev fs2 : List SFunc := Cert.prog Attacker2.cert

/-- The start configuration: no accessed storage keys, the accessed addresses
`prepareMessage` warmed. -/
def c0tx : Cfg :=
  ⟨e0tx.dyna, Attacker2.t_0000_c0, [], [], praguePrecompiles ++ [eAddress, a2Address],
    storShadowOf poolWritesTx, acsTx1⟩

theorem c0tx_agree : Agree c0tx :=
  ⟨e0tx_keys, e0tx_adrs,
    fun a k => (e0tx_stor a k).trans (storOf_stateFoldStor poolWritesTx storOf_worldTx_base a k),
    acctAgree_acsTx1⟩

/-- The certificate run over `A'`'s own bytes, from the real transaction-shaped entry, for
33 nodes: 8 to decide the dispatcher (`CALLDATALOAD(0) >> 224 == 0x12345678`, true, since
`msg0tx.data = START`) and land at `t_0064_c0` (the "start" branch, unconsumed), 1 more for
`t_0064_c0`'s own `.dest` wrapper (the `JUMPDEST` it is a jump target for), then 24 more
(the same count the message-level witness's old attacker needed for its structurally
identical body) to reach the `CALL`. -/
def callCfg : Cfg :=
  match wrun fs2 e0tx.sta 33 c0tx with | .cont c => c | _ => c0tx

theorem callCfg_eq : wrun fs2 e0tx.sta 33 c0tx = .cont callCfg := by kernel_rfl

theorem callCfg_agree : Agree callCfg := (wrun_cont callCfg_eq).1 c0tx_agree

/-- A placeholder spawn (never reached: every use is pinned by a kernel equation). -/
def noPrep : CallPrep := ⟨Frame.ofCall default, default, 0, 0, []⟩

/-- `A'`'s `CALL` up to its spawn: the generic `callPrep`, not any V--specific lemma. -/
def cp0 : CallPrep := (callPrep e0tx.sta callCfg).getD noPrep

theorem cp0_eq : callPrep e0tx.sta callCfg = some cp0 := by kernel_rfl

theorem cp0_spec :
    Xinst.step e0tx.sta callCfg.devm .call = .spawn cp0.f (.call cp0.p cp0.oi cp0.os) ∧
      (∀ a, a ∈ cp0.p.accessedAddresses ↔ a ∈ cp0.adrs) ∧
      cp0.p.accessedStorageKeys = callCfg.devm.accessedStorageKeys ∧
      cp0.f.isCreate = false ∧ cp0.f.inner.accessedAddresses = cp0.p.accessedAddresses ∧
      cp0.f.inner.accessedStorageKeys = cp0.p.accessedStorageKeys ∧
      cp0.f.inner.benv.stat.rules.stateGas = none ∧ cp0.f.inner.benv.state = callCfg.devm.state :=
  callPrep_spec cp0_eq callCfg_agree.2.1 callCfg_agree.2.2.2

/-- **The spawn is the intended call**: `A'`'s `CALL` spawns a message to `P` with
`remove_liquidity(200, [0, 0], A')` calldata, value 0. -/
theorem cp0_facts : (cp0.f.inner.currentTarget, cp0.f.inner.target, cp0.f.inner.data,
    cp0.f.inner.value, cp0.f.inner.isStatic, cp0.f.isCreate) =
    (proxyAddress, some proxyAddress, removeCalldata2, 0, false, false) := by kernel_rfl

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop
