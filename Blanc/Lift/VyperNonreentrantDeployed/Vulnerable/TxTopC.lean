import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop
import Blanc.ExecutionTrace
import Blanc.TransactionFork

/-!
V- as an admitted transaction under every covered fork (`TxC`), stage 1: the transaction.

`TxTop.tx0` carries 30,021,064 gas, above the per-transaction cap of 2^24 = 16,777,216 that
EIP-7825 enforces from Osaka on, so under Osaka, BPO1 and BPO2 it is not a valid transaction.
`txC` is the same transaction from the same EOA `E` to the same dispatcher attacker `A'` with
calldata `START` and zero fees, with **16,043,200 gas** (the run uses about 160,000) and an
EIP-2930 access list naming every precompile Osaka defines (the 17 Prague ones and `P256VERIFY`,
`0x100`) and `A'`.  `prepareMessage` pre-warms the fork's own precompiles (EIP-2929) and the
fork defines a different set (Osaka adds `P256VERIFY`); with every one of them already in the
access list the pre-warming inserts nothing, so the prepared message's accessed addresses are the
same set *term* under every covered fork (`Blanc/TransactionFork.lean`): the 18 precompiles, `E`
(the coinbase, warm from Shanghai) and `A'`.  The access list's 19 addresses cost 45,600 gas: the
intrinsic gas is 66,664 and the message runs with 15,976,536 gas.

The pre-state, the block and the chain are `TxTop`'s.  The signature is a real one over the new
signing hash, checked by the `#guard` below.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Witness
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop

/-- The signature `(r, s)` of `txC` under `E`'s key over `txC`'s signing hash (`v = 0`, low `s`),
computed outside Lean; that it recovers `E` is checked by the `#guard` below (evaluation, not the
kernel: `secp256k1.recover` is not kernel-reducible). -/
def sigRC : Bytes :=
  [2, 107, 40, 147, 207, 207, 8, 151, 9, 73, 250, 60, 167, 47, 209, 200, 79, 210, 155, 165, 218,
    222, 124, 138, 34, 120, 94, 94, 157, 67, 59, 42]

def sigSC : Bytes :=
  [118, 229, 47, 181, 107, 73, 229, 248, 41, 4, 233, 64, 58, 31, 158, 38, 173, 99, 25, 37, 125,
    154, 130, 95, 153, 96, 20, 105, 250, 161, 245, 33]

/-- The access list: every precompile Osaka defines, and `A'`. -/
def accessListC : List (Adr × List B256) :=
  (osakaPrecompiles.map fun a => (a, ([] : List B256))) ++ [(a2Address, [])]

/-- **The transaction**: type 2, zero fees, zero value, from `E` to `A'`, calldata `START`, nonce
0, 16,043,200 gas (below the 2^24 cap) and the access list `accessListC`. -/
def txC : Tx :=
  { nonce := 0, gas := 16043200, value := 0, data := START, v := 0, r := sigRC, s := sigSC,
    type := .two (0 : UInt64) 0 0 (some a2Address) accessListC }

#guard (recoverSender 0 txC).toOption == some eAddress

/-- The gas the message runs with: the transaction's less the intrinsic 66,664 (21,000, the 64 of
the four nonzero calldata bytes and the 2,400 of each of the access list's 19 addresses). -/
def msgGasC : Nat := 15976536

/-- The transaction environment `processTransaction` builds (index 0 in the block). -/
def tenv0C : Tenv := transactionTenv benv0 txC 0 eAddress 0 66664 []

/-- The message `prepareMessage` produces for `txC` over `benv0`/`tenv0C`. -/
def msgC : Msg :=
  match prepareMessage benv0 tenv0C txC with
  | .ok m => m
  | .error _ => default

theorem msgC_eq : prepareMessage benv0 tenv0C txC = .ok msgC := by kernel_rfl

/-- The addresses the message pre-warms, as a list: the 17 Prague precompiles, `P256VERIFY`,
`E` and `A'`. -/
def warmC : List Adr := praguePrecompiles ++ [(0x100 : Adr), eAddress, a2Address]

/-- An address in the access list (or `E`, the coinbase) is warm in the transaction environment. -/
theorem accessListC_contains {l : List Adr}
    (hl : ∀ a ∈ l, a ∈ eAddress :: accessListC.map Prod.fst) :
    ∀ a ∈ l, tenv0C.stat.accessListAddresses.contains a = true := by
  intro a ha
  rw [show tenv0C.stat.accessListAddresses =
    Std.HashSet.ofList (eAddress :: accessListC.map Prod.fst) from rfl,
    Std.HashSet.contains_ofList, List.contains_eq_mem]
  exact decide_eq_true (hl a ha)

/-- The access list warms every address the preparation inserts, so the prepared message's
accessed addresses are the transaction's access-list set itself, under every covered fork
(`TransactionFork.hashSet_insertMany_of_subset`). -/
theorem msgC_adrs_eq : msgC.accessedAddresses = tenv0C.stat.accessListAddresses := by
  have h : prepareMessage benv0 tenv0C txC = .ok msgC := msgC_eq
  unfold prepareMessage at h
  simp only [show txC.type.receiver? = some a2Address from rfl] at h
  have hm := Except.ok.inj h
  rw [← hm]
  exact TransactionFork.hashSet_insertMany_of_subset _ _ (accessListC_contains (by
    show ∀ a ∈ praguePrecompiles ++ [eAddress, a2Address],
      a ∈ eAddress :: accessListC.map Prod.fst
    decide +kernel))

theorem msgC_adrs : ∀ a, a ∈ msgC.accessedAddresses ↔ a ∈ warmC := by
  intro a
  rw [msgC_adrs_eq, show tenv0C.stat.accessListAddresses =
    Std.HashSet.ofList (eAddress :: accessListC.map Prod.fst) from rfl, Std.HashSet.mem_ofList]
  simp only [List.contains_eq_mem, decide_eq_true_eq, accessListC, List.map_append, List.map_map,
    List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false, warmC,
    osakaPrecompiles, Function.comp_def, exists_eq_right, exists_eq_left]
  tauto

theorem msgC_keys_empty : msgC.accessedStorageKeys = (Std.HashSet.ofList [] : KeySet) := by
  kernel_rfl

theorem msgC_facts : (msgC.caller, msgC.currentTarget, msgC.code, msgC.data,
    msgC.value, msgC.depth, msgC.benv.stat.fork, msgC.gas) =
    (eAddress, a2Address, Attacker2.code, START, 0, 1024, .prague, msgGasC) := by kernel_rfl

/-! ### The frame enters -/

def f0C : Frame := Frame.ofCall msgC

def e0C : Evm := match frameEnterS f0C acsTx0 with | .run e => e | .done _ => default

theorem e0C_eq : frameEnterS f0C acsTx0 = .run e0C := by kernel_rfl

/-- The real `Frame.enter` (what `Exec`/`processMessage` actually use) agrees with the
shadow-based, kernel-cheap `frameEnterS` once the account shadow agrees with the world --
exactly the bridge the message-level witness's `f0_enter` uses. -/
theorem f0C_enter : f0C.enter = .run e0C := by
  rw [frame_enter_eq_B, frameEnterB_eq_S (acs := acsTx0) acctAgree_worldTx]; exact e0C_eq

theorem e0C_facts : (e0C.pc, e0C.sta.code, e0C.sta.data, e0C.sta.benvStat.fork) =
    (0, Attacker2.code, START, .prague) := by kernel_rfl

theorem e0C_meta : ∃ benv, benvAfterTransferS msgC acsTx0 = .ok benv ∧
    e0C = initEvm (msgC.withBenv benv) := frameEnterS_run e0C_eq

theorem e0C_adrs : ∀ a, a ∈ e0C.dyna.accessedAddresses ↔
    a ∈ warmC := by
  obtain ⟨benv, -, he⟩ := e0C_meta
  intro a
  show a ∈ e0C.dyna.accessedAddresses ↔ _
  rw [he]
  show a ∈ msgC.accessedAddresses ↔ _
  exact msgC_adrs a

theorem e0C_keys : ∀ x, x ∈ e0C.dyna.accessedStorageKeys ↔ x ∈ ([] : List (Adr × B256)) := by
  obtain ⟨benv, -, he⟩ := e0C_meta
  intro x
  show x ∈ e0C.dyna.accessedStorageKeys ↔ _
  rw [he]
  show x ∈ msgC.accessedStorageKeys ↔ _
  rw [msgC_keys_empty]
  simp only [Std.HashSet.ofList_nil, Std.HashSet.not_mem_empty, List.not_mem_nil]

theorem e0C_stor : ∀ a k, storOf e0C.dyna.state a k = storOf worldTx a k := by
  obtain ⟨benv, hb, he⟩ := e0C_meta
  have hbB : benvAfterTransferB msgC = .ok benv := by
    rw [benvAfterTransfer_eq_S acctAgree_worldTx]; exact hb
  intro a k
  show storOf e0C.dyna.state a k = _
  rw [he]
  show storOf benv.state a k = _
  rw [benvAfterTransferB_stor hbB]
  rfl

/-- The account shadow after the (zero) value transfer of the top-level message. -/
def acsC1 : AcctShadow := acsTransfer msgC acsTx0

theorem acctAgree_acsC1 : AcctAgree e0C.dyna.state acsC1 := by
  obtain ⟨benv, hb, he⟩ := e0C_meta
  show AcctAgree e0C.dyna.state _
  rw [he]
  exact acctAgree_transfer acctAgree_worldTx hb

/-! ### The certificate run, to the intended `CALL` -/

/-- The start configuration: no accessed storage keys, the accessed addresses
`prepareMessage` warmed. -/
def c0C : Cfg :=
  ⟨e0C.dyna, Attacker2.t_0000_c0, [], [], warmC,
    storShadowOf poolWritesTx, acsC1⟩

theorem c0C_agree : Agree c0C :=
  ⟨e0C_keys, e0C_adrs,
    fun a k => (e0C_stor a k).trans (storOf_stateFoldStor poolWritesTx storOf_worldTx_base a k),
    acctAgree_acsC1⟩

/-- The certificate run over `A'`'s own bytes, from the real transaction-shaped entry, for
33 nodes: 8 to decide the dispatcher (`CALLDATALOAD(0) >> 224 == 0x12345678`, true, since
`msgC.data = START`) and land at `t_0064_c0` (the "start" branch, unconsumed), 1 more for
`t_0064_c0`'s own `.dest` wrapper (the `JUMPDEST` it is a jump target for), then 24 more
(the same count the message-level witness's old attacker needed for its structurally
identical body) to reach the `CALL`. -/
def callCfgC : Cfg :=
  match wrun fs2 e0C.sta 33 c0C with | .cont c => c | _ => c0C

theorem callCfgC_eq : wrun fs2 e0C.sta 33 c0C = .cont callCfgC := by kernel_rfl

theorem callCfgC_agree : Agree callCfgC := (wrun_cont callCfgC_eq).1 c0C_agree

/-- `A'`'s `CALL` up to its spawn: the generic `callPrep`, not any V--specific lemma. -/
def cp0C : CallPrep := (callPrep e0C.sta callCfgC).getD noPrep

theorem cp0C_eq : callPrep e0C.sta callCfgC = some cp0C := by kernel_rfl

theorem cp0C_spec :
    Xinst.step e0C.sta callCfgC.devm .call = .spawn cp0C.f (.call cp0C.p cp0C.oi cp0C.os) ∧
      (∀ a, a ∈ cp0C.p.accessedAddresses ↔ a ∈ cp0C.adrs) ∧
      cp0C.p.accessedStorageKeys = callCfgC.devm.accessedStorageKeys ∧
      cp0C.f.isCreate = false ∧ cp0C.f.inner.accessedAddresses = cp0C.p.accessedAddresses ∧
      cp0C.f.inner.accessedStorageKeys = cp0C.p.accessedStorageKeys ∧
      cp0C.f.inner.benv.stat.rules.stateGas = none ∧ cp0C.f.inner.benv.state = callCfgC.devm.state :=
  callPrep_spec cp0C_eq callCfgC_agree.2.1 callCfgC_agree.2.2.2

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC
