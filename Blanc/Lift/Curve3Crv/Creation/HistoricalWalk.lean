import Blanc.Lift.Curve3Crv.Creation.Deploy
import Blanc.Lift.CreateSettlementMeta

/-!
# The 3Crv constructor under Muir Glacier

The constructor walk (`Creation/Walk.lean`) is stated once, over the actual-rule `SSTORE`
successors and charges. Under Muir Glacier (flat access, EIP-2200 net metering), in a freshly
created account with empty storage:

* `ctorCost_muir`: the constructor costs exactly 125,151 gas: six fresh nonzero sets at 20,000
  (the two `name` words, the two `symbol` words, `decimals`, `minter`), two zero writes at 800
  (`balanceOf[caller]`, `total_supply`), and 3,551 for everything else;
* `ctor_run_muir`: from `G + 125151` gas the constructor halts with `G` left, returning the
  runtime window, leaving the storage `deployedStor deployer`, the refund counter, deletion set
  and created set unchanged, and appending the one event `Transfer(0, deployer, 0)`.

The slot distinctness facts the costs and refunds need are kernel-evaluated hashes.
-/

namespace Blanc.Lift.Curve3Crv.Creation

open Jaune Blanc.Lift Blanc.Lift.Curve3Crv

/-! ## Bookkeeping through the walk -/

theorem loopWorld_createdAccounts {sevm : Sevm} {b : Devm} {M : Mem} {sl : UInt8} {src : Nat} :
    ∀ i, (loopWorld sevm b M sl src i).createdAccounts = b.createdAccounts
  | 0 => rfl
  | i + 1 => by rw [loopWorld, afterSstoreH_createdAccounts, loopWorld_createdAccounts i]

theorem loopWorld_getStor_succ {sevm : Sevm} {b : Devm} {M : Mem} {sl : UInt8} {src : Nat}
    (i : Nat) :
    Devm.getStor (loopWorld sevm b M sl src (i + 1)) sevm.currentTarget =
      (Devm.getStor (loopWorld sevm b M sl src i) sevm.currentTarget).set
        (strBase sl + Nat.toB256 i) (loopWord M sl src i) :=
  afterSstoreH_getStor_self _ _ _ _

/-! ## The storage after each store -/

/-- The storage after the `name` length word. -/
def stor1 : Stor := Stor.empty.set vyNameBase (Nat.toB256 22)
/-- The storage after the `name` data word. -/
def stor2 : Stor := stor1.set (vyNameBase + Nat.toB256 1) (curveStrWord curveShapedName)
/-- The storage after the `symbol` length word. -/
def stor3 : Stor := stor2.set vySymbolBase (Nat.toB256 4)

section
variable {sevm : Sevm} {b : Devm} (hempty : Devm.getStor b sevm.currentTarget = Stor.empty)
include hempty

theorem stor_w1 : Devm.getStor (loopWorld sevm b mB4 0x00 0x1c0 1) sevm.currentTarget = stor1 := by
  rw [loopWorld_getStor_succ, loopWord_name0, strBase0]
  show (Devm.getStor b sevm.currentTarget).set (vyNameBase + 0) _ = _
  rw [B256.add_zero, hempty]; rfl

theorem stor_w2 : Devm.getStor (worldName sevm b) sevm.currentTarget = stor2 := by
  rw [worldName, loopWorld_getStor_succ, stor_w1 hempty, loopWord_name1, strBase0]; rfl

theorem stor_w3 :
    Devm.getStor (loopWorld sevm (worldName sevm b) memName 0x01 0x240 1) sevm.currentTarget =
      stor3 := by
  rw [loopWorld_getStor_succ, loopWord_symbol0, strBase1]
  show (Devm.getStor (worldName sevm b) sevm.currentTarget).set (vySymbolBase + 0) _ = _
  rw [B256.add_zero, stor_w2 hempty]; rfl

theorem stor_w4 : Devm.getStor (worldSymbol sevm b) sevm.currentTarget = stringsStor := by
  rw [worldSymbol, loopWorld_getStor_succ, stor_w3 hempty, loopWord_symbol1, strBase1]; rfl

end

/-! ## The slot facts (kernel-evaluated hashes) -/

theorem cur1 : stor1.get (vyNameBase + Nat.toB256 1) = 0 := by decide +kernel
theorem cur2 : stor2.get vySymbolBase = 0 := by decide +kernel
theorem cur3 : stor3.get (vySymbolBase + Nat.toB256 1) = 0 := by decide +kernel
theorem cur4 : stringsStor.get 2 = 0 := by decide +kernel
theorem cur6 : (stringsStor.set 2 18).get 6 = 0 := by decide +kernel
theorem cur5 : (stringsStor.set 2 18).get 5 = 0 := by decide +kernel

theorem nameData_ne : curveStrWord curveShapedName ≠ 0 := by decide +kernel
theorem symbolData_ne : curveStrWord curveShapedSymbol ≠ 0 := by decide +kernel
theorem deployer_ne : deployer.toB256 ≠ 0 := by decide +kernel

/-! ## The current value at each store -/

section
variable {sevm : Sevm} {b : Devm} (hempty : Devm.getStor b sevm.currentTarget = Stor.empty)
include hempty

theorem z0 : (Devm.getStor (loopWorld sevm b mB4 0x00 0x1c0 0) sevm.currentTarget).get
    (strBase 0x00 + Nat.toB256 0) = 0 := by
  show (Devm.getStor b sevm.currentTarget).get _ = 0
  rw [hempty]; rfl

theorem z1 : (Devm.getStor (loopWorld sevm b mB4 0x00 0x1c0 1) sevm.currentTarget).get
    (strBase 0x00 + Nat.toB256 1) = 0 := by
  rw [stor_w1 hempty, strBase0]; exact cur1

theorem z2 : (Devm.getStor (loopWorld sevm (worldName sevm b) memName 0x01 0x240 0)
    sevm.currentTarget).get (strBase 0x01 + Nat.toB256 0) = 0 := by
  show (Devm.getStor (worldName sevm b) sevm.currentTarget).get _ = 0
  rw [stor_w2 hempty, strBase1, show (Nat.toB256 0 : B256) = 0 from rfl, B256.add_zero]
  exact cur2

theorem z3 : (Devm.getStor (loopWorld sevm (worldName sevm b) memName 0x01 0x240 1)
    sevm.currentTarget).get (strBase 0x01 + Nat.toB256 1) = 0 := by
  rw [stor_w3 hempty, strBase1]; exact cur3

theorem z4 : (Devm.getStor (worldSymbol sevm b) sevm.currentTarget).get 2 = 0 := by
  rw [stor_w4 hempty]; exact cur4

theorem stor_tw4 : Devm.getStor (tw4 sevm (worldSymbol sevm b)) sevm.currentTarget =
    stringsStor.set 2 18 := by
  rw [tw4, afterSstoreH_getStor_self, stor_w4 hempty]

theorem z5 (hbal : balSlotOf sevm.caller.toB256 ∉ vyFixedSlots) :
    (Devm.getStor (tw4 sevm (worldSymbol sevm b)) sevm.currentTarget).get
      (balSlotOf sevm.caller.toB256) = 0 := by
  have h5 : (5 : B256) ≠ balSlotOf sevm.caller.toB256 := fun h =>
    hbal (h ▸ by simp only [vyFixedSlots, vySupplySlot, List.mem_cons, true_or, or_true])
  have hcore : coreStor.get (balSlotOf sevm.caller.toB256) = 0 := by
    by_contra h
    exact hbal (coreStor_support _ h)
  rw [stor_tw4 hempty, ← hcore, coreStor, Stor.get_set_ite (stringsStor.set 2 18) 5 0, ite_eq_right h5]

theorem z6 : (Devm.getStor (tw5 sevm (worldSymbol sevm b)) sevm.currentTarget).get 5 = 0 := by
  rw [tw5, afterSstoreH_getStor_self, stor_tw4 hempty, Stor.get_set_ite]
  split
  · rfl
  · exact cur5

theorem z7 : (Devm.getStor (tw6 sevm (worldSymbol sevm b)) sevm.currentTarget).get 6 = 0 := by
  rw [tw6, afterSstoreH_getStor_self, tw5, afterSstoreH_getStor_self, stor_tw4 hempty,
    Stor.get_set_ite, Stor.get_set_ite, ite_eq_right (by decide)]
  split
  · rfl
  · exact cur6

end

/-! ## The exact Muir cost -/

/-- **The constructor's exact Muir Glacier cost**: 125,151 gas from a created account with
empty storage, whatever the (nonzero) caller. -/
theorem ctorCost_muir {sevm : Sevm} (hmuir : sevm.benvStat.rules = muirGlacierRules) {b : Devm}
    (hcreated : sevm.currentTarget ∈ b.createdAccounts)
    (hempty : Devm.getStor b sevm.currentTarget = Stor.empty)
    (hcaller : sevm.caller.toB256 ≠ 0) :
    ctorCost sevm b = 125151 := by
  have cw : ∀ i, sevm.currentTarget ∈ (loopWorld sevm b mB4 0x00 0x1c0 i).createdAccounts :=
    fun i => by rw [loopWorld_createdAccounts]; exact hcreated
  have cs : ∀ i, sevm.currentTarget ∈
      (loopWorld sevm (worldName sevm b) memName 0x01 0x240 i).createdAccounts :=
    fun i => by rw [loopWorld_createdAccounts, worldName, loopWorld_createdAccounts]; exact hcreated
  have c4 : sevm.currentTarget ∈ (worldSymbol sevm b).createdAccounts := cs 2
  unfold ctorCost tailCost loopCost
  rw [sstoreCostH_muir_fresh_set hmuir (cw 0) (z0 hempty) (by rw [loopWord_name0]; decide),
    sstoreCostH_muir_fresh_set hmuir (cw 1) (z1 hempty) (by rw [loopWord_name1]; exact nameData_ne),
    sstoreCostH_muir_fresh_set hmuir (cs 0) (z2 hempty) (by rw [loopWord_symbol0]; decide),
    sstoreCostH_muir_fresh_set hmuir (cs 1) (z3 hempty)
      (by rw [loopWord_symbol1]; exact symbolData_ne),
    sstoreCostH_muir_fresh_set hmuir c4 (z4 hempty) (by decide),
    sstoreCostH_muir_created_zero (base := tw5 sevm (worldSymbol sevm b)) hmuir (by
      rw [tw5, afterSstoreH_createdAccounts, tw4, afterSstoreH_createdAccounts]; exact c4),
    sstoreCostH_muir_created_zero (base := tw4 sevm (worldSymbol sevm b)) hmuir (by
      rw [tw4, afterSstoreH_createdAccounts]; exact c4),
    sstoreCostH_muir_fresh_set (base := tw6 sevm (worldSymbol sevm b)) hmuir (by
      rw [tw6, afterSstoreH_createdAccounts, tw5, afterSstoreH_createdAccounts, tw4,
        afterSstoreH_createdAccounts]; exact c4) (z7 hempty) hcaller]

/-! ## The run, with its settlement metadata -/

/-- A fresh `SSTORE` (created account, current value zero) leaves the refund counter. -/
private theorem refund_fresh {sevm : Sevm} {b : Devm} {k v : B256}
    (hc : sevm.currentTarget ∈ b.createdAccounts)
    (hz : (Devm.getStor b sevm.currentTarget).get k = 0) :
    (afterSstoreH sevm b k v).refundCounter = b.refundCounter := by
  have horig : b.getOrigStorVal sevm sevm.currentTarget k = 0 := by
    unfold Devm.getOrigStorVal
    rw [ite_eq_left hc]
  rw [afterSstoreH_refundCounter, horig, show b.getStorVal sevm.currentTarget k = 0 from hz,
    sstoreRefundH_zero_zero]

theorem loopWorld_logs {sevm : Sevm} {b : Devm} {M : Mem} {sl : UInt8} {src : Nat} :
    ∀ i, (loopWorld sevm b M sl src i).logs = b.logs
  | 0 => rfl
  | i + 1 => by rw [loopWorld, afterSstoreH_logs, loopWorld_logs i]

theorem loopWorld_accountsToDelete {sevm : Sevm} {b : Devm} {M : Mem} {sl : UInt8} {src : Nat} :
    ∀ i, (loopWorld sevm b M sl src i).accountsToDelete = b.accountsToDelete
  | 0 => rfl
  | i + 1 => by rw [loopWorld, afterSstoreH_accountsToDelete, loopWorld_accountsToDelete i]

/-- The constructor's event: `Transfer(0, c, 0)` from `t`. -/
def transferLog (t : Adr) (c : B256) : Log := ⟨t, [transferTopic, 0, c], (0 : B256).toBytes⟩

/-- **The 3Crv constructor under Muir Glacier, gas-exact, with its settlement facts.** From a
created account with empty storage, the recorded deployer as caller and `G + 125151` gas, the
lifted constructor halts with `G` left, returning the runtime window, leaving
`deployedStor deployer`, the refund counter and deletion set unchanged, and appending the one
event `Transfer(0, deployer, 0)`. -/
theorem ctor_run_muir {sevm : Sevm} (hmuir : sevm.benvStat.rules = muirGlacierRules)
    (hstatic : sevm.isStatic = false) (hcode : sevm.code = code) (hvalue : sevm.value = 0)
    (hdata : sevm.data = []) (hcaller : sevm.caller = deployer) {b : Devm}
    (hcreated : sevm.currentTarget ∈ b.createdAccounts)
    (hempty : Devm.getStor b sevm.currentTarget = Stor.empty) {G : Nat} (hG : 2300 < G) :
    ∃ post, SProg.RunExact prog sevm (St b [] Mem.empty (G + 125151)) post ∧
      post.output = runtimeWindow ∧ post.error = b.error ∧
      Devm.getStor post sevm.currentTarget = deployedStor deployer.toB256 ∧
      post.gasLeft = G ∧ post.refundCounter = b.refundCounter ∧
      post.logs = b.logs ++ [transferLog sevm.currentTarget deployer.toB256] ∧
      post.accountsToDelete = b.accountsToDelete := by
  have hc0 : sevm.caller.toB256 ≠ 0 := by rw [hcaller]; exact deployer_ne
  have hbal : balSlotOf sevm.caller.toB256 ∉ vyFixedSlots := by
    rw [hcaller]; exact deployer_balSlot
  have fr : CtorFrame sevm := ⟨by rw [hmuir]; rfl, hstatic⟩
  have hrun := ctor_run fr hcode hvalue hdata (b := b) hG
  rw [ctorCost_muir hmuir hcreated hempty hc0] at hrun
  have cw : ∀ i, sevm.currentTarget ∈ (loopWorld sevm b mB4 0x00 0x1c0 i).createdAccounts :=
    fun i => by rw [loopWorld_createdAccounts]; exact hcreated
  have cs : ∀ i, sevm.currentTarget ∈
      (loopWorld sevm (worldName sevm b) memName 0x01 0x240 i).createdAccounts :=
    fun i => by rw [loopWorld_createdAccounts, worldName, loopWorld_createdAccounts]; exact hcreated
  have c4 : sevm.currentTarget ∈ (worldSymbol sevm b).createdAccounts := cs 2
  have c5 : sevm.currentTarget ∈ (tw4 sevm (worldSymbol sevm b)).createdAccounts := by
    rw [tw4, afterSstoreH_createdAccounts]; exact c4
  have c6 : sevm.currentTarget ∈ (tw5 sevm (worldSymbol sevm b)).createdAccounts := by
    rw [tw5, afterSstoreH_createdAccounts]; exact c5
  have c7 : sevm.currentTarget ∈ (tw6 sevm (worldSymbol sevm b)).createdAccounts := by
    rw [tw6, afterSstoreH_createdAccounts]; exact c6
  have hname : (worldName sevm b).refundCounter = b.refundCounter := by
    rw [worldName, loopWorld, refund_fresh (cw 1) (z1 hempty), loopWorld,
      refund_fresh (cw 0) (z0 hempty)]; rfl
  have hsym : (worldSymbol sevm b).refundCounter = b.refundCounter := by
    rw [worldSymbol, loopWorld, refund_fresh (cs 1) (z3 hempty), loopWorld,
      refund_fresh (cs 0) (z2 hempty)]; exact hname
  have hrefund : (tw7 sevm (worldSymbol sevm b)).refundCounter = b.refundCounter := by
    rw [tw7, refund_fresh c7 (z7 hempty), tw6, refund_fresh c6 (z6 hempty), tw5,
      refund_fresh c5 (z5 hempty hbal), tw4, refund_fresh c4 (z4 hempty)]; exact hsym
  have hlogs : (tw7 sevm (worldSymbol sevm b)).logs = b.logs := by
    rw [tw7, afterSstoreH_logs, tw6, afterSstoreH_logs, tw5, afterSstoreH_logs, tw4,
      afterSstoreH_logs, worldSymbol, loopWorld_logs, worldName, loopWorld_logs]
  have hdel : (tw7 sevm (worldSymbol sevm b)).accountsToDelete = b.accountsToDelete := by
    rw [tw7, afterSstoreH_accountsToDelete, tw6, afterSstoreH_accountsToDelete, tw5,
      afterSstoreH_accountsToDelete, tw4, afterSstoreH_accountsToDelete, worldSymbol,
      loopWorld_accountsToDelete, worldName, loopWorld_accountsToDelete]
  have hdata0 : ((tailMem2 memSymbol sevm.caller.toB256).read 0x2c0 32).1 = (0 : B256).toBytes :=
    Mem.read_write_word_of_wf ((memSymbol_wf.write _ _).write _ _) _ _
  obtain ⟨p1, p2, p3, p4⟩ := returnPost_facts (St (tw8 sevm (worldSymbol sevm b) memSymbol)
    [Nat.toB256 0, Nat.toB256 2276] (tailMem3 memSymbol sevm.caller.toB256) G) (Nat.toB256 0)
    (Nat.toB256 2276) []
  refine ⟨_, hrun, ?_, ?_, ?_, p4, ?_, ?_, ?_⟩
  · rw [p1, St.memory, toNat_toB256' (show 2276 < 2 ^ 256 by decide),
      toNat_toB256' (show 0 < 2 ^ 256 by decide)]
    exact tailMem3_read memSymbol_wf _
  · rw [p2, St_error]
    simp only [tw8, Devm.addLog_error, tw7, tw6, tw5, tw4, afterSstoreH_error, worldSymbol,
      loopWorld_error, worldName]
  · rw [p3, St_getStor, ctor_stor sevm b hempty, hcaller]
  · exact hrefund
  · show (tw7 sevm (worldSymbol sevm b)).logs ++ [_] = _
    rw [hlogs, hdata0, hcaller]; rfl
  · exact hdel

end Blanc.Lift.Curve3Crv.Creation
