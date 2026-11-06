import Blanc.Lift.SystemExecution.BeaconRoots.AmsterdamProbeExact
import Batteries.Tactic.OpenPrivate

/-!
# W1 probe: the EIP-4788 system path under Amsterdam

Probe only; does not land.
-/

namespace Blanc.Lift.SystemExecution.BeaconRoots.AmsterdamProbe

open Jaune
open ExecutionTrace
open Blanc.Lift
open Blanc.Lift.SystemExecution.BeaconRoots.AmsterdamProbeExact

/-- The rule facts Amsterdam gives. -/
theorem amsterdam_stateGas {s : BenvStat} (h : s.fork = .amsterdam) :
    s.rules.stateGas = some amsterdamStateGasRules := by
  show (Fork.ruleSet s.fork).stateGas = _
  rw [h]; rfl

theorem amsterdam_push0 {s : BenvStat} (h : s.fork = .amsterdam) :
    s.rules.op.push0 = true := by
  show (Fork.ruleSet s.fork).op.push0 = _
  rw [h]; rfl

/-- A storage charge is at most `storageSet`. -/
theorem sstoreChargeA_le (state : StateGasRules) (sevm : Sevm) (b : Devm) (k v : B256) :
    sstoreChargeA state sevm b k v ≤ state.storageSet := by
  unfold sstoreChargeA sstoreAmsterdamStateGas
  split <;> omega

/-- The rule-relative bound on one `SSTORE`'s execution gas. -/
theorem sstoreCostA_le (state : StateGasRules) (sevm : Sevm) (b : Devm) (k v : B256) :
    sstoreCostA state sevm b k v ≤ gasColdSload + state.storageWrite := by
  unfold sstoreCostA sstoreAmsterdamGasCost
  have : gasWarmAccess ≤ gasColdSload := by decide
  split <;> split <;> omega

section walk

variable (sevm : Sevm) (b : Devm)

abbrev A := amsterdamStateGasRules

/-- The timestamp slot. -/
def keyA : B256 := sevm.benvStat.time % (0x1fff : B256)
/-- The root slot. -/
def rootKeyA : B256 := (0x1fff : B256) + keyA sevm
/-- The frame after the timestamp store. -/
def midA : Devm := afterSstoreA A sevm b (keyA sevm) sevm.benvStat.time
/-- The frame after the root store. -/
def endA : Devm := afterSstoreA A sevm (midA sevm b) (rootKeyA sevm) (Sevm.dataWord sevm 0)
/-- The two execution-gas charges. -/
def c1A : Nat := sstoreCostA A sevm b (keyA sevm) sevm.benvStat.time
def c2A : Nat := sstoreCostA A sevm (midA sevm b) (rootKeyA sevm) (Sevm.dataWord sevm 0)

end walk

/-- The second store's meter side conditions follow from the first's. -/
theorem midA_meter {sevm : Sevm} {b : Devm} (hspill : b.stateGas.spilled = 0)
    (hres : 2 * A.storageSet ≤ b.stateGas.left) :
    (midA sevm b).stateGas.spilled = 0 ∧ A.storageSet ≤ (midA sevm b).stateGas.left := by
  have hc := sstoreChargeA_le A sevm b (keyA sevm) sevm.benvStat.time
  unfold midA
  rw [afterSstoreA_stateGas]
  refine ⟨hspill, ?_⟩
  show A.storageSet ≤ b.stateGas.left + _ - sstoreChargeA A sevm b (keyA sevm) sevm.benvStat.time
  omega

/-- The body: the analogue of `body_run` under Amsterdam, on any base with reservoir room. -/
theorem body_runA {fs : List SFunc} {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    (hfork : sevm.benvStat.fork = .amsterdam) (hstatic : sevm.isStatic = false)
    (hsent : gCallStipend < G) (hspill : b.stateGas.spilled = 0)
    (hres : 2 * A.storageSet ≤ b.stateGas.left) :
    SFunc.RunExact fs sevm
      (St b [] M (G + c2A sevm b + 3 + 3 + 3 + 3 + 2 + c1A sevm b + 3 + 2 + 5 + 2 + 3 + 1))
      t_004d_c0 (.halted (St (endA sevm b) [] M G)) := by
  have hsg := amsterdam_stateGas (s := sevm.benvStat) hfork
  have hmid := midA_meter (sevm := sevm) hspill hres
  dsimp only [t_004d_c0]
  refine rx_dest ?_
  refine rx_push (S := []) (x := 0x00) (xs := [0x1f, 0xff]) (w := (0x1fff : B256))
    (by decide +kernel) (by decide) ?_
  refine Blanc.Lift.rx_timestamp (S := [(0x1fff : B256)]) (by decide) ?_
  refine rx_mod (by rfl) (by rroom) ?_
  refine Blanc.Lift.rx_timestamp (S := [sevm.benvStat.time % (0x1fff : B256)])
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  rdup
  refine rx_sstoreA hsg ?_ hstatic hspill ?_ ?_
  · unfold c2A at *; show gCallStipend < _; unfold gCallStipend at *; omega
  · refine le_trans (sstoreChargeA_le A sevm b _ _) ?_
    omega
  refine rx_push0 (amsterdam_push0 hfork)
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_calldataload (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_swap1 ?_
  refine rx_push (x := 0x00) (xs := [0x1f, 0xff]) (w := (0x1fff : B256))
    (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_add (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_sstoreA hsg ?_ hstatic hmid.1 ?_ ?_
  · unfold gCallStipend at *; omega
  · refine le_trans (sstoreChargeA_le A sevm _ _ _) ?_
    exact le_trans hmid.2 (Nat.le_add_right _ _)
  exact Blanc.Lift.rx_stop

/-- The root: the analogue of `root_run` under Amsterdam. -/
theorem root_runA {fs : List SFunc} {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    (hfork : sevm.benvStat.fork = .amsterdam) (hstatic : sevm.isStatic = false)
    (hcaller : sevm.caller = systemAddress)
    (hsent : gCallStipend < G) (hspill : b.stateGas.spilled = 0)
    (hres : 2 * A.storageSet ≤ b.stateGas.left) :
    SFunc.RunExact fs sevm
      (St b [] M (G + c2A sevm b + 3 + 3 + 3 + 3 + 2 + c1A sevm b + 3 + 2 + 5 + 2 + 3 + 1
        + 10 + 3 + 3 + 3 + 2))
      t_0000_c0 (.halted (St (endA sevm b) [] M G)) := by
  have hbody := body_runA (fs := fs) (M := M) hfork hstatic hsent hspill hres
  dsimp only [t_0000_c0]
  refine rx_caller (S := []) (by decide) ?_
  refine rx_push (S := [sevm.caller.toB256]) (w := systemAddress.toB256) rfl
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_eq (S := []) (x := systemAddress.toB256) (y := sevm.caller.toB256) (v := 1)
    (by rw [hcaller]; simp only [B256.eqCheck, ite_true])
    (by simp only [List.length_nil]; decide) ?_
  refine rx_push rfl (by decide) ?_
  exact rx_branch_succ (by decide) hbody

/-- The Beacon runtime has no call-family instruction at any byte position. -/
theorem beacon_noExec : NoExecCode beaconRootsCode := by
  have hall : (List.range beaconRootsCode.size).all (fun pc =>
      match beaconRootsCode.getInst pc with
      | some (.next (.exec _)) => false
      | _ => true) = true := by decide +kernel
  intro pc x hat
  have hat' : beaconRootsCode.getInst pc = some (.next (.exec x)) := hat
  have hlt : pc < beaconRootsCode.size := by
    by_contra hge
    simp only [ByteArray.getInst, hge, dite_false, Option.some.injEq, reduceCtorEq] at hat'
  have := List.all_eq_true.mp hall pc (List.mem_range.mpr hlt)
  simp only [hat', Bool.false_eq_true] at this

/-- The gas left when the frame halts. -/
def postGasA (sevm : Sevm) (b : Devm) : Nat :=
  systemTransactionGas - (51 + c1A sevm b + c2A sevm b)

/-- The exact halted frame. -/
def postA (sevm : Sevm) (b : Devm) : Devm := St (endA sevm b) [] .empty (postGasA sevm b)

/-- **The raw system frame under Amsterdam**, from any base with the system gas and reservoir room:
the analogue of `system_exec`. -/
theorem system_execA {sevm : Sevm} {b : Devm}
    (hfork : sevm.benvStat.fork = .amsterdam) (hcode : sevm.code = beaconRootsCode)
    (hstatic : sevm.isStatic = false) (hcaller : sevm.caller = systemAddress)
    (hspill : b.stateGas.spilled = 0) (hres : 2 * A.storageSet ≤ b.stateGas.left) :
    exec ⟨0, sevm, St b [] .empty systemTransactionGas⟩ = .ok (postA sevm b) := by
  have hc1 := sstoreCostA_le A sevm b (keyA sevm) sevm.benvStat.time
  have hc2 := sstoreCostA_le A sevm (midA sevm b) (rootKeyA sevm) (Sevm.dataWord sevm 0)
  have hwrite : A.storageWrite = 10000 := rfl
  have hcold : gasColdSload = 2100 := rfl
  have hgas : systemTransactionGas = 30000000 := rfl
  have hstip : gCallStipend = 2300 := rfl
  have hc1' : c1A sevm b ≤ 12100 := by unfold c1A; omega
  have hc2' : c2A sevm b ≤ 12100 := by unfold c2A; omega
  have hsent : gCallStipend < postGasA sevm b := by unfold postGasA; omega
  have hrun := root_runA (fs := prog) (M := .empty) (G := postGasA sevm b) hfork hstatic hcaller
    hsent hspill hres
  have hG : postGasA sevm b + c2A sevm b + 3 + 3 + 3 + 3 + 2 + c1A sevm b + 3 + 2 + 5 + 2 + 3 + 1
      + 10 + 3 + 3 + 3 + 2 = systemTransactionGas := by unfold postGasA; omega
  rw [hG] at hrun
  have hexec : Nonempty (Exec 0 sevm (St b [] .empty systemTransactionGas) (.ok (postA sevm b))) :=
    lift_exact_lane cert_check jumps_ok hcode (hcode ▸ beacon_noExec) ⟨t_0000_c0, prog_root, hrun⟩
  exact (exec_iff_exec_eq _ _ _ _).mp hexec

/-- **`system_exec` under Amsterdam, on the message `systemMsg` as it stands.** The body of `systemMsg`
needs no restatement: `processSystemTransactionMsg` already reads the rules. -/
theorem system_exec_amsterdam {benv : Benv} (hfork : benv.stat.fork = .amsterdam) :
    exec (initEvm (systemMsg benv)) =
      .ok (postA (systemSevm benv) (systemBase benv)) := by
  have h := system_execA (sevm := systemSevm benv) (b := systemBase benv) hfork rfl rfl rfl
    rfl ?_
  · exact h
  · have hs : (benv.beginTransaction).stat.rules.stateGas = some amsterdamStateGasRules :=
      amsterdam_stateGas hfork
    show 2 * A.storageSet ≤ (match (benv.beginTransaction).stat.rules.stateGas with
      | none => 0
      | some state => state.systemReservoir)
    rw [hs]
    decide

end Blanc.Lift.SystemExecution.BeaconRoots.AmsterdamProbe

namespace Blanc.Lift.SystemExecution.BeaconRoots.AmsterdamProbe

open Jaune
open Blanc.Lift

open private preparedTopLevelMsg resolveTopLevelCallAmsterdam dispatchTopLevelAmsterdam
  finishTopLevelAmsterdam runPreparedTopFrame msgCallOutputAmsterdam from Jaune.Transaction

/-- The machine the top-level Amsterdam call prepares: two read records on `initDevm`. -/
def preparedBase (benv : Benv) : Devm :=
  let rules := (systemMsg benv).benv.stat.rules
  (((initDevm (systemMsg benv)).balReadAccount rules beaconRootsAddress).balReadAccount
    rules beaconRootsAddress)

theorem beacon_notDelegated : getDelegatedCodeAddress beaconRootsCode = none := by
  decide +kernel

theorem preparedTopLevelMsg_systemMsg (benv : Benv) : preparedTopLevelMsg (systemMsg benv)
      (Devm.balReadAccount (systemMsg benv).benv.stat.rules (systemMsg benv).currentTarget
        (Devm.balReadAccount (systemMsg benv).benv.stat.rules (systemMsg benv).currentTarget
          (initDevm (systemMsg benv)))) = systemMsg benv := by
  unfold preparedTopLevelMsg
  simp only [Devm.balReadAccount_accessedAddresses, Devm.balReadAccount_accessedStorageKeys,
    Devm.balReadAccount_createdAccounts, Devm.balReadAccount_transientStorage]
  rfl

theorem withCode_systemMsg (benv : Benv) :
    ({ systemMsg benv with code := beaconRootsCode } : Msg) = systemMsg benv := rfl

theorem delegationCost_systemMsg {benv : Benv} (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode beaconRootsAddress = beaconRootsCode) :
    (systemMsg benv).benv.stat.rules.delegationCost
      (Devm.balReadAccount (systemMsg benv).benv.stat.rules (systemMsg benv).currentTarget
        (initDevm (systemMsg benv))) (systemMsg benv).currentTarget =
      (false, (systemMsg benv).currentTarget, 0) := by
  have hdel := beacon_notDelegated
  have hen : (systemMsg benv).benv.stat.rules.delegationEnabled = true := by
    show (Fork.ruleSet (systemMsg benv).benv.stat.fork).delegationEnabled = true
    rw [show (systemMsg benv).benv.stat.fork = .amsterdam from hfork]
    rfl
  have hstate : ∀ a b : ForkRules, ∀ x y : Adr,
      (Devm.balReadAccount a x (initDevm (systemMsg benv))).state.getCode y = benv.state.getCode y :=
    fun _ _ _ _ => rfl
  simp only [ForkRules.delegationCost, hen, ↓reduceIte, GasSchedule.delegationCost]
  rw [hstate _ (systemMsg benv).benv.stat.rules]
  show (match getDelegatedCodeAddress (benv.state.getCode beaconRootsAddress) with
    | some delegated => _
    | none => _) = _
  rw [installed, hdel]

theorem prepare_systemMsg {benv : Benv} (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode beaconRootsAddress = beaconRootsCode) :
    prepareTopLevelAmsterdam A (systemMsg benv) = .ok (systemMsg benv, preparedBase benv) := by
  unfold prepareTopLevelAmsterdam finishTopLevelAmsterdam dispatchTopLevelAmsterdam
    resolveTopLevelCallAmsterdam
  have hauth : (systemMsg benv).tenv.stat.auths.isEmpty = true := rfl
  have htarget : (systemMsg benv).target.isNone = false := rfl
  have hvalue : ((systemMsg benv).value != 0) = false := by
    show ((0 : B256) != 0) = false
    simp only [bne_self_eq_false]
  have hcost := delegationCost_systemMsg hfork installed
  have hz : ∀ d : Devm, chargeGas 0 d = .ok d := fun d => by
    rw [chargeGas_eq_ok (Nat.zero_le _)]
    rfl
  simp only [hauth, ↓reduceIte]
  simp only [htarget, Bool.false_eq_true, ↓reduceIte]
  simp only [hvalue, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  simp only [bind, Except.bind]
  rw [hcost]
  simp only [hz, completeDelegationAccess, Bool.false_eq_true, ↓reduceIte]
  rw [preparedTopLevelMsg_systemMsg]
  show Except.ok ({ systemMsg benv with code := benv.state.getCode beaconRootsAddress },
    preparedBase benv) = _
  rw [installed, withCode_systemMsg]

end Blanc.Lift.SystemExecution.BeaconRoots.AmsterdamProbe
