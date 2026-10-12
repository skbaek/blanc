import Blanc.BeaconDepositSuccessPublic
import Blanc.MessageExecutionInversion

/-!
# Kernel refutation of the pre-re-pin P2 settled-success header (evidence)

Jaune `ca9f27d` prices `SSTORE` from the machine read `Devm.getOrigStorVal`,
which is zero for an owner in `createdAccounts`.  The registered header of
`deposit_success_settled_effects` still prices the terminal branch write with
the raw transaction-start snapshot (`insertionFirstLiveStoreCost`, inside
`depositRuntimeSuccessGas`) and promises the exact residual gas `G`.

This module states that header verbatim as `OldSettledEffects` and refutes it
with one concrete message: a created owner whose snapshot branch cell equals
its current nonzero branch cell.  The raw price is `2100 + 2900`, the machine
price `2100 + 100`; the actual run from the same message therefore settles
with `G + 2800`, not `G`.  The actual run is the unit's machine-priced chain
(`deposit_success_runCompiled` at `orig := base.getOrigStorVal …`).

Evidence only: nothing imports this module and it changes no claim.
-/

namespace Blanc.BeaconDeposit.RepinRefutation

open Jaune Blanc Blanc.BeaconDeposit
open Jaune.Ninst Blanc.Ninst

/-- The registered P2 header of `deposit_success_settled_effects`, verbatim
(binders turned into a proposition). -/
def OldSettledEffects : Prop :=
  ∀ {msg : Msg} {benv : Benv} {codeAddress : Adr}
    (sevm : Sevm) (base : Devm)
    (_hfork : CoveredFork sevm.benvStat.fork)
    (pubkey withdrawalCredentials signature : Bytes)
    (depositDataRoot : B256) (s' : Acc) (ev : DepositEvent)
    (stor : Stor) (keys : KeySet) (countCost n G : Nat)
    (_htransfer : msg.benvAfterTransfer = .ok benv)
    (_hcodeAddress : msg.codeAddress = some codeAddress)
    (_hnotPrecompile :
      decide (benv.stat.rules.isPrecomp codeAddress) = false)
    (_hsevm : sevm = initSevm (msg.withBenv benv))
    (_hbase : base = initDevm (msg.withBenv benv))
    (_hdataBound : sevm.data.length < 2 ^ 256)
    (_hdec : DepositAbiDecodable sevm.data pubkey withdrawalCredentials
      signature depositDataRoot)
    (_hOk : deposit Bytes.sha256
      (accOfStor (Devm.getStor base sevm.currentTarget))
      pubkey withdrawalCredentials signature depositDataRoot
      sevm.value.toNat = .ok (s', ev))
    (_hstor : Devm.getStor
      (afterSstore sevm (afterSload sevm base depositCountSlot)
        depositCountSlot
        (Nat.toB256
          (accOfStor (Devm.getStor base sevm.currentTarget)).count + 1))
      sevm.currentTarget = stor)
    (_hkeys :
      (afterSstore sevm (afterSload sevm base depositCountSlot)
        depositCountSlot
        (Nat.toB256
          (accOfStor
            (Devm.getStor base sevm.currentTarget)).count + 1)).accessedStorageKeys =
        keys)
    (_hcount : sstoreCost sevm
      (afterSload sevm base depositCountSlot) depositCountSlot
      (Nat.toB256
        (accOfStor (Devm.getStor base sevm.currentTarget)).count + 1) =
      countCost)
    (_hheight : n < 32)
    (_hfirst : FirstLive
      ((accOfStor (Devm.getStor base sevm.currentTarget)).count + 1) n)
    (_hselector : Sevm.selector sevm = depositSelector)
    (_hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (_hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (_hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (_hdepth : sevm.depth ≠ 0)
    (_hstatic : sevm.isStatic = false)
    (_hbranchSentry : gCallStipend < G + 2 +
      insertionFirstLiveStoreCost sevm stor keys 0 n depositDataRoot)
    (_hbound :
      (G + 46 +
          insertionFirstLiveStoreCost sevm stor keys 0 n depositDataRoot) +
        insertionDeadGas sevm.currentTarget stor n
          (insertionNatState 0
            ((accOfStor
              (Devm.getStor base sevm.currentTarget)).count + 1)
            depositDataRoot keys) < 2 ^ 256)
    (_hcountSentry : gCallStipend <
      ((G + 46 +
          insertionFirstLiveStoreCost sevm stor keys 0 n depositDataRoot) +
        insertionDeadGas sevm.currentTarget stor n
          (insertionNatState 0
            ((accOfStor
              (Devm.getStor base sevm.currentTarget)).count + 1)
            depositDataRoot keys)) + 14 + countCost)
    (_hreconstructBound :
      ((((G + 46 +
          insertionFirstLiveStoreCost sevm stor keys 0 n depositDataRoot) +
        insertionDeadGas sevm.currentTarget stor n
          (insertionNatState 0
            ((accOfStor
              (Devm.getStor base sevm.currentTarget)).count + 1)
            depositDataRoot keys)) + 38 + countCost) + 59) +
        1762 < 2 ^ 256)
    (_hcode : sevm.code.toList = code)
    (_hgasEntry : base.gasLeft =
      depositRuntimeSuccessGas sevm base stor keys depositDataRoot n
        ((accOfStor (Devm.getStor base sevm.currentTarget)).count + 1)
        countCost G),
    ∃ settled,
      processMessage msg = .ok settled ∧
      settled.stack = [] ∧
      settled.gasLeft = G ∧
      settled.logs = base.logs ++
        [depositEventLog sevm.currentTarget ev] ∧
      CanonicalDepositEventData ev
        (depositEventLog sevm.currentTarget ev).data ∧
      stor =
        (Devm.getStor base sevm.currentTarget).set depositCountSlot
          (Nat.toB256
            (accOfStor (Devm.getStor base sevm.currentTarget)).count + 1) ∧
      (∀ a, Devm.getStor settled a =
        if a = sevm.currentTarget then
          stor.set (branchSlot n)
            (accumulatedNode Bytes.sha256 (accOfStor stor).branch
              0 n depositDataRoot)
        else Devm.getStor base a) ∧
      (∀ a, settled.getCode a = base.getCode a) ∧
      settled.accessedAddresses = base.accessedAddresses ∧
      settled.output = base.output ∧
      settled.error = base.error ∧
      some sevm.code.toList = Prog.compile runtime

/-! ## The witness -/

def wPubkey : Bytes := List.replicate 48 0
def wCredentials : Bytes := List.replicate 32 0
def wSignature : Bytes := List.replicate 96 0
def wValue : B256 := Nat.toB256 oneEther

/-- The model's deposit-data root for the witness inputs.  It is never
evaluated: the proof only splits on whether it equals `1`. -/
def wNode : B256 :=
  depositDataNode Bytes.sha256 wPubkey wCredentials wSignature
    (le64 (oneEther / oneGwei))

/-- A nonzero branch word distinct from the deposited node. -/
def wCell : B256 := if wNode = 1 then 2 else 1

def wOwner : Adr := 0x1000
def wCaller : Adr := 0x1001

def wStor : Stor := Stor.empty.set (branchSlot 0) wCell

def wAcct : Acct := ⟨1, 0, wStor, ⟨⟨code⟩⟩⟩

def wState : State := State.set Std.TreeMap.empty wOwner wAcct

def wStat : BenvStat := { (default : BenvStat) with
  fork := .prague, origState := wState }

/-- The owner was created earlier in this transaction (for example a
storage-only original wiped by `CREATE`), so the machine original read of its
storage is zero while the snapshot keeps `wCell`. -/
def wBenv : Benv :=
  { state := wState
    createdAccounts := (Std.HashSet.emptyWithCapacity : AdrSet).insert wOwner
    stat := wStat }

def wMsg (gas : Nat) : Msg :=
  { benv := wBenv
    tenv := default
    caller := wCaller
    target := some wOwner
    currentTarget := wOwner
    gas := gas
    value := wValue
    data := abiDepositCall wPubkey wCredentials wSignature wNode
    codeAddress := some wOwner
    code := ⟨⟨code⟩⟩
    depth := 1
    shouldTransferValue := false
    isStatic := false
    accessedAddresses := (Std.HashSet.emptyWithCapacity : AdrSet).insert 2
    accessedStorageKeys := Std.HashSet.emptyWithCapacity
    disablePrecompiles := false }

/-- The entry machines `processMessage` builds for the witness. -/
abbrev wSevm (gas : Nat) : Sevm := initSevm ((wMsg gas).withBenv wBenv)
abbrev wBase (gas : Nat) : Devm := initDevm ((wMsg gas).withBenv wBenv)

/-! ## Elementary witness facts -/

theorem wCell_ne_node : wCell ≠ wNode := by
  unfold wCell
  split
  · rename_i h
    rw [h]
    decide
  · rename_i h
    exact fun h' => h h'.symm

theorem wCell_ne_zero : wCell ≠ 0 := by
  unfold wCell
  split <;> decide

theorem branchSlot_zero_ne_count : branchSlot 0 ≠ depositCountSlot := by
  decide +kernel

theorem wAcct_stor : wAcct.stor = wStor := by
  unfold wAcct
  dsimp only

theorem wState_get_owner : wState.get wOwner = wAcct :=
  State.get_set_self _ _ _

theorem wState_get_two : wState.get 2 = Acct.nil := by
  unfold wState
  rw [State.get_set_ne _ (by decide)]
  rfl

theorem wStor_count : wStor.get depositCountSlot = 0 := by
  unfold wStor
  rw [Stor.get_set_ne _ branchSlot_zero_ne_count]
  rfl

theorem wStor_branch : wStor.get (branchSlot 0) = wCell := by
  unfold wStor
  rw [Stor.get_set_self]

theorem wBase_getStor (gas : Nat) :
    Devm.getStor (wBase gas) wOwner = wStor := by
  change (wState.get wOwner).stor = wStor
  rw [wState_get_owner, wAcct_stor]

theorem wBase_created (gas : Nat) : wOwner ∈ (wBase gas).createdAccounts := by
  simp only [wBase, initDevm, Devm.createdAccounts, Msg.withBenv, wBenv]
  exact Std.HashSet.mem_insert_self

theorem wValue_toNat : wValue.toNat = oneEther :=
  B256.toNat_toB256_of_lt (by norm_num only [oneEther])

theorem accOfStor_wStor_count : (accOfStor wStor).count = 0 := by
  rw [accOfStor_count, wStor_count]
  rfl

theorem wDeposit_ok :
    deposit Bytes.sha256 (accOfStor wStor) wPubkey wCredentials wSignature
      wNode oneEther =
    .ok (⟨setSlot (accOfStor wStor).branch 0 wNode, 1⟩,
      ⟨wPubkey, wCredentials, le64 (oneEther / oneGwei), wSignature,
        le64 0⟩) := by
  have hp : wPubkey.length = 48 := List.length_replicate
  have hw : wCredentials.length = 32 := List.length_replicate
  have hs : wSignature.length = 96 := List.length_replicate
  unfold deposit
  rw [if_neg (by rw [hp]; decide), if_neg (by rw [hw]; decide),
    if_neg (by rw [hs]; decide),
    if_neg (by norm_num only [oneEther]),
    if_neg (by norm_num only [oneEther, oneGwei]),
    if_neg (by norm_num only [oneEther, oneGwei])]
  dsimp only
  rw [if_neg (by rw [wNode]; exact not_not.mpr rfl), accOfStor_wStor_count,
    if_neg (by norm_num only)]
  rfl

/-! ## Header premises of the witness -/

section premises

variable (gas : Nat)

theorem w_fork : CoveredFork (wSevm gas).benvStat.fork := by
  change CoveredFork Fork.prague
  exact CoveredFork.prague

theorem w_transfer : (wMsg gas).benvAfterTransfer = .ok wBenv := by
  unfold Msg.benvAfterTransfer
  rw [if_neg (by simp only [wMsg, Bool.false_eq_true, false_and,
    not_false_eq_true])]
  rfl

theorem w_codeAddress : (wMsg gas).codeAddress = some wOwner := rfl

theorem w_notPrecompile :
    decide (wBenv.stat.rules.isPrecomp wOwner) = false := by
  change decide ((Fork.ruleSet Fork.prague).isPrecomp wOwner) = false
  decide

theorem w_data : (wSevm gas).data =
    abiDepositCall wPubkey wCredentials wSignature wNode := rfl

theorem w_calldataLength :
    (abiDepositCall wPubkey wCredentials wSignature wNode).length = 420 := by
  rw [abiDepositCall_length]
  simp only [wPubkey, wCredentials, wSignature, List.length_replicate]
  decide

theorem w_dataBound : (wSevm gas).data.length < 2 ^ 256 := by
  rw [w_data, w_calldataLength]
  norm_num only

theorem w_dec : DepositAbiDecodable (wSevm gas).data wPubkey wCredentials
    wSignature wNode := by
  rw [w_data]
  exact canonicalDepositCalldata_decodable
    ⟨rfl, by rw [w_calldataLength]; norm_num only⟩

theorem w_selector : Sevm.selector (wSevm gas) = depositSelector := by
  apply selector_eq_of_data_eq_abiSelectorBytes_append
    (tail := (Nat.toB256 firstDepositTailOffset).toBytes ++
      (Nat.toB256 (secondDepositTailOffset wPubkey)).toBytes ++
      (Nat.toB256
        (thirdDepositTailOffset wPubkey wCredentials)).toBytes ++
      wNode.toBytes ++
      abiBytesTail wPubkey ++
      abiBytesTail wCredentials ++
      abiBytesTail wSignature)
  · rw [depositSelector_eq]
    decide +kernel
  · rw [w_data]
    simp only [abiDepositCall, List.append_assoc]

theorem w_code : (wSevm gas).code.toList = code := by
  change (⟨⟨code⟩⟩ : ByteArray).toList = code
  rw [ByteArray.toList_eq_toList_data]

theorem w_nodeleg : getDelegatedCodeAddress ((wBase gas).getCode 2) = none := by
  change getDelegatedCodeAddress (wState.get 2).code = none
  rw [wState_get_two]
  rfl

theorem w_warm : (2 : Adr) ∈ (wBase gas).accessedAddresses := by
  simp only [wBase, initDevm, Devm.accessedAddresses, Msg.withBenv, wMsg]
  exact Std.HashSet.mem_insert_self

theorem w_pre : decide ((wSevm gas).benvStat.rules.isPrecomp 2) = true := by
  change decide ((Fork.ruleSet Fork.prague).isPrecomp 2) = true
  decide

theorem w_depth : (wSevm gas).depth ≠ 0 := by
  change (1 : Nat) ≠ 0
  decide

theorem w_static : (wSevm gas).isStatic = false := rfl

theorem w_value : (wSevm gas).value.toNat = oneEther := wValue_toNat

theorem w_currentTarget : (wSevm gas).currentTarget = wOwner := rfl

theorem w_getStor : Devm.getStor (wBase gas) (wSevm gas).currentTarget = wStor :=
  wBase_getStor gas

end premises

/-! ## Selected storage, keys and prices -/

theorem mem_sloadAccessedStorageKeys {target : Adr} {keys : KeySet}
    {key : B256} {p : Adr × B256} :
    p ∈ sloadAccessedStorageKeys target keys key ↔
      (target, key) = p ∨ p ∈ keys := by
  unfold sloadAccessedStorageKeys
  split
  · rename_i h
    constructor
    · exact Or.inr
    · rintro (rfl | hp)
      · exact h
      · exact hp
  · simp only [Std.HashSet.mem_insert, beq_iff_eq]

section prices

variable (gas : Nat)

/-- The count-updated machine after the count `SLOAD`/`SSTORE`. -/
abbrev wCounted : Devm :=
  afterSstore (wSevm gas) (afterSload (wSevm gas) (wBase gas) depositCountSlot)
    depositCountSlot
    (Nat.toB256 (accOfStor (Devm.getStor (wBase gas)
      (wSevm gas).currentTarget)).count + 1)

theorem w_countWord :
    Nat.toB256 (accOfStor (Devm.getStor (wBase gas)
      (wSevm gas).currentTarget)).count + 1 = 1 := by
  rw [w_getStor, accOfStor_wStor_count]
  decide

theorem w_counted_getStor :
    Devm.getStor (wCounted gas) (wSevm gas).currentTarget =
      wStor.set depositCountSlot 1 := by
  rw [Blanc.afterSstore_getStor_self, Blanc.afterSload_getStor, w_getStor,
    accOfStor_wStor_count, show Nat.toB256 0 + 1 = (1 : B256) by decide]

theorem w_counted_branch :
    (Devm.getStor (wCounted gas) (wSevm gas).currentTarget).get
      (branchSlot 0) = wCell := by
  rw [w_counted_getStor, Stor.get_set_ne _ branchSlot_zero_ne_count.symm,
    wStor_branch]

theorem w_counted_branch_cold :
    ((wSevm gas).currentTarget, branchSlot 0) ∉
      (wCounted gas).accessedStorageKeys := by
  rw [Blanc.afterSstore_accessedStorageKeys, mem_sloadAccessedStorageKeys,
    Blanc.afterSload_accessedStorageKeys, mem_sloadAccessedStorageKeys]
  rintro (h | h | h)
  · exact branchSlot_zero_ne_count (congrArg Prod.snd h).symm
  · exact branchSlot_zero_ne_count (congrArg Prod.snd h).symm
  · exact (Std.HashSet.not_mem_emptyWithCapacity h)

theorem w_rawOrig :
    getOrigStorVal (wSevm gas) (wSevm gas).currentTarget (branchSlot 0) =
      wCell := by
  change (wState.get wOwner).stor.get (branchSlot 0) = wCell
  rw [wState_get_owner, wAcct_stor, wStor_branch]

theorem w_machineOrig :
    (wBase gas).getOrigStorVal (wSevm gas) (wSevm gas).currentTarget
      (branchSlot 0) = 0 := by
  unfold Devm.getOrigStorVal
  exact if_pos (wBase_created gas)

theorem w_rawCost :
    insertionFirstLiveStoreCost (wSevm gas)
      (Devm.getStor (wCounted gas) (wSevm gas).currentTarget)
      (wCounted gas).accessedStorageKeys 0 0 wNode = 5000 := by
  unfold insertionFirstLiveStoreCost
  simp only [Nat.add_zero, insertionNatKeys, accumulatedNode,
    w_counted_branch_cold gas, ↓reduceIte, w_rawOrig, w_counted_branch]
  unfold sstoreValueCost
  rw [if_pos ⟨rfl, wCell_ne_node⟩, if_neg wCell_ne_zero]
  rfl

theorem w_actualCost :
    insertionFirstLiveStoreCostOf
      ((wBase gas).getOrigStorVal (wSevm gas) (wSevm gas).currentTarget
        (branchSlot 0)) (wSevm gas)
      (Devm.getStor (wCounted gas) (wSevm gas).currentTarget)
      (wCounted gas).accessedStorageKeys 0 0 wNode = 2200 := by
  unfold insertionFirstLiveStoreCostOf
  simp only [Nat.add_zero, insertionNatKeys, accumulatedNode,
    w_counted_branch_cold gas, ↓reduceIte, w_machineOrig, w_counted_branch]
  unfold sstoreValueCost
  rw [if_neg (fun h => wCell_ne_zero h.1.symm)]
  rfl

theorem w_countCost :
    sstoreCost (wSevm gas) (afterSload (wSevm gas) (wBase gas) depositCountSlot)
      depositCountSlot
      (Nat.toB256 (accOfStor (Devm.getStor (wBase gas)
        (wSevm gas).currentTarget)).count + 1) = 20000 := by
  have hwarm : ((wSevm gas).currentTarget, depositCountSlot) ∈
      (afterSload (wSevm gas) (wBase gas) depositCountSlot).accessedStorageKeys := by
    rw [Blanc.afterSload_accessedStorageKeys, mem_sloadAccessedStorageKeys]
    exact Or.inl rfl
  have horig : (afterSload (wSevm gas) (wBase gas) depositCountSlot).getOrigStorVal
      (wSevm gas) (wSevm gas).currentTarget depositCountSlot = 0 := by
    unfold Devm.getOrigStorVal
    rw [Blanc.afterSload_createdAccounts]
    exact if_pos (wBase_created gas)
  have hcur : (afterSload (wSevm gas) (wBase gas) depositCountSlot).getStorVal
      (wSevm gas).currentTarget depositCountSlot = 0 := by
    change (Devm.getStor (afterSload (wSevm gas) (wBase gas) depositCountSlot)
      (wSevm gas).currentTarget).get depositCountSlot = 0
    rw [Blanc.afterSload_getStor, w_getStor, wStor_count]
  unfold sstoreCost
  rw [if_pos hwarm, horig, hcur, w_getStor, accOfStor_wStor_count,
    show Nat.toB256 0 + 1 = (1 : B256) by decide]
  unfold sstoreValueCost
  rw [if_pos ⟨rfl, by decide⟩, if_pos rfl]
  rfl

theorem w_sloadCost :
    sloadCost (wSevm gas) (wBase gas) depositCountSlot = 2100 := by
  have hcold : ((wSevm gas).currentTarget, depositCountSlot) ∉
      (wBase gas).accessedStorageKeys := by
    simp only [wBase, initDevm, Devm.accessedStorageKeys, Msg.withBenv, wMsg]
    exact Std.HashSet.not_mem_emptyWithCapacity
  unfold sloadCost
  rw [if_neg hcold]
  rfl

end prices

/-! ## The refutation -/

/-- Entry gas of the witness message: the raw-priced header budget for
residual `100000`, which is also the machine-priced budget for `102800`. -/
def wGas : Nat := 135649

theorem w_rawEntry :
    depositRuntimeSuccessGas (wSevm wGas) (wBase wGas)
      (Devm.getStor (wCounted wGas) (wSevm wGas).currentTarget)
      (wCounted wGas).accessedStorageKeys wNode 0
      ((accOfStor (Devm.getStor (wBase wGas)
        (wSevm wGas).currentTarget)).count + 1)
      20000 100000 = wGas := by
  unfold depositRuntimeSuccessGas depositEndpointSuccessGas
  rw [w_rawCost, w_sloadCost]
  simp only [insertionDeadGas, depositGuardsGas, depositRouteGas, wGas]

theorem w_actualEntry :
    depositRuntimeSuccessGasOf
      ((wBase wGas).getOrigStorVal (wSevm wGas) (wSevm wGas).currentTarget
        (branchSlot 0))
      (wSevm wGas) (wBase wGas)
      (Devm.getStor (wCounted wGas) (wSevm wGas).currentTarget)
      (wCounted wGas).accessedStorageKeys wNode 0
      ((accOfStor (Devm.getStor (wBase wGas)
        (wSevm wGas).currentTarget)).count + 1)
      20000 102800 = wGas := by
  unfold depositRuntimeSuccessGasOf depositEndpointSuccessGasOf
  rw [w_actualCost, w_sloadCost]
  simp only [insertionDeadGas, depositGuardsGas, depositRouteGas, wGas]

theorem w_firstLive :
    FirstLive ((accOfStor (Devm.getStor (wBase wGas)
      (wSevm wGas).currentTarget)).count + 1) 0 := by
  rw [w_getStor, accOfStor_wStor_count]
  exact ⟨by norm_num only, fun j hj => absurd hj (Nat.not_lt_zero j)⟩

theorem w_ok :
    deposit Bytes.sha256
      (accOfStor (Devm.getStor (wBase wGas) (wSevm wGas).currentTarget))
      wPubkey wCredentials wSignature wNode (wSevm wGas).value.toNat =
    .ok (⟨setSlot (accOfStor wStor).branch 0 wNode, 1⟩,
      ⟨wPubkey, wCredentials, le64 (oneEther / oneGwei), wSignature,
        le64 0⟩) := by
  rw [w_getStor, w_value]
  exact wDeposit_ok

/-- **The registered P2 settled-success header is false under Jaune
`ca9f27d`.**  Every premise holds for the witness message, yet the actual
settlement leaves `102800` gas where the header promises `100000`. -/
theorem not_oldSettledEffects : ¬ OldSettledEffects := by
  intro H
  obtain ⟨settled, hsettled, -, hsettledGas, -⟩ :=
    H (msg := wMsg wGas) (benv := wBenv) (codeAddress := wOwner)
      (wSevm wGas) (wBase wGas) (w_fork wGas)
      wPubkey wCredentials wSignature wNode _ _
      (Devm.getStor (wCounted wGas) (wSevm wGas).currentTarget)
      (wCounted wGas).accessedStorageKeys 20000 0 100000
      (w_transfer wGas) (w_codeAddress wGas) w_notPrecompile rfl rfl
      (w_dataBound wGas) (w_dec wGas) w_ok rfl rfl (w_countCost wGas)
      (by norm_num only) w_firstLive (w_selector wGas) (w_nodeleg wGas)
      (w_warm wGas) (w_pre wGas) (w_depth wGas) (w_static wGas)
      (by rw [w_rawCost]; norm_num only [gCallStipend])
      (by rw [w_rawCost]; simp only [insertionDeadGas]; norm_num only)
      (by rw [w_rawCost]; simp only [insertionDeadGas]; norm_num only [gCallStipend])
      (by rw [w_rawCost]; simp only [insertionDeadGas]; norm_num only)
      (w_code wGas) (by rw [w_rawEntry]; rfl)
  obtain ⟨post, hrun, -, hpostGas, -, -, -, -, -, -, hpostError, hcompile⟩ :=
    deposit_success_runCompiled (hfork := w_fork wGas) (wSevm wGas) (wBase wGas)
      wPubkey wCredentials wSignature wNode _ _
      (Devm.getStor (wCounted wGas) (wSevm wGas).currentTarget)
      (wCounted wGas).accessedStorageKeys 20000 0 102800
      (w_dataBound wGas) (w_dec wGas) w_ok rfl rfl (w_countCost wGas)
      (by norm_num only) w_firstLive (w_selector wGas) (w_nodeleg wGas)
      (w_warm wGas) (w_pre wGas) (w_depth wGas) (w_static wGas)
      (by rw [w_actualCost]; norm_num only [gCallStipend])
      (by rw [w_actualCost]; simp only [insertionDeadGas]; norm_num only)
      (by rw [w_actualCost]; simp only [insertionDeadGas]; norm_num only [gCallStipend])
      (by rw [w_actualCost]; simp only [insertionDeadGas]; norm_num only)
      (w_code wGas) rfl
  rw [w_actualEntry] at hrun
  have hentry : (wBase wGas).setMach
      ⟨[], Mem.empty, wGas, (wBase wGas).stateGas⟩ = wBase wGas := rfl
  rw [hentry] at hrun
  have hexec : exec ⟨0, wSevm wGas, wBase wGas⟩ = .ok post :=
    Prog.exec_of_runCompiledTo (Prog.RunCompiledTo.of_runCompiled hrun)
      hcompile
  have hcodeEntry :
      executeCode.enter ((wMsg wGas).withBenv wBenv) =
        .inl (initEvm ((wMsg wGas).withBenv wBenv)) :=
    MessageExecution.executeCode_enter_of_codeAddress_not_precompile
      (wMsg wGas) wBenv wOwner (w_codeAddress wGas) w_notPrecompile
  have hprocess : processMessage (wMsg wGas) = .ok post :=
    MessageExecution.processMessage_clean_of_exec_afterTransfer_of_codeEntry
      (wMsg wGas) wBenv post (w_transfer wGas) hcodeEntry hexec
      (by rw [hpostError]; rfl)
  rw [hprocess] at hsettled
  cases hsettled
  rw [hpostGas] at hsettledGas
  exact absurd hsettledGas (by decide)

/-! ## The underfunded direction (P6 and P2 chronology)

`deposit_success_artifactInv` and `deposit_success_retainedStorageEffectTriples`
do not pin the residual gas, so the overfunded witness above leaves them true.
They fail in the opposite direction: a created owner whose snapshot cell is
nonzero while its current cell is zero.  The raw header price is then the
warm/dirty `100`, the machine price the clean-set `20000`, so the header's
entry budget is `19900` short at the terminal branch store.  The scalar gap is
kernel-checked here; the out-of-gas walk itself is not, because
`Func.RunCompiledTo` represents failure only at a terminal instruction and no
mid-walk `SSTORE` out-of-gas step exists in the library. -/
theorem underfunded_value_gap (raw node : B256) (hraw : raw ≠ 0)
    (hnode : node ≠ 0) :
    sstoreValueCost 0 0 node = sstoreValueCost raw 0 node + 19900 := by
  unfold sstoreValueCost
  rw [if_pos ⟨rfl, fun h => hnode h.symm⟩, if_pos rfl,
    if_neg (fun h => hraw h.1)]
  rfl

end Blanc.BeaconDeposit.RepinRefutation
