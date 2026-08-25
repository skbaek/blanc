import Blanc.LidoCircuitBreakerFreshRegistration

/-!
A fully instantiated admin-registration world for the Lido CircuitBreaker.

`Blanc/LidoCircuitBreakerFreshRegistration.lean` states the fresh-registration
chronology against an abstract message, abstract entry storage, abstract
original words, abstract SSTORE value costs and abstract accessed-key warmth.
Nothing there exhibits a single machine at which all of those premises hold at
once, so the chronology is certified in one direction only: *if* such a world
exists, the run happens.

This leaf closes that gap with one concrete closed world — concrete admin
caller, contract owner, target, new pauser, storage, warm/cold accessed key
set and gas — and discharges every premise of
`registerPauser_runCompiledTo_freshNonzero` at it.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune

/-! ## The concrete world -/

/-- The CircuitBreaker deployment: the contract account that owns the
Registry storage and carries the generated runtime. -/
def freshWorldOwner : Adr := Nat.toAdr 100

/-- The admin caller.  `officialParams.admin` as an address. -/
def freshWorldAdmin : Adr :=
  Nat.toAdr 0x3e40D73EB977Dc6a537aF587D48316feE66E9C8c

/-- The pausable target being registered. -/
def freshWorldTarget : B256 := 7

/-- The pauser the target is assigned to. -/
def freshWorldPauser : B256 := 9

/-- Block timestamp at the registering call. -/
def freshWorldTime : B256 := 10

/-- The configured heartbeat interval, read from `heartbeatIntervalSlot`. -/
def freshWorldInterval : B256 := 2592000

/-- The heartbeat expiry the registration installs: `time + interval`. -/
def freshWorldExpiry : B256 := 2592010

/-- The deployed account storage: an empty Registry carrying only the
configured heartbeat interval. -/
def freshWorldStor : Stor :=
  Stor.empty.set heartbeatIntervalSlot freshWorldInterval

/-- The installed generated runtime bytes. -/
def freshWorldCode : ByteArray :=
  ByteArray.mk (lidoCircuitBreakerCode officialParams).toArray

/-- World state: the CircuitBreaker account alone. -/
def freshWorldState : State :=
  State.set (.empty : State) freshWorldOwner
    { Acct.nil with
      stor := freshWorldStor
      code := freshWorldCode }

/-- The warm accessed-storage-key set at message entry: the assignment slot,
the array length slot, the fresh array entry slot, the target's index slot and
the new pauser's expiry slot.  The new pauser's count slot and the heartbeat
interval slot are deliberately absent — the chronology charges them cold. -/
def freshWorldKeys : Std.HashSet (Adr × B256) :=
  ((((Std.HashSet.emptyWithCapacity.insert
    (freshWorldOwner, assignmentSlot freshWorldTarget)).insert
    (freshWorldOwner, arrayLengthSlot)).insert
    (freshWorldOwner, arrayEntrySlot 1)).insert
    (freshWorldOwner, indexSlot freshWorldTarget)).insert
    (freshWorldOwner, expirySlot freshWorldPauser)

/-! ## Payload bounds and slot separation

Every slot this world touches is `slot region payload` for a region below `16`
and a payload below `2 ^ 252`, so `slot_ne_of_region_ne` separates any two of
them whose regions differ.  Those are the only separations the world needs. -/

private theorem freshWorld_payload_zero : (0 : B256).toNat < 2 ^ 252 := by
  change (0 : Nat) < 2 ^ 252
  norm_num

private theorem freshWorld_payload_one : (1 : B256).toNat < 2 ^ 252 := by
  change (1 : Nat) < 2 ^ 252
  norm_num

private theorem freshWorld_payload_target :
    freshWorldTarget.toNat < 2 ^ 252 := by
  unfold freshWorldTarget
  change (7 : Nat) < 2 ^ 252
  norm_num

private theorem freshWorld_payload_pauser :
    freshWorldPauser.toNat < 2 ^ 252 := by
  unfold freshWorldPauser
  change (9 : Nat) < 2 ^ 252
  norm_num

theorem freshWorld_targetValid : nonzeroCanonicalAddress freshWorldTarget := by
  constructor
  · decide
  · unfold canonicalAddress freshWorldTarget
    change (7 : Nat) < 2 ^ 160
    norm_num

theorem freshWorld_pauserValid : nonzeroCanonicalAddress freshWorldPauser := by
  constructor
  · decide
  · unfold canonicalAddress freshWorldPauser
    change (9 : Nat) < 2 ^ 160
    norm_num

private theorem freshWorld_payload_of_canonical {w : B256}
    (h : canonicalAddress w) : w.toNat < 2 ^ 252 := by
  unfold canonicalAddress at h
  exact lt_trans h (by norm_num)

/-- The configured-interval slot is separated from every registry slot by its
region alone. -/
private theorem freshWorld_interval_ne
    {region : Nat} {payload : B256}
    (hregion : region < 16) (hpayload : payload.toNat < 2 ^ 252)
    (hne : configRegion ≠ region) :
    heartbeatIntervalSlot ≠ slot region payload := by
  simpa only [heartbeatIntervalSlot] using
    slot_ne_of_region_ne (leftRegion := configRegion) (rightRegion := region)
      (left := (1 : B256)) (right := payload)
      (by norm_num [configRegion]) hregion freshWorld_payload_one hpayload hne

private theorem freshWorld_stor_get_zero {k : B256}
    (h : heartbeatIntervalSlot ≠ k) : freshWorldStor.get k = 0 := by
  rw [freshWorldStor, Stor.get_set_ne _ h]
  simp [Stor.get, Stor.empty]

private theorem freshWorld_stor_assignment {t : B256}
    (h : canonicalAddress t) : freshWorldStor.get (assignmentSlot t) = 0 :=
  freshWorld_stor_get_zero
    (freshWorld_interval_ne (by norm_num [assignmentRegion])
      (freshWorld_payload_of_canonical h)
      (by norm_num [configRegion, assignmentRegion]))

private theorem freshWorld_stor_index {t : B256}
    (h : canonicalAddress t) : freshWorldStor.get (indexSlot t) = 0 :=
  freshWorld_stor_get_zero
    (freshWorld_interval_ne (by norm_num [indexRegion])
      (freshWorld_payload_of_canonical h)
      (by norm_num [configRegion, indexRegion]))

private theorem freshWorld_stor_count {p : B256}
    (h : canonicalAddress p) : freshWorldStor.get (countSlot p) = 0 :=
  freshWorld_stor_get_zero
    (freshWorld_interval_ne (by norm_num [countRegion])
      (freshWorld_payload_of_canonical h)
      (by norm_num [configRegion, countRegion]))

private theorem freshWorld_stor_arrayLength :
    freshWorldStor.get arrayLengthSlot = 0 :=
  freshWorld_stor_get_zero
    (freshWorld_interval_ne (by norm_num [arrayRegion]) freshWorld_payload_zero
      (by norm_num [configRegion, arrayRegion]))

private theorem freshWorld_stor_arrayEntry {i : B256}
    (h : i.toNat < 2 ^ 252) : freshWorldStor.get (arrayEntrySlot i) = 0 :=
  freshWorld_stor_get_zero
    (freshWorld_interval_ne (by norm_num [arrayRegion]) h
      (by norm_num [configRegion, arrayRegion]))

private theorem freshWorld_stor_expiry {p : B256}
    (h : canonicalAddress p) : freshWorldStor.get (expirySlot p) = 0 :=
  freshWorld_stor_get_zero
    (freshWorld_interval_ne (by norm_num [expiryRegion])
      (freshWorld_payload_of_canonical h)
      (by norm_num [configRegion, expiryRegion]))

private theorem freshWorld_stor_interval :
    freshWorldStor.get heartbeatIntervalSlot = freshWorldInterval := by
  rw [freshWorldStor, Stor.get_set_self]

/-- The deployed storage carries an empty Registry: the configured heartbeat
interval sits in the config region, which no Registry projection reads. -/
theorem freshWorldStor_witness :
    RegistryWitness (logicalStorageOfStor freshWorldStor) [] := by
  refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro entry member; simp at member
  · intro entry member; simp at member
  · show freshWorldStor.get arrayLengthSlot = Nat.toB256 ([] : List Entry).length
    rw [freshWorld_stor_arrayLength]
    rfl
  · intro index bound; simp at bound
  · intro t canonical
    show freshWorldStor.get (assignmentSlot t) = assignmentAt [] t
    rw [freshWorld_stor_assignment canonical]
    rfl
  · intro t canonical
    show freshWorldStor.get (indexSlot t) = Nat.toB256 (oneBasedIndexAt [] t)
    rw [freshWorld_stor_index canonical]
    rfl
  · intro p canonical
    show freshWorldStor.get (countSlot p) = Nat.toB256 (assignmentCount [] p)
    rw [freshWorld_stor_count canonical]
    rfl
  · show freshWorldStor.get (countSlot 0) = 0
    exact freshWorld_stor_count (by
      unfold canonicalAddress
      change (0 : Nat) < 2 ^ 160
      norm_num)

/-! ## Gas

Every one of the five Registry writes lands on a slot whose original and
current words are `0` and whose new word is nonzero, so each carries
`gasStorageSet`.  Two of the three staged SLOADs are warm and the new pauser's
count slot is cold, so the body reserve is a closed term in the world's own
data — it never mentions the message whose `gas` field it fills. -/

private theorem freshWorld_setCost {new : B256} (h : new ≠ 0) :
    sstoreValueCost 0 0 new = gasStorageSet := by
  rw [sstoreValueCost, if_pos ⟨rfl, fun hc => h hc.symm⟩, if_pos rfl]

/-- The exact body reserve of the fresh registration at this world:
`221` decoder/admin prefix, `25756` kernel walk, `6` memory extension, two warm
staged SLOADs, one cold count SLOAD, and five `gasStorageSet` writes. -/
def freshWorldBodyGas : Nat := 128283

/-- The exact message gas: dispatch prefix plus body reserve, leaving `0`. -/
def freshWorldGas : Nat := 128458

private theorem freshWorldGas_split :
    freshWorldGas = registerPauserDispatchGas + freshWorldBodyGas := by
  norm_num [freshWorldGas, freshWorldBodyGas, registerPauserDispatchGas]

/-- The staged registration image extends memory by one word beyond the
scratch frame: six gas. -/
private theorem freshWorld_memoryCost :
    arrayLengthMemoryCost (registerMemory freshWorldTarget freshWorldPauser) =
      6 := by
  decide

/-! ## The message -/

/-- The concrete admin `registerPauser(7, 9)` call. -/
def freshWorldMsg : Msg :=
  { (default : Msg) with
    benv :=
      { (default : Benv) with
        state := freshWorldState
        stat :=
          { (default : BenvStat) with
            origState := freshWorldState
            time := freshWorldTime } }
    tenv := default
    caller := freshWorldAdmin
    target := some freshWorldOwner
    currentTarget := freshWorldOwner
    gas := freshWorldGas
    value := 0
    data := registerPauserCalldata freshWorldTarget freshWorldPauser
    codeAddress := some freshWorldOwner
    code := freshWorldCode
    depth := 0
    shouldTransferValue := false
    isStatic := false
    accessedAddresses := .emptyWithCapacity
    accessedStorageKeys := freshWorldKeys
    disablePrecompiles := false }

def freshWorldSevm : Sevm := initSevm freshWorldMsg

def freshWorldPre : Devm := initDevm freshWorldMsg

/-! ## Frame-shape facts

Everything the chronology asks about the message frame itself. -/

private theorem byteArray_ofList_toList (bs : Bytes) :
    (ByteArray.mk bs.toArray).toList = bs := by
  rw [ByteArray.toList_eq_toList_data]

theorem freshWorld_currentTarget :
    freshWorldSevm.currentTarget = freshWorldOwner := rfl

theorem freshWorld_value : freshWorldSevm.value = 0 := rfl

theorem freshWorld_static : freshWorldSevm.isStatic = false := rfl

theorem freshWorld_codeAddress :
    freshWorldSevm.codeAddress = some freshWorldSevm.currentTarget := rfl

theorem freshWorld_time : freshWorldSevm.benvStat.time = freshWorldTime := rfl

theorem freshWorld_admin :
    freshWorldSevm.caller.toB256 = officialParams.admin := rfl

theorem freshWorld_codeBytes :
    freshWorldSevm.code.toList = lidoCircuitBreakerCode officialParams := by
  simpa only [freshWorldSevm, freshWorldMsg, initSevm, freshWorldCode] using
    byteArray_ofList_toList (lidoCircuitBreakerCode officialParams)

/-- The message frame really enters the code frame this world is about: the
CircuitBreaker address is not a precompile, and the call transfers no value. -/
theorem freshWorld_frameEntry :
    (Frame.ofCall freshWorldMsg).enter =
      .run ⟨0, freshWorldSevm, freshWorldPre⟩ := rfl

theorem freshWorld_data :
    freshWorldSevm.data =
      registerPauserCalldata freshWorldTarget freshWorldPauser := rfl

theorem freshWorld_find : findEntry ([] : List Entry) freshWorldTarget = none :=
  rfl

private theorem freshWorld_one : Nat.toB256 1 = (1 : B256) := by decide

private theorem freshWorld_zero : Nat.toB256 0 = (0 : B256) := by decide

/-! ## Storage facts -/

theorem freshWorld_getStor :
    Devm.getStor freshWorldPre freshWorldOwner = freshWorldStor := by
  change (freshWorldState.get freshWorldOwner).stor = freshWorldStor
  rw [freshWorldState, State.get_set_self]

theorem freshWorld_getOrigStor {key : B256} :
    getOrigStorVal freshWorldSevm freshWorldOwner key =
      freshWorldStor.get key := by
  change (freshWorldState.get freshWorldOwner).stor.get key = _
  rw [freshWorldState, State.get_set_self]

theorem freshWorld_preWitness :
    RegistryWitness
      (logicalStorageOfStor (Devm.getStor freshWorldPre freshWorldOwner))
      [] := by
  rw [freshWorld_getStor]
  exact freshWorldStor_witness

/-! ## Accessed storage keys

Five keys are warm at entry and two are cold.  Membership is settled by the
`insert` chain alone; non-membership is settled by region separation, never by
deciding a `HashSet`. -/

theorem freshWorld_accessed :
    freshWorldPre.accessedStorageKeys = freshWorldKeys := rfl

theorem freshWorld_warmAssignment :
    (freshWorldOwner, assignmentSlot freshWorldTarget) ∈ freshWorldKeys := by
  rw [freshWorldKeys]
  exact Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
    (Or.inr (Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
      (Or.inr Std.HashSet.mem_insert_self)))))))

theorem freshWorld_warmArrayLength :
    (freshWorldOwner, arrayLengthSlot) ∈ freshWorldKeys := by
  rw [freshWorldKeys]
  exact Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
    (Or.inr (Std.HashSet.mem_insert.mpr
      (Or.inr Std.HashSet.mem_insert_self)))))

theorem freshWorld_warmArrayEntry :
    (freshWorldOwner, arrayEntrySlot 1) ∈ freshWorldKeys := by
  rw [freshWorldKeys]
  exact Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
    (Or.inr Std.HashSet.mem_insert_self)))

theorem freshWorld_warmIndex :
    (freshWorldOwner, indexSlot freshWorldTarget) ∈ freshWorldKeys := by
  rw [freshWorldKeys]
  exact Std.HashSet.mem_insert.mpr (Or.inr Std.HashSet.mem_insert_self)

theorem freshWorld_warmExpiry :
    (freshWorldOwner, expirySlot freshWorldPauser) ∈ freshWorldKeys :=
  Std.HashSet.mem_insert_self

theorem freshWorld_coldInterval :
    (freshWorldOwner, heartbeatIntervalSlot) ∉ freshWorldKeys := by
  rw [freshWorldKeys]
  simp only [Std.HashSet.mem_insert, Std.HashSet.not_mem_emptyWithCapacity,
    or_false, not_or, beq_iff_eq, Prod.mk.injEq, not_and]
  refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
  · show slot expiryRegion freshWorldPauser ≠ slot configRegion 1
    exact slot_ne_of_region_ne (by norm_num [expiryRegion])
      (by norm_num [configRegion]) freshWorld_payload_pauser
      freshWorld_payload_one (by norm_num [expiryRegion, configRegion])
  · show slot indexRegion freshWorldTarget ≠ slot configRegion 1
    exact slot_ne_of_region_ne (by norm_num [indexRegion])
      (by norm_num [configRegion]) freshWorld_payload_target
      freshWorld_payload_one (by norm_num [indexRegion, configRegion])
  · show slot arrayRegion 1 ≠ slot configRegion 1
    exact slot_ne_of_region_ne (by norm_num [arrayRegion])
      (by norm_num [configRegion]) freshWorld_payload_one
      freshWorld_payload_one (by norm_num [arrayRegion, configRegion])
  · show slot arrayRegion 0 ≠ slot configRegion 1
    exact slot_ne_of_region_ne (by norm_num [arrayRegion])
      (by norm_num [configRegion]) freshWorld_payload_zero
      freshWorld_payload_one (by norm_num [arrayRegion, configRegion])
  · show slot assignmentRegion freshWorldTarget ≠ slot configRegion 1
    exact slot_ne_of_region_ne (by norm_num [assignmentRegion])
      (by norm_num [configRegion]) freshWorld_payload_target
      freshWorld_payload_one (by norm_num [assignmentRegion, configRegion])

theorem freshWorld_coldCount :
    (freshWorldOwner, countSlot freshWorldPauser) ∉ freshWorldKeys := by
  rw [freshWorldKeys]
  simp only [Std.HashSet.mem_insert, Std.HashSet.not_mem_emptyWithCapacity,
    or_false, not_or, beq_iff_eq, Prod.mk.injEq, not_and]
  refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
  · show slot expiryRegion freshWorldPauser ≠ slot countRegion freshWorldPauser
    exact slot_ne_of_region_ne (by norm_num [expiryRegion])
      (by norm_num [countRegion]) freshWorld_payload_pauser
      freshWorld_payload_pauser (by norm_num [expiryRegion, countRegion])
  · show slot indexRegion freshWorldTarget ≠ slot countRegion freshWorldPauser
    exact slot_ne_of_region_ne (by norm_num [indexRegion])
      (by norm_num [countRegion]) freshWorld_payload_target
      freshWorld_payload_pauser (by norm_num [indexRegion, countRegion])
  · show slot arrayRegion 1 ≠ slot countRegion freshWorldPauser
    exact slot_ne_of_region_ne (by norm_num [arrayRegion])
      (by norm_num [countRegion]) freshWorld_payload_one
      freshWorld_payload_pauser (by norm_num [arrayRegion, countRegion])
  · show slot arrayRegion 0 ≠ slot countRegion freshWorldPauser
    exact slot_ne_of_region_ne (by norm_num [arrayRegion])
      (by norm_num [countRegion]) freshWorld_payload_zero
      freshWorld_payload_pauser (by norm_num [arrayRegion, countRegion])
  · show slot assignmentRegion freshWorldTarget ≠
      slot countRegion freshWorldPauser
    exact slot_ne_of_region_ne (by norm_num [assignmentRegion])
      (by norm_num [countRegion]) freshWorld_payload_target
      freshWorld_payload_pauser (by norm_num [assignmentRegion, countRegion])

/-! ## The assignment-write boundary

The chronology phrases its array/index/count/interval/expiry premises at
`assignmentPost` — the state after the fresh path has read and replaced the
target's assignment word.  Because the assignment slot is already warm, that
state carries exactly the entry accessed-key set, and its storage differs from
the entry storage only at the assignment slot. -/

theorem freshWorld_assignmentBase :
    assignmentBase freshWorldSevm freshWorldPre freshWorldTarget =
      freshWorldPre := by
  rw [assignmentBase, temporalSloadBase]
  split
  · rfl
  · rename_i hcold
    exact absurd freshWorld_warmAssignment hcold

theorem freshWorld_assignmentPost_accessed :
    (assignmentPost freshWorldSevm freshWorldPre freshWorldTarget
      freshWorldPauser).accessedStorageKeys = freshWorldKeys := by
  rw [assignmentPost, temporalSstorePost_accessedStorageKeys,
    freshWorld_assignmentBase]
  rfl

theorem freshWorld_getStorVal {key : B256} :
    freshWorldPre.getStorVal freshWorldOwner key = freshWorldStor.get key := by
  change (freshWorldState.get freshWorldOwner).stor.get key = _
  rw [freshWorldState, State.get_set_self]

theorem freshWorld_assignmentPost_getStorVal {key : B256}
    (h : assignmentSlot freshWorldTarget ≠ key) :
    (assignmentPost freshWorldSevm freshWorldPre freshWorldTarget
      freshWorldPauser).getStorVal freshWorldOwner key =
      freshWorldStor.get key := by
  rw [assignmentPost,
    temporalSstorePost_other freshWorldSevm
      (assignmentBase freshWorldSevm freshWorldPre freshWorldTarget)
      (assignmentSlot freshWorldTarget) freshWorldPauser freshWorldOwner key
      (by
        intro hpair
        exact h (Prod.mk.injEq .. ▸ hpair).2.symm),
    freshWorld_assignmentBase, freshWorld_getStorVal]

private theorem freshWorld_assignment_ne_arrayEntry :
    assignmentSlot freshWorldTarget ≠ arrayEntrySlot 1 :=
  slot_ne_of_region_ne (leftRegion := assignmentRegion)
    (rightRegion := arrayRegion) (by norm_num [assignmentRegion])
    (by norm_num [arrayRegion]) freshWorld_payload_target
    freshWorld_payload_one (by norm_num [assignmentRegion, arrayRegion])

private theorem freshWorld_assignment_ne_interval :
    assignmentSlot freshWorldTarget ≠ heartbeatIntervalSlot :=
  slot_ne_of_region_ne (leftRegion := assignmentRegion)
    (rightRegion := configRegion) (by norm_num [assignmentRegion])
    (by norm_num [configRegion]) freshWorld_payload_target
    freshWorld_payload_one (by norm_num [assignmentRegion, configRegion])

private theorem freshWorld_assignment_ne_expiry :
    assignmentSlot freshWorldTarget ≠ expirySlot freshWorldPauser :=
  slot_ne_of_region_ne (leftRegion := assignmentRegion)
    (rightRegion := expiryRegion) (by norm_num [assignmentRegion])
    (by norm_num [expiryRegion]) freshWorld_payload_target
    freshWorld_payload_pauser (by norm_num [assignmentRegion, expiryRegion])

/-! ### Original words

Every slot the five writes touch was zero in the message-entry world state,
which is also the transaction's original state. -/

theorem freshWorld_origAssignment :
    getOrigStorVal freshWorldSevm freshWorldOwner
      (assignmentSlot freshWorldTarget) = 0 := by
  rw [freshWorld_getOrigStor]
  exact freshWorld_stor_assignment freshWorld_targetValid.2

theorem freshWorld_origArray :
    getOrigStorVal freshWorldSevm freshWorldOwner (arrayEntrySlot 1) = 0 := by
  rw [freshWorld_getOrigStor]
  exact freshWorld_stor_arrayEntry freshWorld_payload_one

theorem freshWorld_origIndex :
    getOrigStorVal freshWorldSevm freshWorldOwner
      (indexSlot freshWorldTarget) = 0 := by
  rw [freshWorld_getOrigStor]
  exact freshWorld_stor_index freshWorld_targetValid.2

theorem freshWorld_origLength :
    getOrigStorVal freshWorldSevm freshWorldOwner arrayLengthSlot = 0 := by
  rw [freshWorld_getOrigStor]
  exact freshWorld_stor_arrayLength

theorem freshWorld_origCount :
    getOrigStorVal freshWorldSevm freshWorldOwner
      (countSlot freshWorldPauser) = 0 := by
  rw [freshWorld_getOrigStor]
  exact freshWorld_stor_count freshWorld_pauserValid.2

theorem freshWorld_origExpiry :
    getOrigStorVal freshWorldSevm freshWorldOwner
      (expirySlot freshWorldPauser) = 0 := by
  rw [freshWorld_getOrigStor]
  exact freshWorld_stor_expiry freshWorld_pauserValid.2

/-! ### Reads at the assignment-write boundary -/

theorem freshWorld_postArray :
    (assignmentPost freshWorldSevm freshWorldPre freshWorldTarget
      freshWorldPauser).getStorVal freshWorldOwner (arrayEntrySlot 1) = 0 := by
  rw [freshWorld_assignmentPost_getStorVal freshWorld_assignment_ne_arrayEntry]
  exact freshWorld_stor_arrayEntry freshWorld_payload_one

theorem freshWorld_postInterval :
    (assignmentPost freshWorldSevm freshWorldPre freshWorldTarget
      freshWorldPauser).getStorVal freshWorldOwner heartbeatIntervalSlot =
      freshWorldInterval := by
  rw [freshWorld_assignmentPost_getStorVal freshWorld_assignment_ne_interval]
  exact freshWorld_stor_interval

theorem freshWorld_postExpiry :
    (assignmentPost freshWorldSevm freshWorldPre freshWorldTarget
      freshWorldPauser).getStorVal freshWorldOwner
      (expirySlot freshWorldPauser) = 0 := by
  rw [freshWorld_assignmentPost_getStorVal freshWorld_assignment_ne_expiry]
  exact freshWorld_stor_expiry freshWorld_pauserValid.2

/-! ### Value costs, successor words and the checked extension -/

theorem freshWorld_assignmentCost :
    sstoreValueCost 0 0 freshWorldPauser = gasStorageSet :=
  freshWorld_setCost freshWorld_pauserValid.1

theorem freshWorld_arrayCost :
    sstoreValueCost 0 0 freshWorldTarget = gasStorageSet :=
  freshWorld_setCost freshWorld_targetValid.1

theorem freshWorld_indexCost :
    sstoreValueCost 0 0 (Nat.toB256 1) = gasStorageSet :=
  freshWorld_setCost (by decide)

theorem freshWorld_lengthCost :
    sstoreValueCost 0 (Nat.toB256 0) (Nat.toB256 1) = gasStorageSet :=
  freshWorld_setCost (by decide)

theorem freshWorld_countCost :
    sstoreValueCost 0 (Nat.toB256 (assignmentCount [] freshWorldPauser))
      (Nat.toB256 (assignmentCount [] freshWorldPauser + 1)) =
      gasStorageSet :=
  freshWorld_setCost (by decide)

theorem freshWorld_lengthNextWord :
    (1 : B256) + Nat.toB256 ([] : List Entry).length = Nat.toB256 1 := by
  decide

theorem freshWorld_countNextWord :
    (1 : B256) + Nat.toB256 (assignmentCount [] freshWorldPauser) =
      Nat.toB256 (assignmentCount [] freshWorldPauser + 1) := by
  decide

theorem freshWorld_extension :
    CheckedHeartbeatExtension freshWorldTime freshWorldInterval
      freshWorldExpiry := by
  constructor
  · unfold freshWorldTime freshWorldInterval
    change (10 : Nat) + 2592000 < 2 ^ 256
    norm_num
  · decide

theorem freshWorld_expiryNonzero : freshWorldExpiry ≠ 0 := by decide

private theorem freshWorld_warmCost {base : Devm} {key : B256}
    (h : base.accessedStorageKeys = freshWorldKeys)
    (hk : (freshWorldOwner, key) ∈ freshWorldKeys) :
    temporalSloadCost freshWorldSevm base key = gasWarmAccess := by
  rw [temporalSloadCost]
  split
  · rfl
  · rename_i hno
    refine absurd ?_ hno
    show (freshWorldOwner, key) ∈ base.accessedStorageKeys
    rw [h]
    exact hk

private theorem freshWorld_coldCost {base : Devm} {key : B256}
    (h : base.accessedStorageKeys = freshWorldKeys)
    (hk : (freshWorldOwner, key) ∉ freshWorldKeys) :
    temporalSloadCost freshWorldSevm base key = gasColdSload := by
  rw [temporalSloadCost]
  split
  · rename_i hyes
    refine absurd ?_ hk
    show (freshWorldOwner, key) ∈ freshWorldKeys
    rw [← h]
    exact hyes
  · rfl

private theorem freshWorld_arrayLengthLoadBase :
    temporalSloadBase freshWorldSevm
        (assignmentPost freshWorldSevm freshWorldPre freshWorldTarget
          freshWorldPauser) arrayLengthSlot =
      assignmentPost freshWorldSevm freshWorldPre freshWorldTarget
        freshWorldPauser := by
  rw [temporalSloadBase]
  split
  · rfl
  · rename_i hno
    refine absurd ?_ hno
    show (freshWorldOwner, arrayLengthSlot) ∈
      (assignmentPost freshWorldSevm freshWorldPre freshWorldTarget
        freshWorldPauser).accessedStorageKeys
    rw [freshWorld_assignmentPost_accessed]
    exact freshWorld_warmArrayLength

/-- The chronology's body reserve at this world is the closed numeral the
message carries. -/
theorem freshWorld_bodyGasEq :
    freshRegisterBodyGas freshWorldSevm freshWorldPre [] freshWorldTarget
        freshWorldPauser gasStorageSet gasStorageSet gasStorageSet
        gasStorageSet gasStorageSet = freshWorldBodyGas := by
  have htower :
      (temporalSstorePost freshWorldSevm
        (temporalSstorePost freshWorldSevm
          (temporalSstorePost freshWorldSevm
            (assignmentPost freshWorldSevm freshWorldPre freshWorldTarget
              freshWorldPauser)
            (arrayEntrySlot (Nat.toB256 (([] : List Entry).length + 1)))
            freshWorldTarget)
          (indexSlot freshWorldTarget)
          (Nat.toB256 (([] : List Entry).length + 1)))
        arrayLengthSlot
        (Nat.toB256 (([] : List Entry).length + 1))).accessedStorageKeys =
      freshWorldKeys := freshWorld_assignmentPost_accessed
  simp only [freshRegisterBodyGas, freshSetPauserKernelGas]
  rw [freshWorld_memoryCost,
    freshWorld_warmCost freshWorld_accessed freshWorld_warmAssignment,
    freshWorld_warmCost freshWorld_assignmentPost_accessed
      freshWorld_warmArrayLength,
    freshWorld_arrayLengthLoadBase,
    freshWorld_coldCost htower freshWorld_coldCount]
  norm_num [freshWorldBodyGas, gasStorageSet, gasWarmAccess, gasColdSload]

/-! ### Warm and cold keys at the assignment-write boundary -/

theorem freshWorld_postWarmArrayEntry :
    (freshWorldOwner, arrayEntrySlot 1) ∈
      (assignmentPost freshWorldSevm freshWorldPre freshWorldTarget
        freshWorldPauser).accessedStorageKeys := by
  rw [freshWorld_assignmentPost_accessed]
  exact freshWorld_warmArrayEntry

theorem freshWorld_postWarmIndex :
    (freshWorldOwner, indexSlot freshWorldTarget) ∈
      (assignmentPost freshWorldSevm freshWorldPre freshWorldTarget
        freshWorldPauser).accessedStorageKeys := by
  rw [freshWorld_assignmentPost_accessed]
  exact freshWorld_warmIndex

theorem freshWorld_postWarmExpiry :
    (freshWorldOwner, expirySlot freshWorldPauser) ∈
      (assignmentPost freshWorldSevm freshWorldPre freshWorldTarget
        freshWorldPauser).accessedStorageKeys := by
  rw [freshWorld_assignmentPost_accessed]
  exact freshWorld_warmExpiry

theorem freshWorld_postColdCount :
    (freshWorldOwner, countSlot freshWorldPauser) ∉
      (assignmentPost freshWorldSevm freshWorldPre freshWorldTarget
        freshWorldPauser).accessedStorageKeys := by
  rw [freshWorld_assignmentPost_accessed]
  exact freshWorld_coldCount

theorem freshWorld_postColdInterval :
    (freshWorldOwner, heartbeatIntervalSlot) ∉
      (assignmentPost freshWorldSevm freshWorldPre freshWorldTarget
        freshWorldPauser).accessedStorageKeys := by
  rw [freshWorld_assignmentPost_accessed]
  exact freshWorld_coldInterval

/-! ### Calldata -/

theorem freshWorld_dataFacts :
    freshWorldSevm.data.length.toB256 = 68 ∧
      Sevm.selector freshWorldSevm =
        selector "registerPauser" [.address, .address] ∧
      Sevm.dataWord freshWorldSevm 4 = freshWorldTarget ∧
      Sevm.dataWord freshWorldSevm 36 = freshWorldPauser :=
  registerPauserCalldata_spec freshWorldSevm freshWorldTarget freshWorldPauser
    freshWorld_data

/-! ## The payoff -/

/-- A fully inhabited production-runtime fresh registration.  The admin of
`officialParams` calls `registerPauser(7, 9)` on a CircuitBreaker deployed at
address `100` whose Registry is empty and whose configured heartbeat interval
is thirty days, with exactly `128458` gas, at block time `10`, five warm and
two cold storage keys.  Every premise of the fresh-registration chronology
holds at this one machine, so the exact compiled run actually happens: the
source trace exists, the post-Registry witness holds, the walk reaches `ok`
with the gas exhausted to zero, the new pauser's heartbeat expiry is
`2592010`, and the two events are emitted in order. -/
theorem freshRegistrationWorld_run :
    ∃ trace post,
      setPauserSourceTrace [] freshWorldTarget freshWorldPauser = some trace ∧
      trace.postEntries = [(freshWorldTarget, freshWorldPauser)] ∧
      RegistryWitness
        (logicalStorageOfStor (applyRegistryWrites
          (Devm.getStor freshWorldPre freshWorldOwner) trace.writes))
        trace.postEntries ∧
      Prog.RunCompiledTo freshWorldSevm freshWorldPre
        (runtime officialParams) (.ok post) ∧
      exec ⟨0, freshWorldSevm, freshWorldPre⟩ = .ok post ∧
      Nonempty (Exec 0 freshWorldSevm freshWorldPre (.ok post)) ∧
      post.gasLeft = 0 ∧
      post.getStorVal freshWorldOwner (expirySlot freshWorldPauser) =
        freshWorldExpiry ∧
      post.logs =
        [⟨freshWorldOwner,
            [pauserSetEvent, freshWorldTarget, 0, freshWorldPauser], []⟩,
          ⟨freshWorldOwner, [heartbeatUpdatedEvent, freshWorldPauser],
            freshWorldExpiry.toBytes⟩] ∧
      some freshWorldSevm.code.toList = Prog.compile (runtime officialParams) := by
  rcases freshWorld_dataFacts with ⟨hlength, hselector, hargTarget, hargNew⟩
  rcases registerPauser_runCompiledTo_freshNonzero officialParams
      freshWorldSevm freshWorldPre [] freshWorldTarget freshWorldPauser
      freshWorldTime freshWorldInterval freshWorldExpiry 0 0 0 0 0
      gasStorageSet gasStorageSet gasStorageSet gasStorageSet gasStorageSet 0
      hlength freshWorld_value hselector freshWorld_codeAddress
      freshWorld_codeBytes freshWorld_admin hargTarget hargNew
      freshWorld_preWitness freshWorld_find freshWorld_targetValid
      freshWorld_pauserValid freshWorld_time freshWorld_origAssignment
      freshWorld_assignmentCost freshWorld_postArray freshWorld_origArray
      freshWorld_arrayCost freshWorld_postWarmArrayEntry
      freshWorld_origIndex freshWorld_indexCost freshWorld_postWarmIndex
      freshWorld_origLength freshWorld_lengthCost freshWorld_lengthNextWord
      freshWorld_origCount freshWorld_countCost freshWorld_countNextWord
      freshWorld_postColdCount freshWorld_postInterval
      freshWorld_postColdInterval freshWorld_postExpiry freshWorld_origExpiry
      freshWorld_postWarmExpiry freshWorld_static freshWorld_extension
      freshWorld_expiryNonzero with
    ⟨trace, post, htrace, hpostEntries, hwitness, hrun, hgas, hexpiry, hlogs,
      hcompile⟩
  have hentry :
      freshWorldPre.setMach ⟨[], Mem.empty,
        0 + registerPauserDispatchGas +
          freshRegisterBodyGas freshWorldSevm freshWorldPre []
            freshWorldTarget freshWorldPauser gasStorageSet gasStorageSet
            gasStorageSet gasStorageSet gasStorageSet⟩ = freshWorldPre := by
    rw [freshWorld_bodyGasEq]
    rfl
  rw [hentry] at hrun
  have hexec : exec ⟨0, freshWorldSevm, freshWorldPre⟩ = .ok post :=
    Prog.exec_of_runCompiledTo hrun hcompile
  exact ⟨trace, post, htrace, hpostEntries, hwitness, hrun, hexec,
    (exec_iff_exec_eq 0 freshWorldSevm freshWorldPre (.ok post)).mpr hexec,
    hgas, hexpiry, hlogs, hcompile⟩

/-- Message-altitude settlement at this world.

The chronology exposes the raw poststate's gas, storage and logs but says
nothing about its `error` flag, and nothing landed propagates `Devm.error`
across a compiled walk — so cleanliness stays an explicit antecedent here
rather than a discharged premise.  Given it, the frame settles onto the raw
poststate itself: no rollback, and the concrete registration is what the
message leaves behind. -/
theorem freshRegistrationWorld_settles :
    ∃ post,
      exec ⟨0, freshWorldSevm, freshWorldPre⟩ = .ok post ∧
      post.gasLeft = 0 ∧
      post.getStorVal freshWorldOwner (expirySlot freshWorldPauser) =
        freshWorldExpiry ∧
      post.logs =
        [⟨freshWorldOwner,
            [pauserSetEvent, freshWorldTarget, 0, freshWorldPauser], []⟩,
          ⟨freshWorldOwner, [heartbeatUpdatedEvent, freshWorldPauser],
            freshWorldExpiry.toBytes⟩] ∧
      (post.error.isNone = true →
        ProcessMessage freshWorldMsg
          (.some ⟨⟨0, freshWorldSevm, freshWorldPre⟩, .ok post⟩)
          (.ok post)) := by
  obtain ⟨trace, post, _htrace, _hentries, _hwitness, _hrun, hexec, _hfilled,
    hgas, hexpiry, hlogs, _hcompile⟩ := freshRegistrationWorld_run
  refine ⟨post, hexec, hgas, hexpiry, hlogs, ?_⟩
  intro hclean
  have hnot : post.error.isSome ≠ true := by
    cases herror : post.error <;> simp_all
  have hprocess := RunFrame.of_run (f := Frame.ofCall freshWorldMsg)
    (raw := (.ok post : Execution)) freshWorld_frameEntry
  have hsettle :
      (Frame.ofCall freshWorldMsg).settle (.ok post) = .ok post := by
    simp only [Frame.settle, Frame.settleMsg, Frame.ofCall,
      executeCode.handleError, processMessage.settle, bind, Except.bind,
      if_neg hnot]
    rfl
  rwa [hsettle] at hprocess

end Blanc.LidoCircuitBreaker
