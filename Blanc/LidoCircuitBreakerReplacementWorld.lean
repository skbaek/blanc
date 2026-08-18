import Blanc.LidoCircuitBreakerReplacementRegistration

/-!
Two fully instantiated admin-replacement worlds for the Lido CircuitBreaker.

`Blanc/LidoCircuitBreakerReplacementRegistration.lean` states both arms of the
replacement chronology against an abstract message, abstract entry storage,
abstract original words, abstract `SSTORE` value costs and abstract
accessed-key warmth.  Nothing there exhibits a single machine at which all of
those premises hold at once, so each arm is certified in one direction only:
*if* such a world exists, the run happens.

This leaf closes that gap the way
`Blanc/LidoCircuitBreakerRegistrationWorld.lean` closes it for the fresh
chronology, and with one shared skeleton rather than two: the admin reassigns
target `7` from pauser `9` to pauser `11` on a CircuitBreaker deployed at
address `100`, and the *only* thing that separates the two worlds is the old
pauser's entry assignment count.  At `2` the decrement leaves `1`, so
`registerAfterSet` takes its retained arm; at `1` it leaves `0`, so the old
pauser's heartbeat expiry is cleared first.

Every storage key either world reads or writes is warm at message entry except
the configured-interval slot, which both chronologies charge cold.  That is not
cosmetic: it makes every `temporalSloadBase` layer of the four-, six- and
seven-layer post-state towers the identity, so the towers' accessed-key sets
and storage values are settled by `temporalSstorePost_other` and
`temporalSstorePost_self` alone and no `Std.HashSet` is ever decided.

**No `RegistryWitness` appears here, and that is a real limitation, not a
convenience.**  Neither `registerPauser_runCompiledTo_*` theorem consumes one —
the model-side characterisation enters the replacement chronology at the
settled-effects boundary, as a hypothetical — so a world that only has to
inhabit the *execution* premises does not need the Registry projections to
hold.  These worlds do not satisfy them: the entry storage records target `7`
as assigned to pauser `9` while leaving the array length and the target's
reverse index at zero, which no `registerPauser` call could ever produce.
`Blanc/LidoCircuitBreakerRegistrationWorld.lean` is stronger on exactly this
point — it carries `freshWorldStor_witness`.

So read what these two worlds establish at its actual width.  Each is a
genuine, gas-exact execution of the production runtime from a concrete
`Msg`, which is everything `Attainable` consumes and everything
`Blanc/LidoCircuitBreakerAttainment.lean` asks of them.  Neither is a claim
that its entry state is reachable from a genesis-consistent history, and
neither should be read as one.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune

/-! ## The shared skeleton -/

/-- The CircuitBreaker deployment: the contract account that owns the Registry
storage and carries the generated runtime. -/
def replWorldOwner : Adr := Nat.toAdr 100

/-- The admin caller.  `officialParams.admin` as an address. -/
def replWorldAdmin : Adr :=
  Nat.toAdr 0x3e40D73EB977Dc6a537aF587D48316feE66E9C8c

/-- The pausable target being reassigned. -/
def replWorldTarget : B256 := 7

/-- The pauser the target is recorded to at entry. -/
def replWorldOldPauser : B256 := 9

/-- The pauser the target is reassigned to.  Distinct from the old pauser, so
the two count writes land on two slots and the old pauser's remaining count is
the decrement rather than the increment. -/
def replWorldNewPauser : B256 := 11

/-- Block timestamp at the replacing call. -/
def replWorldTime : B256 := 10

/-- The configured heartbeat interval, read from `heartbeatIntervalSlot`. -/
def replWorldInterval : B256 := 2592000

/-- The heartbeat expiry the replacement installs: `time + interval`. -/
def replWorldExpiry : B256 := 2592010

/-- The old pauser's heartbeat expiry at entry.  Only the old-last world
clears it; the retained world never touches the cell. -/
def replWorldOldExpiry : B256 := 100

/-- The deployed account storage, parameterised by the old pauser's assignment
count: the configured interval, the target's recorded assignment, that count,
and the old pauser's heartbeat expiry. -/
def replWorldStor (oldCount : B256) : Stor :=
  (((Stor.empty.set heartbeatIntervalSlot replWorldInterval).set
    (assignmentSlot replWorldTarget) replWorldOldPauser).set
    (countSlot replWorldOldPauser) oldCount).set
    (expirySlot replWorldOldPauser) replWorldOldExpiry

/-- The installed generated runtime bytes. -/
def replWorldCode : ByteArray :=
  ByteArray.mk (lidoCircuitBreakerCode officialParams).toArray

/-- World state: the CircuitBreaker account alone. -/
def replWorldState (oldCount : B256) : State :=
  State.set (.empty : State) replWorldOwner
    { Acct.nil with
      stor := replWorldStor oldCount
      code := replWorldCode }

/-- The warm accessed-storage-key set at message entry: the target's
assignment slot, both count slots and both expiry slots.  The heartbeat
interval slot is deliberately absent — both chronologies charge it cold. -/
def replWorldKeys : Std.HashSet (Adr × B256) :=
  ((((Std.HashSet.emptyWithCapacity.insert
    (replWorldOwner, assignmentSlot replWorldTarget)).insert
    (replWorldOwner, countSlot replWorldOldPauser)).insert
    (replWorldOwner, countSlot replWorldNewPauser)).insert
    (replWorldOwner, expirySlot replWorldOldPauser)).insert
    (replWorldOwner, expirySlot replWorldNewPauser)

/-! ## Payload bounds and slot separation

Every slot either world touches is `slot region payload` for a region below
`16` and a payload below `2 ^ 252`, so `slot_ne_of_region_ne` separates any two
whose regions differ and `slot_injective_payload` separates the two count slots
and the two expiry slots, whose regions do not. -/

private theorem replWorld_payload_one : (1 : B256).toNat < 2 ^ 252 := by
  change (1 : Nat) < 2 ^ 252
  norm_num

private theorem replWorld_payload_target :
    replWorldTarget.toNat < 2 ^ 252 := by
  unfold replWorldTarget
  change (7 : Nat) < 2 ^ 252
  norm_num

private theorem replWorld_payload_old : replWorldOldPauser.toNat < 2 ^ 252 := by
  unfold replWorldOldPauser
  change (9 : Nat) < 2 ^ 252
  norm_num

private theorem replWorld_payload_new : replWorldNewPauser.toNat < 2 ^ 252 := by
  unfold replWorldNewPauser
  change (11 : Nat) < 2 ^ 252
  norm_num

theorem replWorld_targetValid : nonzeroCanonicalAddress replWorldTarget := by
  refine ⟨by decide, ?_⟩
  unfold canonicalAddress replWorldTarget
  change (7 : Nat) < 2 ^ 160
  norm_num

theorem replWorld_oldValid : nonzeroCanonicalAddress replWorldOldPauser := by
  refine ⟨by decide, ?_⟩
  unfold canonicalAddress replWorldOldPauser
  change (9 : Nat) < 2 ^ 160
  norm_num

theorem replWorld_newValid : nonzeroCanonicalAddress replWorldNewPauser := by
  refine ⟨by decide, ?_⟩
  unfold canonicalAddress replWorldNewPauser
  change (11 : Nat) < 2 ^ 160
  norm_num

/-- The two count slots are separated by their payloads alone. -/
theorem replWorld_newCount_ne_oldCount :
    countSlot replWorldNewPauser ≠ countSlot replWorldOldPauser := by
  intro heq
  exact absurd (slot_injective_payload (by norm_num [countRegion])
    replWorld_payload_new replWorld_payload_old heq) (by decide)

/-- The two expiry slots, likewise. -/
theorem replWorld_newExpiry_ne_oldExpiry :
    expirySlot replWorldNewPauser ≠ expirySlot replWorldOldPauser := by
  intro heq
  exact absurd (slot_injective_payload (by norm_num [expiryRegion])
    replWorld_payload_new replWorld_payload_old heq) (by decide)

theorem replWorld_assignment_ne_oldCount :
    assignmentSlot replWorldTarget ≠ countSlot replWorldOldPauser :=
  slot_ne_of_region_ne (by norm_num [assignmentRegion])
    (by norm_num [countRegion]) replWorld_payload_target replWorld_payload_old
    (by norm_num [assignmentRegion, countRegion])

theorem replWorld_assignment_ne_newCount :
    assignmentSlot replWorldTarget ≠ countSlot replWorldNewPauser :=
  slot_ne_of_region_ne (by norm_num [assignmentRegion])
    (by norm_num [countRegion]) replWorld_payload_target replWorld_payload_new
    (by norm_num [assignmentRegion, countRegion])

theorem replWorld_assignment_ne_newExpiry :
    assignmentSlot replWorldTarget ≠ expirySlot replWorldNewPauser :=
  slot_ne_of_region_ne (by norm_num [assignmentRegion])
    (by norm_num [expiryRegion]) replWorld_payload_target replWorld_payload_new
    (by norm_num [assignmentRegion, expiryRegion])

theorem replWorld_assignment_ne_oldExpiry :
    assignmentSlot replWorldTarget ≠ expirySlot replWorldOldPauser :=
  slot_ne_of_region_ne (by norm_num [assignmentRegion])
    (by norm_num [expiryRegion]) replWorld_payload_target replWorld_payload_old
    (by norm_num [assignmentRegion, expiryRegion])

theorem replWorld_assignment_ne_interval :
    assignmentSlot replWorldTarget ≠ heartbeatIntervalSlot :=
  slot_ne_of_region_ne (by norm_num [assignmentRegion])
    (by norm_num [configRegion]) replWorld_payload_target replWorld_payload_one
    (by norm_num [assignmentRegion, configRegion])

theorem replWorld_oldCount_ne_newExpiry :
    countSlot replWorldOldPauser ≠ expirySlot replWorldNewPauser :=
  slot_ne_of_region_ne (by norm_num [countRegion]) (by norm_num [expiryRegion])
    replWorld_payload_old replWorld_payload_new
    (by norm_num [countRegion, expiryRegion])

theorem replWorld_oldCount_ne_oldExpiry :
    countSlot replWorldOldPauser ≠ expirySlot replWorldOldPauser :=
  slot_ne_of_region_ne (by norm_num [countRegion]) (by norm_num [expiryRegion])
    replWorld_payload_old replWorld_payload_old
    (by norm_num [countRegion, expiryRegion])

theorem replWorld_oldCount_ne_interval :
    countSlot replWorldOldPauser ≠ heartbeatIntervalSlot :=
  slot_ne_of_region_ne (by norm_num [countRegion]) (by norm_num [configRegion])
    replWorld_payload_old replWorld_payload_one
    (by norm_num [countRegion, configRegion])

theorem replWorld_newCount_ne_newExpiry :
    countSlot replWorldNewPauser ≠ expirySlot replWorldNewPauser :=
  slot_ne_of_region_ne (by norm_num [countRegion]) (by norm_num [expiryRegion])
    replWorld_payload_new replWorld_payload_new
    (by norm_num [countRegion, expiryRegion])

theorem replWorld_newCount_ne_oldExpiry :
    countSlot replWorldNewPauser ≠ expirySlot replWorldOldPauser :=
  slot_ne_of_region_ne (by norm_num [countRegion]) (by norm_num [expiryRegion])
    replWorld_payload_new replWorld_payload_old
    (by norm_num [countRegion, expiryRegion])

theorem replWorld_newCount_ne_interval :
    countSlot replWorldNewPauser ≠ heartbeatIntervalSlot :=
  slot_ne_of_region_ne (by norm_num [countRegion]) (by norm_num [configRegion])
    replWorld_payload_new replWorld_payload_one
    (by norm_num [countRegion, configRegion])

theorem replWorld_oldExpiry_ne_interval :
    expirySlot replWorldOldPauser ≠ heartbeatIntervalSlot :=
  slot_ne_of_region_ne (by norm_num [expiryRegion]) (by norm_num [configRegion])
    replWorld_payload_old replWorld_payload_one
    (by norm_num [expiryRegion, configRegion])

theorem replWorld_newExpiry_ne_interval :
    expirySlot replWorldNewPauser ≠ heartbeatIntervalSlot :=
  slot_ne_of_region_ne (by norm_num [expiryRegion]) (by norm_num [configRegion])
    replWorld_payload_new replWorld_payload_one
    (by norm_num [expiryRegion, configRegion])

/-! ## The entry storage, read cell by cell -/

private theorem replWorld_stor_zero {oldCount key : B256}
    (hA : heartbeatIntervalSlot ≠ key)
    (hB : assignmentSlot replWorldTarget ≠ key)
    (hC : countSlot replWorldOldPauser ≠ key)
    (hD : expirySlot replWorldOldPauser ≠ key) :
    (replWorldStor oldCount).get key = 0 := by
  rw [replWorldStor, Stor.get_set_ne _ hD, Stor.get_set_ne _ hC,
    Stor.get_set_ne _ hB, Stor.get_set_ne _ hA]
  simp [Stor.get, Stor.empty]

theorem replWorld_stor_oldExpiry (oldCount : B256) :
    (replWorldStor oldCount).get (expirySlot replWorldOldPauser) =
      replWorldOldExpiry := by
  rw [replWorldStor, Stor.get_set_self]

theorem replWorld_stor_oldCount (oldCount : B256) :
    (replWorldStor oldCount).get (countSlot replWorldOldPauser) = oldCount := by
  rw [replWorldStor, Stor.get_set_ne _ replWorld_oldCount_ne_oldExpiry.symm,
    Stor.get_set_self]

theorem replWorld_stor_assignment (oldCount : B256) :
    (replWorldStor oldCount).get (assignmentSlot replWorldTarget) =
      replWorldOldPauser := by
  rw [replWorldStor, Stor.get_set_ne _ replWorld_assignment_ne_oldExpiry.symm,
    Stor.get_set_ne _ replWorld_assignment_ne_oldCount.symm, Stor.get_set_self]

theorem replWorld_stor_interval (oldCount : B256) :
    (replWorldStor oldCount).get heartbeatIntervalSlot = replWorldInterval := by
  rw [replWorldStor, Stor.get_set_ne _ replWorld_oldExpiry_ne_interval,
    Stor.get_set_ne _ replWorld_oldCount_ne_interval,
    Stor.get_set_ne _ replWorld_assignment_ne_interval, Stor.get_set_self]

theorem replWorld_stor_newCount (oldCount : B256) :
    (replWorldStor oldCount).get (countSlot replWorldNewPauser) = 0 :=
  replWorld_stor_zero replWorld_newCount_ne_interval.symm
    replWorld_assignment_ne_newCount replWorld_newCount_ne_oldCount.symm
    replWorld_newCount_ne_oldExpiry.symm

theorem replWorld_stor_newExpiry (oldCount : B256) :
    (replWorldStor oldCount).get (expirySlot replWorldNewPauser) = 0 :=
  replWorld_stor_zero replWorld_newExpiry_ne_interval.symm
    replWorld_assignment_ne_newExpiry replWorld_oldCount_ne_newExpiry
    replWorld_newExpiry_ne_oldExpiry.symm

/-! ## The message

One constructor, parameterised by the old pauser's entry count and by the
message gas.  The two worlds below are its two instantiations. -/

/-- The concrete admin `registerPauser(7, 11)` call at a deployment whose
target `7` is already recorded to pauser `9` with `oldCount` assignments. -/
def replWorldMsg (oldCount : B256) (gas : Nat) : Msg :=
  { (default : Msg) with
    benv :=
      { (default : Benv) with
        state := replWorldState oldCount
        stat :=
          { (default : BenvStat) with
            origState := replWorldState oldCount
            time := replWorldTime } }
    tenv := default
    caller := replWorldAdmin
    target := some replWorldOwner
    currentTarget := replWorldOwner
    gas := gas
    value := 0
    data := registerPauserCalldata replWorldTarget replWorldNewPauser
    codeAddress := some replWorldOwner
    code := replWorldCode
    depth := 0
    shouldTransferValue := false
    isStatic := false
    accessedAddresses := .emptyWithCapacity
    accessedStorageKeys := replWorldKeys
    disablePrecompiles := false }

def replWorldSevm (oldCount : B256) (gas : Nat) : Sevm :=
  initSevm (replWorldMsg oldCount gas)

def replWorldPre (oldCount : B256) (gas : Nat) : Devm :=
  initDevm (replWorldMsg oldCount gas)

/-! ## Frame-shape facts -/

private theorem replWorld_byteArray_ofList_toList (bs : Bytes) :
    (ByteArray.mk bs.toArray).toList = bs := by
  rw [ByteArray.toList_eq_toList_data]

theorem replWorld_currentTarget (oldCount : B256) (gas : Nat) :
    (replWorldSevm oldCount gas).currentTarget = replWorldOwner := rfl

theorem replWorld_value (oldCount : B256) (gas : Nat) :
    (replWorldSevm oldCount gas).value = 0 := rfl

theorem replWorld_static (oldCount : B256) (gas : Nat) :
    (replWorldSevm oldCount gas).isStatic = false := rfl

theorem replWorld_codeAddress (oldCount : B256) (gas : Nat) :
    (replWorldSevm oldCount gas).codeAddress =
      some (replWorldSevm oldCount gas).currentTarget := rfl

theorem replWorld_time (oldCount : B256) (gas : Nat) :
    (replWorldSevm oldCount gas).benvStat.time = replWorldTime := rfl

theorem replWorld_admin (oldCount : B256) (gas : Nat) :
    (replWorldSevm oldCount gas).caller.toB256 = officialParams.admin := rfl

theorem replWorld_data (oldCount : B256) (gas : Nat) :
    (replWorldSevm oldCount gas).data =
      registerPauserCalldata replWorldTarget replWorldNewPauser := rfl

theorem replWorld_codeBytes (oldCount : B256) (gas : Nat) :
    (replWorldSevm oldCount gas).code.toList =
      lidoCircuitBreakerCode officialParams := by
  simpa only [replWorldSevm, replWorldMsg, initSevm, replWorldCode] using
    replWorld_byteArray_ofList_toList (lidoCircuitBreakerCode officialParams)

theorem replWorld_dataFacts (oldCount : B256) (gas : Nat) :
    (replWorldSevm oldCount gas).data.length.toB256 = 68 ∧
      Sevm.selector (replWorldSevm oldCount gas) =
        selector "registerPauser" [.address, .address] ∧
      Sevm.dataWord (replWorldSevm oldCount gas) 4 = replWorldTarget ∧
      Sevm.dataWord (replWorldSevm oldCount gas) 36 = replWorldNewPauser :=
  registerPauserCalldata_spec (replWorldSevm oldCount gas) replWorldTarget
    replWorldNewPauser (replWorld_data oldCount gas)

/-! ## Storage at message entry -/

theorem replWorld_getStorVal {oldCount : B256} {gas : Nat} {key : B256} :
    (replWorldPre oldCount gas).getStorVal replWorldOwner key =
      (replWorldStor oldCount).get key := by
  change ((replWorldState oldCount).get replWorldOwner).stor.get key = _
  rw [replWorldState, State.get_set_self]

theorem replWorld_getOrigStorVal {oldCount : B256} {gas : Nat} {key : B256} :
    getOrigStorVal (replWorldSevm oldCount gas) replWorldOwner key =
      (replWorldStor oldCount).get key := by
  change ((replWorldState oldCount).get replWorldOwner).stor.get key = _
  rw [replWorldState, State.get_set_self]

theorem replWorld_getStor (oldCount : B256) (gas : Nat) :
    Devm.getStor (replWorldPre oldCount gas) replWorldOwner =
      replWorldStor oldCount := by
  change ((replWorldState oldCount).get replWorldOwner).stor = _
  rw [replWorldState, State.get_set_self]

/-! ## Accessed storage keys

Five keys are warm at entry and the configured-interval slot is cold.
Membership is settled by the `insert` chain alone; non-membership is settled by
region separation, never by deciding a `HashSet`. -/

theorem replWorld_accessed (oldCount : B256) (gas : Nat) :
    (replWorldPre oldCount gas).accessedStorageKeys = replWorldKeys := rfl

theorem replWorld_warmAssignment :
    (replWorldOwner, assignmentSlot replWorldTarget) ∈ replWorldKeys := by
  rw [replWorldKeys]
  exact Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
    (Or.inr (Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
      (Or.inr Std.HashSet.mem_insert_self)))))))

theorem replWorld_warmOldCount :
    (replWorldOwner, countSlot replWorldOldPauser) ∈ replWorldKeys := by
  rw [replWorldKeys]
  exact Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
    (Or.inr (Std.HashSet.mem_insert.mpr
      (Or.inr Std.HashSet.mem_insert_self)))))

theorem replWorld_warmNewCount :
    (replWorldOwner, countSlot replWorldNewPauser) ∈ replWorldKeys := by
  rw [replWorldKeys]
  exact Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
    (Or.inr Std.HashSet.mem_insert_self)))

theorem replWorld_warmOldExpiry :
    (replWorldOwner, expirySlot replWorldOldPauser) ∈ replWorldKeys := by
  rw [replWorldKeys]
  exact Std.HashSet.mem_insert.mpr (Or.inr Std.HashSet.mem_insert_self)

theorem replWorld_warmNewExpiry :
    (replWorldOwner, expirySlot replWorldNewPauser) ∈ replWorldKeys :=
  Std.HashSet.mem_insert_self

theorem replWorld_coldInterval :
    (replWorldOwner, heartbeatIntervalSlot) ∉ replWorldKeys := by
  rw [replWorldKeys]
  simp only [Std.HashSet.mem_insert, Std.HashSet.not_mem_emptyWithCapacity,
    or_false, not_or, beq_iff_eq, Prod.mk.injEq, not_and]
  exact ⟨fun _ => replWorld_newExpiry_ne_interval,
    fun _ => replWorld_oldExpiry_ne_interval,
    fun _ => replWorld_newCount_ne_interval,
    fun _ => replWorld_oldCount_ne_interval,
    fun _ => replWorld_assignment_ne_interval⟩

/-! ## The post-state towers

Every read key is warm at entry, so each `temporalSloadBase` layer of the
chronology's four-, six- and seven-layer towers is the identity.  That is what
lets `temporalSstorePost_other` and `temporalSstorePost_self` settle every
storage value and every warmth question below without a `Std.HashSet` ever
being decided. -/

section Towers

variable (oldCount : B256) (gas : Nat)

theorem replWorld_assignmentBase :
    assignmentBase (replWorldSevm oldCount gas) (replWorldPre oldCount gas)
      replWorldTarget = replWorldPre oldCount gas := by
  rw [assignmentBase, temporalSloadBase]
  split
  · rfl
  · rename_i hcold
    exact absurd replWorld_warmAssignment hcold

theorem replWorld_assignmentPost_accessed :
    (assignmentPost (replWorldSevm oldCount gas) (replWorldPre oldCount gas)
      replWorldTarget replWorldNewPauser).accessedStorageKeys =
      replWorldKeys := by
  rw [assignmentPost, temporalSstorePost_accessedStorageKeys,
    replWorld_assignmentBase]
  rfl

theorem replWorld_assignmentPost_getStorVal {oldCount gas} {key : B256}
    (h : assignmentSlot replWorldTarget ≠ key) :
    (assignmentPost (replWorldSevm oldCount gas) (replWorldPre oldCount gas)
      replWorldTarget replWorldNewPauser).getStorVal replWorldOwner key =
      (replWorldStor oldCount).get key := by
  rw [assignmentPost,
    temporalSstorePost_other (replWorldSevm oldCount gas)
      (assignmentBase (replWorldSevm oldCount gas) (replWorldPre oldCount gas)
        replWorldTarget)
      (assignmentSlot replWorldTarget) replWorldNewPauser replWorldOwner key
      (by
        intro hpair
        exact h (Prod.mk.injEq .. ▸ hpair).2.symm),
    replWorld_assignmentBase, replWorld_getStorVal]

private theorem replWorld_oldCountLoadBase :
    temporalSloadBase (replWorldSevm oldCount gas)
        (assignmentPost (replWorldSevm oldCount gas)
          (replWorldPre oldCount gas) replWorldTarget replWorldNewPauser)
        (countSlot replWorldOldPauser) =
      assignmentPost (replWorldSevm oldCount gas) (replWorldPre oldCount gas)
        replWorldTarget replWorldNewPauser := by
  rw [temporalSloadBase]
  split
  · rfl
  · rename_i hcold
    refine absurd ?_ hcold
    show (replWorldOwner, countSlot replWorldOldPauser) ∈
      (assignmentPost (replWorldSevm oldCount gas) (replWorldPre oldCount gas)
        replWorldTarget replWorldNewPauser).accessedStorageKeys
    rw [replWorld_assignmentPost_accessed]
    exact replWorld_warmOldCount

theorem replWorld_foundKernelPost_accessed :
    (foundKernelPost (replWorldSevm oldCount gas) (replWorldPre oldCount gas)
      replWorldTarget replWorldNewPauser replWorldOldPauser
      oldCount).accessedStorageKeys = replWorldKeys := by
  rw [foundKernelPost, temporalSstorePost_accessedStorageKeys,
    replWorld_oldCountLoadBase, replWorld_assignmentPost_accessed]

theorem replWorld_foundKernelPost_getStorVal {oldCount gas} {key : B256}
    (hcount : countSlot replWorldOldPauser ≠ key)
    (hassignment : assignmentSlot replWorldTarget ≠ key) :
    (foundKernelPost (replWorldSevm oldCount gas) (replWorldPre oldCount gas)
      replWorldTarget replWorldNewPauser replWorldOldPauser
      oldCount).getStorVal replWorldOwner key =
      (replWorldStor oldCount).get key := by
  rw [foundKernelPost,
    temporalSstorePost_other (replWorldSevm oldCount gas)
      (temporalSloadBase (replWorldSevm oldCount gas)
        (assignmentPost (replWorldSevm oldCount gas)
          (replWorldPre oldCount gas) replWorldTarget replWorldNewPauser)
        (countSlot replWorldOldPauser))
      (countSlot replWorldOldPauser) (oldCount - 1) replWorldOwner key
      (by
        intro hpair
        exact hcount (Prod.mk.injEq .. ▸ hpair).2.symm),
    replWorld_oldCountLoadBase,
    replWorld_assignmentPost_getStorVal hassignment]

theorem replWorld_foundKernelPost_oldCount :
    (foundKernelPost (replWorldSevm oldCount gas) (replWorldPre oldCount gas)
      replWorldTarget replWorldNewPauser replWorldOldPauser
      oldCount).getStorVal replWorldOwner (countSlot replWorldOldPauser) =
      oldCount - 1 :=
  temporalSstorePost_self _ _ _ _

private theorem replWorld_newCountLoadBase :
    temporalSloadBase (replWorldSevm oldCount gas)
        (foundKernelPost (replWorldSevm oldCount gas)
          (replWorldPre oldCount gas) replWorldTarget replWorldNewPauser
          replWorldOldPauser oldCount)
        (countSlot replWorldNewPauser) =
      foundKernelPost (replWorldSevm oldCount gas) (replWorldPre oldCount gas)
        replWorldTarget replWorldNewPauser replWorldOldPauser oldCount := by
  rw [temporalSloadBase]
  split
  · rfl
  · rename_i hcold
    refine absurd ?_ hcold
    show (replWorldOwner, countSlot replWorldNewPauser) ∈
      (foundKernelPost (replWorldSevm oldCount gas) (replWorldPre oldCount gas)
        replWorldTarget replWorldNewPauser replWorldOldPauser
        oldCount).accessedStorageKeys
    rw [replWorld_foundKernelPost_accessed]
    exact replWorld_warmNewCount

theorem replWorld_foundNonzeroKernelPost_accessed (nextCount : B256) :
    (foundNonzeroKernelPost (replWorldSevm oldCount gas)
      (replWorldPre oldCount gas) replWorldTarget replWorldNewPauser
      replWorldOldPauser oldCount nextCount).accessedStorageKeys =
      replWorldKeys := by
  rw [foundNonzeroKernelPost, temporalSstorePost_accessedStorageKeys,
    replWorld_newCountLoadBase, replWorld_foundKernelPost_accessed]

theorem replWorld_foundNonzeroKernelPost_getStorVal {oldCount gas}
    {nextCount key : B256}
    (hnewCount : countSlot replWorldNewPauser ≠ key)
    (hcount : countSlot replWorldOldPauser ≠ key)
    (hassignment : assignmentSlot replWorldTarget ≠ key) :
    (foundNonzeroKernelPost (replWorldSevm oldCount gas)
      (replWorldPre oldCount gas) replWorldTarget replWorldNewPauser
      replWorldOldPauser oldCount nextCount).getStorVal replWorldOwner key =
      (replWorldStor oldCount).get key := by
  rw [foundNonzeroKernelPost,
    temporalSstorePost_other (replWorldSevm oldCount gas)
      (temporalSloadBase (replWorldSevm oldCount gas)
        (foundKernelPost (replWorldSevm oldCount gas)
          (replWorldPre oldCount gas) replWorldTarget replWorldNewPauser
          replWorldOldPauser oldCount)
        (countSlot replWorldNewPauser))
      (countSlot replWorldNewPauser) nextCount replWorldOwner key
      (by
        intro hpair
        exact hnewCount (Prod.mk.injEq .. ▸ hpair).2.symm),
    replWorld_newCountLoadBase,
    replWorld_foundKernelPost_getStorVal hcount hassignment]

theorem replWorld_foundNonzeroKernelPost_oldCount (nextCount : B256) :
    (foundNonzeroKernelPost (replWorldSevm oldCount gas)
      (replWorldPre oldCount gas) replWorldTarget replWorldNewPauser
      replWorldOldPauser oldCount nextCount).getStorVal replWorldOwner
        (countSlot replWorldOldPauser) = oldCount - 1 := by
  rw [foundNonzeroKernelPost,
    temporalSstorePost_other (replWorldSevm oldCount gas)
      (temporalSloadBase (replWorldSevm oldCount gas)
        (foundKernelPost (replWorldSevm oldCount gas)
          (replWorldPre oldCount gas) replWorldTarget replWorldNewPauser
          replWorldOldPauser oldCount)
        (countSlot replWorldNewPauser))
      (countSlot replWorldNewPauser) nextCount replWorldOwner
      (countSlot replWorldOldPauser)
      (by
        intro hpair
        exact replWorld_newCount_ne_oldCount
          (Prod.mk.injEq .. ▸ hpair).2.symm),
    replWorld_newCountLoadBase, replWorld_foundKernelPost_oldCount]

end Towers

/-! ## Value charges and gas

Both worlds write the same five cells with the same value cases: the
assignment and the old count are nonzero-to-nonzero resets, the new count and
the new pauser's expiry are zero-to-nonzero sets, and the old-last world's
expiry clear is a third reset.  So the whole gas figure is a closed numeral in
the world's own data, and it never mentions the message whose `gas` field it
fills. -/

/-- The value charge of a nonzero-to-nonzero reset, above the warmth charge the
key already carries. -/
def replWorldResetCost : Nat := gasStorageUpdate - gasColdSload

private theorem replWorld_resetCost {orig new : B256} (hnew : orig ≠ new)
    (hzero : ¬ orig = 0) : sstoreValueCost orig orig new =
      replWorldResetCost := by
  rw [sstoreValueCost, if_pos ⟨rfl, hnew⟩, if_neg hzero, replWorldResetCost]

private theorem replWorld_setCost {new : B256} (h : new ≠ 0) :
    sstoreValueCost 0 0 new = gasStorageSet := by
  rw [sstoreValueCost, if_pos ⟨rfl, fun hc => h hc.symm⟩, if_pos rfl]

private theorem replWorld_warmCost {oldCount : B256} {gas : Nat} {base : Devm}
    {key : B256} (h : base.accessedStorageKeys = replWorldKeys)
    (hk : (replWorldOwner, key) ∈ replWorldKeys) :
    temporalSloadCost (replWorldSevm oldCount gas) base key =
      gasWarmAccess := by
  rw [temporalSloadCost]
  split
  · rfl
  · rename_i hno
    refine absurd ?_ hno
    show (replWorldOwner, key) ∈ base.accessedStorageKeys
    rw [h]
    exact hk

/-- The checked extension both worlds install: `10 + 2592000`, computed without
wrapping. -/
theorem replWorld_extension :
    CheckedHeartbeatExtension replWorldTime replWorldInterval
      replWorldExpiry := by
  constructor
  · unfold replWorldTime replWorldInterval
    change (10 : Nat) + 2592000 < 2 ^ 256
    norm_num
  · decide

/-! ## The retained world

The old pauser holds two assignments at entry, so the decrement leaves one and
`registerAfterSet` takes its retained arm: no expiry moves but the new
pauser's. -/

/-- The old pauser's entry assignment count in the retained world. -/
def replRetainedWorldCount : B256 := 2

/-- The exact body reserve of the retained replacement at this world: `221`
decoder/admin prefix, the found-nonzero kernel walk, three warm staged loads,
two resets and two sets. -/
def replRetainedWorldBodyGas : Nat := 52161

/-- The exact message gas: dispatch prefix plus body reserve, leaving `0`. -/
def replRetainedWorldGas : Nat := 52336

theorem replRetained_bodyGasEq :
    replacementRetainedRegisterBodyGas
        (replWorldSevm replRetainedWorldCount replRetainedWorldGas)
        (replWorldPre replRetainedWorldCount replRetainedWorldGas)
        replWorldTarget replWorldNewPauser replWorldOldPauser
        replRetainedWorldCount replWorldResetCost replWorldResetCost
        gasStorageSet gasStorageSet = replRetainedWorldBodyGas := by
  simp only [replacementRetainedRegisterBodyGas,
    replacementRetainedSetPauserKernelGas, foundSetPauserKernelPrefixGas]
  rw [replWorld_warmCost (replWorld_accessed _ _) replWorld_warmAssignment,
    replWorld_warmCost (replWorld_assignmentPost_accessed _ _)
      replWorld_warmOldCount,
    replWorld_warmCost (replWorld_foundKernelPost_accessed _ _)
      replWorld_warmNewCount]
  norm_num [replRetainedWorldBodyGas, replWorldResetCost, gasStorageSet,
    gasWarmAccess, gasStorageUpdate, gasColdSload]

set_option maxHeartbeats 800000 in
/-- A fully inhabited production-runtime **retained** replacement.  The admin
of `officialParams` calls `registerPauser(7, 11)` on a CircuitBreaker deployed
at address `100` whose target `7` is recorded to pauser `9` with two
assignments, with exactly `52336` gas, at block time `10`, five warm and one
cold storage key.  Every execution premise of the retained arm holds at this
one machine, so the exact compiled run actually happens. -/
theorem replRetainedWorld_run :
    ∃ post,
      Prog.RunCompiledTo
        (replWorldSevm replRetainedWorldCount replRetainedWorldGas)
        (replWorldPre replRetainedWorldCount replRetainedWorldGas)
        (runtime officialParams) (.ok post) ∧
      some (replWorldSevm replRetainedWorldCount
          replRetainedWorldGas).code.toList =
        Prog.compile (runtime officialParams) := by
  rcases replWorld_dataFacts replRetainedWorldCount replRetainedWorldGas with
    ⟨hlength, hselector, hargTarget, hargNew⟩
  rcases registerPauser_runCompiledTo_retainedNonzero officialParams
      (replWorldSevm replRetainedWorldCount replRetainedWorldGas)
      (replWorldPre replRetainedWorldCount replRetainedWorldGas)
      replWorldTarget replWorldNewPauser replWorldOldPauser
      replRetainedWorldCount 0 1 1 replWorldTime replWorldInterval
      replWorldExpiry 0 0 replWorldOldPauser replRetainedWorldCount 0
      replWorldResetCost replWorldResetCost gasStorageSet gasStorageSet 0
      hlength (replWorld_value _ _) hselector (replWorld_codeAddress _ _)
      (replWorld_codeBytes _ _) (replWorld_admin _ _) hargTarget hargNew
      replWorld_targetValid replWorld_newValid replWorld_oldValid
      (by
        rw [replWorld_currentTarget, replWorld_getStorVal]
        exact replWorld_stor_assignment _)
      (by
        rw [replWorld_currentTarget, replWorld_getOrigStorVal]
        exact replWorld_stor_assignment _)
      (replWorld_resetCost (by decide) (by decide))
      (by
        rw [replWorld_currentTarget,
          replWorld_assignmentPost_getStorVal replWorld_assignment_ne_oldCount]
        exact replWorld_stor_oldCount _)
      (by
        rw [replWorld_currentTarget, replWorld_getOrigStorVal]
        exact replWorld_stor_oldCount _)
      (replWorld_resetCost (by decide) (by decide))
      (by
        rw [replWorld_currentTarget,
          replWorld_foundKernelPost_getStorVal
            replWorld_newCount_ne_oldCount.symm replWorld_assignment_ne_newCount]
        exact replWorld_stor_newCount _)
      (by
        rw [replWorld_currentTarget, replWorld_getOrigStorVal]
        exact replWorld_stor_newCount _)
      (by decide) (replWorld_setCost (by decide)) (by decide)
      (by
        rw [replWorld_currentTarget, replWorld_foundNonzeroKernelPost_oldCount]
        decide)
      (replWorld_time _ _)
      (by
        rw [replWorld_currentTarget,
          replWorld_foundNonzeroKernelPost_getStorVal
            replWorld_newCount_ne_interval replWorld_oldCount_ne_interval
            replWorld_assignment_ne_interval]
        exact replWorld_stor_interval _)
      (by
        rw [replWorld_currentTarget,
          replWorld_foundNonzeroKernelPost_accessed]
        exact replWorld_coldInterval)
      (by
        rw [replWorld_currentTarget,
          replWorld_foundNonzeroKernelPost_getStorVal
            replWorld_newCount_ne_newExpiry replWorld_oldCount_ne_newExpiry
            replWorld_assignment_ne_newExpiry]
        exact replWorld_stor_newExpiry _)
      (by
        rw [replWorld_currentTarget, replWorld_getOrigStorVal]
        exact replWorld_stor_newExpiry _)
      (by
        rw [replWorld_currentTarget,
          replWorld_foundNonzeroKernelPost_accessed]
        exact replWorld_warmNewExpiry)
      (replWorld_setCost (by decide)) (by decide) (replWorld_static _ _)
      replWorld_extension with
    ⟨post, hrun, _hgas, _hstore, _hlogs, _hexpiries, hcompile⟩
  have hentry :
      (replWorldPre replRetainedWorldCount replRetainedWorldGas).setMach
        ⟨[], Mem.empty,
          0 + registerPauserDispatchGas +
            replacementRetainedRegisterBodyGas
              (replWorldSevm replRetainedWorldCount replRetainedWorldGas)
              (replWorldPre replRetainedWorldCount replRetainedWorldGas)
              replWorldTarget replWorldNewPauser replWorldOldPauser
              replRetainedWorldCount replWorldResetCost replWorldResetCost
              gasStorageSet gasStorageSet⟩ =
        replWorldPre replRetainedWorldCount replRetainedWorldGas := by
    rw [replRetained_bodyGasEq]
    rfl
  rw [hentry] at hrun
  exact ⟨post, hrun, hcompile⟩

/-! ## The old-last world

The old pauser holds exactly one assignment at entry, so the decrement leaves
zero and `registerAfterSet` takes its old-last arm: the retiring pauser's
heartbeat expiry is cleared, and a zero-payload record is emitted, before the
new pauser's expiry is stored.

Only the entry count differs from the retained world.  Everything the two
share — the state skeleton, the warm key set, the slot separations and the
tower lemmas — is stated once above, parametrically in that count. -/

/-- The old pauser's entry assignment count in the old-last world. -/
def replOldLastWorldCount : B256 := 1

/-- The exact body reserve of the old-last replacement at this world: the
retained figure plus the old-last `finishSetPauser` arm's extra `1417` gas and
its expiry clear. -/
def replOldLastWorldBodyGas : Nat := 56478

/-- The exact message gas: dispatch prefix plus body reserve, leaving `0`. -/
def replOldLastWorldGas : Nat := 56653

/-- The state after the retiring pauser's expiry clear, read at a cell the
clear misses. -/
theorem replWorld_clearPost_getStorVal {oldCount : B256} {gas : Nat}
    {nextCount key : B256}
    (hclear : expirySlot replWorldOldPauser ≠ key)
    (hnewCount : countSlot replWorldNewPauser ≠ key)
    (hcount : countSlot replWorldOldPauser ≠ key)
    (hassignment : assignmentSlot replWorldTarget ≠ key) :
    (temporalSstorePost (replWorldSevm oldCount gas)
      (foundNonzeroKernelPost (replWorldSevm oldCount gas)
        (replWorldPre oldCount gas) replWorldTarget replWorldNewPauser
        replWorldOldPauser oldCount nextCount)
      (expirySlot replWorldOldPauser) 0).getStorVal replWorldOwner key =
      (replWorldStor oldCount).get key := by
  rw [temporalSstorePost_other (replWorldSevm oldCount gas)
      (foundNonzeroKernelPost (replWorldSevm oldCount gas)
        (replWorldPre oldCount gas) replWorldTarget replWorldNewPauser
        replWorldOldPauser oldCount nextCount)
      (expirySlot replWorldOldPauser) 0 replWorldOwner key
      (by
        intro hpair
        exact hclear (Prod.mk.injEq .. ▸ hpair).2.symm),
    replWorld_foundNonzeroKernelPost_getStorVal hnewCount hcount hassignment]

theorem replOldLast_bodyGasEq :
    replacementOldLastRegisterBodyGas
        (replWorldSevm replOldLastWorldCount replOldLastWorldGas)
        (replWorldPre replOldLastWorldCount replOldLastWorldGas)
        replWorldTarget replWorldNewPauser replWorldOldPauser
        replOldLastWorldCount replWorldResetCost replWorldResetCost
        gasStorageSet replWorldResetCost gasStorageSet =
      replOldLastWorldBodyGas := by
  simp only [replacementOldLastRegisterBodyGas,
    replacementOldLastSetPauserKernelGas, foundSetPauserKernelPrefixGas]
  rw [replWorld_warmCost (replWorld_accessed _ _) replWorld_warmAssignment,
    replWorld_warmCost (replWorld_assignmentPost_accessed _ _)
      replWorld_warmOldCount,
    replWorld_warmCost (replWorld_foundKernelPost_accessed _ _)
      replWorld_warmNewCount]
  norm_num [replOldLastWorldBodyGas, replWorldResetCost, gasStorageSet,
    gasWarmAccess, gasStorageUpdate, gasColdSload]

set_option maxHeartbeats 800000 in
/-- A fully inhabited production-runtime **old-last** replacement.  The admin
of `officialParams` calls `registerPauser(7, 11)` on a CircuitBreaker deployed
at address `100` whose target `7` is recorded to pauser `9` with its only
assignment and a live heartbeat expiry, with exactly `56653` gas, at block time
`10`, five warm and one cold storage key.  Every execution premise of the
old-last arm holds at this one machine, so the exact compiled run actually
happens. -/
theorem replOldLastWorld_run :
    ∃ post,
      Prog.RunCompiledTo
        (replWorldSevm replOldLastWorldCount replOldLastWorldGas)
        (replWorldPre replOldLastWorldCount replOldLastWorldGas)
        (runtime officialParams) (.ok post) ∧
      some (replWorldSevm replOldLastWorldCount
          replOldLastWorldGas).code.toList =
        Prog.compile (runtime officialParams) := by
  rcases replWorld_dataFacts replOldLastWorldCount replOldLastWorldGas with
    ⟨hlength, hselector, hargTarget, hargNew⟩
  rcases registerPauser_runCompiledTo_oldLastNonzero officialParams
      (replWorldSevm replOldLastWorldCount replOldLastWorldGas)
      (replWorldPre replOldLastWorldCount replOldLastWorldGas)
      replWorldTarget replWorldNewPauser replWorldOldPauser
      replOldLastWorldCount 0 1 replWorldOldExpiry replWorldOldExpiry
      replWorldTime replWorldInterval replWorldExpiry 0 0
      replWorldOldPauser replOldLastWorldCount 0
      replWorldResetCost replWorldResetCost gasStorageSet replWorldResetCost
      gasStorageSet 0
      hlength (replWorld_value _ _) hselector (replWorld_codeAddress _ _)
      (replWorld_codeBytes _ _) (replWorld_admin _ _) hargTarget hargNew
      replWorld_targetValid replWorld_newValid replWorld_oldValid
      (by
        rw [replWorld_currentTarget, replWorld_getStorVal]
        exact replWorld_stor_assignment _)
      (by
        rw [replWorld_currentTarget, replWorld_getOrigStorVal]
        exact replWorld_stor_assignment _)
      (replWorld_resetCost (by decide) (by decide))
      (by
        rw [replWorld_currentTarget,
          replWorld_assignmentPost_getStorVal replWorld_assignment_ne_oldCount]
        exact replWorld_stor_oldCount _)
      (by
        rw [replWorld_currentTarget, replWorld_getOrigStorVal]
        exact replWorld_stor_oldCount _)
      (replWorld_resetCost (by decide) (by decide))
      (by
        rw [replWorld_currentTarget,
          replWorld_foundKernelPost_getStorVal
            replWorld_newCount_ne_oldCount.symm replWorld_assignment_ne_newCount]
        exact replWorld_stor_newCount _)
      (by
        rw [replWorld_currentTarget, replWorld_getOrigStorVal]
        exact replWorld_stor_newCount _)
      (by decide) (replWorld_setCost (by decide))
      (by
        rw [replWorld_currentTarget, replWorld_foundNonzeroKernelPost_oldCount]
        decide)
      (by
        rw [replWorld_currentTarget,
          replWorld_foundNonzeroKernelPost_getStorVal
            replWorld_newCount_ne_oldExpiry replWorld_oldCount_ne_oldExpiry
            replWorld_assignment_ne_oldExpiry]
        exact replWorld_stor_oldExpiry _)
      (by
        rw [replWorld_currentTarget, replWorld_getOrigStorVal]
        exact replWorld_stor_oldExpiry _)
      (by
        rw [replWorld_currentTarget,
          replWorld_foundNonzeroKernelPost_accessed]
        exact replWorld_warmOldExpiry)
      (replWorld_resetCost (by decide) (by decide)) (replWorld_time _ _)
      (by
        rw [replWorld_currentTarget,
          replWorld_clearPost_getStorVal replWorld_oldExpiry_ne_interval
            replWorld_newCount_ne_interval replWorld_oldCount_ne_interval
            replWorld_assignment_ne_interval]
        exact replWorld_stor_interval _)
      (by
        rw [replWorld_currentTarget,
          replWorld_foundNonzeroKernelPost_accessed]
        exact replWorld_coldInterval)
      (by
        rw [replWorld_currentTarget,
          replWorld_clearPost_getStorVal
            replWorld_newExpiry_ne_oldExpiry.symm
            replWorld_newCount_ne_newExpiry replWorld_oldCount_ne_newExpiry
            replWorld_assignment_ne_newExpiry]
        exact replWorld_stor_newExpiry _)
      (by
        rw [replWorld_currentTarget, replWorld_getOrigStorVal]
        exact replWorld_stor_newExpiry _)
      (by
        rw [replWorld_currentTarget,
          replWorld_foundNonzeroKernelPost_accessed]
        exact replWorld_warmNewExpiry)
      (replWorld_setCost (by decide)) (by decide) (replWorld_static _ _)
      replWorld_extension with
    ⟨post, hrun, _hgas, _hstore, _hlogs, _hold, _hexpiries, hcompile⟩
  have hentry :
      (replWorldPre replOldLastWorldCount replOldLastWorldGas).setMach
        ⟨[], Mem.empty,
          0 + registerPauserDispatchGas +
            replacementOldLastRegisterBodyGas
              (replWorldSevm replOldLastWorldCount replOldLastWorldGas)
              (replWorldPre replOldLastWorldCount replOldLastWorldGas)
              replWorldTarget replWorldNewPauser replWorldOldPauser
              replOldLastWorldCount replWorldResetCost replWorldResetCost
              gasStorageSet replWorldResetCost gasStorageSet⟩ =
        replWorldPre replOldLastWorldCount replOldLastWorldGas := by
    rw [replOldLast_bodyGasEq]
    rfl
  rw [hentry] at hrun
  exact ⟨post, hrun, hcompile⟩

end Blanc.LidoCircuitBreaker
