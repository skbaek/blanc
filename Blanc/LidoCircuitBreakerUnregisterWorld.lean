import Blanc.LidoCircuitBreakerUnregisterRegistration

/-!
A fully instantiated admin-**unregistration** world for the Lido
CircuitBreaker.

`Blanc/LidoCircuitBreakerUnregisterRegistration.lean` states the
unregistration chronology against an abstract message, abstract entry storage,
abstract original words, abstract `SSTORE` value costs and abstract
accessed-key warmth.  Nothing there exhibits a single machine at which all of
those premises hold at once, so the chronology is certified in one direction
only: *if* such a world exists, the run happens.

This leaf closes that gap with one concrete closed world — concrete admin
caller, contract owner, target, storage, warm accessed key set and gas — and
discharges every premise of `registerPauser_runCompiledTo_foundZeroOldLast` at
it.  The admin calls `registerPauser(7, 0)` on a CircuitBreaker deployed at
address `100` whose Registry holds exactly one entry, target `7` assigned to
pauser `9`.  That entry is the array's last, and pauser `9` holds no other
assignment, so the call removes the entry *and* retires the pauser: its
heartbeat expiry cell is cleared and a zero-payload `HeartbeatUpdated(9)`
follows the `PauserSet(7, 9, 0)` record.

**Unlike `Blanc/LidoCircuitBreakerReplacementWorld.lean`, this world is
Registry-well-formed.**  That file documents its own self-limitation in its
header: its entry storage records target `7` as assigned to pauser `9` while
leaving the array length and the target's reverse index at zero, which no
`registerPauser` call could ever produce, and no `RegistryWitness` appears
there.  Here `unregWorldStor_witness` holds: array length `1`, array slot `1`
carrying target `7`, the target's assignment and one-based index, pauser `9`'s
assignment count, and zero everywhere else the projections read.  The
chronology consumes that witness, and hands back the corresponding witness for
the post-Registry, which is the *empty* entry list.

Read that at its actual width.  `RegistryWitness` is the model-side projection
relation: it says the entry storage is the image of the one-entry list under
the Registry's own slot layout.  It is **not** a claim that this entry state is
reachable from a genesis-consistent history — no deployment, no constructor and
no prior transaction is exhibited anywhere below — and it should not be read as
one.  What the world does establish is a genuine, gas-exact execution of the
production runtime from a concrete `Msg`, which is everything `Attainable` and
`Blanc/LidoCircuitBreakerAttainment.lean` consume.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune

/-! ## The concrete world -/

/-- The CircuitBreaker deployment: the contract account that owns the Registry
storage and carries the generated runtime. -/
def unregWorldOwner : Adr := Nat.toAdr 100

/-- The admin caller.  `officialParams.admin` as an address. -/
def unregWorldAdmin : Adr :=
  Nat.toAdr 0x3e40D73EB977Dc6a537aF587D48316feE66E9C8c

/-- The pausable target being unregistered. -/
def unregWorldTarget : B256 := 7

/-- The pauser the target is recorded to at entry, and which this call
retires: it holds exactly one assignment, so the decrement leaves zero. -/
def unregWorldPauser : B256 := 9

/-- Block timestamp at the unregistering call.  The unregistration path reads
no clock, so this value is inert; it is fixed only so the world is closed. -/
def unregWorldTime : B256 := 10

/-- The configured heartbeat interval, sitting in the config region.  The
unregistration path never reads it — it clears an expiry rather than extending
one — so it is present only because a deployed CircuitBreaker has one. -/
def unregWorldInterval : B256 := 2592000

/-- The retiring pauser's heartbeat expiry at entry.  It has to be nonzero:
the chronology's stipend premise needs the expiry clear to carry a full
nonzero-to-zero reset charge. -/
def unregWorldOldExpiry : B256 := 100

/-- The deployed account storage: the configured heartbeat interval plus the
five Registry cells that record the single entry `(7, 9)` — array length `1`,
array slot `1`, the target's assignment and one-based index, and the pauser's
assignment count — together with the pauser's heartbeat expiry. -/
def unregWorldStor : Stor :=
  ((((((Stor.empty.set heartbeatIntervalSlot unregWorldInterval).set
    arrayLengthSlot 1).set
    (arrayEntrySlot 1) unregWorldTarget).set
    (assignmentSlot unregWorldTarget) unregWorldPauser).set
    (indexSlot unregWorldTarget) 1).set
    (countSlot unregWorldPauser) 1).set
    (expirySlot unregWorldPauser) unregWorldOldExpiry

/-- The installed generated runtime bytes. -/
def unregWorldCode : ByteArray :=
  ByteArray.mk (lidoCircuitBreakerCode officialParams).toArray

/-- World state: the CircuitBreaker account alone. -/
def unregWorldState : State :=
  State.set (.empty : State) unregWorldOwner
    { Acct.nil with
      stor := unregWorldStor
      code := unregWorldCode }

/-- The warm accessed-storage-key set at message entry: every cell the
unregistration reads or writes — the target's assignment slot and one-based
index slot, the retiring pauser's count and expiry slots, the array length
slot and the array's last entry slot.

The configured-interval slot is deliberately absent, and stays cold: this
chronology never touches it.  Because every *read* key is warm, each
`temporalSloadBase` layer of the chronology's post-state tower is the identity,
so both staged loads are charged `gasWarmAccess` and no `Std.HashSet` is ever
decided. -/
def unregWorldKeys : Std.HashSet (Adr × B256) :=
  (((((Std.HashSet.emptyWithCapacity.insert
    (unregWorldOwner, assignmentSlot unregWorldTarget)).insert
    (unregWorldOwner, indexSlot unregWorldTarget)).insert
    (unregWorldOwner, arrayLengthSlot)).insert
    (unregWorldOwner, arrayEntrySlot 1)).insert
    (unregWorldOwner, countSlot unregWorldPauser)).insert
    (unregWorldOwner, expirySlot unregWorldPauser)

/-! ## Payload bounds and slot separation

Every slot this world touches is `slot region payload` for a region below `16`
and a payload below `2 ^ 252`, so `slot_ne_of_region_ne` separates any two of
them whose regions differ and `slot_injective_payload` separates the two array
slots and the per-address slots, whose regions do not. -/

private theorem unregWorld_payload_zero : (0 : B256).toNat < 2 ^ 252 := by
  change (0 : Nat) < 2 ^ 252
  norm_num

private theorem unregWorld_payload_one : (1 : B256).toNat < 2 ^ 252 := by
  change (1 : Nat) < 2 ^ 252
  norm_num

private theorem unregWorld_payload_target :
    unregWorldTarget.toNat < 2 ^ 252 := by
  unfold unregWorldTarget
  change (7 : Nat) < 2 ^ 252
  norm_num

private theorem unregWorld_payload_pauser :
    unregWorldPauser.toNat < 2 ^ 252 := by
  unfold unregWorldPauser
  change (9 : Nat) < 2 ^ 252
  norm_num

private theorem unregWorld_payload_of_canonical {w : B256}
    (h : canonicalAddress w) : w.toNat < 2 ^ 252 := by
  unfold canonicalAddress at h
  exact lt_trans h (by norm_num)

theorem unregWorld_targetValid : nonzeroCanonicalAddress unregWorldTarget := by
  refine ⟨by decide, ?_⟩
  unfold canonicalAddress unregWorldTarget
  change (7 : Nat) < 2 ^ 160
  norm_num

theorem unregWorld_pauserValid : nonzeroCanonicalAddress unregWorldPauser := by
  refine ⟨by decide, ?_⟩
  unfold canonicalAddress unregWorldPauser
  change (9 : Nat) < 2 ^ 160
  norm_num

/-! ### The fifteen separations the entry storage is read through

The seven written cells are listed innermost-first in `unregWorldStor`, so
reading the `n`-th from the outside peels the `n - 1` cells outside it. -/

theorem unregWorld_expiry_ne_count :
    expirySlot unregWorldPauser ≠ countSlot unregWorldPauser :=
  slot_ne_of_region_ne (by norm_num [expiryRegion]) (by norm_num [countRegion])
    unregWorld_payload_pauser unregWorld_payload_pauser
    (by norm_num [expiryRegion, countRegion])

theorem unregWorld_expiry_ne_index :
    expirySlot unregWorldPauser ≠ indexSlot unregWorldTarget :=
  slot_ne_of_region_ne (by norm_num [expiryRegion]) (by norm_num [indexRegion])
    unregWorld_payload_pauser unregWorld_payload_target
    (by norm_num [expiryRegion, indexRegion])

theorem unregWorld_expiry_ne_assignment :
    expirySlot unregWorldPauser ≠ assignmentSlot unregWorldTarget :=
  slot_ne_of_region_ne (by norm_num [expiryRegion])
    (by norm_num [assignmentRegion]) unregWorld_payload_pauser
    unregWorld_payload_target (by norm_num [expiryRegion, assignmentRegion])

theorem unregWorld_expiry_ne_entry :
    expirySlot unregWorldPauser ≠ arrayEntrySlot 1 :=
  slot_ne_of_region_ne (by norm_num [expiryRegion]) (by norm_num [arrayRegion])
    unregWorld_payload_pauser unregWorld_payload_one
    (by norm_num [expiryRegion, arrayRegion])

theorem unregWorld_expiry_ne_length :
    expirySlot unregWorldPauser ≠ arrayLengthSlot :=
  slot_ne_of_region_ne (by norm_num [expiryRegion]) (by norm_num [arrayRegion])
    unregWorld_payload_pauser unregWorld_payload_zero
    (by norm_num [expiryRegion, arrayRegion])

theorem unregWorld_expiry_ne_interval :
    expirySlot unregWorldPauser ≠ heartbeatIntervalSlot :=
  slot_ne_of_region_ne (by norm_num [expiryRegion])
    (by norm_num [configRegion]) unregWorld_payload_pauser
    unregWorld_payload_one (by norm_num [expiryRegion, configRegion])

theorem unregWorld_count_ne_index :
    countSlot unregWorldPauser ≠ indexSlot unregWorldTarget :=
  slot_ne_of_region_ne (by norm_num [countRegion]) (by norm_num [indexRegion])
    unregWorld_payload_pauser unregWorld_payload_target
    (by norm_num [countRegion, indexRegion])

theorem unregWorld_count_ne_assignment :
    countSlot unregWorldPauser ≠ assignmentSlot unregWorldTarget :=
  slot_ne_of_region_ne (by norm_num [countRegion])
    (by norm_num [assignmentRegion]) unregWorld_payload_pauser
    unregWorld_payload_target (by norm_num [countRegion, assignmentRegion])

theorem unregWorld_count_ne_entry :
    countSlot unregWorldPauser ≠ arrayEntrySlot 1 :=
  slot_ne_of_region_ne (by norm_num [countRegion]) (by norm_num [arrayRegion])
    unregWorld_payload_pauser unregWorld_payload_one
    (by norm_num [countRegion, arrayRegion])

theorem unregWorld_count_ne_length :
    countSlot unregWorldPauser ≠ arrayLengthSlot :=
  slot_ne_of_region_ne (by norm_num [countRegion]) (by norm_num [arrayRegion])
    unregWorld_payload_pauser unregWorld_payload_zero
    (by norm_num [countRegion, arrayRegion])

theorem unregWorld_index_ne_assignment :
    indexSlot unregWorldTarget ≠ assignmentSlot unregWorldTarget :=
  slot_ne_of_region_ne (by norm_num [indexRegion])
    (by norm_num [assignmentRegion]) unregWorld_payload_target
    unregWorld_payload_target (by norm_num [indexRegion, assignmentRegion])

theorem unregWorld_index_ne_entry :
    indexSlot unregWorldTarget ≠ arrayEntrySlot 1 :=
  slot_ne_of_region_ne (by norm_num [indexRegion]) (by norm_num [arrayRegion])
    unregWorld_payload_target unregWorld_payload_one
    (by norm_num [indexRegion, arrayRegion])

theorem unregWorld_index_ne_length :
    indexSlot unregWorldTarget ≠ arrayLengthSlot :=
  slot_ne_of_region_ne (by norm_num [indexRegion]) (by norm_num [arrayRegion])
    unregWorld_payload_target unregWorld_payload_zero
    (by norm_num [indexRegion, arrayRegion])

theorem unregWorld_assignment_ne_entry :
    assignmentSlot unregWorldTarget ≠ arrayEntrySlot 1 :=
  slot_ne_of_region_ne (by norm_num [assignmentRegion])
    (by norm_num [arrayRegion]) unregWorld_payload_target
    unregWorld_payload_one (by norm_num [assignmentRegion, arrayRegion])

theorem unregWorld_assignment_ne_length :
    assignmentSlot unregWorldTarget ≠ arrayLengthSlot :=
  slot_ne_of_region_ne (by norm_num [assignmentRegion])
    (by norm_num [arrayRegion]) unregWorld_payload_target
    unregWorld_payload_zero (by norm_num [assignmentRegion, arrayRegion])

/-- The array's length cell and its first entry cell share the array region, so
only their payloads separate them. -/
theorem unregWorld_entry_ne_length : arrayEntrySlot 1 ≠ arrayLengthSlot := by
  intro heq
  exact absurd (slot_injective_payload (by norm_num [arrayRegion])
    unregWorld_payload_one unregWorld_payload_zero heq) (by decide)

/-! ## The entry storage, read cell by cell -/

/-- Every key outside the seven cells the deployment writes reads back zero. -/
private theorem unregWorld_stor_zero {key : B256}
    (hinterval : heartbeatIntervalSlot ≠ key)
    (hlength : arrayLengthSlot ≠ key)
    (hentry : arrayEntrySlot 1 ≠ key)
    (hassignment : assignmentSlot unregWorldTarget ≠ key)
    (hindex : indexSlot unregWorldTarget ≠ key)
    (hcount : countSlot unregWorldPauser ≠ key)
    (hexpiry : expirySlot unregWorldPauser ≠ key) :
    unregWorldStor.get key = 0 := by
  rw [unregWorldStor, Stor.get_set_ne _ hexpiry, Stor.get_set_ne _ hcount,
    Stor.get_set_ne _ hindex, Stor.get_set_ne _ hassignment,
    Stor.get_set_ne _ hentry, Stor.get_set_ne _ hlength,
    Stor.get_set_ne _ hinterval]
  simp [Stor.get, Stor.empty]

theorem unregWorld_stor_expiry :
    unregWorldStor.get (expirySlot unregWorldPauser) =
      unregWorldOldExpiry := by
  rw [unregWorldStor, Stor.get_set_self]

theorem unregWorld_stor_count :
    unregWorldStor.get (countSlot unregWorldPauser) = 1 := by
  rw [unregWorldStor, Stor.get_set_ne _ unregWorld_expiry_ne_count,
    Stor.get_set_self]

theorem unregWorld_stor_index :
    unregWorldStor.get (indexSlot unregWorldTarget) = 1 := by
  rw [unregWorldStor, Stor.get_set_ne _ unregWorld_expiry_ne_index,
    Stor.get_set_ne _ unregWorld_count_ne_index, Stor.get_set_self]

theorem unregWorld_stor_assignment :
    unregWorldStor.get (assignmentSlot unregWorldTarget) =
      unregWorldPauser := by
  rw [unregWorldStor, Stor.get_set_ne _ unregWorld_expiry_ne_assignment,
    Stor.get_set_ne _ unregWorld_count_ne_assignment,
    Stor.get_set_ne _ unregWorld_index_ne_assignment, Stor.get_set_self]

theorem unregWorld_stor_entry :
    unregWorldStor.get (arrayEntrySlot 1) = unregWorldTarget := by
  rw [unregWorldStor, Stor.get_set_ne _ unregWorld_expiry_ne_entry,
    Stor.get_set_ne _ unregWorld_count_ne_entry,
    Stor.get_set_ne _ unregWorld_index_ne_entry,
    Stor.get_set_ne _ unregWorld_assignment_ne_entry, Stor.get_set_self]

theorem unregWorld_stor_length : unregWorldStor.get arrayLengthSlot = 1 := by
  rw [unregWorldStor, Stor.get_set_ne _ unregWorld_expiry_ne_length,
    Stor.get_set_ne _ unregWorld_count_ne_length,
    Stor.get_set_ne _ unregWorld_index_ne_length,
    Stor.get_set_ne _ unregWorld_assignment_ne_length,
    Stor.get_set_ne _ unregWorld_entry_ne_length, Stor.get_set_self]

/-- Every canonical target other than `7` is unassigned. -/
theorem unregWorld_stor_assignment_other {t : B256}
    (hcanonical : canonicalAddress t) (hne : t ≠ unregWorldTarget) :
    unregWorldStor.get (assignmentSlot t) = 0 := by
  have hp : t.toNat < 2 ^ 252 := unregWorld_payload_of_canonical hcanonical
  refine unregWorld_stor_zero ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact slot_ne_of_region_ne (by norm_num [configRegion])
      (by norm_num [assignmentRegion]) unregWorld_payload_one hp
      (by norm_num [configRegion, assignmentRegion])
  · exact slot_ne_of_region_ne (by norm_num [arrayRegion])
      (by norm_num [assignmentRegion]) unregWorld_payload_zero hp
      (by norm_num [arrayRegion, assignmentRegion])
  · exact slot_ne_of_region_ne (by norm_num [arrayRegion])
      (by norm_num [assignmentRegion]) unregWorld_payload_one hp
      (by norm_num [arrayRegion, assignmentRegion])
  · intro heq
    exact hne (slot_injective_payload (by norm_num [assignmentRegion])
      unregWorld_payload_target hp heq).symm
  · exact slot_ne_of_region_ne (by norm_num [indexRegion])
      (by norm_num [assignmentRegion]) unregWorld_payload_target hp
      (by norm_num [indexRegion, assignmentRegion])
  · exact slot_ne_of_region_ne (by norm_num [countRegion])
      (by norm_num [assignmentRegion]) unregWorld_payload_pauser hp
      (by norm_num [countRegion, assignmentRegion])
  · exact slot_ne_of_region_ne (by norm_num [expiryRegion])
      (by norm_num [assignmentRegion]) unregWorld_payload_pauser hp
      (by norm_num [expiryRegion, assignmentRegion])

/-- Every canonical target other than `7` has a zero reverse index. -/
theorem unregWorld_stor_index_other {t : B256}
    (hcanonical : canonicalAddress t) (hne : t ≠ unregWorldTarget) :
    unregWorldStor.get (indexSlot t) = 0 := by
  have hp : t.toNat < 2 ^ 252 := unregWorld_payload_of_canonical hcanonical
  refine unregWorld_stor_zero ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact slot_ne_of_region_ne (by norm_num [configRegion])
      (by norm_num [indexRegion]) unregWorld_payload_one hp
      (by norm_num [configRegion, indexRegion])
  · exact slot_ne_of_region_ne (by norm_num [arrayRegion])
      (by norm_num [indexRegion]) unregWorld_payload_zero hp
      (by norm_num [arrayRegion, indexRegion])
  · exact slot_ne_of_region_ne (by norm_num [arrayRegion])
      (by norm_num [indexRegion]) unregWorld_payload_one hp
      (by norm_num [arrayRegion, indexRegion])
  · exact slot_ne_of_region_ne (by norm_num [assignmentRegion])
      (by norm_num [indexRegion]) unregWorld_payload_target hp
      (by norm_num [assignmentRegion, indexRegion])
  · intro heq
    exact hne (slot_injective_payload (by norm_num [indexRegion])
      unregWorld_payload_target hp heq).symm
  · exact slot_ne_of_region_ne (by norm_num [countRegion])
      (by norm_num [indexRegion]) unregWorld_payload_pauser hp
      (by norm_num [countRegion, indexRegion])
  · exact slot_ne_of_region_ne (by norm_num [expiryRegion])
      (by norm_num [indexRegion]) unregWorld_payload_pauser hp
      (by norm_num [expiryRegion, indexRegion])

/-- Every canonical pauser other than `9` holds no assignment. -/
theorem unregWorld_stor_count_other {p : B256}
    (hcanonical : canonicalAddress p) (hne : p ≠ unregWorldPauser) :
    unregWorldStor.get (countSlot p) = 0 := by
  have hp : p.toNat < 2 ^ 252 := unregWorld_payload_of_canonical hcanonical
  refine unregWorld_stor_zero ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact slot_ne_of_region_ne (by norm_num [configRegion])
      (by norm_num [countRegion]) unregWorld_payload_one hp
      (by norm_num [configRegion, countRegion])
  · exact slot_ne_of_region_ne (by norm_num [arrayRegion])
      (by norm_num [countRegion]) unregWorld_payload_zero hp
      (by norm_num [arrayRegion, countRegion])
  · exact slot_ne_of_region_ne (by norm_num [arrayRegion])
      (by norm_num [countRegion]) unregWorld_payload_one hp
      (by norm_num [arrayRegion, countRegion])
  · exact slot_ne_of_region_ne (by norm_num [assignmentRegion])
      (by norm_num [countRegion]) unregWorld_payload_target hp
      (by norm_num [assignmentRegion, countRegion])
  · exact slot_ne_of_region_ne (by norm_num [indexRegion])
      (by norm_num [countRegion]) unregWorld_payload_target hp
      (by norm_num [indexRegion, countRegion])
  · intro heq
    exact hne (slot_injective_payload (by norm_num [countRegion])
      unregWorld_payload_pauser hp heq).symm
  · exact slot_ne_of_region_ne (by norm_num [expiryRegion])
      (by norm_num [countRegion]) unregWorld_payload_pauser hp
      (by norm_num [expiryRegion, countRegion])

/-- Every canonical pauser other than `9` has a zero heartbeat expiry. -/
theorem unregWorld_stor_expiry_other {p : B256}
    (hcanonical : canonicalAddress p) (hne : p ≠ unregWorldPauser) :
    unregWorldStor.get (expirySlot p) = 0 := by
  have hp : p.toNat < 2 ^ 252 := unregWorld_payload_of_canonical hcanonical
  refine unregWorld_stor_zero ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact slot_ne_of_region_ne (by norm_num [configRegion])
      (by norm_num [expiryRegion]) unregWorld_payload_one hp
      (by norm_num [configRegion, expiryRegion])
  · exact slot_ne_of_region_ne (by norm_num [arrayRegion])
      (by norm_num [expiryRegion]) unregWorld_payload_zero hp
      (by norm_num [arrayRegion, expiryRegion])
  · exact slot_ne_of_region_ne (by norm_num [arrayRegion])
      (by norm_num [expiryRegion]) unregWorld_payload_one hp
      (by norm_num [arrayRegion, expiryRegion])
  · exact slot_ne_of_region_ne (by norm_num [assignmentRegion])
      (by norm_num [expiryRegion]) unregWorld_payload_target hp
      (by norm_num [assignmentRegion, expiryRegion])
  · exact slot_ne_of_region_ne (by norm_num [indexRegion])
      (by norm_num [expiryRegion]) unregWorld_payload_target hp
      (by norm_num [indexRegion, expiryRegion])
  · exact slot_ne_of_region_ne (by norm_num [countRegion])
      (by norm_num [expiryRegion]) unregWorld_payload_pauser hp
      (by norm_num [countRegion, expiryRegion])
  · intro heq
    exact hne (slot_injective_payload (by norm_num [expiryRegion])
      unregWorld_payload_pauser hp heq).symm

/-! ## The Registry witness

The deployed storage is the image of the one-entry list `[(7, 9)]` under the
Registry's slot layout: length `1`, array slot `1` carrying `7`, `7`'s
assignment `9` and one-based index `1`, `9`'s count `1`, and zero at every
other projected cell. -/

private theorem unregWorld_toB256_one : Nat.toB256 1 = (1 : B256) := by decide

private theorem unregWorld_toB256_zero : Nat.toB256 0 = (0 : B256) := by decide

theorem unregWorldStor_witness :
    RegistryWitness (logicalStorageOfStor unregWorldStor)
      [(unregWorldTarget, unregWorldPauser)] := by
  refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro entry member
    rw [List.mem_singleton] at member
    subst member
    exact unregWorld_targetValid
  · intro entry member
    rw [List.mem_singleton] at member
    subst member
    exact unregWorld_pauserValid
  · show unregWorldStor.get arrayLengthSlot = Nat.toB256 1
    rw [unregWorld_stor_length, unregWorld_toB256_one]
  · intro index bound
    have hzero : index = 0 := by
      simp only [List.length_singleton] at bound
      omega
    subst hzero
    show unregWorldStor.get (arrayEntrySlot (Nat.toB256 1)) = unregWorldTarget
    rw [unregWorld_toB256_one, unregWorld_stor_entry]
  · intro t canonical
    show unregWorldStor.get (assignmentSlot t) =
      assignmentAt [(unregWorldTarget, unregWorldPauser)] t
    by_cases ht : t = unregWorldTarget
    · subst ht
      rw [unregWorld_stor_assignment]
      simp [assignmentAt]
    · rw [unregWorld_stor_assignment_other canonical ht]
      have hne : unregWorldTarget ≠ t := fun h => ht h.symm
      simp [assignmentAt, hne]
  · intro t canonical
    show unregWorldStor.get (indexSlot t) =
      Nat.toB256 (oneBasedIndexAt [(unregWorldTarget, unregWorldPauser)] t)
    by_cases ht : t = unregWorldTarget
    · subst ht
      rw [unregWorld_stor_index]
      simp only [oneBasedIndexAt]
      exact unregWorld_toB256_one.symm
    · rw [unregWorld_stor_index_other canonical ht]
      have hne : unregWorldTarget ≠ t := fun h => ht h.symm
      simp only [oneBasedIndexAt, if_neg hne]
      exact unregWorld_toB256_zero.symm
  · intro p canonical
    show unregWorldStor.get (countSlot p) =
      Nat.toB256 (assignmentCount [(unregWorldTarget, unregWorldPauser)] p)
    by_cases hp : p = unregWorldPauser
    · subst hp
      rw [unregWorld_stor_count]
      simp only [assignmentCount]
      exact unregWorld_toB256_one.symm
    · rw [unregWorld_stor_count_other canonical hp]
      have hne : unregWorldPauser ≠ p := fun h => hp h.symm
      simp only [assignmentCount, if_neg hne]
      exact unregWorld_toB256_zero.symm
  · show unregWorldStor.get (countSlot 0) = 0
    refine unregWorld_stor_count_other ?_ (by decide)
    unfold canonicalAddress
    change (0 : Nat) < 2 ^ 160
    norm_num

/-! ## Gas

The four writes that clear a nonzero cell — the target's assignment, the
pauser's count, the array's last entry and the target's index — plus the
length restore and the retiring pauser's expiry clear each carry a
nonzero-to-nonzero reset charge.  The array hole-fill and the moved-index
repair write back the word already there, so each is charged `gasWarmAccess`.
Both staged loads are warm.  The whole reserve is therefore a closed numeral in
the world's own data, and never mentions the message whose `gas` field it
fills. -/

/-- The value charge of a nonzero-to-nonzero reset, above the warmth charge the
key already carries. -/
def unregWorldResetCost : Nat := gasStorageUpdate - gasColdSload

private theorem unregWorld_resetCost {orig new : B256} (hnew : orig ≠ new)
    (hzero : ¬ orig = 0) :
    sstoreValueCost orig orig new = unregWorldResetCost := by
  rw [sstoreValueCost, if_pos ⟨rfl, hnew⟩, if_neg hzero, unregWorldResetCost]

private theorem unregWorld_noopCost {orig cur : B256} :
    sstoreValueCost orig cur cur = gasWarmAccess := by
  rw [sstoreValueCost, if_neg (by simp)]

/-- The exact body reserve of the retiring unregistration at this world: `221`
decoder/admin prefix and `21931` of kernel walk, staged loads and value
charges. -/
def unregWorldBodyGas : Nat := 22152

/-- The exact message gas: dispatch prefix plus body reserve, leaving `0`. -/
def unregWorldGas : Nat := 22327

theorem unregWorldGas_split :
    unregWorldGas = registerPauserDispatchGas + unregWorldBodyGas := by
  norm_num [unregWorldGas, unregWorldBodyGas, registerPauserDispatchGas]

/-! ## The message -/

/-- The concrete admin `registerPauser(7, 0)` call: an unregistration of
target `7`. -/
def unregWorldMsg : Msg :=
  { (default : Msg) with
    benv :=
      { (default : Benv) with
        state := unregWorldState
        stat :=
          { (default : BenvStat) with
            origState := unregWorldState
            time := unregWorldTime } }
    tenv := default
    caller := unregWorldAdmin
    target := some unregWorldOwner
    currentTarget := unregWorldOwner
    gas := unregWorldGas
    value := 0
    data := registerPauserCalldata unregWorldTarget 0
    codeAddress := some unregWorldOwner
    code := unregWorldCode
    depth := 0
    shouldTransferValue := false
    isStatic := false
    accessedAddresses := .emptyWithCapacity
    accessedStorageKeys := unregWorldKeys
    disablePrecompiles := false }

/-- The message's symbolic half. -/
def unregWorldSevm : Sevm := initSevm unregWorldMsg

/-- The message's dynamic half at entry: the prestate the run starts from. -/
def unregWorldPre : Devm := initDevm unregWorldMsg

/-! ## Frame-shape facts

Everything the chronology asks about the message frame itself. -/

private theorem unregWorld_byteArray_ofList_toList (bs : Bytes) :
    (ByteArray.mk bs.toArray).toList = bs := by
  rw [ByteArray.toList_eq_toList_data]

theorem unregWorld_currentTarget :
    unregWorldSevm.currentTarget = unregWorldOwner := rfl

theorem unregWorld_value : unregWorldSevm.value = 0 := rfl

theorem unregWorld_static : unregWorldSevm.isStatic = false := rfl

theorem unregWorld_codeAddress :
    unregWorldSevm.codeAddress = some unregWorldOwner := rfl

theorem unregWorld_codeAddress_currentTarget :
    unregWorldSevm.codeAddress = some unregWorldSevm.currentTarget := rfl

theorem unregWorld_time : unregWorldSevm.benvStat.time = unregWorldTime := rfl

theorem unregWorld_admin :
    unregWorldSevm.caller.toB256 = officialParams.admin := rfl

theorem unregWorld_memory : unregWorldPre.memory = Mem.empty := rfl

theorem unregWorld_logs : unregWorldPre.logs = [] := rfl

theorem unregWorld_codeBytes :
    unregWorldSevm.code.toList = lidoCircuitBreakerCode officialParams := by
  simpa only [unregWorldSevm, unregWorldMsg, initSevm, unregWorldCode] using
    unregWorld_byteArray_ofList_toList (lidoCircuitBreakerCode officialParams)

/-- The message frame really enters the code frame this world is about: the
CircuitBreaker address is not a precompile, and the call transfers no value. -/
theorem unregWorld_frameEntry :
    (Frame.ofCall unregWorldMsg).enter =
      .run ⟨0, unregWorldSevm, unregWorldPre⟩ := rfl

theorem unregWorld_data :
    unregWorldSevm.data = registerPauserCalldata unregWorldTarget 0 := rfl

/-! ### The same facts at the `Msg` itself

The message-altitude settlement theorem phrases its frame premises on
`unregWorldMsg` rather than on `initSevm unregWorldMsg`, so they are restated
here. -/

theorem unregWorld_msgTarget : unregWorldMsg.target = some unregWorldOwner :=
  rfl

theorem unregWorld_msgOwner :
    unregWorldMsg.currentTarget = unregWorldOwner := rfl

theorem unregWorld_msgCodeAddress :
    unregWorldMsg.codeAddress = some unregWorldOwner := rfl

theorem unregWorld_msgValue : unregWorldMsg.value = 0 := rfl

theorem unregWorld_msgAdmin :
    unregWorldMsg.caller.toB256 = officialParams.admin := rfl

theorem unregWorld_msgData :
    unregWorldMsg.data = registerPauserCalldata unregWorldTarget 0 := rfl

theorem unregWorld_msgCode :
    unregWorldMsg.code.toList = lidoCircuitBreakerCode officialParams := by
  simpa only [unregWorldMsg, unregWorldCode] using
    unregWorld_byteArray_ofList_toList (lidoCircuitBreakerCode officialParams)

/-! ### Calldata -/

theorem unregWorld_dataFacts :
    unregWorldSevm.data.length.toB256 = 68 ∧
      Sevm.selector unregWorldSevm =
        selector "registerPauser" [.address, .address] ∧
      Sevm.dataWord unregWorldSevm 4 = unregWorldTarget ∧
      Sevm.dataWord unregWorldSevm 36 = 0 :=
  registerPauserCalldata_spec unregWorldSevm unregWorldTarget 0 unregWorld_data

theorem unregWorld_selector :
    Sevm.selector unregWorldSevm =
      selector "registerPauser" [.address, .address] :=
  unregWorld_dataFacts.2.1

theorem unregWorld_dataWord_target :
    Sevm.dataWord unregWorldSevm 4 = unregWorldTarget :=
  unregWorld_dataFacts.2.2.1

theorem unregWorld_dataWord_new : Sevm.dataWord unregWorldSevm 36 = 0 :=
  unregWorld_dataFacts.2.2.2

theorem unregWorld_argTarget :
    Sevm.argWord unregWorldSevm 0 = unregWorldTarget := by
  have h : 32 * (0 : B256) + 4 = 4 := by decide
  rw [Sevm.argWord, h]
  exact unregWorld_dataWord_target

theorem unregWorld_argNew : Sevm.argWord unregWorldSevm 1 = 0 := by
  have h : 32 * (1 : B256) + 4 = 36 := by decide
  rw [Sevm.argWord, h]
  exact unregWorld_dataWord_new

theorem unregWorld_dataLength : unregWorldSevm.data.length = 68 := by
  show (registerPauserCalldata unregWorldTarget 0).length = 68
  simp only [registerPauserCalldata, List.length_append,
    abiSelectorBytes_length, B256.length_toBytes]

/-! ## Storage at message entry -/

theorem unregWorld_getStor :
    Devm.getStor unregWorldPre unregWorldOwner = unregWorldStor := by
  change (unregWorldState.get unregWorldOwner).stor = unregWorldStor
  rw [unregWorldState, State.get_set_self]

theorem unregWorld_getStorVal {key : B256} :
    unregWorldPre.getStorVal unregWorldOwner key = unregWorldStor.get key := by
  change (unregWorldState.get unregWorldOwner).stor.get key = _
  rw [unregWorldState, State.get_set_self]

theorem unregWorld_getOrigStor {key : B256} :
    getOrigStorVal unregWorldSevm unregWorldOwner key =
      unregWorldStor.get key := by
  change (unregWorldState.get unregWorldOwner).stor.get key = _
  rw [unregWorldState, State.get_set_self]

theorem unregWorld_assignment :
    Devm.getStorVal unregWorldPre unregWorldOwner
      (assignmentSlot unregWorldTarget) = unregWorldPauser := by
  rw [unregWorld_getStorVal, unregWorld_stor_assignment]

/-- The admin address is a canonical address distinct from the retiring
pauser, so its own heartbeat cell is untouched and zero. -/
theorem unregWorld_adminCanonical :
    canonicalAddress unregWorldAdmin.toB256 := by
  unfold canonicalAddress unregWorldAdmin
  decide

theorem unregWorld_expiry_admin_zero :
    Devm.getStorVal unregWorldPre unregWorldOwner
      (expirySlot unregWorldAdmin.toB256) = 0 := by
  rw [unregWorld_getStorVal]
  exact unregWorld_stor_expiry_other unregWorld_adminCanonical (by decide)

theorem unregWorld_preWitness :
    RegistryWitness
      (logicalStorageOfStor (Devm.getStor unregWorldPre unregWorldOwner))
      [(unregWorldTarget, unregWorldPauser)] := by
  rw [unregWorld_getStor]
  exact unregWorldStor_witness

/-! ## Accessed storage keys

Six keys are warm at entry; the configured-interval slot is the one written
cell left cold, and this chronology never reads it.  Membership is settled by
the `insert` chain alone, never by deciding a `HashSet`. -/

theorem unregWorld_accessed :
    unregWorldPre.accessedStorageKeys = unregWorldKeys := rfl

theorem unregWorld_warmAssignment :
    (unregWorldOwner, assignmentSlot unregWorldTarget) ∈ unregWorldKeys := by
  rw [unregWorldKeys]
  exact Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
    (Or.inr (Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
      (Or.inr (Std.HashSet.mem_insert.mpr
        (Or.inr Std.HashSet.mem_insert_self)))))))))

theorem unregWorld_warmIndex :
    (unregWorldOwner, indexSlot unregWorldTarget) ∈ unregWorldKeys := by
  rw [unregWorldKeys]
  exact Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
    (Or.inr (Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
      (Or.inr Std.HashSet.mem_insert_self)))))))

theorem unregWorld_warmLength :
    (unregWorldOwner, arrayLengthSlot) ∈ unregWorldKeys := by
  rw [unregWorldKeys]
  exact Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
    (Or.inr (Std.HashSet.mem_insert.mpr
      (Or.inr Std.HashSet.mem_insert_self)))))

theorem unregWorld_warmEntry :
    (unregWorldOwner, arrayEntrySlot 1) ∈ unregWorldKeys := by
  rw [unregWorldKeys]
  exact Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
    (Or.inr Std.HashSet.mem_insert_self)))

theorem unregWorld_warmCount :
    (unregWorldOwner, countSlot unregWorldPauser) ∈ unregWorldKeys := by
  rw [unregWorldKeys]
  exact Std.HashSet.mem_insert.mpr (Or.inr Std.HashSet.mem_insert_self)

theorem unregWorld_warmExpiry :
    (unregWorldOwner, expirySlot unregWorldPauser) ∈ unregWorldKeys :=
  Std.HashSet.mem_insert_self

/-! ## The assignment-write boundary

The chronology phrases its count premise at `assignmentPost` — the state after
the unregistration path has read the target's assignment word and replaced it
with zero.  Because the assignment slot is already warm, that state carries
exactly the entry accessed-key set, and its storage differs from the entry
storage only at the assignment slot. -/

theorem unregWorld_assignmentBase :
    assignmentBase unregWorldSevm unregWorldPre unregWorldTarget =
      unregWorldPre := by
  rw [assignmentBase, temporalSloadBase]
  split
  · rfl
  · rename_i hcold
    exact absurd unregWorld_warmAssignment hcold

theorem unregWorld_assignmentPost_accessed :
    (assignmentPost unregWorldSevm unregWorldPre unregWorldTarget
      0).accessedStorageKeys = unregWorldKeys := by
  rw [assignmentPost, temporalSstorePost_accessedStorageKeys,
    unregWorld_assignmentBase]
  rfl

theorem unregWorld_assignmentPost_getStorVal {key : B256}
    (h : assignmentSlot unregWorldTarget ≠ key) :
    (assignmentPost unregWorldSevm unregWorldPre unregWorldTarget
      0).getStorVal unregWorldOwner key = unregWorldStor.get key := by
  rw [assignmentPost,
    temporalSstorePost_other unregWorldSevm
      (assignmentBase unregWorldSevm unregWorldPre unregWorldTarget)
      (assignmentSlot unregWorldTarget) 0 unregWorldOwner key
      (by
        intro hpair
        exact h (Prod.mk.injEq .. ▸ hpair).2.symm),
    unregWorld_assignmentBase, unregWorld_getStorVal]

theorem unregWorld_postCount :
    (assignmentPost unregWorldSevm unregWorldPre unregWorldTarget
      0).getStorVal unregWorldOwner (countSlot unregWorldPauser) = 1 := by
  rw [unregWorld_assignmentPost_getStorVal
    unregWorld_count_ne_assignment.symm, unregWorld_stor_count]

/-! ### Original words

Every cell the six writes touch carried its entry word in the transaction's
original state too: this world's `origState` is its entry state. -/

theorem unregWorld_origAssignment :
    getOrigStorVal unregWorldSevm unregWorldOwner
      (assignmentSlot unregWorldTarget) = unregWorldPauser := by
  rw [unregWorld_getOrigStor, unregWorld_stor_assignment]

theorem unregWorld_origCount :
    getOrigStorVal unregWorldSevm unregWorldOwner
      (countSlot unregWorldPauser) = 1 := by
  rw [unregWorld_getOrigStor, unregWorld_stor_count]

theorem unregWorld_origExpiry :
    getOrigStorVal unregWorldSevm unregWorldOwner
      (expirySlot unregWorldPauser) = unregWorldOldExpiry := by
  rw [unregWorld_getOrigStor, unregWorld_stor_expiry]

theorem unregWorld_origArray :
    getOrigStorVal unregWorldSevm unregWorldOwner (arrayEntrySlot 1) =
      unregWorldTarget := by
  rw [unregWorld_getOrigStor, unregWorld_stor_entry]

theorem unregWorld_origIndex :
    getOrigStorVal unregWorldSevm unregWorldOwner
      (indexSlot unregWorldTarget) = 1 := by
  rw [unregWorld_getOrigStor, unregWorld_stor_index]

theorem unregWorld_origLength :
    getOrigStorVal unregWorldSevm unregWorldOwner arrayLengthSlot = 1 := by
  rw [unregWorld_getOrigStor, unregWorld_stor_length]

theorem unregWorld_entryExpiry :
    unregWorldPre.getStorVal unregWorldOwner (expirySlot unregWorldPauser) =
      unregWorldOldExpiry := by
  rw [unregWorld_getStorVal, unregWorld_stor_expiry]

/-! ### Staged-load warmth and the closed body reserve -/

private theorem unregWorld_warmCost {base : Devm} {key : B256}
    (h : base.accessedStorageKeys = unregWorldKeys)
    (hk : (unregWorldOwner, key) ∈ unregWorldKeys) :
    temporalSloadCost unregWorldSevm base key = gasWarmAccess := by
  rw [temporalSloadCost]
  split
  · rfl
  · rename_i hno
    refine absurd ?_ hno
    show (unregWorldOwner, key) ∈ base.accessedStorageKeys
    rw [h]
    exact hk

set_option maxRecDepth 16384 in
/-- The chronology's body reserve at this world is the closed numeral the
message carries. -/
theorem unregWorld_bodyGasEq :
    foundZeroOldLastRegisterBodyGas unregWorldSevm unregWorldPre
        unregWorldTarget unregWorldPauser unregWorldResetCost
        unregWorldResetCost gasWarmAccess gasWarmAccess unregWorldResetCost
        unregWorldResetCost unregWorldResetCost unregWorldResetCost =
      unregWorldBodyGas := by
  show 221 + (4131 +
      temporalSloadCost unregWorldSevm unregWorldPre
        (assignmentSlot unregWorldTarget) + unregWorldResetCost +
      temporalSloadCost unregWorldSevm
        (assignmentPost unregWorldSevm unregWorldPre unregWorldTarget 0)
        (countSlot unregWorldPauser) + unregWorldResetCost + gasWarmAccess +
      gasWarmAccess + unregWorldResetCost + unregWorldResetCost +
      unregWorldResetCost + unregWorldResetCost) = unregWorldBodyGas
  rw [unregWorld_warmCost unregWorld_accessed unregWorld_warmAssignment,
    unregWorld_warmCost unregWorld_assignmentPost_accessed
      unregWorld_warmCount]
  norm_num [unregWorldBodyGas, unregWorldResetCost, gasWarmAccess,
    gasStorageUpdate, gasColdSload]

/-- The message's own `gas` field is that reserve on the nose, with `G = 0`:
the run leaves nothing behind. -/
theorem unregWorld_gasEntry :
    unregWorldMsg.gas = 0 + registerPauserDispatchGas +
      foundZeroOldLastRegisterBodyGas unregWorldSevm unregWorldPre
        unregWorldTarget unregWorldPauser unregWorldResetCost
        unregWorldResetCost gasWarmAccess gasWarmAccess unregWorldResetCost
        unregWorldResetCost unregWorldResetCost unregWorldResetCost := by
  rw [unregWorld_bodyGasEq]
  show unregWorldGas = 0 + registerPauserDispatchGas + unregWorldBodyGas
  norm_num [unregWorldGas, unregWorldBodyGas, registerPauserDispatchGas]

/-! ### The model-side entry list -/

theorem unregWorld_find :
    findEntry [(unregWorldTarget, unregWorldPauser)] unregWorldTarget =
      some (0, unregWorldPauser) := by
  simp [findEntry]

theorem unregWorld_last :
    0 + 1 = ([(unregWorldTarget, unregWorldPauser)] : List Entry).length := rfl

theorem unregWorld_swapPop :
    swapPop [(unregWorldTarget, unregWorldPauser)] 0 = [] := rfl

/-! ## The payoff -/

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2400000 in
/-- A fully inhabited production-runtime **unregistration**.  The admin of
`officialParams` calls `registerPauser(7, 0)` on a CircuitBreaker deployed at
address `100` whose Registry holds exactly the entry `(7, 9)`, with exactly
`22327` gas, six warm and one cold storage key.  Every premise of the
retiring-old-last chronology holds at this one machine, so the exact compiled
run actually happens: the source trace exists, the post-Registry is the *empty*
Registry and is witnessed as such, the walk reaches `ok` with the gas exhausted
to zero, the retired pauser's heartbeat expiry is cleared, no other canonical
pauser's expiry moves, and the two events are emitted in order. -/
theorem unregisterWorld_effects :
    ∃ trace post,
      setPauserSourceTrace [(unregWorldTarget, unregWorldPauser)]
          unregWorldTarget 0 = some trace ∧
      trace.postEntries = [] ∧
      RegistryWitness
        (logicalStorageOfStor (applyRegistryWrites
          (Devm.getStor unregWorldPre unregWorldOwner) trace.writes))
        trace.postEntries ∧
      Prog.RunCompiledTo unregWorldSevm unregWorldPre
        (runtime officialParams) (.ok post) ∧
      exec ⟨0, unregWorldSevm, unregWorldPre⟩ = .ok post ∧
      Nonempty (Exec 0 unregWorldSevm unregWorldPre (.ok post)) ∧
      post.gasLeft = 0 ∧
      post.getStorVal unregWorldOwner (expirySlot unregWorldPauser) = 0 ∧
      (∀ pauser, canonicalAddress pauser → pauser ≠ unregWorldPauser →
        post.getStorVal unregWorldOwner (expirySlot pauser) =
          unregWorldPre.getStorVal unregWorldOwner (expirySlot pauser)) ∧
      post.logs =
        [⟨unregWorldOwner,
            [pauserSetEvent, unregWorldTarget, unregWorldPauser, 0], []⟩,
          ⟨unregWorldOwner, [heartbeatUpdatedEvent, unregWorldPauser],
            (0 : B256).toBytes⟩] ∧
      some unregWorldSevm.code.toList = Prog.compile (runtime officialParams) := by
  rcases unregWorld_dataFacts with ⟨hlength, hselector, hargTarget, hargNew⟩
  rcases registerPauser_runCompiledTo_foundZeroOldLast officialParams
      unregWorldSevm unregWorldPre [(unregWorldTarget, unregWorldPauser)]
      unregWorldTarget 0 unregWorldPauser 1 unregWorldOldExpiry
      unregWorldOldExpiry unregWorldPauser 1 unregWorldTarget 1 1
      unregWorldResetCost unregWorldResetCost gasWarmAccess gasWarmAccess
      unregWorldResetCost unregWorldResetCost unregWorldResetCost
      unregWorldResetCost 0
      hlength unregWorld_value hselector unregWorld_codeAddress_currentTarget
      unregWorld_codeBytes unregWorld_admin hargTarget hargNew
      unregWorld_preWitness unregWorld_find unregWorld_last
      unregWorld_targetValid unregWorld_pauserValid unregWorld_origAssignment
      (unregWorld_resetCost (by decide) (by decide))
      unregWorld_postCount unregWorld_origCount
      (unregWorld_resetCost (by decide) (by decide)) (by decide)
      unregWorld_entryExpiry unregWorld_origExpiry
      (unregWorld_resetCost (by decide) (by decide))
      unregWorld_origArray unregWorld_origIndex unregWorld_origLength
      unregWorld_noopCost unregWorld_noopCost
      (unregWorld_resetCost (by decide) (by decide))
      (unregWorld_resetCost (by decide) (by decide))
      (unregWorld_resetCost (by decide) (by decide))
      unregWorld_warmEntry unregWorld_warmIndex unregWorld_warmLength
      unregWorld_warmExpiry (by norm_num [gCallStipend, unregWorldResetCost,
        gasStorageUpdate, gasColdSload]) unregWorld_static with
    ⟨trace, post, htrace, hpostEntries, hwitness, hrun, hgas, hlogs,
      holdExpiry, hexpiries, hcompile⟩
  have hentry :
      unregWorldPre.setMach ⟨[], Mem.empty,
        0 + registerPauserDispatchGas +
          foundZeroOldLastRegisterBodyGas unregWorldSevm unregWorldPre
            unregWorldTarget unregWorldPauser unregWorldResetCost
            unregWorldResetCost gasWarmAccess gasWarmAccess
            unregWorldResetCost unregWorldResetCost unregWorldResetCost
            unregWorldResetCost⟩ = unregWorldPre := by
    rw [unregWorld_bodyGasEq]
    rfl
  rw [hentry] at hrun
  have hexec : exec ⟨0, unregWorldSevm, unregWorldPre⟩ = .ok post :=
    Prog.exec_of_runCompiledTo hrun hcompile
  refine ⟨trace, post, htrace, ?_, ?_, hrun, hexec,
    (exec_iff_exec_eq 0 unregWorldSevm unregWorldPre (.ok post)).mpr hexec,
    hgas, holdExpiry, hexpiries, hlogs, hcompile⟩
  · rw [hpostEntries]
    exact unregWorld_swapPop
  · exact hwitness

/-- The shape `attainable_of_entryRoute_frame` in
`Blanc/LidoCircuitBreakerAttainment.lean` consumes. -/
theorem unregisterWorld_run :
    ∃ post,
      Prog.RunCompiledTo unregWorldSevm unregWorldPre
        (runtime officialParams) (.ok post) ∧
        some unregWorldSevm.code.toList =
          Prog.compile (runtime officialParams) := by
  obtain ⟨_trace, post, _htrace, _hentries, _hwitness, hrun, _hexec, _hfilled,
    _hgas, _holdExpiry, _hexpiries, _hlogs, hcompile⟩ :=
    unregisterWorld_effects
  exact ⟨post, hrun, hcompile⟩


set_option maxRecDepth 40000 in
set_option maxHeartbeats 2400000 in
/-- Message-altitude settlement at this world.

The chronology exposes the raw poststate's gas, storage and logs but says
nothing about its `error` flag, and nothing landed propagates `Devm.error`
across a compiled walk — so cleanliness stays an explicit antecedent here
rather than a discharged premise.  Given it, the frame settles onto the raw
poststate itself: no rollback, and what the message leaves behind is the
unregistration.

That is the step past `unregisterWorld_run`.  The run theorem says only that
the compiled walk reaches `ok`; this one says what the settled state *is*.  The
Registry the message leaves behind is witnessed by the swap-popped entry list,
which for this one-entry world is the empty list: target `7` really is removed,
its pauser's heartbeat cell really is cleared, every other canonical pauser's
expiry is untouched, and the two records are emitted in order.

It remains a statement about this message and nothing beyond it.  No claim is
made that the entry state is reachable from a genesis-consistent history, and
none about any later message. -/
theorem unregisterWorld_settles :
    ∃ post,
      exec ⟨0, unregWorldSevm, unregWorldPre⟩ = .ok post ∧
      (post.error.isNone = true →
        ProcessMessage unregWorldMsg
            (.some ⟨⟨0, unregWorldSevm, unregWorldPre⟩, .ok post⟩)
            (.ok post) ∧
          ∃ trace,
            setPauserSourceTrace [(unregWorldTarget, unregWorldPauser)]
                unregWorldTarget 0 = some trace ∧
            trace.postEntries = [] ∧
            RegistryWitness
              (logicalStorageOfStor (applyRegistryWrites
                (Devm.getStor unregWorldPre unregWorldOwner) trace.writes))
              trace.postEntries ∧
            post.gasLeft = 0 ∧
            post.logs =
              [⟨unregWorldOwner,
                  [pauserSetEvent, unregWorldTarget, unregWorldPauser, 0], []⟩,
                ⟨unregWorldOwner, [heartbeatUpdatedEvent, unregWorldPauser],
                  (0 : B256).toBytes⟩] ∧
            post.getStorVal unregWorldOwner (expirySlot unregWorldPauser) = 0 ∧
            ∀ pauser, canonicalAddress pauser → pauser ≠ unregWorldPauser →
              post.getStorVal unregWorldOwner (expirySlot pauser) =
                unregWorldPre.getStorVal unregWorldOwner
                  (expirySlot pauser)) := by
  obtain ⟨_trace, post, _htrace, _hentries, _hwitness, _hrun, hexec, hfilled,
    _hgas, _holdExpiry, _hexpiries, _hlogs, _hcompile⟩ :=
    unregisterWorld_effects
  refine ⟨post, hexec, ?_⟩
  intro hclean
  have hnot : post.error.isSome ≠ true := by
    cases herror : post.error <;> simp_all
  have hprocess := RunFrame.of_run (f := Frame.ofCall unregWorldMsg)
    (raw := (.ok post : Execution)) unregWorld_frameEntry
  have hsettle :
      (Frame.ofCall unregWorldMsg).settle (.ok post) = .ok post := by
    simp only [Frame.settle, Frame.settleMsg, Frame.ofCall,
      executeCode.handleError, processMessage.settle, bind, Except.bind,
      if_neg hnot]
    rfl
  rw [hsettle] at hprocess
  refine ⟨hprocess, ?_⟩
  rcases registerPauser_foundZeroOldLast_success_settled_effects officialParams
      [(unregWorldTarget, unregWorldPauser)] unregWorldTarget 0
      unregWorldPauser 1 unregWorldOldExpiry unregWorldOldExpiry
      unregWorldPauser 1 unregWorldTarget 1 1
      unregWorldResetCost unregWorldResetCost gasWarmAccess gasWarmAccess
      unregWorldResetCost unregWorldResetCost unregWorldResetCost
      unregWorldResetCost 0
      unregWorld_msgTarget unregWorld_msgOwner unregWorld_msgCodeAddress
      unregWorld_msgCode unregWorld_msgValue unregWorld_msgData
      unregWorld_gasEntry unregWorld_msgAdmin
      unregWorld_preWitness unregWorld_find unregWorld_last
      unregWorld_targetValid unregWorld_pauserValid unregWorld_origAssignment
      (unregWorld_resetCost (by decide) (by decide))
      unregWorld_postCount unregWorld_origCount
      (unregWorld_resetCost (by decide) (by decide)) (by decide)
      unregWorld_entryExpiry unregWorld_origExpiry
      (unregWorld_resetCost (by decide) (by decide))
      unregWorld_origArray unregWorld_origIndex unregWorld_origLength
      unregWorld_noopCost unregWorld_noopCost
      (unregWorld_resetCost (by decide) (by decide))
      (unregWorld_resetCost (by decide) (by decide))
      (unregWorld_resetCost (by decide) (by decide))
      unregWorld_warmEntry unregWorld_warmIndex unregWorld_warmLength
      unregWorld_warmExpiry
      (by norm_num [gCallStipend, unregWorldResetCost, gasStorageUpdate,
        gasColdSload])
      unregWorld_static hprocess hfilled hclean with
    ⟨trace, htrace, hpostEntries, hwitness, hgas, hlogs, holdExpiry,
      hexpiries⟩
  refine ⟨trace, htrace, ?_, hwitness, hgas, hlogs, holdExpiry, hexpiries⟩
  rw [hpostEntries]
  exact unregWorld_swapPop

end Blanc.LidoCircuitBreaker
