import Blanc.LidoCircuitBreakerEnumeration

/-! Small, gate-owned positive controls for the enumeration proof owner. -/

namespace Blanc.LidoCircuitBreaker.EnumerationControls

open Jaune

set_option maxHeartbeats 800000
set_option maxRecDepth 16384

/-! Exact-code resource witnesses.  The recursive storage construction uses
the production Registry transition theorem at every step, so the 64-entry
control inhabits the same universal premise used by the public runtime theorem. -/

def controlEntries : Nat → List Entry
  | 0 => []
  | n + 1 => controlEntries n ++
      [(Nat.toB256 (n + 1), Nat.toB256 (n + 65))]

def controlStor : Nat → Stor
  | 0 => Stor.empty
  | n + 1 =>
      let target := Nat.toB256 (n + 1)
      let pauser := Nat.toB256 (n + 65)
      applyRegistryWrites (controlStor n)
        [(assignmentSlot target, pauser),
         (arrayEntrySlot (Nat.toB256 ((controlEntries n).length + 1)), target),
         (indexSlot target, Nat.toB256 ((controlEntries n).length + 1)),
         (arrayLengthSlot, Nat.toB256 ((controlEntries n).length + 1)),
         (countSlot pauser,
           Nat.toB256 (assignmentCount (controlEntries n) pauser + 1))]

private theorem findEntry_none_of_not_mem
    {entries : List Entry} {target : B256}
    (h : target ∉ entries.map Prod.fst) :
    findEntry entries target = none := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at h
      simp [findEntry, Ne.symm h.1, ih h.2]

private theorem controlEntries_target_toNat_le :
    ∀ {n : Nat} {target : B256}, n ≤ 64 →
      target ∈ (controlEntries n).map Prod.fst → target.toNat ≤ n := by
  intro n
  induction n with
  | zero => simp [controlEntries]
  | succ n ih =>
      intro target hn hmem
      simp only [controlEntries, List.map_append, List.map_cons, List.map_nil,
        List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hmem | rfl
      · exact Nat.le_trans (ih (by omega) hmem) (by omega)
      · rw [B256.toNat_toB256_of_lt (by norm_num; omega)]

private theorem controlEntries_fresh_not_mem (n : Nat) (hn : n < 64) :
    Nat.toB256 (n + 1) ∉ (controlEntries n).map Prod.fst := by
  intro hmem
  have hle := controlEntries_target_toNat_le (n := n) (by omega) hmem
  rw [B256.toNat_toB256_of_lt (by norm_num; omega)] at hle
  omega

private theorem controlTarget_valid (n : Nat) (hn : n < 64) :
    nonzeroCanonicalAddress (Nat.toB256 (n + 1)) := by
  constructor
  · intro h
    have hnat := congrArg B256.toNat h
    rw [B256.toNat_toB256_of_lt (by norm_num; omega),
      B256.toNat_zero] at hnat
    omega
  · unfold canonicalAddress
    rw [B256.toNat_toB256_of_lt (by norm_num; omega)]
    norm_num
    omega

private theorem controlPauser_valid (n : Nat) (hn : n < 64) :
    nonzeroCanonicalAddress (Nat.toB256 (n + 65)) := by
  constructor
  · intro h
    have hnat := congrArg B256.toNat h
    rw [B256.toNat_toB256_of_lt (by norm_num; omega),
      B256.toNat_zero] at hnat
    omega
  · unfold canonicalAddress
    rw [B256.toNat_toB256_of_lt (by norm_num; omega)]
    norm_num
    omega

theorem controlRegistryWitness : ∀ n, n ≤ 64 →
    RegistryWitness (logicalStorageOfStor (controlStor n)) (controlEntries n)
  | 0, _ => by
      change RegistryWitness emptyStorage []
      exact emptyWitness
  | n + 1, hn => by
      have previous := controlRegistryWitness n (by omega)
      have fresh := previous.applyFreshWrites
        (controlTarget_valid n (by omega)) (controlPauser_valid n (by omega))
        (findEntry_none_of_not_mem (controlEntries_fresh_not_mem n (by omega)))
      simpa only [controlStor, controlEntries] using fresh

def exactCodeOwner : Adr := Nat.toAdr 100

def exactCodeBytes : ByteArray :=
  ByteArray.mk (lidoCircuitBreakerCode officialParams).toArray

def exactCodeSevm : Sevm :=
  { (default : Sevm) with
    currentTarget := exactCodeOwner
    codeAddress := some exactCodeOwner
    code := exactCodeBytes
    data := abiSelectorBytes (selector "getPausables" [])
    value := 0 }

def exactCodeBase (n : Nat) : Devm :=
  (default : Devm).withState
    ((default : State).setStor exactCodeOwner (controlStor n))

theorem exactCodeBase_getStor (n : Nat) :
    Devm.getStor (exactCodeBase n) exactCodeOwner = controlStor n := by
  change ((((default : State).setStor exactCodeOwner (controlStor n)).get
    exactCodeOwner).stor) = controlStor n
  unfold State.setStor
  rw [State.get_set_self]

def ExactCodeEnumerationControl (n : Nat) : Prop :=
    Prog.RunCompiled exactCodeSevm
      (preparedEnumerationRuntimeState exactCodeSevm
        (exactCodeBase n) (controlEntries n))
      (runtime officialParams)
      (((preparedEnumerationRuntimeState exactCodeSevm
        (exactCodeBase n) (controlEntries n)).setMach
          ⟨[], enumPrefixMemory (controlEntries n) (controlEntries n),
            (preparedEnumerationRuntimeState exactCodeSevm
              (exactCodeBase n) (controlEntries n)).gasLeft -
                getPausablesRuntimeGas (controlEntries n)⟩).withOutput
                  (abiAddressArray (controlEntries n))) ∧
    some exactCodeSevm.code.toList = Prog.compile (runtime officialParams)

theorem exactCodeEnumerationRun (n : Nat) (hn : n ≤ 64) :
    ExactCodeEnumerationControl n := by
  unfold ExactCodeEnumerationControl
  apply EnumerationRuntimeResources.getPausables_runCompiled
    (enumerationRuntimeResources_prepared exactCodeSevm
      (exactCodeBase n) (controlEntries n))
  · decide
  · rfl
  · decide
  · simp only [exactCodeSevm, exactCodeBytes]
  · simp only [exactCodeSevm, exactCodeBytes]
    rw [ByteArray.toList_eq_toList_data]
  · have hprepared : Devm.getStor
        (preparedEnumerationRuntimeState exactCodeSevm (exactCodeBase n)
          (controlEntries n)) exactCodeOwner = controlStor n := by
      change Devm.getStor
        (prepareEnumerationStorage exactCodeSevm (exactCodeBase n)
          (controlEntries n)) exactCodeOwner = controlStor n
      rw [show Devm.getStor
          (prepareEnumerationStorage exactCodeSevm (exactCodeBase n)
            (controlEntries n)) exactCodeOwner =
            Devm.getStor (exactCodeBase n) exactCodeOwner by
        exact (prepareEnumerationStorage_worldEq exactCodeSevm
          (exactCodeBase n) (controlEntries n)).getStor exactCodeOwner |>.symm]
      exact exactCodeBase_getStor n
    rw [show exactCodeSevm.currentTarget = exactCodeOwner by rfl, hprepared]
    exact controlRegistryWitness n hn

theorem exact_code_empty_control : ExactCodeEnumerationControl 0 :=
  exactCodeEnumerationRun 0 (by omega)

theorem exact_code_singleton_control : ExactCodeEnumerationControl 1 :=
  exactCodeEnumerationRun 1 (by omega)

theorem exact_code_sixty_four_control : ExactCodeEnumerationControl 64 :=
  exactCodeEnumerationRun 64 (by omega)

def singleton : List Entry := [(1, 2)]

def two : List Entry := [(1, 2), (3, 4)]

def sixtyFour : List Entry :=
  (List.range 64).map (fun n => (Nat.toB256 (n + 1), Nat.toB256 (n + 65)))

theorem empty_image_control :
    abiAddressArray ([] : List Entry) =
      (Nat.toB256 32).toBytes ++ (Nat.toB256 0).toBytes := by
  simp [abiAddressArray]

theorem singleton_size_control :
    (abiAddressArray singleton).length = 96 := by
  simpa [singleton] using abiAddressArray_length singleton

theorem sixtyFour_size_control :
    (abiAddressArray sixtyFour).length = 2112 := by
  rw [abiAddressArray_length]
  simp [sixtyFour]

theorem sixtyFour_not_capped_at_one : sixtyFour.length ≠ 1 := by
  simp [sixtyFour]

theorem full_prefix_image_control :
    ((enumPrefixMemory sixtyFour sixtyFour).read 0 2112).1 =
      abiAddressArray sixtyFour := by
  simpa [sixtyFour] using enumPrefixMemory_full_read sixtyFour

theorem cursor_not_memory_resident_control
    (base : Devm) (done : List Entry) (cursor cursor' G : Nat) :
    (base.setMach ⟨[Nat.toB256 cursor], enumPrefixMemory sixtyFour done, G⟩).memory =
      (base.setMach ⟨[Nat.toB256 cursor'], enumPrefixMemory sixtyFour done, G⟩).memory :=
  enumLoop_pre_memory_independent_of_cursor base sixtyFour done cursor cursor' G

def cursorAliasedSingletonMemory : Mem :=
  (enumPrefixMemory singleton []).write 64 (Nat.toB256 96).toBytes

/-- Storing the recursive cursor in the first output word overwrites the
singleton target with `96`; the production stack-resident cursor cannot have
this collision. -/
theorem memory_resident_cursor_alias_rejected :
    Bytes.toB256 ((cursorAliasedSingletonMemory.read 64 32).1) = 96 ∧
    Bytes.toB256 ((cursorAliasedSingletonMemory.read 64 32).1) ≠ 1 := by
  decide

theorem reachable_writer_rejected_control :
    (enumerationWritingMutant officialParams).entrySstoreFree
      getPausables enumerationComponent = false :=
  enumeration_writing_mutant_rejected

theorem writer_certificate_rejected_control :
    ¬ (enumerationWritingMutant officialParams).EntrySstoreFree
      getPausables enumerationComponent := by
  intro accepted
  have hbool := Prog.entrySstoreFree_iff.mpr accepted
  rw [enumeration_writing_mutant_rejected] at hbool
  contradiction

theorem order_omission_duplication_and_truncation_rejected :
    abiAddressArray two ≠ abiAddressArray two.reverse ∧
    abiAddressArray two ≠ abiAddressArray [two[0]!] ∧
    abiAddressArray two ≠ abiAddressArray [two[0]!, two[0]!] ∧
    abiAddressArray sixtyFour ≠
      abiAddressArray (sixtyFour.take 1) := by
  decide

theorem abi_header_size_and_padding_control :
    Bytes.toB256 ((abiAddressArray singleton).sliceD 0 32 0) = 32 ∧
    Bytes.toB256 ((abiAddressArray singleton).sliceD 32 32 0) = 1 ∧
    (abiAddressArray singleton).length = 96 ∧
    (abiAddressArray singleton).sliceD 64 12 0 = List.replicate 12 0 := by
  decide

theorem unbounded_offset_needs_witness_bound :
    ¬ 64 + 32 * (2 ^ 256) < 2 ^ 256 := by
  norm_num

theorem noop_shaped_transitions_still_exist :
    setPauser ([] : List Entry) 7 0 = some [] ∧
    setPauser [(7, 9)] 7 9 = some [(7, 9)] := by
  decide

/-- A theorem that weakened `PauserSet` coverage by requiring an actual
assignment change would exclude both source-valid no-op-shaped cases. -/
theorem noop_event_omission_premise_rejected :
    ¬ assignmentAt ([] : List Entry) 7 ≠ 0 ∧
    ¬ assignmentAt [(7, 9)] 7 ≠ 9 := by
  decide

def expectedEvent : Log :=
  ⟨Nat.toAdr 100, [pauserSetEvent, 7, 9, 11], []⟩

set_option maxRecDepth 2000 in
theorem event_shape_mutants_rejected :
    expectedEvent ≠ ⟨Nat.toAdr 101,
      [pauserSetEvent, 7, 9, 11], []⟩ ∧
    expectedEvent ≠ ⟨Nat.toAdr 100, [0, 7, 9, 11], []⟩ ∧
    expectedEvent ≠ ⟨Nat.toAdr 100, [pauserSetEvent, 9, 7, 11], []⟩ ∧
    expectedEvent ≠ ⟨Nat.toAdr 100, [pauserSetEvent, 7, 9, 11], [0]⟩ := by
  constructor
  · intro h
    have ha := congrArg Log.address h
    have hne : Nat.toAdr 100 ≠ Nat.toAdr 101 := by decide
    exact hne (by simpa [expectedEvent] using ha)
  constructor
  · intro h
    have ht := congrArg Log.topics h
    have hne : pauserSetEvent ≠ (0 : B256) := by decide
    have ht' : pauserSetEvent = 0 := by
      simpa [expectedEvent] using ht
    exact hne ht'
  constructor
  · intro h
    have ht := congrArg Log.topics h
    have hne : (7 : B256) ≠ 9 := by decide
    have ht' : (7 : B256) = 9 ∧ (9 : B256) = 7 := by
      simpa [expectedEvent] using ht
    exact hne ht'.1
  · intro h
    have hd := congrArg Log.data h
    simp [expectedEvent] at hd

end Blanc.LidoCircuitBreaker.EnumerationControls
