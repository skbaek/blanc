import Blanc.LidoCircuitBreakerEnumeration

/-! Small, gate-owned positive controls for the enumeration proof owner. -/

namespace Blanc.LidoCircuitBreaker.EnumerationControls

open Jaune

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

theorem reachable_writer_rejected_control :
    (enumerationWritingMutant officialParams).entrySstoreFree
      getPausables enumerationComponent = false :=
  enumeration_writing_mutant_rejected

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

def expectedEvent : Log :=
  ⟨Nat.toAdr 100, [pauserSetEvent, 7, 9, 11], []⟩

set_option maxRecDepth 2000 in
theorem event_shape_mutants_rejected :
    expectedEvent ≠ ⟨Nat.toAdr 100, [0, 7, 9, 11], []⟩ ∧
    expectedEvent ≠ ⟨Nat.toAdr 100, [pauserSetEvent, 9, 7, 11], []⟩ ∧
    expectedEvent ≠ ⟨Nat.toAdr 100, [pauserSetEvent, 7, 9, 11], [0]⟩ := by
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
