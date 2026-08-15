import Blanc.LidoCircuitBreakerCore

/-! Pure public-boundary Registry model for LidoCircuitBreaker.
It is deliberately a model/witness relation, not an S2 preservation theorem. -/

namespace Blanc.LidoCircuitBreaker

open Jaune

abbrev Entry := B256 × B256

def findEntry : List Entry → B256 → Option (Nat × B256)
  | [], _ => none
  | (target, pauser) :: rest, wanted =>
      if target = wanted then some (0, pauser)
      else match findEntry rest wanted with
        | none => none
        | some (index, found) => some (index + 1, found)

def setEntryAt : Nat → Entry → List Entry → List Entry
  | _, _, [] => []
  | 0, entry, _ :: rest => entry :: rest
  | index + 1, entry, head :: rest => head :: setEntryAt index entry rest

def dropLast : List Entry → List Entry
  | [] => []
  | [_] => []
  | head :: rest => head :: dropLast rest

def last? : List Entry → Option Entry
  | [] => none
  | [entry] => some entry
  | _ :: rest => last? rest

def swapPop : List Entry → Nat → List Entry
  | entries, index =>
      match last? entries with
      | none => entries
      | some last => dropLast (setEntryAt index last entries)

/-- The sole pure model kernel used by registration and pausing.  The absent
target/zero-pauser path intentionally has an unchanged boundary list even
though the Solidity implementation executes append/remove storage effects. -/
def setPauser : List Entry → B256 → B256 → Option (List Entry)
  | entries, target, newPauser =>
      if target = 0 then none
      else match findEntry entries target with
        | none => if newPauser = 0 then some entries else some (entries ++ [(target, newPauser)])
        | some (index, _) =>
            if newPauser = 0 then some (swapPop entries index)
            else some (setEntryAt index (target, newPauser) entries)

def targetAt : List Entry → Nat → B256
  | [], _ => 0
  | (target, _) :: _, 0 => target
  | _ :: rest, index + 1 => targetAt rest index

def assignmentAt : List Entry → B256 → B256
  | [], _ => 0
  | (target, pauser) :: rest, wanted => if target = wanted then pauser else assignmentAt rest wanted

def oneBasedIndexAt : List Entry → B256 → Nat
  | [], _ => 0
  | (target, _) :: rest, wanted =>
      if target = wanted then 1
      else let tail := oneBasedIndexAt rest wanted; if tail = 0 then 0 else tail + 1

theorem findEntry_targetAt {entries target index pauser}
    (h : findEntry entries target = some (index, pauser)) :
    targetAt entries index = target := by
  induction entries generalizing index pauser with
  | nil => simp [findEntry] at h
  | cons entry rest ih =>
      by_cases heq : entry.1 = target
      · simp [findEntry, heq] at h
        obtain ⟨rfl, rfl⟩ := h
        simpa [targetAt] using heq
      · cases hfind : findEntry rest target with
        | none => simp [findEntry, heq, hfind] at h
        | some found =>
            obtain ⟨foundIndex, foundPauser⟩ := found
            simp [findEntry, heq, hfind] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ih hfind

theorem findEntry_assignmentAt {entries target index pauser}
    (h : findEntry entries target = some (index, pauser)) :
    assignmentAt entries target = pauser := by
  induction entries generalizing index pauser with
  | nil => simp [findEntry] at h
  | cons entry rest ih =>
      by_cases heq : entry.1 = target
      · simp [findEntry, heq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [assignmentAt, heq]
      · cases hfind : findEntry rest target with
        | none => simp [findEntry, heq, hfind] at h
        | some found =>
            obtain ⟨foundIndex, foundPauser⟩ := found
            simp [findEntry, heq, hfind] at h
            obtain ⟨rfl, rfl⟩ := h
            simpa [assignmentAt, heq] using ih hfind

theorem findEntry_oneBasedIndexAt {entries target index pauser}
    (h : findEntry entries target = some (index, pauser)) :
    oneBasedIndexAt entries target = index + 1 := by
  induction entries generalizing index pauser with
  | nil => simp [findEntry] at h
  | cons entry rest ih =>
      by_cases heq : entry.1 = target
      · simp [findEntry, heq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [oneBasedIndexAt, heq]
      · cases hfind : findEntry rest target with
        | none => simp [findEntry, heq, hfind] at h
        | some found =>
            obtain ⟨foundIndex, foundPauser⟩ := found
            simp [findEntry, heq, hfind] at h
            obtain ⟨rfl, rfl⟩ := h
            simp [oneBasedIndexAt, heq, ih hfind]

def assignmentCount : List Entry → B256 → Nat
  | [], _ => 0
  | (_, pauser) :: rest, wanted => (if pauser = wanted then 1 else 0) + assignmentCount rest wanted

theorem findEntry_none_target_not_mem_targets
    {entries : List Entry} {target : B256}
    (h : findEntry entries target = none) :
    target ∉ entries.map Prod.fst := by
  induction entries with
  | nil => simp
  | cons entry rest ih =>
      by_cases heq : entry.1 = target
      · simp [findEntry, heq] at h
      · cases hfind : findEntry rest target with
        | none =>
            simp only [List.map_cons, List.mem_cons]
            intro hmem
            rcases hmem with hmem | hmem
            · exact heq hmem.symm
            · exact ih hfind hmem
        | some found =>
            simp [findEntry, heq, hfind] at h

theorem findEntry_none_assignmentAt
    {entries : List Entry} {target : B256}
    (h : findEntry entries target = none) :
    assignmentAt entries target = 0 := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      by_cases heq : entry.1 = target
      · simp [findEntry, heq] at h
      · cases hfind : findEntry rest target with
        | none => simp [assignmentAt, heq, ih hfind]
        | some found => simp [findEntry, heq, hfind] at h

theorem findEntry_none_oneBasedIndexAt
    {entries : List Entry} {target : B256}
    (h : findEntry entries target = none) :
    oneBasedIndexAt entries target = 0 := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      by_cases heq : entry.1 = target
      · simp [findEntry, heq] at h
      · cases hfind : findEntry rest target with
        | none => simp [oneBasedIndexAt, heq, ih hfind]
        | some found => simp [findEntry, heq, hfind] at h

theorem targetAt_append_old
    (entries : List Entry) (entry : Entry) {index : Nat}
    (hindex : index < entries.length) :
    targetAt (entries ++ [entry]) index = targetAt entries index := by
  induction entries generalizing index with
  | nil => simp at hindex
  | cons head rest ih =>
      cases index with
      | zero => rfl
      | succ index =>
          simp only [List.cons_append, targetAt]
          exact ih (Nat.lt_of_succ_lt_succ hindex)

theorem findEntry_append_of_none
    {entries : List Entry} {target pauser : B256}
    (h : findEntry entries target = none) :
    findEntry (entries ++ [(target, pauser)]) target =
      some (entries.length, pauser) := by
  induction entries with
  | nil => simp [findEntry]
  | cons entry rest ih =>
      by_cases heq : entry.1 = target
      · simp [findEntry, heq] at h
      · cases hfind : findEntry rest target with
        | none =>
            simp [findEntry, heq, ih hfind]
        | some found =>
            simp [findEntry, heq, hfind] at h

theorem targetAt_append_length_of_findEntry_none
    {entries : List Entry} {target pauser : B256}
    (h : findEntry entries target = none) :
    targetAt (entries ++ [(target, pauser)]) entries.length = target :=
  findEntry_targetAt (findEntry_append_of_none h)

theorem assignmentAt_append_of_ne
    (entries : List Entry) (target pauser wanted : B256)
    (hneq : wanted ≠ target) :
    assignmentAt (entries ++ [(target, pauser)]) wanted =
      assignmentAt entries wanted := by
  induction entries with
  | nil => simp [assignmentAt, Ne.symm hneq]
  | cons entry rest ih =>
      by_cases hhead : entry.1 = wanted
      · simp [assignmentAt, hhead]
      · simp [assignmentAt, hhead, ih]

theorem assignmentAt_append_target_of_findEntry_none
    {entries : List Entry} {target pauser : B256}
    (h : findEntry entries target = none) :
    assignmentAt (entries ++ [(target, pauser)]) target = pauser :=
  findEntry_assignmentAt (findEntry_append_of_none h)

theorem oneBasedIndexAt_append_of_ne
    (entries : List Entry) (target pauser wanted : B256)
    (hneq : wanted ≠ target) :
    oneBasedIndexAt (entries ++ [(target, pauser)]) wanted =
      oneBasedIndexAt entries wanted := by
  induction entries with
  | nil => simp [oneBasedIndexAt, Ne.symm hneq]
  | cons entry rest ih =>
      by_cases hhead : entry.1 = wanted
      · simp [oneBasedIndexAt, hhead]
      · simp [oneBasedIndexAt, hhead, ih]

theorem oneBasedIndexAt_append_target_of_findEntry_none
    {entries : List Entry} {target pauser : B256}
    (h : findEntry entries target = none) :
    oneBasedIndexAt (entries ++ [(target, pauser)]) target =
      entries.length + 1 :=
  findEntry_oneBasedIndexAt (findEntry_append_of_none h)

theorem assignmentCount_append
    (entries : List Entry) (entry : Entry) (wanted : B256) :
    assignmentCount (entries ++ [entry]) wanted =
      (if entry.2 = wanted then 1 else 0) + assignmentCount entries wanted := by
  induction entries with
  | nil => simp [assignmentCount]
  | cons head rest ih =>
      simp [assignmentCount, ih, Nat.add_left_comm]

/-- One ordered entry list witnesses every projected Registry region.  Raw
Solidity slot equality and global Keccak-injectivity are intentionally absent. -/
structure RegistryWitness (storage : LogicalStorage) (entries : List Entry) : Prop where
  targetsNodup : (entries.map Prod.fst).Nodup
  targetsValid : ∀ entry ∈ entries, nonzeroCanonicalAddress entry.1
  pausersValid : ∀ entry ∈ entries, nonzeroCanonicalAddress entry.2
  lengthWord : storage.read arrayLengthSlot = Nat.toB256 entries.length
  arrayWords : ∀ index, index < entries.length →
    storage.read (arrayEntrySlot (Nat.toB256 (index + 1))) = targetAt entries index
  assignments : ∀ target, canonicalAddress target →
    storage.read (assignmentSlot target) = assignmentAt entries target
  indices : ∀ target, canonicalAddress target →
    storage.read (indexSlot target) = Nat.toB256 (oneBasedIndexAt entries target)
  counts : ∀ pauser, canonicalAddress pauser →
    storage.read (countSlot pauser) = Nat.toB256 (assignmentCount entries pauser)
  zeroCount : storage.read (countSlot 0) = 0

def emptyStorage : LogicalStorage := { read := fun _ => 0 }

theorem emptyWitness : RegistryWitness emptyStorage [] := by
  refine ⟨by simp, ?_, ?_, by rfl, ?_, ?_, ?_, ?_, by rfl⟩
  · intro entry member; simp at member
  · intro entry member; simp at member
  · intro index bound; simp at bound
  · intro target canonical; rfl
  · intro target canonical; rfl
  · intro pauser canonical; rfl

/-- Observable ABI image of `getPausables`, preserving the witness list order. -/
def abiAddressArray (entries : List Entry) : Bytes :=
  (Nat.toB256 32).toBytes ++ (Nat.toB256 entries.length).toBytes ++
    (entries.map Prod.fst).flatMap B256.toBytes

def movedIndexRepairOmitted : List (B256 × Nat) := [(7, 1), (11, 3)]
def indexRowsFrom : Nat → List Entry → List (B256 × Nat)
  | _, [] => []
  | index, (target, _) :: rest =>
      (target, index + 1) :: indexRowsFrom (index + 1) rest

def indexRows (entries : List Entry) : List (B256 × Nat) := indexRowsFrom 0 entries

/-- Explicit falsifier fixtures retained for the later gate/proof lanes. -/
def movedIndexRepairMutantRejected : Bool :=
  movedIndexRepairOmitted != indexRows [(7, 9), (11, 12)]

def abiAddressArrayReversedMutant (entries : List Entry) : Bytes :=
  abiAddressArray entries.reverse

def abiAddressArrayOrderMutantRejected : Bool :=
  abiAddressArrayReversedMutant [(7, 9), (8, 10)] != abiAddressArray [(7, 9), (8, 10)]

theorem assignmentCount_le_length (entries : List Entry) (pauser : B256) :
    assignmentCount entries pauser ≤ entries.length := by
  induction entries with
  | nil => simp [assignmentCount]
  | cons entry rest ih =>
      simp only [assignmentCount, List.length_cons]
      split <;> omega

theorem oneBasedIndexAt_le_length (entries : List Entry) (target : B256) :
    oneBasedIndexAt entries target ≤ entries.length := by
  induction entries with
  | nil => simp [oneBasedIndexAt]
  | cons entry rest ih =>
      simp only [oneBasedIndexAt, List.length_cons]
      split
      · omega
      · split <;> omega

theorem findEntry_index_lt {entries target index pauser}
    (h : findEntry entries target = some (index, pauser)) :
    index < entries.length := by
  induction entries generalizing index pauser with
  | nil => simp [findEntry] at h
  | cons entry rest ih =>
      by_cases heq : entry.1 = target
      · simp [findEntry, heq] at h
        obtain ⟨hindex, hpauser⟩ := h
        rw [← hindex]
        exact Nat.zero_lt_succ _
      · cases hfind : findEntry rest target with
        | none => simp [findEntry, heq, hfind] at h
        | some found =>
            obtain ⟨foundIndex, foundPauser⟩ := found
            simp [findEntry, heq, hfind] at h
            obtain ⟨rfl, rfl⟩ := h
            exact Nat.succ_lt_succ (ih hfind)

theorem assignmentCount_pos_of_findEntry {entries target index pauser}
    (h : findEntry entries target = some (index, pauser)) :
    0 < assignmentCount entries pauser := by
  induction entries generalizing index with
  | nil => simp [findEntry] at h
  | cons entry rest ih =>
      by_cases heq : entry.1 = target
      · simp [findEntry, heq] at h
        obtain ⟨hindex, hpauser⟩ := h
        simp [assignmentCount, hpauser]
      · cases hfind : findEntry rest target with
        | none => simp [findEntry, heq, hfind] at h
        | some found =>
            obtain ⟨foundIndex, foundPauser⟩ := found
            simp [findEntry, heq, hfind] at h
            obtain ⟨rfl, rfl⟩ := h
            simp only [assignmentCount]
            split
            · omega
            · simpa using ih hfind

theorem setEntryAt_length_of_lt
    (entries : List Entry) (entry : Entry) {index : Nat}
    (hindex : index < entries.length) :
    (setEntryAt index entry entries).length = entries.length := by
  induction entries generalizing index with
  | nil => simp at hindex
  | cons head rest ih =>
      cases index with
      | zero => simp [setEntryAt]
      | succ index =>
          simp [setEntryAt, ih (Nat.lt_of_succ_lt_succ hindex)]

theorem setEntryAt_targets_of_findEntry
    {entries : List Entry} {target newPauser : B256} {index : Nat} {oldPauser : B256}
    (h : findEntry entries target = some (index, oldPauser)) :
    (setEntryAt index (target, newPauser) entries).map Prod.fst =
      entries.map Prod.fst := by
  induction entries generalizing index oldPauser with
  | nil => simp [findEntry] at h
  | cons entry rest ih =>
      by_cases heq : entry.1 = target
      · simp [findEntry, heq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [setEntryAt, heq]
      · cases hfind : findEntry rest target with
        | none => simp [findEntry, heq, hfind] at h
        | some found =>
            obtain ⟨foundIndex, foundPauser⟩ := found
            simp [findEntry, heq, hfind] at h
            obtain ⟨rfl, rfl⟩ := h
            simp [setEntryAt, ih hfind]

theorem findEntry_setEntryAt_of_findEntry
    {entries : List Entry} {target newPauser : B256} {index : Nat} {oldPauser : B256}
    (h : findEntry entries target = some (index, oldPauser)) :
    findEntry (setEntryAt index (target, newPauser) entries) target =
      some (index, newPauser) := by
  induction entries generalizing index oldPauser with
  | nil => simp [findEntry] at h
  | cons entry rest ih =>
      by_cases heq : entry.1 = target
      · simp [findEntry, heq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [findEntry, setEntryAt]
      · cases hfind : findEntry rest target with
        | none => simp [findEntry, heq, hfind] at h
        | some found =>
            obtain ⟨foundIndex, foundPauser⟩ := found
            simp [findEntry, heq, hfind] at h
            obtain ⟨rfl, rfl⟩ := h
            simp [findEntry, setEntryAt, heq, ih hfind]

theorem targetAt_setEntryAt_of_findEntry
    {entries : List Entry} {target newPauser : B256} {index : Nat} {oldPauser : B256}
    (h : findEntry entries target = some (index, oldPauser))
    {wantedIndex : Nat} (hwanted : wantedIndex < entries.length) :
    targetAt (setEntryAt index (target, newPauser) entries) wantedIndex =
      targetAt entries wantedIndex := by
  induction entries generalizing index oldPauser wantedIndex with
  | nil => simp [findEntry] at h
  | cons entry rest ih =>
      by_cases heq : entry.1 = target
      · simp [findEntry, heq] at h
        obtain ⟨rfl, rfl⟩ := h
        cases wantedIndex with
        | zero => simpa [setEntryAt, targetAt] using heq.symm
        | succ wantedIndex => rfl
      · cases hfind : findEntry rest target with
        | none => simp [findEntry, heq, hfind] at h
        | some found =>
            obtain ⟨foundIndex, foundPauser⟩ := found
            simp [findEntry, heq, hfind] at h
            obtain ⟨rfl, rfl⟩ := h
            cases wantedIndex with
            | zero => rfl
            | succ wantedIndex =>
                simp only [setEntryAt, targetAt]
                exact ih hfind (Nat.lt_of_succ_lt_succ hwanted)

theorem assignmentAt_setEntryAt_of_findEntry_ne
    {entries : List Entry} {target newPauser wanted : B256} {index : Nat} {oldPauser : B256}
    (h : findEntry entries target = some (index, oldPauser))
    (hneq : wanted ≠ target) :
    assignmentAt (setEntryAt index (target, newPauser) entries) wanted =
      assignmentAt entries wanted := by
  induction entries generalizing index oldPauser with
  | nil => simp [findEntry] at h
  | cons entry rest ih =>
      by_cases heq : entry.1 = target
      · simp [findEntry, heq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [setEntryAt, assignmentAt, heq, Ne.symm hneq]
      · cases hfind : findEntry rest target with
        | none => simp [findEntry, heq, hfind] at h
        | some found =>
            obtain ⟨foundIndex, foundPauser⟩ := found
            simp [findEntry, heq, hfind] at h
            obtain ⟨rfl, rfl⟩ := h
            by_cases hwanted : entry.1 = wanted
            · simp [setEntryAt, assignmentAt, hwanted]
            · simp [setEntryAt, assignmentAt, hwanted, ih hfind]

theorem oneBasedIndexAt_setEntryAt_of_findEntry
    {entries : List Entry} {target newPauser wanted : B256} {index : Nat} {oldPauser : B256}
    (h : findEntry entries target = some (index, oldPauser)) :
    oneBasedIndexAt (setEntryAt index (target, newPauser) entries) wanted =
      oneBasedIndexAt entries wanted := by
  induction entries generalizing index oldPauser with
  | nil => simp [findEntry] at h
  | cons entry rest ih =>
      by_cases heq : entry.1 = target
      · simp [findEntry, heq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [setEntryAt, oneBasedIndexAt, heq]
      · cases hfind : findEntry rest target with
        | none => simp [findEntry, heq, hfind] at h
        | some found =>
            obtain ⟨foundIndex, foundPauser⟩ := found
            simp [findEntry, heq, hfind] at h
            obtain ⟨rfl, rfl⟩ := h
            by_cases hwanted : entry.1 = wanted
            · simp [setEntryAt, oneBasedIndexAt, hwanted]
            · simp [setEntryAt, oneBasedIndexAt, hwanted, ih hfind]

theorem assignmentCount_setEntryAt_of_findEntry
    {entries : List Entry} {target newPauser wanted : B256} {index : Nat} {oldPauser : B256}
    (h : findEntry entries target = some (index, oldPauser)) :
    assignmentCount (setEntryAt index (target, newPauser) entries) wanted =
      (assignmentCount entries wanted - (if oldPauser = wanted then 1 else 0)) +
        (if newPauser = wanted then 1 else 0) := by
  induction entries generalizing index oldPauser with
  | nil => simp [findEntry] at h
  | cons entry rest ih =>
      by_cases heq : entry.1 = target
      · simp [findEntry, heq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [setEntryAt, assignmentCount, Nat.add_comm]
      · cases hfind : findEntry rest target with
        | none => simp [findEntry, heq, hfind] at h
        | some found =>
            obtain ⟨foundIndex, foundPauser⟩ := found
            simp [findEntry, heq, hfind] at h
            obtain ⟨rfl, rfl⟩ := h
            simp only [setEntryAt, assignmentCount]
            rw [ih hfind]
            have hpos : 0 < assignmentCount rest foundPauser :=
              assignmentCount_pos_of_findEntry hfind
            by_cases hfound : foundPauser = wanted
            · subst wanted
              simp at hpos ⊢
              omega
            · simp [hfound, Nat.add_assoc]

theorem setEntryAt_targetsValid_of_findEntry
    {entries : List Entry} {target newPauser : B256} {index : Nat} {oldPauser : B256}
    (h : findEntry entries target = some (index, oldPauser))
    (hvalid : ∀ entry ∈ entries, nonzeroCanonicalAddress entry.1) :
    ∀ entry ∈ setEntryAt index (target, newPauser) entries,
      nonzeroCanonicalAddress entry.1 := by
  intro entry hentry
  have hmem : entry.1 ∈ entries.map Prod.fst := by
    rw [← setEntryAt_targets_of_findEntry h]
    exact List.mem_map.mpr ⟨entry, hentry, rfl⟩
  obtain ⟨oldEntry, holdEntry, htarget⟩ := List.mem_map.mp hmem
  rw [← htarget]
  exact hvalid oldEntry holdEntry

theorem setEntryAt_pausersValid_of_findEntry
    {entries : List Entry} {target newPauser : B256} {index : Nat} {oldPauser : B256}
    (h : findEntry entries target = some (index, oldPauser))
    (hvalid : ∀ entry ∈ entries, nonzeroCanonicalAddress entry.2)
    (hnew : nonzeroCanonicalAddress newPauser) :
    ∀ entry ∈ setEntryAt index (target, newPauser) entries,
      nonzeroCanonicalAddress entry.2 := by
  revert hvalid hnew
  induction entries generalizing index oldPauser with
  | nil => simp [findEntry] at h
  | cons entry rest ih =>
      intro hvalid hnew
      by_cases heq : entry.1 = target
      · simp [findEntry, heq] at h
        obtain ⟨rfl, rfl⟩ := h
        intro candidate hcandidate
        simp only [setEntryAt, List.mem_cons] at hcandidate
        rcases hcandidate with hcandidate | hcandidate
        · simpa [hcandidate] using hnew
        · exact hvalid candidate (by simp [hcandidate])
      · cases hfind : findEntry rest target with
        | none => simp [findEntry, heq, hfind] at h
        | some found =>
            obtain ⟨foundIndex, foundPauser⟩ := found
            simp [findEntry, heq, hfind] at h
            obtain ⟨rfl, rfl⟩ := h
            intro candidate hcandidate
            simp only [setEntryAt, List.mem_cons] at hcandidate
            rcases hcandidate with hcandidate | hcandidate
            · exact hvalid candidate (by simp [hcandidate])
            · exact ih hfind
                (fun old hold => hvalid old (by simp [hold]))
                hnew candidate hcandidate

theorem setEntryAt_length_of_findEntry
    {entries : List Entry} {target newPauser : B256} {index : Nat} {oldPauser : B256}
    (h : findEntry entries target = some (index, oldPauser)) :
    (setEntryAt index (target, newPauser) entries).length = entries.length :=
  setEntryAt_length_of_lt entries (target, newPauser) (findEntry_index_lt h)

theorem assignmentAt_setEntryAt_target_of_findEntry
    {entries : List Entry} {target newPauser : B256} {index : Nat} {oldPauser : B256}
    (h : findEntry entries target = some (index, oldPauser)) :
    assignmentAt (setEntryAt index (target, newPauser) entries) target = newPauser :=
  findEntry_assignmentAt (findEntry_setEntryAt_of_findEntry h)

theorem dropLast_length (entries : List Entry) :
    (dropLast entries).length = entries.length - 1 := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      cases rest with
      | nil => rfl
      | cons head tail =>
          simp only [dropLast, List.length_cons, ih]
          omega

theorem last_some_of_length_pos (entries : List Entry) (h : 0 < entries.length) :
    ∃ last, last? entries = some last := by
  induction entries with
  | nil => simp at h
  | cons entry rest ih =>
      cases rest with
      | nil => exact ⟨entry, rfl⟩
      | cons head tail =>
          simpa [last?] using ih (by simp)

theorem last_some_of_findEntry {entries target index pauser}
    (h : findEntry entries target = some (index, pauser)) :
    ∃ last, last? entries = some last :=
  last_some_of_length_pos entries (by
    have hindex := findEntry_index_lt h
    omega)

theorem last_mem_of_last
    (entries : List Entry) {last : Entry} (h : last? entries = some last) :
    last ∈ entries := by
  induction entries with
  | nil => simp [last?] at h
  | cons entry rest ih =>
      cases rest with
      | nil =>
          simp [last?] at h
          exact h.symm ▸ List.mem_singleton_self entry
      | cons head tail =>
          simp only [last?] at h
          exact List.mem_cons_of_mem _ (ih h)

theorem dropLast_mem
    (entries : List Entry) {candidate : Entry}
    (h : candidate ∈ dropLast entries) : candidate ∈ entries := by
  induction entries with
  | nil => simp [dropLast] at h
  | cons entry rest ih =>
      cases rest with
      | nil => simp [dropLast] at h
      | cons head tail =>
          simp only [dropLast, List.mem_cons] at h ⊢
          rcases h with h | h
          · exact Or.inl h
          · exact Or.inr (by simpa using ih h)

theorem targetAt_last_of_last
    (entries : List Entry) {last : Entry}
    (h : last? entries = some last) :
    targetAt entries (entries.length - 1) = last.1 := by
  induction entries with
  | nil => simp [last?] at h
  | cons entry rest ih =>
      cases rest with
      | nil =>
          simp [last?] at h
          obtain rfl := h
          rfl
      | cons head tail =>
          simp only [List.length_cons, Nat.succ_sub_one, targetAt]
          exact ih h

theorem targetAt_dropLast_of_lt
    (entries : List Entry) {index : Nat}
    (hindex : index < entries.length - 1) :
    targetAt (dropLast entries) index = targetAt entries index := by
  induction entries generalizing index with
  | nil => simp at hindex
  | cons entry rest ih =>
      cases rest with
      | nil => simp at hindex
      | cons head tail =>
          cases index with
          | zero => rfl
          | succ index =>
              simp only [dropLast, targetAt]
              apply ih
              simp only [List.length_cons, Nat.succ_sub_one] at hindex ⊢
              omega

theorem targetAt_setEntryAt_self
    (entries : List Entry) (entry : Entry) {index : Nat}
    (hindex : index < entries.length) :
    targetAt (setEntryAt index entry entries) index = entry.1 := by
  induction entries generalizing index with
  | nil => simp at hindex
  | cons head rest ih =>
      cases index with
      | zero => rfl
      | succ index =>
          simp only [setEntryAt, targetAt]
          exact ih (Nat.lt_of_succ_lt_succ hindex)

theorem swapPop_length_of_lt
    (entries : List Entry) (index : Nat) (hindex : index < entries.length) :
    (swapPop entries index).length = entries.length - 1 := by
  obtain ⟨last, hlast⟩ := last_some_of_length_pos entries (by omega)
  simp only [swapPop, hlast, dropLast_length]
  rw [setEntryAt_length_of_lt entries last hindex]

theorem swapPop_length_of_findEntry {entries target index pauser}
    (h : findEntry entries target = some (index, pauser)) :
    (swapPop entries index).length = entries.length - 1 :=
  swapPop_length_of_lt entries index (findEntry_index_lt h)

theorem targetAt_swapPop_moved_of_lt_last
    (entries : List Entry) {index : Nat}
    (hindex : index + 1 < entries.length) :
    targetAt (swapPop entries index) index =
      targetAt entries (entries.length - 1) := by
  obtain ⟨last, hlast⟩ := last_some_of_length_pos entries (by omega)
  simp only [swapPop, hlast]
  rw [targetAt_dropLast_of_lt (setEntryAt index last entries) (by
    rw [setEntryAt_length_of_lt entries last (by omega)]
    omega)]
  rw [targetAt_setEntryAt_self entries last (by omega)]
  exact (targetAt_last_of_last entries hlast).symm

theorem targetAt_setEntryAt_of_ne
    (entries : List Entry) (entry : Entry) {index wantedIndex : Nat}
    (hindex : index < entries.length) (hneq : wantedIndex ≠ index) :
    targetAt (setEntryAt index entry entries) wantedIndex =
      targetAt entries wantedIndex := by
  induction entries generalizing index wantedIndex with
  | nil => simp at hindex
  | cons head rest ih =>
      cases index with
      | zero =>
          cases wantedIndex with
          | zero => simp at hneq
          | succ wantedIndex => rfl
      | succ index =>
          cases wantedIndex with
          | zero => rfl
          | succ wantedIndex =>
              simp only [setEntryAt, targetAt]
              apply ih (Nat.lt_of_succ_lt_succ hindex)
              exact fun h => hneq (congrArg Nat.succ h)

theorem targetAt_swapPop_of_ne
    (entries : List Entry) {index wantedIndex : Nat}
    (hindex : index < entries.length)
    (hwanted : wantedIndex < entries.length - 1)
    (hneq : wantedIndex ≠ index) :
    targetAt (swapPop entries index) wantedIndex =
      targetAt entries wantedIndex := by
  obtain ⟨last, hlast⟩ := last_some_of_length_pos entries (by omega)
  simp only [swapPop, hlast]
  rw [targetAt_dropLast_of_lt (setEntryAt index last entries) (by
    rw [setEntryAt_length_of_lt entries last hindex]
    exact hwanted)]
  exact targetAt_setEntryAt_of_ne entries last hindex hneq

theorem targetAt_mem_targets_of_lt
    (entries : List Entry) {index : Nat} (hindex : index < entries.length) :
    targetAt entries index ∈ entries.map Prod.fst := by
  induction entries generalizing index with
  | nil => simp at hindex
  | cons entry rest ih =>
      cases index with
      | zero => simp [targetAt]
      | succ index =>
          simp only [targetAt, List.map_cons, List.mem_cons]
          exact Or.inr (ih (Nat.lt_of_succ_lt_succ hindex))

theorem oneBasedIndexAt_targetAt_of_lt
    (entries : List Entry) {index : Nat}
    (hnodup : (entries.map Prod.fst).Nodup)
    (hindex : index < entries.length) :
    oneBasedIndexAt entries (targetAt entries index) = index + 1 := by
  induction entries generalizing index with
  | nil => simp at hindex
  | cons entry rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases hnodup with ⟨hnot, hrestNodup⟩
      cases index with
      | zero => simp [targetAt, oneBasedIndexAt]
      | succ index =>
          have hmem := targetAt_mem_targets_of_lt rest
            (Nat.lt_of_succ_lt_succ hindex)
          have hne : entry.1 ≠ targetAt rest index := by
            intro heq
            apply hnot
            rw [heq]
            exact hmem
          have htail := ih hrestNodup (Nat.lt_of_succ_lt_succ hindex)
          simp [targetAt, oneBasedIndexAt, hne, htail]

private theorem last?_eq_getLast? (entries : List Entry) :
    last? entries = entries.getLast? := by
  induction entries with
  | nil => rfl
  | cons head rest ih =>
      cases rest with
      | nil => rfl
      | cons next tail => simpa [last?] using ih

private theorem setEntryAt_eq_set
    (entries : List Entry) (index : Nat) (entry : Entry) :
    setEntryAt index entry entries = entries.set index entry := by
  induction entries generalizing index with
  | nil => cases index <;> rfl
  | cons head rest ih =>
      cases index with
      | zero => rfl
      | succ index =>
          simp only [setEntryAt, List.set]
          rw [ih]

private theorem dropLast_eq_listDropLast (entries : List Entry) :
    dropLast entries = entries.dropLast := by
  induction entries with
  | nil => rfl
  | cons head rest ih =>
      cases rest with
      | nil => rfl
      | cons next tail =>
          simp only [dropLast, List.dropLast_cons_cons]
          rw [ih]

private theorem last_cons_of_ne_nil (head : Entry) (rest : List Entry)
    (h : rest ≠ []) : last? (head :: rest) = last? rest := by
  cases rest with
  | nil => simp at h
  | cons head' rest' => rfl

private theorem setEntryAt_ne_nil_of_lt
    (entries : List Entry) (entry : Entry) {index : Nat}
    (hindex : index < entries.length) :
    setEntryAt index entry entries ≠ [] := by
  intro hnil
  have hlength := setEntryAt_length_of_lt entries entry hindex
  rw [hnil] at hlength
  simp at hlength
  omega

theorem last_setEntryAt_self_last
    (entries : List Entry) {last : Entry} {index : Nat}
    (hlast : last? entries = some last) (hindex : index < entries.length) :
    last? (setEntryAt index last entries) = some last := by
  induction entries generalizing index with
  | nil => simp at hindex
  | cons entry rest ih =>
      cases index with
      | zero =>
          cases rest with
          | nil =>
              simp [last?] at hlast
              obtain rfl := hlast
              rfl
          | cons head tail =>
              simp only [setEntryAt]
              rw [last_cons_of_ne_nil]
              · exact hlast
              · simp
      | succ index =>
          have hrest : index < rest.length := Nat.lt_of_succ_lt_succ hindex
          have hrestne : rest ≠ [] := by
            intro hnil
            simp [hnil] at hrest
          have hlastRest : last? rest = some last := by
            rw [← last_cons_of_ne_nil entry rest hrestne]
            exact hlast
          simp only [setEntryAt]
          rw [last_cons_of_ne_nil _ _ (setEntryAt_ne_nil_of_lt rest last hrest)]
          exact ih hlastRest hrest

/-- Swap-pop removes exactly the indexed entry up to permutation.  This is the
structural kernel used to transport the target and assignment model fields. -/
theorem swapPop_perm_eraseIdx_of_lt
    (entries : List Entry) (index : Nat) (hindex : index < entries.length) :
    List.Perm (swapPop entries index) (entries.eraseIdx index) := by
  obtain ⟨last, hlast⟩ := last_some_of_length_pos entries (by omega)
  have hupdatedLength :
      (setEntryAt index last entries).length = entries.length :=
    setEntryAt_length_of_lt entries last hindex
  have hupdatedLast :
      last? (setEntryAt index last entries) = some last :=
    last_setEntryAt_self_last entries hlast hindex
  have hgetLast :
      (setEntryAt index last entries)[entries.length - 1]? = some last := by
    rw [last?_eq_getLast?] at hupdatedLast
    rw [List.getLast?_eq_getElem?] at hupdatedLast
    simpa [hupdatedLength] using hupdatedLast
  have hperm :
      List.Perm (setEntryAt index last entries)
        (last :: entries.eraseIdx index) := by
    rw [setEntryAt_eq_set]
    exact List.set_perm_cons_eraseIdx hindex last
  have hsame :
      (setEntryAt index last entries)[entries.length - 1]? =
        (last :: entries.eraseIdx index)[0]? := by
    simpa using hgetLast
  have herased :
      List.Perm
        ((setEntryAt index last entries).eraseIdx (entries.length - 1))
        ((last :: entries.eraseIdx index).eraseIdx 0) :=
    (List.perm_eraseIdx_of_getElem?_eq hsame).mpr hperm
  simp only [swapPop, hlast]
  rw [dropLast_eq_listDropLast]
  rw [List.dropLast_eq_eraseIdx (by omega : entries.length - 1 + 1 =
    (setEntryAt index last entries).length)]
  simpa using herased

theorem swapPop_targetsNodup_of_findEntry
    {entries : List Entry} {target oldPauser : B256} {index : Nat}
    (hfind : findEntry entries target = some (index, oldPauser))
    (hnodup : (entries.map Prod.fst).Nodup) :
    ((swapPop entries index).map Prod.fst).Nodup := by
  have hperm :=
    (swapPop_perm_eraseIdx_of_lt entries index (findEntry_index_lt hfind)).map
      Prod.fst
  apply hperm.nodup_iff.mpr
  simpa only [List.eraseIdx_map] using hnodup.eraseIdx index

theorem swapPop_targetsValid_of_findEntry
    {entries : List Entry} {target oldPauser : B256} {index : Nat}
    (hfind : findEntry entries target = some (index, oldPauser))
    (hvalid : ∀ entry ∈ entries, nonzeroCanonicalAddress entry.1) :
    ∀ entry ∈ swapPop entries index, nonzeroCanonicalAddress entry.1 := by
  intro entry hentry
  have hperm := swapPop_perm_eraseIdx_of_lt entries index
    (findEntry_index_lt hfind)
  have herased : entry ∈ entries.eraseIdx index := hperm.mem_iff.mp hentry
  exact hvalid entry (List.mem_of_mem_eraseIdx herased)

theorem swapPop_pausersValid_of_findEntry
    {entries : List Entry} {target oldPauser : B256} {index : Nat}
    (hfind : findEntry entries target = some (index, oldPauser))
    (hvalid : ∀ entry ∈ entries, nonzeroCanonicalAddress entry.2) :
    ∀ entry ∈ swapPop entries index, nonzeroCanonicalAddress entry.2 := by
  intro entry hentry
  have hperm := swapPop_perm_eraseIdx_of_lt entries index
    (findEntry_index_lt hfind)
  have herased : entry ∈ entries.eraseIdx index := hperm.mem_iff.mp hentry
  exact hvalid entry (List.mem_of_mem_eraseIdx herased)

private theorem assignmentAt_eq_of_mem_of_nodup
    {entries : List Entry} {wanted pauser : B256}
    (hnodup : (entries.map Prod.fst).Nodup)
    (hmem : (wanted, pauser) ∈ entries) :
    assignmentAt entries wanted = pauser := by
  induction entries with
  | nil => simp at hmem
  | cons entry rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases hnodup with ⟨hnot, hrestNodup⟩
      simp only [List.mem_cons] at hmem
      rcases hmem with hmem | hmem
      · subst entry
        simp [assignmentAt]
      · by_cases heq : entry.1 = wanted
        · exfalso
          apply hnot
          rw [heq]
          exact List.mem_map.mpr ⟨(wanted, pauser), hmem, rfl⟩
        · simp [assignmentAt, heq, ih hrestNodup hmem]

private theorem assignmentAt_eq_zero_of_not_mem_targets
    {entries : List Entry} {wanted : B256}
    (hnot : wanted ∉ entries.map Prod.fst) :
    assignmentAt entries wanted = 0 := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      have hhead : entry.1 ≠ wanted := by
        intro heq
        apply hnot
        simp [heq]
      have hrest : wanted ∉ rest.map Prod.fst := by
        intro hmem
        exact hnot (by simp [hmem])
      simp [assignmentAt, hhead, ih hrest]

private theorem assignmentAt_eq_of_perm_targetsNodup
    {left right : List Entry} (hperm : List.Perm left right)
    (hnodup : (left.map Prod.fst).Nodup) (wanted : B256) :
    assignmentAt left wanted = assignmentAt right wanted := by
  have hmapPerm := hperm.map Prod.fst
  have hrightNodup : (right.map Prod.fst).Nodup :=
    hmapPerm.nodup_iff.mp hnodup
  by_cases hmem : wanted ∈ left.map Prod.fst
  · obtain ⟨⟨foundTarget, foundPauser⟩, hentry, heq⟩ :=
      List.mem_map.mp hmem
    simp only at heq
    subst foundTarget
    have hrightMem : (wanted, foundPauser) ∈ right :=
      hperm.mem_iff.mp hentry
    calc
      assignmentAt left wanted = foundPauser :=
        assignmentAt_eq_of_mem_of_nodup hnodup hentry
      _ = assignmentAt right wanted :=
        (assignmentAt_eq_of_mem_of_nodup hrightNodup hrightMem).symm
  · have hrightNot : wanted ∉ right.map Prod.fst := by
      intro hright
      exact hmem (hmapPerm.mem_iff.mpr hright)
    rw [assignmentAt_eq_zero_of_not_mem_targets hmem,
      assignmentAt_eq_zero_of_not_mem_targets hrightNot]

private theorem assignmentAt_eraseIdx_target_of_findEntry
    {entries : List Entry} {target oldPauser : B256} {index : Nat}
    (hfind : findEntry entries target = some (index, oldPauser))
    (hnodup : (entries.map Prod.fst).Nodup) :
    assignmentAt (entries.eraseIdx index) target = 0 := by
  induction entries generalizing index oldPauser with
  | nil => simp [findEntry] at hfind
  | cons entry rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases hnodup with ⟨hnot, hrestNodup⟩
      by_cases heq : entry.1 = target
      · simp [findEntry, heq] at hfind
        obtain ⟨rfl, rfl⟩ := hfind
        exact assignmentAt_eq_zero_of_not_mem_targets (by
          simpa [heq] using hnot)
      · cases hrest : findEntry rest target with
        | none => simp [findEntry, heq, hrest] at hfind
        | some found =>
            obtain ⟨foundIndex, foundPauser⟩ := found
            simp [findEntry, heq, hrest] at hfind
            obtain ⟨rfl, rfl⟩ := hfind
            simp [List.eraseIdx, assignmentAt, heq, ih hrest hrestNodup]

private theorem assignmentAt_eraseIdx_of_findEntry_ne
    {entries : List Entry} {target oldPauser wanted : B256} {index : Nat}
    (hfind : findEntry entries target = some (index, oldPauser))
    (hneq : wanted ≠ target) :
    assignmentAt (entries.eraseIdx index) wanted =
      assignmentAt entries wanted := by
  induction entries generalizing index oldPauser with
  | nil => simp [findEntry] at hfind
  | cons entry rest ih =>
      by_cases heq : entry.1 = target
      · simp [findEntry, heq] at hfind
        obtain ⟨rfl, rfl⟩ := hfind
        simp [assignmentAt, heq, Ne.symm hneq]
      · cases hrest : findEntry rest target with
        | none => simp [findEntry, heq, hrest] at hfind
        | some found =>
            obtain ⟨foundIndex, foundPauser⟩ := found
            simp [findEntry, heq, hrest] at hfind
            obtain ⟨rfl, rfl⟩ := hfind
            by_cases hwanted : entry.1 = wanted
            · simp [List.eraseIdx, assignmentAt, hwanted]
            · simp [List.eraseIdx, assignmentAt, hwanted, ih hrest]

theorem assignmentAt_swapPop_target_of_findEntry
    {entries : List Entry} {target oldPauser : B256} {index : Nat}
    (hfind : findEntry entries target = some (index, oldPauser))
    (hnodup : (entries.map Prod.fst).Nodup) :
    assignmentAt (swapPop entries index) target = 0 := by
  have hperm := swapPop_perm_eraseIdx_of_lt entries index
    (findEntry_index_lt hfind)
  have hpostNodup := swapPop_targetsNodup_of_findEntry hfind hnodup
  rw [assignmentAt_eq_of_perm_targetsNodup hperm hpostNodup target]
  exact assignmentAt_eraseIdx_target_of_findEntry hfind hnodup

theorem assignmentAt_swapPop_of_findEntry_ne
    {entries : List Entry} {target oldPauser wanted : B256} {index : Nat}
    (hfind : findEntry entries target = some (index, oldPauser))
    (hnodup : (entries.map Prod.fst).Nodup) (hneq : wanted ≠ target) :
    assignmentAt (swapPop entries index) wanted =
      assignmentAt entries wanted := by
  have hperm := swapPop_perm_eraseIdx_of_lt entries index
    (findEntry_index_lt hfind)
  have hpostNodup := swapPop_targetsNodup_of_findEntry hfind hnodup
  rw [assignmentAt_eq_of_perm_targetsNodup hperm hpostNodup wanted]
  exact assignmentAt_eraseIdx_of_findEntry_ne hfind hneq

private theorem oneBasedIndexAt_eq_zero_of_not_mem_targets
    {entries : List Entry} {wanted : B256}
    (hnot : wanted ∉ entries.map Prod.fst) :
    oneBasedIndexAt entries wanted = 0 := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      have hhead : entry.1 ≠ wanted := by
        intro heq
        apply hnot
        simp [heq]
      have hrest : wanted ∉ rest.map Prod.fst := by
        intro hmem
        exact hnot (by simp [hmem])
      simp [oneBasedIndexAt, hhead, ih hrest]

private theorem target_not_mem_eraseIdx_of_findEntry
    {entries : List Entry} {target oldPauser : B256} {index : Nat}
    (hfind : findEntry entries target = some (index, oldPauser))
    (hnodup : (entries.map Prod.fst).Nodup) :
    target ∉ (entries.eraseIdx index).map Prod.fst := by
  induction entries generalizing index oldPauser with
  | nil => simp [findEntry] at hfind
  | cons entry rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases hnodup with ⟨hnot, hrestNodup⟩
      by_cases heq : entry.1 = target
      · simp [findEntry, heq] at hfind
        obtain ⟨rfl, rfl⟩ := hfind
        simpa [heq] using hnot
      · cases hrest : findEntry rest target with
        | none => simp [findEntry, heq, hrest] at hfind
        | some found =>
            obtain ⟨foundIndex, foundPauser⟩ := found
            simp [findEntry, heq, hrest] at hfind
            obtain ⟨rfl, rfl⟩ := hfind
            simp [List.eraseIdx, Ne.symm heq, ih hrest hrestNodup]

theorem oneBasedIndexAt_swapPop_target_of_findEntry
    {entries : List Entry} {target oldPauser : B256} {index : Nat}
    (hfind : findEntry entries target = some (index, oldPauser))
    (hnodup : (entries.map Prod.fst).Nodup) :
    oneBasedIndexAt (swapPop entries index) target = 0 := by
  have hmapPerm :=
    (swapPop_perm_eraseIdx_of_lt entries index (findEntry_index_lt hfind)).map
      Prod.fst
  apply oneBasedIndexAt_eq_zero_of_not_mem_targets
  intro hmem
  exact target_not_mem_eraseIdx_of_findEntry hfind hnodup
    (hmapPerm.mem_iff.mp hmem)

theorem oneBasedIndexAt_swapPop_moved_of_lt_last
    (entries : List Entry) {target oldPauser : B256} {index : Nat}
    {last : Entry}
    (hfind : findEntry entries target = some (index, oldPauser))
    (hnodup : (entries.map Prod.fst).Nodup)
    (hlast : last? entries = some last)
    (hindex : index + 1 < entries.length) :
    oneBasedIndexAt (swapPop entries index) last.1 = index + 1 := by
  have hpostNodup := swapPop_targetsNodup_of_findEntry hfind hnodup
  have hpostIndex : index < (swapPop entries index).length := by
    rw [swapPop_length_of_findEntry hfind]
    omega
  have hone := oneBasedIndexAt_targetAt_of_lt
    (swapPop entries index) hpostNodup hpostIndex
  have htarget : targetAt (swapPop entries index) index = last.1 := by
    rw [targetAt_swapPop_moved_of_lt_last entries hindex]
    exact targetAt_last_of_last entries hlast
  rw [htarget] at hone
  exact hone

theorem oneBasedIndexAt_swapPop_of_findEntry_none
    {entries : List Entry} {target oldPauser wanted : B256} {index : Nat}
    (hremove : findEntry entries target = some (index, oldPauser))
    (hwanted : findEntry entries wanted = none) :
    oneBasedIndexAt (swapPop entries index) wanted = 0 := by
  have hmapPerm :=
    (swapPop_perm_eraseIdx_of_lt entries index
      (findEntry_index_lt hremove)).map Prod.fst
  apply oneBasedIndexAt_eq_zero_of_not_mem_targets
  intro hmem
  have herased := hmapPerm.mem_iff.mp hmem
  have herasedTargets : wanted ∈ (entries.map Prod.fst).eraseIdx index := by
    simpa only [List.eraseIdx_map] using herased
  exact findEntry_none_target_not_mem_targets hwanted
    (List.mem_of_mem_eraseIdx herasedTargets)

theorem oneBasedIndexAt_swapPop_of_findEntry_ne_last
    {entries : List Entry} {target oldPauser wanted wantedPauser : B256}
    {index wantedIndex : Nat} {last : Entry}
    (hremove : findEntry entries target = some (index, oldPauser))
    (hwanted : findEntry entries wanted = some (wantedIndex, wantedPauser))
    (hnodup : (entries.map Prod.fst).Nodup)
    (hlast : last? entries = some last)
    (hneqTarget : wanted ≠ target) (hneqLast : wanted ≠ last.1) :
    oneBasedIndexAt (swapPop entries index) wanted = wantedIndex + 1 := by
  have hremoveIndex := findEntry_index_lt hremove
  have hwantedIndex := findEntry_index_lt hwanted
  have hneqIndex : wantedIndex ≠ index := by
    intro heq
    have hwantedTarget := findEntry_targetAt hwanted
    have hremoveTarget := findEntry_targetAt hremove
    rw [heq, hremoveTarget] at hwantedTarget
    exact hneqTarget hwantedTarget.symm
  have hneqFinal : wantedIndex ≠ entries.length - 1 := by
    intro heq
    have hwantedTarget := findEntry_targetAt hwanted
    have hlastTarget := targetAt_last_of_last entries hlast
    rw [heq, hlastTarget] at hwantedTarget
    exact hneqLast hwantedTarget.symm
  have hpostIndex : wantedIndex < entries.length - 1 := by omega
  have hpostNodup := swapPop_targetsNodup_of_findEntry hremove hnodup
  have hpostLength :
      (swapPop entries index).length = entries.length - 1 :=
    swapPop_length_of_findEntry hremove
  have hone := oneBasedIndexAt_targetAt_of_lt
    (swapPop entries index) hpostNodup (by
      rw [hpostLength]
      exact hpostIndex)
  have htarget := targetAt_swapPop_of_ne entries hremoveIndex hpostIndex
    hneqIndex
  rw [htarget, findEntry_targetAt hwanted] at hone
  exact hone

private theorem assignmentCount_pos_of_last
    (entries : List Entry) {last : Entry} (h : last? entries = some last) :
    0 < assignmentCount entries last.2 := by
  induction entries with
  | nil => simp [last?] at h
  | cons entry rest ih =>
      cases rest with
      | nil =>
          simp [last?] at h
          obtain rfl := h
          simp [assignmentCount]
      | cons head tail =>
          simp only [last?] at h
          have hpos := ih h
          simpa [assignmentCount] using
            Nat.lt_of_lt_of_le hpos (Nat.le_add_left _ _)

private theorem assignmentCount_setEntryAt_snd
    (entries : List Entry) (index : Nat) (left right : B256) (pauser : B256)
    (wanted : B256) :
    assignmentCount (setEntryAt index (left, pauser) entries) wanted =
      assignmentCount (setEntryAt index (right, pauser) entries) wanted := by
  induction entries generalizing index with
  | nil => simp [setEntryAt, assignmentCount]
  | cons entry rest ih =>
      cases index with
      | zero => rfl
      | succ index =>
          simp [setEntryAt, assignmentCount, ih index]

theorem assignmentCount_dropLast_of_last
    (entries : List Entry) {last : Entry} (h : last? entries = some last)
    (wanted : B256) :
    assignmentCount (dropLast entries) wanted =
      assignmentCount entries wanted - (if last.2 = wanted then 1 else 0) := by
  induction entries with
  | nil => simp [last?] at h
  | cons entry rest ih =>
      cases rest with
      | nil =>
          simp [last?] at h
          obtain rfl := h
          simp [assignmentCount, dropLast]
      | cons head tail =>
          simp only [dropLast, assignmentCount]
          rw [ih h]
          by_cases hlast : last.2 = wanted
          · subst wanted
            have hpos := assignmentCount_pos_of_last (head :: tail) h
            simp [assignmentCount] at hpos ⊢
            omega
          · simp [hlast, assignmentCount]

theorem assignmentCount_swapPop_of_findEntry
    {entries : List Entry} {target wanted : B256} {index : Nat} {oldPauser : B256}
    (hfind : findEntry entries target = some (index, oldPauser)) :
    assignmentCount (swapPop entries index) wanted =
      assignmentCount entries wanted - (if oldPauser = wanted then 1 else 0) := by
  obtain ⟨last, hlast⟩ := last_some_of_findEntry hfind
  simp only [swapPop, hlast]
  rw [assignmentCount_dropLast_of_last (setEntryAt index last entries)
    (last_setEntryAt_self_last entries hlast (findEntry_index_lt hfind))]
  rw [assignmentCount_setEntryAt_snd entries index last.1 target last.2 wanted]
  rw [assignmentCount_setEntryAt_of_findEntry (wanted := wanted) hfind]
  by_cases hlastWanted : last.2 = wanted
  · simp [hlastWanted]
  · simp [hlastWanted]

end Blanc.LidoCircuitBreaker
