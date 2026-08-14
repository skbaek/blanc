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

def assignmentCount : List Entry → B256 → Nat
  | [], _ => 0
  | (_, pauser) :: rest, wanted => (if pauser = wanted then 1 else 0) + assignmentCount rest wanted

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

end Blanc.LidoCircuitBreaker
