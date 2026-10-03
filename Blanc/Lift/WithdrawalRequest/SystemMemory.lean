import Blanc.Lift.WithdrawalRequest.Layout
import Blanc.MemoryLayout
import Blanc.WordByteCodecs

/-!
# The queue body's exact ordered memory writes

Word offsets and values retain the actual modulo-word arithmetic. The last
word store spans record bytes 52 through 83; the eight following byte writes
replace bytes 75 down through 68. Nothing truncates the trailing padding.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune

/-- The literal high-128-bit mask used by the certified body. -/
def systemPubkeyMask : B256 := WordByteCodecs.high128Mask

def systemRecordOffset (index : B256) : B256 := 76 * index
def systemRecordPubkeyOffset (index : B256) : B256 := 20 + systemRecordOffset index
def systemRecordSuffixOffset (index : B256) : B256 := 32 + systemRecordPubkeyOffset index
def systemRecordAmountOffset (index : B256) : B256 := 16 + systemRecordSuffixOffset index

/-- The three overlapping word writes, retaining the suffix padding. -/
def systemRecordWordStage (index caller pubkey packed : B256) : MemoryStage :=
  [( (systemRecordOffset index).toNat, (caller <<< 96).toBytes),
   ( (systemRecordPubkeyOffset index).toNat, pubkey.toBytes),
   ( (systemRecordSuffixOffset index).toNat, (systemPubkeyMask &&& packed).toBytes)]

/-- The actual decreasing-offset singleton stores for the reversed amount. -/
def systemRecordAmountStage (index packed : B256) : MemoryStage :=
  [( (7 + systemRecordAmountOffset index).toNat, [((packed >>> 64) >>> 56).2.2.toUInt8]),
   ( (6 + systemRecordAmountOffset index).toNat, [((packed >>> 64) >>> 48).2.2.toUInt8]),
   ( (5 + systemRecordAmountOffset index).toNat, [((packed >>> 64) >>> 40).2.2.toUInt8]),
   ( (4 + systemRecordAmountOffset index).toNat, [((packed >>> 64) >>> 32).2.2.toUInt8]),
   ( (3 + systemRecordAmountOffset index).toNat, [((packed >>> 64) >>> 24).2.2.toUInt8]),
   ( (2 + systemRecordAmountOffset index).toNat, [((packed >>> 64) >>> 16).2.2.toUInt8]),
   ( (1 + systemRecordAmountOffset index).toNat, [((packed >>> 64) >>> 8).2.2.toUInt8]),
   ( (systemRecordAmountOffset index).toNat, [(packed >>> 64).2.2.toUInt8])]

/-- All eleven writes in execution order, with ordinary last-write-wins overlap. -/
def systemRecordStage (index caller pubkey packed : B256) : MemoryStage :=
  systemRecordWordStage index caller pubkey packed ++ systemRecordAmountStage index packed

def systemRecordMemory (index caller pubkey packed : B256) (memory : Mem) : Mem :=
  (systemRecordStage index caller pubkey packed).applyMemory memory

def systemRecordImage (index caller pubkey packed : B256) (image : Bytes) : Bytes :=
  (systemRecordStage index caller pubkey packed).applyImage image

/-- The exact machine image correspondence retains the full padded footprint. -/
theorem systemRecordMemory_image (index caller pubkey packed : B256)
    {memory : Mem} {image : Bytes} (wf : Mem.Wf memory) (reads : Mem.Reads memory image) :
    Mem.Wf (systemRecordMemory index caller pubkey packed memory) ∧
      Mem.Reads (systemRecordMemory index caller pubkey packed memory)
        (systemRecordImage index caller pubkey packed image) :=
  MemoryStage.wf_reads (systemRecordStage index caller pubkey packed) wf reads

/-- The actual accesses used for allocation, including the 32-byte suffix store. -/
theorem systemRecordStage_footprint (index caller pubkey packed : B256) :
    (systemRecordStage index caller pubkey packed).footprint =
      [( (systemRecordOffset index).toNat, 32),
       ( (systemRecordPubkeyOffset index).toNat, 32),
       ( (systemRecordSuffixOffset index).toNat, 32),
       ( (7 + systemRecordAmountOffset index).toNat, 1),
       ( (6 + systemRecordAmountOffset index).toNat, 1),
       ( (5 + systemRecordAmountOffset index).toNat, 1),
       ( (4 + systemRecordAmountOffset index).toNat, 1),
       ( (3 + systemRecordAmountOffset index).toNat, 1),
       ( (2 + systemRecordAmountOffset index).toNat, 1),
       ( (1 + systemRecordAmountOffset index).toNat, 1),
       ( (systemRecordAmountOffset index).toNat, 1)] := by
  simp only [systemRecordStage, systemRecordWordStage, systemRecordAmountStage,
    MemoryStage.footprint, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append,
    B256.length_toBytes, List.length_cons, List.length_nil]

/-- Allocation follows every primitive write, rather than the 76-byte record width. -/
theorem systemRecordMemory_size (index caller pubkey packed : B256) (memory : Mem)
    (aligned : memory.size % 32 = 0) :
    (systemRecordMemory index caller pubkey packed memory).size =
      memExtsSize memory.size (systemRecordStage index caller pubkey packed).footprint :=
  MemoryStage.applyMemory_size (systemRecordStage index caller pubkey packed) memory aligned


/-- The selected expansion-inclusive charge at each actual amount write. -/
def systemRecordAmountCharge (index packed : B256) (memory : Mem) (n : Nat) : Nat :=
  match (systemRecordAmountStage index packed)[n]? with
  | none => 0
  | some (offset, payload) =>
    let before := MemoryStage.applyMemory ((systemRecordAmountStage index packed).take n) memory
    gVerylow + (calculateMemoryGasCost (memExtSize before.size offset payload.length)
      - calculateMemoryGasCost before.size)

/-- The selected expansion-inclusive charge at each actual word write. -/
def systemRecordWordCharge (index caller pubkey packed : B256) (memory : Mem) (n : Nat) : Nat :=
  match (systemRecordWordStage index caller pubkey packed)[n]? with
  | none => 0
  | some (offset, payload) =>
    let before := MemoryStage.applyMemory ((systemRecordWordStage index caller pubkey packed).take n) memory
    gVerylow + (calculateMemoryGasCost (memExtSize before.size offset payload.length)
      - calculateMemoryGasCost before.size)
end Blanc.Lift.WithdrawalRequest
