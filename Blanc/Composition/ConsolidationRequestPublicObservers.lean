import Blanc.SystemContracts
import Blanc.WordFakeExponential

/-!
# EIP-7251 public observers

Short observers reading a `State` directly: the predeploy address and code,
one storage slot, the EIP fee and the quoted fee, and the queue as stored.
Nothing here mentions the delivery model; the correspondence to the model is
proved in `ConsolidationRequestPublicHeadlines`. History observers
(`submissions`, `records116`, checkpoints) live in a later unit, not here.
-/

namespace Blanc.Composition.ConsolidationRequestPublic

open Jaune Blanc

/-- The EIP-7251 predeploy address `0x0000BBdDc7CE488642fb579F8B00f3a590007251`. -/
abbrev addr : Adr := consolidationRequestPredeployAddress

/-- The 414 canonical runtime bytes (SHA-256 `99e3d84d…d661`). -/
abbrev code : ByteArray := Blanc.consolidationRequestCode

/-- The canonical runtime sits at the predeploy. -/
def installed (w : State) : Prop := w.getCode addr = code

/-- Storage slot `k` of the predeploy in world `w`. -/
def word (w : State) (k : B256) : B256 := (w.getStor addr).get k

/-- The EIP's fee at excess `excess`: `fake_exponential(1, excess, 17)`. -/
def SpecFee (excess : B256) : Nat := fakeExp 1 excess.toNat 17

/-- The fee the bytes quote at excess `excess`: the word the fee loop leaves, divided by 17. -/
noncomputable def quotedFee (excess : B256) : Nat :=
  ((Classical.choose (Blanc.WordFakeExponential.run_exists_unique excess 17 1 17 0).exists).2 /
    (17 : B256)).toNat

/-- The loop's iteration count at `excess` (the same unique run). -/
noncomputable def quotedIterations (excess : B256) : Nat :=
  (Classical.choose (Blanc.WordFakeExponential.run_exists_unique excess 17 1 17 0).exists).1

/-- Queue entry `i`, read from slots `4 + 4i` to `4 + 4i + 3`: the source address, then the 96 submitted bytes. -/
def queueRecord (s : B256 → B256) (i : Nat) : Bytes :=
  (s (4 + 4 * i).toB256).toAdr.toBytes ++ (s (4 + 4 * i + 1).toB256).toBytes ++
    (s (4 + 4 * i + 2).toB256).toBytes ++ (s (4 + 4 * i + 3).toB256).toBytes

/-- The live queue: entries from the head word (slot 2) up to, excluding, the tail word (slot 3). -/
def storedQueue (s : B256 → B256) : List Bytes :=
  (List.range ((s 3).toNat - (s 2).toNat)).map fun i => queueRecord s ((s 2).toNat + i)

/-- The queue still stored in world `w`. -/
def remainingQueue (w : State) : List Bytes := storedQueue (w.getStor addr).get

/-- A submission's record: the caller's 20 bytes, then its 96 calldata bytes. -/
def submissionRecord (f : Exec.Frame) : Bytes := f.sevm.caller.toBytes ++ f.sevm.data

end Blanc.Composition.ConsolidationRequestPublic
