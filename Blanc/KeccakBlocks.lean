import Jaune.Hash

/-! Small proof boundaries for concrete Keccak computations. -/
namespace Blanc.KeccakBlocks

open Jaune

def referenceRound (i : Fin 24) (ws : Vector UInt64 25) : Vector UInt64 25 :=
  KECCAK.ι i.val i.isLt KECCAK.rndc
    (KECCAK.χ (KECCAK.ρπ KECCAK.UInt64.rol (KECCAK.θ KECCAK.UInt64.rol ws)))
def sixRounds (start : Nat) (bound : start + 6 ≤ 24)
    (ws : Vector UInt64 25) : Vector UInt64 25 :=
  referenceRound ⟨start + 5, by omega⟩
    (referenceRound ⟨start + 4, by omega⟩
      (referenceRound ⟨start + 3, by omega⟩
        (referenceRound ⟨start + 2, by omega⟩
          (referenceRound ⟨start + 1, by omega⟩
            (referenceRound ⟨start, by omega⟩ ws)))))
theorem f1600_sixRounds (ws : Vector UInt64 25) :
    KECCAK.f1600 ws =
      sixRounds 18 (by decide) (sixRounds 12 (by decide)
        (sixRounds 6 (by decide) (sixRounds 0 (by decide) ws))) := by
  rw [KECCAK.f1600_eq]
  rfl

def squeeze (ws : Vector UInt64 25) : B256 :=
  ⟨⟨UInt64.byteswap ws[0], UInt64.byteswap ws[1]⟩,
    ⟨UInt64.byteswap ws[2], UInt64.byteswap ws[3]⟩⟩
theorem run_empty (wc : Fin 17) (ws : Vector UInt64 25) :
    KECCAK.Bytes.run wc [] ws =
      squeeze (KECCAK.f1600 (KECCAK.xorLane
        (KECCAK.xorLane ws wc.val (by omega) 1) 16 (by decide)
        ((8 : UInt64) <<< 60))) := by
  rfl

end Blanc.KeccakBlocks
