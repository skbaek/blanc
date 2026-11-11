import Jaune.Transaction
import Jaune.RlpEval

/-!
# Closed input for the deposit short-log control

This transaction calls the deposit address with empty calldata. Its signature
scalars are fixed, but its sender is obtained from the actual recovery function;
no known-key sender is assumed. Execution and the frozen control are separate.
-/

namespace Blanc.Composition.DepositShortLogInput

open Jaune

/-- The exact type-2 candidate for the alternate deposit runtime. -/
def controlTx : Tx :=
  { nonce := 2, gas := 2 ^ 20, value := 0, data := [], v := 0
    r := (0x2ba550518ad1955936234bb6ad552eeab937deecff98751c7f495a48a9594055 : B256).toBytes
    s := (0x09a1f8f3576b0e2ffd997b9d4aa4c200a5085b1a60d67f00eb7b3e21adf274ee : B256).toBytes
    type := .two 1 1 8 (some depositContractAddress) [] }

/-- Its actual signing payload, including the deposit receiver. -/
def signingPayload : Bytes :=
  [0x02, 0xe0, 0x01, 0x02, 0x01, 0x08, 0x83, 0x10, 0x00, 0x00, 0x94,
   0x00, 0x00, 0x00, 0x00, 0x21, 0x9a, 0xb5, 0x40, 0x35, 0x6c,
   0xbb, 0x83, 0x9c, 0xbe, 0x05, 0x30, 0x3d, 0x77, 0x05, 0xfa,
   0x80, 0x80, 0xc0]

theorem signing_encoded : controlTx.signingHash = some signingPayload.keccak := by
  simp only [Tx.signingHash, controlTx, AccessList.toBLT, List.map_nil]
  congr 2
  rw [BLT.toBytes_eq_toBytesS]
  simp only [Nat.toBytes_eq_toBytesS]
  decide +kernel

-- This closed cryptographic check is verified by the narrow owned build.
private theorem recovered_away_check :
    (match recoverSender 1 controlTx with
      | .ok sender => decide (sender ≠ depositContractAddress)
      | .error _ => false) = true := by
  rw [recoverSender, signing_encoded]
  decide +kernel

/-- The sender really recovers and differs from the installed logger account. -/
theorem controlTx_sender :
    ∃ sender, recoverSender 1 controlTx = .ok sender ∧
      sender ≠ depositContractAddress := by
  have checked := recovered_away_check
  cases h : recoverSender 1 controlTx with
  | error e => simp only [h, Bool.false_eq_true] at checked
  | ok sender =>
      refine ⟨sender, rfl, ?_⟩
      simpa only [h, decide_eq_true_eq] using checked

end Blanc.Composition.DepositShortLogInput
