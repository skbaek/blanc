import Blanc.BeaconDepositModel
import Blanc.RevertPayload

/-!
# Beacon deposit compiled-port vocabulary

Contract-local storage, selector, ABI, event, and error vocabulary for Blanc's
own BeaconDeposit artifact.  The pure model remains the specification; none of
the definitions below changes it or defines decoding in terms of the program
that will consume the decoded values.
-/

namespace Blanc.BeaconDeposit

open Jaune

/-! ## ABI identities -/

def supportsInterfaceSelector : B256 :=
  selector "supportsInterface" [.bytes 4]

def depositSelector : B256 :=
  selector "deposit" [.dynBytes, .dynBytes, .dynBytes, .bytes 32]

def getDepositCountSelector : B256 :=
  selector "get_deposit_count" []

def getDepositRootSelector : B256 :=
  selector "get_deposit_root" []

def erc165InterfaceId : B256 := 0x01ffc9a7
def depositInterfaceId : B256 := 0x85640907

def depositEventTopic : B256 :=
  signatureHash "DepositEvent"
    [.dynBytes, .dynBytes, .dynBytes, .dynBytes, .dynBytes]

/-! ## Return and event encodings -/

def abiDynamicBytesReturn (data : Bytes) : Bytes :=
  (32 : B256).toBytes ++ abiBytesTail data

def abiBoolReturn (answer : Bool) : Bytes :=
  (if answer then (1 : B256) else 0).toBytes

/-- Exact five-tail ABI image of `DepositEvent`. -/
def abiDepositEvent (event : DepositEvent) : Bytes :=
  (160 : B256).toBytes ++
    (256 : B256).toBytes ++
    (320 : B256).toBytes ++
    (384 : B256).toBytes ++
    (512 : B256).toBytes ++
    abiBytesTail event.pubkey ++
    abiBytesTail event.withdrawal_credentials ++
    abiBytesTail event.amount ++
    abiBytesTail event.signature ++
    abiBytesTail event.index

def depositEventLog (owner : Adr) (event : DepositEvent) : Log :=
  ⟨owner, [depositEventTopic], abiDepositEvent event⟩

end Blanc.BeaconDeposit
