import Blanc.Lift.Usdc.ImplV1Creation.SigningRounds00
import Blanc.Lift.Usdc.ImplV1Creation.SigningRounds01
import Blanc.Lift.Usdc.ImplV1Creation.SigningRounds02
import Blanc.Lift.Usdc.ImplV1Creation.SigningRounds03
import Blanc.Lift.Usdc.ImplV1Creation.SigningRounds04
import Blanc.Lift.Usdc.ImplV1Creation.SigningRounds05
import Blanc.Lift.Usdc.ImplV1Creation.SigningRounds06
import Blanc.Lift.Usdc.ImplV1Creation.SigningRounds07
import Blanc.Lift.Usdc.ImplV1Creation.SigningRounds08
import Blanc.Lift.Usdc.ImplV1Creation.SigningRounds09
import Blanc.Lift.Usdc.ImplV1Creation.SigningRounds10
import Blanc.Lift.Usdc.ImplV1Creation.SigningRounds11
import Blanc.Lift.Usdc.ImplV1Creation.SigningRounds12
import Blanc.Lift.Usdc.ImplV1Creation.SigningRounds13
import Blanc.Lift.Usdc.ImplV1Creation.SigningRounds14
import Blanc.Lift.Usdc.ImplV1Creation.SigningRounds15

/-! Exact hash and signature consumers for the unadopted V1 creation preview. -/
namespace Blanc.Lift.Usdc.ImplV1Creation
open Jaune ExecutionTrace
open SigningBlocks

/-- Kernel hash of the exact conditional EIP-155 signing envelope. -/
theorem signingPayload_hash : signingPayload.keccak =
    (0x3a424731e9075d7b45dcc6ab92455664e56100fbb6419923723a54aa9d5710ad : B256) := by
  change KECCAK.Bytes.run 0 signingPayload state00 = _
  rw [payload_split]
  unfold segment0 segment1 segment2
  simp only [List.append_assoc]
  rewrite [block00, block01, block02, block03, block04, block05]
  rewrite [block06, block07, block08, block09, block10, block11]
  rewrite [block12, block13, block14, block15, block16, block17]
  rewrite [block18, block19, block20, block21, block22, block23]
  rewrite [block24, block25, block26, block27, block28, block29]
  rewrite [block30, block31, block32, block33, block34, block35]
  rewrite [block36, block37, block38, block39, block40, block41]
  rewrite [block42, block43, block44, block45, block46, block47]
  rewrite [block48, block49, block50, block51, block52, block53]
  rewrite [block54, block55, block56, block57, block58, block59]
  rewrite [block60, block61, block62, block63, block64, block65]
  rewrite [block66, block67, block68, block69, block70, block71]
  rewrite [block72, block73, block74, block75, block76, block77]
  rewrite [block78, block79, block80, block81, block82, block83]
  rewrite [block84, block85, block86, block87, block88, block89]
  exact finalHash

/-- Explicit transaction fields determine the signing hash. -/
theorem signingHash {tx : Tx}
    (htype : tx.type = .zero 4000000000 none)
    (hnonce : tx.nonce = 18) (hgas : tx.gas = 6721975)
    (hvalue : tx.value = 0) (hdata : tx.data = code.toList) (hv : tx.v = 38) :
    tx.signingHash = some 0x3a424731e9075d7b45dcc6ab92455664e56100fbb6419923723a54aa9d5710ad := by
  rw [signingEncoded htype hnonce hgas hvalue hdata hv, signingPayload_hash]

/-- These fields and signature recover the registered creator, without a hash premise. -/
theorem recoveredSender {tx : Tx}
    (htype : tx.type = .zero 4000000000 none)
    (hnonce : tx.nonce = 18) (hgas : tx.gas = 6721975)
    (hvalue : tx.value = 0) (hdata : tx.data = code.toList) (hv : tx.v = 38)
    (hr : tx.r.toB256 = 0xb27c0adac33faeeb6a7fc58d536ba8bda38e3054d53461008d39a18031531609)
    (hs : tx.s.toB256 = 0x7a25d7dc3f2f43eda8a8b560f6224aa83270bc4d8804d453b792df8200ba0d15) :
    recoverSender 1 tx = .ok ProxyCreation.originalCreator := by
  exact ImplV1Origin.recoveredSender_of_signingHash htype hv hr hs
    (signingHash htype hnonce hgas hvalue hdata hv)

/-- The original decoded signed transaction and successful receipt install V1.
Only original history, slot/field and receipt correspondence remain explicit. -/
theorem effects_of_encoded_slot
    {pre completed : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed)
    (cut : block.bodyTrace.transactions.TxSplit 30)
    {slot : Bytes ⊕ Tx} {tx : Tx}
    (atIndex : block.block.txs[30]? = some slot)
    (decoded : decodeTx block.fork.ruleSet slot = .ok tx)
    (htype : tx.type = .zero 4000000000 none)
    (hnonce : tx.nonce = 18) (hgas : tx.gas = 6721975)
    (hvalue : tx.value = 0) (hdata : tx.data = code.toList) (hv : tx.v = 38)
    (hr : tx.r.toB256 = 0xb27c0adac33faeeb6a7fc58d536ba8bda38e3054d53461008d39a18031531609)
    (hs : tx.s.toB256 = 0x7a25d7dc3f2f43eda8a8b560f6224aa83270bc4d8804d453b792df8200ba0d15)
    {receipt : Fin 5 × Receipt}
    (lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes (30 : Nat).toBytes)]? =
      some receipt) (succeeded : receipt.2.succeeded = true) :
    cut.afterBenv.state.getCode ProxyCreation.initialImplementation.toAdr = ImplV1.code ∧
      cut.afterBenv.state.getStor ProxyCreation.initialImplementation.toAdr =
        solcOwnerConstructorStorage Stor.empty ProxyCreation.originalCreator := by
  exact effects_of_signed_slot block cut atIndex decoded htype hdata hnonce hv hr hs
    (signingHash htype hnonce hgas hvalue hdata hv) lookup succeeded

end Blanc.Lift.Usdc.ImplV1Creation
