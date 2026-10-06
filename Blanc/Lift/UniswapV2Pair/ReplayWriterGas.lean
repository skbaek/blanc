import Blanc.Lift.UniswapV2Pair.SourceReplay
import Blanc.Lift.UniswapV2Pair.TransferFromSource

/-! Positive exact gas for LP writers at the state carried by a connected
source replay. Configured-history authentication is a separate producer. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

inductive LedgerWriter
  | approve | transfer | transferFrom

namespace LedgerWriter

def selector : LedgerWriter → B256
  | .approve => 0x095ea7b3
  | .transfer => 0xa9059cbb
  | .transferFrom => 0x23b872dd

def entry : LedgerWriter → Sevm → Entry
  | .approve => approveDecodedEntry
  | .transfer => transferDecodedEntry
  | .transferFrom => transferFromDecodedEntry

def keys : LedgerWriter → Sevm → List WriterKey
  | .approve, sevm => approveTouched sevm.caller (approveSpender sevm)
  | .transfer, sevm => transferTouched sevm.caller (transferRecipient sevm)
  | .transferFrom, sevm =>
    transferFromTouched (transferFromOwner sevm) sevm.caller (transferFromRecipient sevm)

def calldataSize : LedgerWriter → Nat
  | .approve | .transfer => 68
  | .transferFrom => 100

/-- Closed costs use the actual physical selected slots and warm/cold state. -/
def cost : LedgerWriter → Sevm → Devm → Nat
  | .approve, sevm, b => sstoreCost sevm b (approveSlot sevm) (approveAmount sevm) + 2342
  | .transfer, sevm, b => transferSourceCharge sevm b + transferDebitCharge sevm b +
      transferRecipientCharge sevm b + transferCreditCharge sevm b + 2740
  | .transferFrom, sevm, b => transferFromPublicGas sevm b

def post : LedgerWriter → Sevm → Devm → Nat → Devm
  | .approve, sevm, b, G => approvePublicPost sevm b [0x095ea7b3] getterInitMemory G
  | .transfer, sevm, b, G => transferPublicPost sevm b [0xa9059cbb] getterInitMemory G
  | .transferFrom, sevm, b, G => transferFromPublicPost sevm b [0x23b872dd] getterInitMemory G

/-- Existing source results retain exact storage, logs, return bytes and residual gas. -/
def Result (writer : LedgerWriter) (K : WriterKey → Prop) (current : Checkpoint)
    (invocation : List Nat) (sevm : Sevm) (b d : Devm) (G : Nat) : Prop :=
  match writer with
  | .approve => ApproveSourceResult K current invocation sevm b d G
  | .transfer => TransferSourceResult K current invocation sevm b d G
  | .transferFrom => TransferFromSourceResult K current invocation sevm b d G

/-- Handler acceptance constructs a positive raw pc-zero execution with the
closed physical cost. A residual above the stipend derives every store sentry. -/
theorem source_live (writer : LedgerWriter) {K : WriterKey → Prop} {current : Checkpoint}
    {invocation : List Nat} {sevm : Sevm} {b : Devm} {G : Nat}
    {sourceFrame : Frame} {returndata : Bytes}
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (fresh : WriterFreshKeys K (writer.keys sevm))
    (representable : sevm.data.length < 2 ^ 256)
    (length : writer.calldataSize ≤ sevm.data.length)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selectorEq : Blanc.Sevm.selector sevm = writer.selector)
    (residual : gCallStipend < G)
    (accepted : startImmediate current (writerContext sevm invocation) (writer.entry sevm) =
      some (.finished sourceFrame returndata)) :
    SProg.RunExact cert.prog sevm (St b [] Mem.empty (G + writer.cost sevm b))
        (writer.post sevm b G) ∧
      Nonempty (Exec 0 sevm (St b [] Mem.empty (G + writer.cost sevm b))
        (.ok (writer.post sevm b G))) ∧
      writer.Result K current invocation sevm b (writer.post sevm b G) G := by
  cases writer with
  | approve =>
    obtain ⟨machine, raw, frameEq, bytesEq, result⟩ :=
      approve_source_bytecode_exact (G := G) rep fresh representable length codeEq fork
        selectorEq rfl (by omega) accepted
    have joined := And.intro machine (And.intro raw result)
    simpa only [cost, post, Result, Nat.add_assoc] using joined
  | transfer =>
    obtain ⟨machine, raw, frameEq, bytesEq, result⟩ :=
      transfer_source_bytecode_exact (G := G) rep fresh representable length codeEq fork
        selectorEq (by omega) (by omega) accepted
    have joined := And.intro machine (And.intro raw result)
    simpa only [cost, post, Result, Nat.add_assoc] using joined
  | transferFrom =>
    obtain ⟨machine, raw, frameEq, bytesEq, result⟩ :=
      transferFrom_source_bytecode_exact (G := G) rep fresh representable length codeEq fork
        selectorEq (by intro _; omega) (by omega) (by omega) accepted
    exact ⟨machine, raw, result⟩

end LedgerWriter

end Blanc.Lift.UniswapV2Pair
