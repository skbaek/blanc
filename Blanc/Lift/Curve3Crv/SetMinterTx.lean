import Blanc.Lift.Curve3Crv.HistDeployment
import Blanc.Lift.CallerProvenance
import Blanc.ExecutionTraceRootFrame
import Blanc.ExecutionHistoryMuirCut
import Blanc.ForwardCall
import Blanc.RlpListEncode

/-!
# The minter assignment: 3Crv's recorded `set_minter(pool)` transaction

The signed legacy call (hash `0x1cf0ab86…49bab898`, block 10,809,482, index 135): sender nonce 45,
gas 27,444, gas price 118,289,796,819 wei, to 3Crv, zero value, calldata
`set_minter(0xbebc…1c7)`, pre-EIP-155 `v = 28`.

* `rawHash`, `tx_encoded`: the signed bytes have the recorded transaction hash and are `tx`'s
  canonical encoding.
* `root_of_success`: under Muir Glacier, a successful message of that transaction leaves a settled
  frame at 3Crv whose calldata is the recorded one.
* `decodeCall_of_data`, `minter_of_setMinter`: such a frame decodes to `set_minter(pool)`, and the
  model's accepted step leaves the pool as minter.

Who the caller is plays no part: the model accepts `set_minter` only from the current minter, so a
successful receipt alone says the assignment took place.
-/

namespace Blanc.Lift.Curve3Crv.SetMinter

open Jaune Blanc.ExecutionTrace Blanc.Lift.Curve3Crv.Creation

/-- The argument word: the 3pool's address. -/
def poolWord : B256 := 0xbebc44782c7db0a1a60cb6fe97d0b483032ff1c7

/-- The recorded calldata: the `set_minter` selector and the pool's word. -/
def callData : Bytes := [0x16, 0x52, 0xe9, 0xfc] ++ poolWord.toBytes

/-- The signature's first scalar. -/
def rBytes : Bytes :=
  [0xf2, 0xc1, 0xd3, 0x5d, 0xb4, 0x86, 0x8a, 0xdc,
   0xc4, 0x7c, 0x6c, 0x4a, 0x2b, 0xc2, 0xd3, 0x5e,
   0x23, 0xae, 0xa7, 0xf2, 0xc5, 0xe8, 0x2b, 0x7e,
   0x6f, 0xcb, 0x04, 0x9d, 0x8e, 0x36, 0x9e, 0x42]

/-- The signature's second scalar. -/
def sBytes : Bytes :=
  [0x5a, 0x25, 0x5f, 0xfb, 0xbe, 0xd4, 0xf1, 0x58,
   0xb6, 0xaf, 0xcc, 0xcf, 0x5f, 0x81, 0xa4, 0x93,
   0xf1, 0x8c, 0x29, 0x9e, 0x08, 0xc2, 0xa2, 0xcf,
   0xf2, 0x52, 0x6d, 0xd2, 0x56, 0xc9, 0x5f, 0xb0]

/-- The recorded `set_minter` transaction. -/
def tx : Tx :=
  { nonce := 45, gas := 27444, value := 0, data := callData,
    v := 28, r := rBytes, s := sBytes, type := .zero 118289796819 (some tokenAddress) }

/-- The recorded signed bytes. -/
def raw : Bytes :=
  [0xf8, 0x88, 0x2d, 0x85, 0x1b, 0x8a, 0x9f, 0x0e, 0xd3, 0x82, 0x6b, 0x34, 0x94] ++
    tokenAddress.toBytes ++ [0x80, 0xa4] ++ callData ++ [0x1c, 0xa0] ++ rBytes ++ [0xa0] ++ sBytes

/-- The signed bytes have the recorded transaction hash. -/
theorem rawHash :
    raw.keccak =
        (0x1cf0ab86da6426d42fc9e45eccf742d9215025c77b4c05b97b0c497f49bab898 : B256) := by
  decide +kernel

/-- The nine legacy byte-string fields. -/
def fields : List BLT :=
  [.bytes [0x2d], .bytes [0x1b, 0x8a, 0x9f, 0x0e, 0xd3], .bytes [0x6b, 0x34],
   .bytes tokenAddress.toBytes, .bytes [], .bytes callData, .bytes [0x1c], .bytes rBytes,
   .bytes sBytes]

theorem tx_toBLT : tx.toBLT = .list fields := by
  simp only [tx, Tx.toBLT, fields]
  simp only [BLT.list.injEq, List.cons.injEq, BLT.bytes.injEq, and_true, true_and]
  decide +kernel

/-- Canonical signed re-encoding returns precisely the recorded bytes. -/
theorem tx_encoded : tx.toBLT.toBytes = raw := by
  rw [tx_toBLT, BLT.toBytes, BLTs.toBytes_eq_wrapS, BLTs.toBytesJoin_eq_toBytesJoinS]
  decide +kernel

/-- A frame with the recorded calldata decodes to `set_minter(pool)`. -/
theorem decodeCall_of_data {sevm : Sevm} (data : sevm.data = callData) :
    decodeCall sevm = .setMinter poolWord := by
  have hlen : ¬ sevm.data.length < 4 := by rw [data]; decide +kernel
  have hsel : Sevm.selector sevm = selSetMinter := by
    unfold Sevm.selector Sevm.dataWord
    rw [data]
    decide +kernel
  have harg : Sevm.argWord sevm 0 = poolWord := by
    unfold Sevm.argWord Sevm.dataWord
    rw [data]
    decide +kernel
  unfold decodeCall
  simp only [hlen, ↓reduceIte, hsel, harg]

/-- The model's accepted `set_minter` leaves its argument as minter. -/
theorem minter_of_setMinter {ctx : Blanc.Curve3Crv.Ctx} {m : B256} {s : Blanc.Curve3Crv.State}
    {out : Blanc.Curve3Crv.Out}
    (h : Blanc.Curve3Crv.step ctx (.setMinter m) s = .ok out) : out.1.minter = m.toAdr := by
  obtain ⟨-, h⟩ := Blanc.Curve3Crv.step_eq_ok.mp h
  obtain ⟨-, -, rfl⟩ := Blanc.Curve3Crv.setMinter_eq_ok.mp h
  rfl

/-- **A successful message of the recorded transaction settles its root frame at 3Crv.** -/
theorem root_of_success {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput} {index : Nat} (trace : TransactionTrace benv bout tx index state bout')
    (hfork : benv.stat.fork = .muirGlacier) (success : trace.messageOut.error = none) :
    ∃ frame, trace.settledFrames = frame :: Exec.descendantFrames frame.run ∧
      frame.sevm.currentTarget = tokenAddress ∧ frame.sevm.data = callData := by
  have hrules : trace.msg.benv.stat.rules = muirGlacierRules := by
    rw [prepareMessage_benv trace.prepared]
    change Fork.ruleSet benv.stat.fork = muirGlacierRules
    rw [hfork]
    rfl
  have prepared := trace.prepared
  have hreceiver : tx.type.receiver? = some tokenAddress := rfl
  simp only [prepareMessage, hreceiver] at prepared
  have same := Except.ok.inj prepared
  have htarget : trace.msg.target.isNone = false := by rw [← same]; rfl
  have hcurrent : trace.msg.currentTarget = tokenAddress := by rw [← same]
  have hdata : trace.msg.data = callData := by rw [← same]; rfl
  have hvalue : trace.msg.value = 0 := by rw [← same]; rfl
  have hcodeAddress : trace.msg.codeAddress = some tokenAddress := by rw [← same]
  have hdisable : trace.msg.disablePrecompiles = false := by rw [← same]
  have hdelegation : messageCallDelegation trace.msg = .ok (trace.msg, 0) :=
    processMessageCall.legacyAuthorization_disabled _ (by rw [hrules]; rfl)
  have hdirect : messageCallExecutionMessage trace.msg = trace.msg := by
    unfold messageCallExecutionMessage Msg.resolveCodeDelegation
    rw [hrules]
    rfl
  have hafter := Msg.benvAfterTransfer_of_value_zero (msg := trace.msg) hvalue
  have henter : (Frame.ofCall trace.msg).enter =
      .run (initEvm (trace.msg.withBenv trace.msg.benv)) := by
    apply Frame.enter_run_of_nonprecompile (f := Frame.ofCall trace.msg) (adr := tokenAddress) hafter hcodeAddress
    change trace.msg.benv.stat.rules.isPrecomp tokenAddress = false
    rw [hrules]
    decide +kernel
  obtain ⟨root, roots, -, hsevm, -⟩ := trace.message.exists_root_of_clean_call
    (by rw [hrules]; rfl) htarget success hdelegation hdirect henter
  refine ⟨root, ?_, ?_, ?_⟩
  · change trace.message.settledFrames = _
    rw [trace.message.settledFrames_eq, roots]
    simp only [rootFrames, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact Exec.Frame.committedFrames_self root
  · rw [hsevm]; exact hcurrent
  · rw [hsevm]; exact hdata

end Blanc.Lift.Curve3Crv.SetMinter
