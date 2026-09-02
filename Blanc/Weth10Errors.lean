-- Weth10Errors.lean : exact deliberate-error paths for WETH10.
--
-- Every statement in this file is message-frame/code-frame altitude.  None is
-- a transaction theorem, an exhaustiveness claim, or an assumption about an
-- external callee that is not written in the theorem itself.

import Blanc.Weth10

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace Weth10

/-! ## Constant `Error(string)` auxiliaries -/

/-! The following equations lock every deliberate WETH10 reason to its stable
auxiliary-table coordinate.  They are kept separate from path theorems so a
new call site can reuse the exact payload without multiplying identical
wrappers. -/

theorem flashTokenError_lookup (dp : DeployParams) :
    ((weth10 dp).main :: weth10Aux)[flashTokenErrorSlot]? =
      some (Func.revertWith "WETH: flash mint only WETH10") := by rfl

theorem individualLimitError_lookup (dp : DeployParams) :
    ((weth10 dp).main :: weth10Aux)[individualLimitErrorSlot]? =
      some (Func.revertWith "WETH: individual loan limit exceeded") := by rfl

theorem totalLimitError_lookup (dp : DeployParams) :
    ((weth10 dp).main :: weth10Aux)[totalLimitErrorSlot]? =
      some (Func.revertWith "WETH: total loan limit exceeded") := by rfl

theorem flashFailedError_lookup (dp : DeployParams) :
    ((weth10 dp).main :: weth10Aux)[flashFailedErrorSlot]? =
      some (Func.revertWith "WETH: flash loan failed") := by rfl

theorem allowanceError_lookup (dp : DeployParams) :
    ((weth10 dp).main :: weth10Aux)[allowanceErrorSlot]? =
      some (Func.revertWith "WETH: request exceeds allowance") := by rfl

theorem burnBalanceError_lookup (dp : DeployParams) :
    ((weth10 dp).main :: weth10Aux)[burnBalanceErrorSlot]? =
      some (Func.revertWith "WETH: burn amount exceeds balance") := by rfl

theorem expiredPermitError_lookup (dp : DeployParams) :
    ((weth10 dp).main :: weth10Aux)[expiredPermitErrorSlot]? =
      some (Func.revertWith "WETH: Expired permit") := by rfl

theorem invalidPermitError_lookup (dp : DeployParams) :
    ((weth10 dp).main :: weth10Aux)[invalidPermitErrorSlot]? =
      some (Func.revertWith "WETH: invalid permit") := by rfl

theorem transferBalanceError_lookup (dp : DeployParams) :
    ((weth10 dp).main :: weth10Aux)[transferBalanceErrorSlot]? =
      some (Func.revertWith "WETH: transfer amount exceeds balance") := by rfl

theorem ethTransferError_lookup (dp : DeployParams) :
    ((weth10 dp).main :: weth10Aux)[ethTransferErrorSlot]? =
      some (Func.revertWith "WETH: ETH transfer failed") := by rfl

theorem etherTransferError_lookup (dp : DeployParams) :
    ((weth10 dp).main :: weth10Aux)[etherTransferErrorSlot]? =
      some (Func.revertWith "WETH: Ether transfer failed") := by rfl

/-- The eleven deliberate `Error(string)` genres in WETH10's append-only
auxiliary prefix. -/
inductive LockedError where
  | flashToken
  | individualLimit
  | totalLimit
  | flashFailed
  | allowance
  | burnBalance
  | expiredPermit
  | invalidPermit
  | transferBalance
  | ethTransfer
  | etherTransfer
  deriving DecidableEq

def LockedError.reason : LockedError → String
  | .flashToken => "WETH: flash mint only WETH10"
  | .individualLimit => "WETH: individual loan limit exceeded"
  | .totalLimit => "WETH: total loan limit exceeded"
  | .flashFailed => "WETH: flash loan failed"
  | .allowance => "WETH: request exceeds allowance"
  | .burnBalance => "WETH: burn amount exceeds balance"
  | .expiredPermit => "WETH: Expired permit"
  | .invalidPermit => "WETH: invalid permit"
  | .transferBalance => "WETH: transfer amount exceeds balance"
  | .ethTransfer => "WETH: ETH transfer failed"
  | .etherTransfer => "WETH: Ether transfer failed"

def LockedError.slot : LockedError → Nat
  | .flashToken => flashTokenErrorSlot
  | .individualLimit => individualLimitErrorSlot
  | .totalLimit => totalLimitErrorSlot
  | .flashFailed => flashFailedErrorSlot
  | .allowance => allowanceErrorSlot
  | .burnBalance => burnBalanceErrorSlot
  | .expiredPermit => expiredPermitErrorSlot
  | .invalidPermit => invalidPermitErrorSlot
  | .transferBalance => transferBalanceErrorSlot
  | .ethTransfer => ethTransferErrorSlot
  | .etherTransfer => etherTransferErrorSlot

theorem lockedError_lookup (dp : DeployParams) (e : LockedError) :
    ((weth10 dp).main :: weth10Aux)[e.slot]? =
      some (Func.revertWith e.reason) := by
  cases e <;> rfl

/-- Every locked WETH10 error genre has one gas-exact branch/call walk to its
exact ABI reason.  `otherwise` is unreachable on the nonzero flag and remains
abstract, so this single theorem applies at every site without manufacturing
duplicate wrappers. -/
theorem lockedErrorGuard_runCompiledTo {dp : DeployParams} {sevm : Sevm}
    {base : Devm} {G : Nat} {w : B256} {stack : List B256} {img : Bytes}
    {otherwise : Func} (e : LockedError)
    (h_ne : w ≠ 0)
    (hwf : Mem.Wf base.memory) (hr : Mem.Reads base.memory img)
    (halign : base.memory.size % 32 = 0)
    (h_blob : (errorData e.reason).length < 2 ^ 256)
    (h_words : 32 * (bytesWords (errorData e.reason)).length < 2 ^ 256)
    (h_room : stack.length < 1022) :
    Func.RunCompiledTo ((weth10 dp).main :: weth10Aux) sevm
      (base.setMach
        ⟨w :: stack, base.memory, G + errorGuardCost base e.reason⟩)
      ((.call e.slot) <?> otherwise)
      (.error (.revert,
        (base.setMach ⟨stack,
          Mem.writeStoresRev base.memory (bytesWords (errorData e.reason)).zipIdx,
          G⟩).withOutput (errorData e.reason))) := by
  exact Func.runCompiledTo_errorGuard (lockedError_lookup dp e) h_ne rfl
    hwf hr halign h_blob h_words (by
      simp only [Devm.gasLeft_setMach, errorGuardCost, errorCallCost,
        errorBodyCost, Devm.extCost, Devm.memory_setMach]) (by
      simp only [Devm.stack_setMach, List.length_cons]
      omega)

/-! ## Exact empty and bubbled callback errors -/

/-- The post-`EXTCODESIZE` continuation shared by typed Boolean callbacks and
the flash callback: a zero code size becomes a nonzero branch flag and
empty-reverts before any child `CALL`. -/
def codelessCallbackCost : Nat :=
  gVerylow + (gVerylow + gHigh + gJumpdest) + (gBase + gBase)

theorem codelessCallbackCost_eq : codelessCallbackCost = 21 := by decide

theorem codelessCallback_runCompiledTo {dp : DeployParams} {sevm : Sevm}
    {base : Devm} {G : Nat} {stack : List B256} {afterCall : Func}
    (h_room : stack.length < 1022) :
    Func.RunCompiledTo ((weth10 dp).main :: weth10Aux) sevm
      (base.setMach ⟨0 :: stack, base.memory, G + codelessCallbackCost⟩)
      (iszero ::: Func.revert <?> afterCall)
      (.error (.revert,
        (base.setMach ⟨stack, base.memory, G⟩).withOutput [])) := by
  rw [codelessCallbackCost_eq]
  func_run (2) [1]
  all_goals try {
    simp only [Devm.stack_setMach, List.length_cons] at *
    omega }
  all_goals try omega
  exact Func.runCompiledTo_revert_func
    (devm := base.setMach ⟨stack, base.memory, G + 4⟩) (G := G) (by
    simp only [Devm.gasLeft_setMach, gBase]) (by
      simp only [Devm.stack_setMach]
      omega)

/-- Exact continuation cost when a preceding child call returned failure.
It includes `ISZERO`, the taken branch, the internal bubble tail-call and the
complete `RETURNDATACOPY; REVERT` program. -/
def bubbleContinuationCost (devm : Devm) : Nat :=
  gVerylow +
    (gVerylow + gHigh + gJumpdest) +
    (gVerylow + gMid + gJumpdest) +
    revertReturnDataCost devm

/-- A failed callback bubbles the child's returndata byte-for-byte.  This is
the common post-`CALL` continuation; `afterSuccess` is unreachable on this
path and is therefore left abstract. -/
theorem callbackBubble_runCompiledTo {dp : DeployParams} {sevm : Sevm}
    {base : Devm} {G : Nat} {stack : List B256} {img : Bytes}
    {afterSuccess : Func}
    (hwf : Mem.Wf base.memory) (hr : Mem.Reads base.memory img)
    (halign : base.memory.size % 32 = 0)
    (h_len : base.returnData.length < 2 ^ 256)
    (h_room : stack.length < 1021) :
    Func.RunCompiledTo ((weth10 dp).main :: weth10Aux) sevm
      (base.setMach
        ⟨0 :: stack, base.memory, G + bubbleContinuationCost base⟩)
      (iszero ::: (.call bubbleRevertSlot) <?> afterSuccess)
      (.error (.revert,
        (base.setMach
          ⟨stack, base.memory.write 0 base.returnData, G⟩).withOutput
            base.returnData)) := by
  rw [show G + bubbleContinuationCost base =
      (G + revertReturnDataCost base) + 29 by
    simp only [bubbleContinuationCost, gVerylow, gHigh, gJumpdest, gMid]
    omega]
  func_run (3) [1]
  all_goals try {
    simp only [Devm.stack_setMach, List.length_cons] at *
    omega }
  all_goals try omega
  exact Func.runCompiledTo_revertReturnData
    (devm := base.setMach
      ⟨stack, base.memory, G + revertReturnDataCost base⟩)
    (G := G) hwf hr halign h_len (by
      simp only [Devm.gasLeft_setMach, revertReturnDataCost,
        Devm.returnData_setMach, Devm.extCost, Devm.memory_setMach]) (by
      simp only [Devm.stack_setMach]
      omega)

/-- Boolean callback failure uses the common byte-for-byte bubble continuation
in Blanc's `boolReturn` auxiliary, matching the deployed oracle. -/
theorem boolReturn_childRevert_runCompiledTo {dp : DeployParams}
    {sevm : Sevm} {base : Devm} {G : Nat} {stack : List B256} {img : Bytes}
    (hwf : Mem.Wf base.memory) (hr : Mem.Reads base.memory img)
    (halign : base.memory.size % 32 = 0)
    (h_len : base.returnData.length < 2 ^ 256)
    (h_room : stack.length < 1021) :
    Func.RunCompiledTo ((weth10 dp).main :: weth10Aux) sevm
      (base.setMach
        ⟨0 :: stack, base.memory, G + bubbleContinuationCost base⟩) boolReturn
      (.error (.revert,
        (base.setMach
          ⟨stack, base.memory.write 0 base.returnData, G⟩).withOutput
            base.returnData)) := by
  simpa only [boolReturn] using
    callbackBubble_runCompiledTo hwf hr halign h_len h_room

/-- The exact post-`CALL` decoder embedded in `flashLoan`. -/
def flashCallbackReturn : Func :=
  iszero :::
  (.call bubbleRevertSlot) <?>
  (returnDataShorterThan 32 +++
    Func.revert <?>
    (checkReturnDataHead CALLBACK_SUCCESS 0 +++ iszero :::
      (.call flashFailedErrorSlot) <?>
      (pop ::: pop ::: .call flashSettleSlot)))

/-- Memory immediately after copying the callback's first returndata word. -/
def flashCallbackCopiedMemory (base : Devm) : Mem :=
  base.memory.write ((0 * 32 : B256)).toNat
    (List.sliceD base.returnData (B256.toNat 0) (B256.toNat 32)
      (0 : UInt8))

/-- Memory after the flash decoder has copied and read the callback's first
returndata word. -/
def flashCallbackHeadMemory (base : Devm) : Mem :=
  (flashCallbackCopiedMemory base).read ((0 * 32 : B256)).toNat 32 |>.2

/-- The exact word compared with WETH10's flash-callback magic value. -/
def flashCallbackReturnDataHead (base : Devm) : B256 :=
  (flashCallbackCopiedMemory base).read
    ((0 * 32 : B256)).toNat 32 |>.1 |>.toB256

/-- A gas-insensitive base carrying the decoder's post-read stack and memory.
It lets the following error-body cost mention exactly the memory image at the
locked flash-failure guard. -/
def flashCallbackHeadBase (base : Devm) (stack : List B256) : Devm :=
  base.setMach ⟨stack, flashCallbackHeadMemory base, 0⟩

/-- Flash callback failure uses the same byte-for-byte bubble auxiliary as
typed Boolean callbacks. -/
theorem flashCallback_childRevert_runCompiledTo {dp : DeployParams}
    {sevm : Sevm} {base : Devm} {G : Nat} {stack : List B256} {img : Bytes}
    (hwf : Mem.Wf base.memory) (hr : Mem.Reads base.memory img)
    (halign : base.memory.size % 32 = 0)
    (h_len : base.returnData.length < 2 ^ 256)
    (h_room : stack.length < 1021) :
    Func.RunCompiledTo ((weth10 dp).main :: weth10Aux) sevm
      (base.setMach
        ⟨0 :: stack, base.memory, G + bubbleContinuationCost base⟩)
      flashCallbackReturn
      (.error (.revert,
        (base.setMach
          ⟨stack, base.memory.write 0 base.returnData, G⟩).withOutput
            base.returnData)) := by
  simpa only [flashCallbackReturn] using
    callbackBubble_runCompiledTo hwf hr halign h_len h_room

/-- Exact cost of accepting a successful child-call flag, detecting returndata
shorter than one word and empty-reverting. -/
def shortReturnCost : Nat :=
  gVerylow + (gVerylow + gHigh) +
    (gVerylow + gBase + gVerylow) +
    (gVerylow + gHigh + gJumpdest) +
    (gBase + gBase)

theorem shortReturnCost_eq : shortReturnCost = 42 := by decide

/-- A successful callback whose returndata is shorter than 32 bytes reverts
with empty data.  The full-word decoder is abstract because this path cannot
reach it. -/
theorem callbackShort_runCompiledTo {dp : DeployParams} {sevm : Sevm}
    {base : Devm} {G : Nat} {stack : List B256} {fullWord : Func}
    (h_short : base.returnData.length < 32)
    (h_room : stack.length < 1020) :
    Func.RunCompiledTo ((weth10 dp).main :: weth10Aux) sevm
      (base.setMach ⟨1 :: stack, base.memory, G + shortReturnCost⟩)
      (iszero :::
        (.call bubbleRevertSlot) <?>
        (returnDataShorterThan 32 +++ Func.revert <?> fullWord))
      (.error (.revert,
        (base.setMach ⟨stack, base.memory, G⟩).withOutput [])) := by
  rw [shortReturnCost_eq]
  func_run (6) [0, 1]
  all_goals try {
    simp only [Devm.stack_setMach, Devm.returnData_setMach,
      List.length_cons] at *
    omega }
  all_goals try omega
  · simp only [B256.ltCheck, Devm.returnData_setMach]
    exact if_pos (by
      rw [B256.lt_iff_toNat_lt_toNat,
        B256.toNat_toB256_of_lt (by omega)]
      exact h_short)
  · exact Func.runCompiledTo_revert_func
      (devm := base.setMach ⟨stack, base.memory, G + 4⟩) (G := G) (by
        simp only [Devm.gasLeft_setMach, gBase]) (by
        simp only [Devm.stack_setMach]
        omega)

theorem boolReturn_short_runCompiledTo {dp : DeployParams} {sevm : Sevm}
    {base : Devm} {G : Nat} {stack : List B256}
    (h_short : base.returnData.length < 32)
    (h_room : stack.length < 1020) :
    Func.RunCompiledTo ((weth10 dp).main :: weth10Aux) sevm
      (base.setMach ⟨1 :: stack, base.memory, G + shortReturnCost⟩) boolReturn
      (.error (.revert,
        (base.setMach ⟨stack, base.memory, G⟩).withOutput [])) := by
  simpa only [boolReturn] using
    callbackShort_runCompiledTo h_short h_room

theorem flashCallback_short_runCompiledTo {dp : DeployParams}
    {sevm : Sevm} {base : Devm} {G : Nat} {stack : List B256}
    (h_short : base.returnData.length < 32)
    (h_room : stack.length < 1020) :
    Func.RunCompiledTo ((weth10 dp).main :: weth10Aux) sevm
      (base.setMach ⟨1 :: stack, base.memory, G + shortReturnCost⟩)
      flashCallbackReturn
      (.error (.revert,
        (base.setMach ⟨stack, base.memory, G⟩).withOutput [])) := by
  simpa only [flashCallbackReturn] using
    callbackShort_runCompiledTo h_short h_room

/-- The successful-call/full-word prefix costs exactly 37 gas before entering
the word decoder.  `fullWord` is abstract so the short-return and magic-word
genres can share this walk without a large all-at-once elaboration. -/
theorem callbackFullWordPrefix_runCompiledTo {dp : DeployParams}
    {sevm : Sevm} {base : Devm} {G : Nat} {stack : List B256}
    {fullWord : Func} {ex : Execution}
    (h_ge : (Nat.toB256 base.returnData.length <? (32 : B256)) = 0)
    (h_tail : Func.RunCompiledTo ((weth10 dp).main :: weth10Aux) sevm
      (base.setMach ⟨stack, base.memory, G⟩) fullWord ex)
    (h_room : stack.length < 1019) :
    Func.RunCompiledTo ((weth10 dp).main :: weth10Aux) sevm
      (base.setMach ⟨1 :: stack, base.memory, G + 37⟩)
      (iszero :::
        (.call bubbleRevertSlot) <?>
        (returnDataShorterThan 32 +++ Func.revert <?> fullWord)) ex := by
  func_run (6) [0, 0]
  all_goals try {
    simp only [Devm.stack_setMach, List.length_cons] at *
    omega }
  all_goals try omega
  simpa only [Devm.memory_setMach, Nat.add_sub_cancel] using h_tail

/-- Copy the callback's first returndata word into covered memory.  This is
the first 13-gas half of `checkReturnDataHead`. -/
theorem callbackHeadCopyPrefix_runCompiledTo {dp : DeployParams}
    {sevm : Sevm} {base : Devm} {G : Nat} {stack : List B256}
    {tail : Func} {ex : Execution}
    (h_len : B256.toNat 0 + B256.toNat 32 ≤ base.returnData.length)
    (h32 : base.memory.size % 32 = 0)
    (h_msz : 64 ≤ base.memory.size)
    (h_tail : Func.RunCompiledTo ((weth10 dp).main :: weth10Aux) sevm
      (base.setMach ⟨stack, flashCallbackCopiedMemory base, G⟩) tail ex)
    (h_room : stack.length < 1019) :
    Func.RunCompiledTo ((weth10 dp).main :: weth10Aux) sevm
      (base.setMach ⟨stack, base.memory, G + 13⟩)
      (pushList [32, 0, 0] +++ returndatacopy ::: tail) ex := by
  func_run (4) [6]
  all_goals try simp only [Devm.stack_setMach, List.length_cons] at *
  all_goals try omega
  · rw [Devm.extCost_zero_of_le h32 (by
      rw [show B256.toNat 0 = 0 from by decide,
        show B256.toNat 32 = 32 from by decide]
      omega)]
    decide
  · simpa only [flashCallbackCopiedMemory, Devm.returnData_setMach,
      Nat.add_sub_cancel,
      show ((0 * 32 : B256)).toNat = B256.toNat 0 from by decide] using h_tail

/-- Read the copied word.  Covered `MLOAD` makes this a five-gas segment. -/
theorem callbackHeadReadPrefix_runCompiledTo {dp : DeployParams}
    {sevm : Sevm} {base : Devm} {G : Nat} {stack : List B256}
    {tail : Func} {ex : Execution}
    (h_copySize : (flashCallbackCopiedMemory base).size = base.memory.size)
    (h32 : base.memory.size % 32 = 0)
    (h_msz : 64 ≤ base.memory.size)
    (h_tail : Func.RunCompiledTo ((weth10 dp).main :: weth10Aux) sevm
      (base.setMach ⟨flashCallbackReturnDataHead base :: stack,
        flashCallbackHeadMemory base, G⟩) tail ex)
    (h_room : stack.length < 1019) :
    Func.RunCompiledTo ((weth10 dp).main :: weth10Aux) sevm
      (base.setMach ⟨stack, flashCallbackCopiedMemory base, G + 5⟩)
      (pushB256 0 ::: mload ::: tail) ex := by
  func_run (2) [3]
  all_goals try simp only [Devm.stack_setMach] at *
  all_goals try omega
  · rw [Devm.extCost_zero_of_le (by rw [h_copySize]; exact h32) (by
      rw [h_copySize]
      rw [show B256.toNat 0 = 0 from by decide]
      omega)]
    decide
  · simpa only [flashCallbackHeadMemory, flashCallbackReturnDataHead,
      Nat.add_sub_cancel,
      show ((0 * 32 : B256)).toNat = B256.toNat 0 from by decide] using h_tail

/-- Compare the copied word and invert the mismatch flag.  The push width is
kept symbolic so this theorem works for an arbitrary expected word without
forcing kernel reduction of its bytes. -/
theorem callbackHeadMismatchFlagPrefix_runCompiledTo {dp : DeployParams}
    {sevm : Sevm} {base : Devm} {G : Nat} {stack : List B256}
    {expected head : B256} {memory : Mem} {tail : Func} {ex : Execution}
    (h_neq : (expected =? head) = 0)
    (h_tail : Func.RunCompiledTo ((weth10 dp).main :: weth10Aux) sevm
      (base.setMach ⟨1 :: stack, memory, G⟩) tail ex)
    (h_room : stack.length < 1019) :
    Func.RunCompiledTo ((weth10 dp).main :: weth10Aux) sevm
      (base.setMach ⟨head :: stack, memory,
        G + (pushCost expected.toBytes.sig + 6)⟩)
      (pushB256 expected ::: eq ::: iszero ::: tail) ex := by
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (w := expected)
      (c := pushCost expected.toBytes.sig) (G := G + 6) rfl (by
        simp only [Devm.gasLeft_setMach]
        omega) (by
        simp only [Devm.stack_setMach, List.length_cons]
        omega)) ?_
  simp only [Devm.setMach_setMach]
  func_run (2) [0, 1]
  all_goals try omega
  simpa only [Devm.memory_setMach, Nat.add_sub_cancel] using h_tail

/-- Read, compare and invert the copied word.  A mismatch leaves the nonzero
guard flag after an exact symbolic push-width charge plus eleven gas. -/
theorem callbackHeadMismatchReadPrefix_runCompiledTo {dp : DeployParams}
    {sevm : Sevm} {base : Devm} {G : Nat} {stack : List B256}
    {expected : B256} {tail : Func} {ex : Execution}
    (h_neq : (expected =? flashCallbackReturnDataHead base) = 0)
    (h_copySize : (flashCallbackCopiedMemory base).size = base.memory.size)
    (h32 : base.memory.size % 32 = 0)
    (h_msz : 64 ≤ base.memory.size)
    (h_tail : Func.RunCompiledTo ((weth10 dp).main :: weth10Aux) sevm
      (base.setMach ⟨1 :: stack, flashCallbackHeadMemory base, G⟩) tail ex)
    (h_room : stack.length < 1018) :
    Func.RunCompiledTo ((weth10 dp).main :: weth10Aux) sevm
      (base.setMach ⟨stack, flashCallbackCopiedMemory base,
        G + (pushCost expected.toBytes.sig + 11)⟩)
      (pushB256 0 ::: mload ::: pushB256 expected :::
        eq ::: iszero ::: tail) ex := by
  rw [show G + (pushCost expected.toBytes.sig + 11) =
      (G + (pushCost expected.toBytes.sig + 6)) + 5 by omega]
  exact callbackHeadReadPrefix_runCompiledTo h_copySize h32 h_msz
    (callbackHeadMismatchFlagPrefix_runCompiledTo h_neq h_tail (by omega))
    (by omega)

/-- A full-word magic mismatch charges the callback-success word's exact push
width plus 24 gas to copy/read/compare and leave a nonzero flag.  Keeping
`tail` and `ex` abstract is the compositional seam used below. -/
theorem callbackMagicMismatchPrefix_runCompiledTo {dp : DeployParams}
    {sevm : Sevm} {base : Devm} {G : Nat} {stack : List B256}
    {tail : Func} {ex : Execution}
    (h_ge : (Nat.toB256 base.returnData.length <? (32 : B256)) = 0)
    (h_neq : (CALLBACK_SUCCESS =? flashCallbackReturnDataHead base) = 0)
    (h32 : base.memory.size % 32 = 0)
    (h_msz : 64 ≤ base.memory.size)
    (h_tail : Func.RunCompiledTo ((weth10 dp).main :: weth10Aux) sevm
      (base.setMach ⟨1 :: stack, flashCallbackHeadMemory base, G⟩) tail ex)
    (h_room : stack.length < 1016) :
    Func.RunCompiledTo ((weth10 dp).main :: weth10Aux) sevm
      (base.setMach ⟨stack, base.memory,
        G + (pushCost CALLBACK_SUCCESS.toBytes.sig + 24)⟩)
      (checkReturnDataHead CALLBACK_SUCCESS 0 +++ iszero ::: tail) ex := by
  have h_len : B256.toNat 0 + B256.toNat 32 ≤ base.returnData.length := by
    have h1 : ¬ Nat.toB256 base.returnData.length < (32 : B256) := by
      intro hc
      rw [show (Nat.toB256 base.returnData.length <? (32 : B256)) =
        if Nat.toB256 base.returnData.length < 32 then (1 : B256) else 0
          from rfl, if_pos hc] at h_ge
      exact (by decide : (1 : B256) ≠ 0) h_ge
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256,
      show ((32 : B256)).toNat = 32 from rfl, Nat.lo_eq] at h1
    have h2 := Nat.mod_le base.returnData.length (2 ^ 256)
    rw [show B256.toNat 0 + B256.toNat 32 = 32 from by decide]
    omega
  have hs1 : (base.memory.write ((0 * 32 : B256)).toNat
      (List.sliceD base.returnData (B256.toNat 0) (B256.toNat 32)
        (0 : UInt8))).size = base.memory.size := by
    apply Mem.size_write_of_le
    rw [show (List.sliceD base.returnData (B256.toNat 0) (B256.toNat 32)
        (0 : UInt8)).length = B256.toNat 32 from List.takeD_length _ _ _,
      show ((0 * 32 : B256)).toNat + B256.toNat 32 = 32 from by decide]
    omega
  rw [show G + (pushCost CALLBACK_SUCCESS.toBytes.sig + 24) =
      (G + (pushCost CALLBACK_SUCCESS.toBytes.sig + 11)) + 13 by omega]
  simpa [checkReturnDataHead, pushList, prepend,
      show (0 * 32 : B256) = 0 from by decide] using
    callbackHeadCopyPrefix_runCompiledTo h_len h32 h_msz
      (callbackHeadMismatchReadPrefix_runCompiledTo h_neq hs1 h32 h_msz
        h_tail (by omega)) (by omega)

/-- From the full-word decoder, a magic mismatch reaches the exact locked
flash-failure payload.  The symbolic-width decoder and error guard are
composed without an all-at-once tactic walk. -/
theorem flashCallback_wrongMagicTail_runCompiledTo {dp : DeployParams}
    {sevm : Sevm} {base : Devm} {G : Nat} {stack : List B256} {img : Bytes}
    (h_ge : (Nat.toB256 base.returnData.length <? (32 : B256)) = 0)
    (h_neq : (CALLBACK_SUCCESS =? flashCallbackReturnDataHead base) = 0)
    (h32 : base.memory.size % 32 = 0)
    (h_msz : 64 ≤ base.memory.size)
    (hwf : Mem.Wf (flashCallbackHeadMemory base))
    (hr : Mem.Reads (flashCallbackHeadMemory base) img)
    (halign : (flashCallbackHeadMemory base).size % 32 = 0)
    (h_blob : (errorData "WETH: flash loan failed").length < 2 ^ 256)
    (h_words : 32 *
      (bytesWords (errorData "WETH: flash loan failed")).length < 2 ^ 256)
    (h_room : stack.length < 1016) :
    Func.RunCompiledTo ((weth10 dp).main :: weth10Aux) sevm
      (base.setMach ⟨stack, base.memory,
        (G + errorGuardCost (flashCallbackHeadBase base stack)
          "WETH: flash loan failed") +
          (pushCost CALLBACK_SUCCESS.toBytes.sig + 24)⟩)
      (checkReturnDataHead CALLBACK_SUCCESS 0 +++ iszero :::
        (.call flashFailedErrorSlot) <?>
        (pop ::: pop ::: .call flashSettleSlot))
      (.error (.revert,
        ((flashCallbackHeadBase base stack).setMach ⟨stack,
          Mem.writeStoresRev (flashCallbackHeadMemory base)
            (bytesWords (errorData "WETH: flash loan failed")).zipIdx,
          G⟩).withOutput (errorData "WETH: flash loan failed"))) := by
  apply callbackMagicMismatchPrefix_runCompiledTo h_ge h_neq h32 h_msz
  · exact Func.runCompiledTo_errorGuard (flashFailedError_lookup dp)
      (by decide) rfl
      (by simpa only [flashCallbackHeadBase, Devm.memory_setMach] using hwf)
      (by simpa only [flashCallbackHeadBase, Devm.memory_setMach] using hr)
      (by simpa only [flashCallbackHeadBase, Devm.memory_setMach] using halign)
      h_blob h_words (by
        simp only [Devm.gasLeft_setMach, errorGuardCost, errorCallCost,
          errorBodyCost, Devm.extCost, flashCallbackHeadBase,
          Devm.memory_setMach]) (by
        simp only [Devm.stack_setMach, List.length_cons]
        omega)
  · exact h_room

/-- The complete post-`CALL` flash decoder, from its success flag, reports the
locked flash-failure payload on a full-word magic mismatch. -/
theorem flashCallback_wrongMagic_runCompiledTo {dp : DeployParams}
    {sevm : Sevm} {base : Devm} {G : Nat} {stack : List B256} {img : Bytes}
    (h_ge : (Nat.toB256 base.returnData.length <? (32 : B256)) = 0)
    (h_neq : (CALLBACK_SUCCESS =? flashCallbackReturnDataHead base) = 0)
    (h32 : base.memory.size % 32 = 0)
    (h_msz : 64 ≤ base.memory.size)
    (hwf : Mem.Wf (flashCallbackHeadMemory base))
    (hr : Mem.Reads (flashCallbackHeadMemory base) img)
    (halign : (flashCallbackHeadMemory base).size % 32 = 0)
    (h_blob : (errorData "WETH: flash loan failed").length < 2 ^ 256)
    (h_words : 32 *
      (bytesWords (errorData "WETH: flash loan failed")).length < 2 ^ 256)
    (h_room : stack.length < 1016) :
    Func.RunCompiledTo ((weth10 dp).main :: weth10Aux) sevm
      (base.setMach ⟨1 :: stack, base.memory,
        ((G + errorGuardCost (flashCallbackHeadBase base stack)
          "WETH: flash loan failed") +
          (pushCost CALLBACK_SUCCESS.toBytes.sig + 24)) + 37⟩)
      flashCallbackReturn
      (.error (.revert,
        ((flashCallbackHeadBase base stack).setMach ⟨stack,
          Mem.writeStoresRev (flashCallbackHeadMemory base)
            (bytesWords (errorData "WETH: flash loan failed")).zipIdx,
          G⟩).withOutput (errorData "WETH: flash loan failed"))) := by
  simpa only [flashCallbackReturn] using
    callbackFullWordPrefix_runCompiledTo h_ge
      (flashCallback_wrongMagicTail_runCompiledTo h_ge h_neq h32 h_msz
        hwf hr halign h_blob h_words h_room) (by omega)

/-! ## Nonpayability -/

def nonpayableRevertCost : Nat :=
  gBase + gVerylow + (gVerylow + gHigh) + (gBase + gBase)

theorem nonpayableRevertCost_eq : nonpayableRevertCost = 22 := by decide

/-- Every selected WETH10 `nonpayable` body empty-reverts on nonzero call
value, before its body can inspect calldata or storage. -/
theorem nonpayable_runCompiledTo {dp : DeployParams} {sevm : Sevm}
    {base : Devm} {G : Nat} {body : Func}
    (h_value : sevm.value ≠ 0)
    (h_room : base.stack.length < 1022) :
    Func.RunCompiledTo ((weth10 dp).main :: weth10Aux) sevm
      (base.setMach
        ⟨base.stack, base.memory, G + nonpayableRevertCost⟩)
      (nonpayable body)
      (.error (.revert,
        (base.setMach ⟨base.stack, base.memory, G⟩).withOutput [])) := by
  rw [nonpayableRevertCost_eq]
  func_run (3) [0]
  all_goals try {
    simp only [Devm.stack_setMach, List.length_cons] at *
    omega }
  all_goals try omega
  · simp [B256.eqCheck, h_value]
  · exact Func.runCompiledTo_revert_func
      (devm := base.setMach ⟨base.stack, base.memory, G + 4⟩) (G := G) (by
      simp only [Devm.gasLeft_setMach, gBase]) (by
        simp only [Devm.stack_setMach]
        omega)

/-! ## Guard precedence at selected-body altitude -/

/-- `flashFee` checks the token before its success return.  A non-WETH10
token therefore reaches the locked flash-token reason without any amount,
storage or callback premise. -/
theorem flashFee_wrongToken_runCompiledTo {dp : DeployParams} {sevm : Sevm}
    {base : Devm} {G : Nat} {stack : List B256} {img : Bytes} {token : B256}
    (h_arg : Sevm.argWord sevm 0 = token)
    (h_ne : token ≠ sevm.currentTarget.toB256)
    (hwf : Mem.Wf base.memory) (hr : Mem.Reads base.memory img)
    (halign : base.memory.size % 32 = 0)
    (h_blob : (errorData "WETH: flash mint only WETH10").length < 2 ^ 256)
    (h_words : 32 *
      (bytesWords (errorData "WETH: flash mint only WETH10")).length <
        2 ^ 256)
    (h_room : stack.length < 1020) :
    Func.RunCompiledTo ((weth10 dp).main :: weth10Aux) sevm
      (base.setMach ⟨stack, base.memory,
        (G + errorGuardCost base "WETH: flash mint only WETH10") + 14⟩)
      flashFee
      (.error (.revert,
        (base.setMach ⟨stack,
          Mem.writeStoresRev base.memory
            (bytesWords (errorData "WETH: flash mint only WETH10")).zipIdx,
          G⟩).withOutput
            (errorData "WETH: flash mint only WETH10"))) := by
  func_run (5) [0]
  all_goals try {
    simp only [Devm.stack_setMach, List.length_cons] at *
    omega }
  all_goals try omega
  · change sevm.currentTarget.toB256 =? Sevm.argWord sevm 0 = 0
    rw [h_arg]
    simp [B256.eqCheck, Ne.symm h_ne]
  · exact Func.runCompiledTo_errorGuard (flashTokenError_lookup dp)
      (by decide) rfl hwf hr halign h_blob h_words (by
        simp only [Devm.gasLeft_setMach, errorGuardCost, errorCallCost,
          errorBodyCost, Devm.extCost, Devm.memory_setMach]
        omega) (by
        simp only [Devm.stack_setMach, List.length_cons]
        omega)

/-! The exact payload theorem above is intentionally shared by every site.
The following source-shape locks record the meaningful ordering edges without
manufacturing a second gas walk for each identical guard.  `lockedGuardChain`
follows the zero/success continuation of the conventional
`(.call errorSlot) <?> continuation` shape and records the error slots it
passes in order. -/

def lockedGuardChain : Func → List Nat
  | .branch ok (.call slot) => slot :: lockedGuardChain ok
  | .next _ rest => lockedGuardChain rest
  | _ => []

/-- `flashLoan` rejects the wrong token before the individual limit and the
individual limit before the total limit.  Its callback is reached only after
all three guards have fallen through. -/
theorem flashLoan_lockedGuardOrder :
    lockedGuardChain flashLoan =
      [flashTokenErrorSlot, individualLimitErrorSlot, totalLimitErrorSlot] := by
  rfl

/-- The two invalid-permit checks are ordered: zero recovery is rejected
before the recovered signer is compared with the owner. -/
theorem permitRecover_lockedGuardOrder :
    lockedGuardChain permitRecover =
      [invalidPermitErrorSlot, invalidPermitErrorSlot] := by
  rfl

/-- Expiry is the outer permit guard.  The nonce is loaded, tentatively
incremented and stored only in the fallthrough continuation; `REVERT`
therefore rolls that tentative write back when either later invalid-permit
guard fires. -/
theorem permit_expiredBeforeNonceUpdate (dp : DeployParams) :
    ∃ afterExpiry,
      permit dp =
        (arg 3 +++ timestamp ::: gt :::
          (.call expiredPermitErrorSlot) <?> afterExpiry) ∧
      ∃ afterNonceUpdate,
        afterExpiry =
          (chainid :::
            addressArg 0 +++ dup 0 ::: tagNonceKey +++ dup 0 ::: sload :::
            dup 0 ::: mstoreAt 4 +++ pushB256 1 ::: add ::: swap 0 ::: sstore :::
            pop ::: afterNonceUpdate) := by
  refine ⟨_, rfl, ?_⟩
  exact ⟨_, rfl⟩

/-- The zero-address transfer arm uses the burn-balance reason and, only
after the debit/emission path, the `ETH`-spelled value-transfer reason.  The
nonzero-address arm uses the transfer-balance reason. -/
theorem transfer_lockedGuardOrder (next : Func) :
    lockedGuardChain (transferZeroThen next) =
      [burnBalanceErrorSlot, ethTransferErrorSlot] ++ lockedGuardChain next ∧
    lockedGuardChain (transferNonzeroThen next) =
      [transferBalanceErrorSlot] ++ lockedGuardChain next := by
  exact ⟨rfl, rfl⟩

/-- `transferFrom` makes the same zero/nonzero reason distinction after its
allowance phase. -/
theorem transferFromCore_lockedGuardOrder :
    lockedGuardChain transferFromZero =
      [burnBalanceErrorSlot, ethTransferErrorSlot] ∧
    lockedGuardChain transferFromNonzero =
      [transferBalanceErrorSlot] := by
  exact ⟨rfl, rfl⟩

/-- Direct caller withdrawals use `ETH`, whereas delegated `withdrawFrom`
uses the compatibility-locked `Ether` spelling.  In every arm the balance
guard precedes the low-level value call. -/
theorem withdraw_lockedGuardOrder :
    lockedGuardChain withdraw =
      [burnBalanceErrorSlot, ethTransferErrorSlot] ∧
    lockedGuardChain withdrawTo =
      [burnBalanceErrorSlot, ethTransferErrorSlot] ∧
    lockedGuardChain withdrawFromCore =
      [burnBalanceErrorSlot, etherTransferErrorSlot] := by
  exact ⟨rfl, rfl, rfl⟩

/-- In a finite allowance arm the allowance error precedes the tail call into
the transfer/withdraw core; its balance error can therefore be reached only
after the allowance check has fallen through. -/
theorem spendCallerAllowanceThen_finitePrecedence
    (amount : B256) (nextSlot : Nat) :
    ∃ finite,
      spendCallerAllowanceThen amount nextSlot =
        (arg 0 +++ caller ::: eq :::
          (.call nextSlot) <?>
          (arg 0 +++ mstoreAt 0 +++ caller ::: mstoreAt 1 +++
            allowanceKeyFromMemory +++ dup 0 ::: sload ::: dup 0 ::: isMax +++
            (pop ::: pop ::: .call nextSlot) <?> finite)) ∧
      finite =
        (arg amount +++ swap 0 ::: balanceTooSmall +++
          (.call allowanceErrorSlot) <?>
          (sub ::: dup 0 ::: swap 1 ::: sstore :::
            arg 0 +++ swap 0 ::: caller ::: emitApproval +++
            pop ::: pop ::: .call nextSlot)) := by
  refine ⟨_, rfl, ?_⟩
  rfl

/-- Flash settlement has the same precedence: a finite allowance failure is
reported before the burn continuation can inspect the receiver balance. -/
theorem flashSettle_finitePrecedence :
    ∃ finite,
      flashSettle =
        (addressArg 0 +++ mstoreAt 0 +++ address ::: mstoreAt 1 +++
          allowanceKeyFromMemory +++ dup 0 ::: sload ::: dup 0 ::: isMax +++
          (pop ::: pop ::: .call flashBurnSlot) <?> finite) ∧
      finite =
        (arg 2 +++ swap 0 ::: balanceTooSmall +++
          (.call allowanceErrorSlot) <?>
          (sub ::: dup 0 ::: swap 1 ::: sstore :::
            emitFlashApproval +++ .call flashBurnSlot)) ∧
      lockedGuardChain flashBurn = [burnBalanceErrorSlot] := by
  refine ⟨_, rfl, rfl, ?_⟩
  rfl

/-- The post-callback decoder orders child bubbling before the short-return
empty revert, and the magic-word mismatch before flash settlement. -/
theorem flashCallback_errorPrecedence :
    flashCallbackReturn =
      (iszero :::
        (.call bubbleRevertSlot) <?>
        (returnDataShorterThan 32 +++
          Func.revert <?>
          (checkReturnDataHead CALLBACK_SUCCESS 0 +++ iszero :::
            (.call flashFailedErrorSlot) <?>
            (pop ::: pop ::: .call flashSettleSlot)))) := by
  rfl

/-! ## Message-frame rollback transport -/

/-- A gas-exact WETH10 compiled walk ending in `REVERT` settles the enclosing
message frame with that exact output and restores persistent and transient
state.  This is deliberately message-call altitude: it says nothing about
transaction validity, intrinsic gas or transaction-level rollback. -/
theorem rollback_revert_of_weth10_runCompiledTo
    {dp : DeployParams} {msg : Msg} {benv : Benv} {xl : Xlot}
    {out d : Devm} {bs : Bytes}
    (h_pm : ProcessMessage msg xl (.ok out))
    (h_fill : Xlot.Filled xl)
    (h_bt : msg.benvAfterTransfer = .ok benv)
    (h_prec : ∀ adr, msg.codeAddress = some adr →
      ¬ (!msg.disablePrecompiles &&
        decide (benv.stat.rules.isPrecomp adr)) = true)
    (h_code : some (initSevm (msg.withBenv benv)).code.toList =
      (weth10 dp).compile)
    (h_run : Prog.RunCompiledTo (initSevm (msg.withBenv benv))
      (initDevm (msg.withBenv benv)) (weth10 dp)
      (.error (.revert, d.withOutput bs))) :
    out.error = some .revert ∧ out.output = bs ∧
      out.state = msg.benv.state ∧
      out.transientStorage = msg.tenv.transientStorage := by
  exact rollback_revert_of_runCompiledTo h_pm h_fill h_bt h_prec h_code h_run

/-- Empty-data WETH10 reverts, including nonpayability and short/codeless
callback failures, restore the message frame and expose exactly `[]`. -/
theorem rollback_empty_of_weth10_runCompiledTo
    {dp : DeployParams} {msg : Msg} {benv : Benv} {xl : Xlot}
    {out d : Devm}
    (h_pm : ProcessMessage msg xl (.ok out))
    (h_fill : Xlot.Filled xl)
    (h_bt : msg.benvAfterTransfer = .ok benv)
    (h_prec : ∀ adr, msg.codeAddress = some adr →
      ¬ (!msg.disablePrecompiles &&
        decide (benv.stat.rules.isPrecomp adr)) = true)
    (h_code : some (initSevm (msg.withBenv benv)).code.toList =
      (weth10 dp).compile)
    (h_run : Prog.RunCompiledTo (initSevm (msg.withBenv benv))
      (initDevm (msg.withBenv benv)) (weth10 dp)
      (.error (.revert, d.withOutput []))) :
    out.error = some .revert ∧ out.output = [] ∧
      out.state = msg.benv.state ∧
      out.transientStorage = msg.tenv.transientStorage := by
  exact rollback_revert_of_weth10_runCompiledTo
    h_pm h_fill h_bt h_prec h_code h_run

/-- A WETH10 `Error(string)` walk restores the frame and exposes precisely the
ABI payload of the selected reason. -/
theorem rollback_errorData_of_weth10_runCompiledTo
    {dp : DeployParams} {msg : Msg} {benv : Benv} {xl : Xlot}
    {out d : Devm} {reason : String}
    (h_pm : ProcessMessage msg xl (.ok out))
    (h_fill : Xlot.Filled xl)
    (h_bt : msg.benvAfterTransfer = .ok benv)
    (h_prec : ∀ adr, msg.codeAddress = some adr →
      ¬ (!msg.disablePrecompiles &&
        decide (benv.stat.rules.isPrecomp adr)) = true)
    (h_code : some (initSevm (msg.withBenv benv)).code.toList =
      (weth10 dp).compile)
    (h_run : Prog.RunCompiledTo (initSevm (msg.withBenv benv))
      (initDevm (msg.withBenv benv)) (weth10 dp)
      (.error (.revert, d.withOutput (errorData reason)))) :
    out.error = some .revert ∧ out.output = errorData reason ∧
      out.state = msg.benv.state ∧
      out.transientStorage = msg.tenv.transientStorage := by
  exact rollback_revert_of_weth10_runCompiledTo
    h_pm h_fill h_bt h_prec h_code h_run

/-- A bubbled callback revert restores the WETH10 message frame while
preserving every byte chosen by the child. -/
theorem rollback_bubbledChild_of_weth10_runCompiledTo
    {dp : DeployParams} {msg : Msg} {benv : Benv} {xl : Xlot}
    {out d : Devm} {childData : Bytes}
    (h_pm : ProcessMessage msg xl (.ok out))
    (h_fill : Xlot.Filled xl)
    (h_bt : msg.benvAfterTransfer = .ok benv)
    (h_prec : ∀ adr, msg.codeAddress = some adr →
      ¬ (!msg.disablePrecompiles &&
        decide (benv.stat.rules.isPrecomp adr)) = true)
    (h_code : some (initSevm (msg.withBenv benv)).code.toList =
      (weth10 dp).compile)
    (h_run : Prog.RunCompiledTo (initSevm (msg.withBenv benv))
      (initDevm (msg.withBenv benv)) (weth10 dp)
      (.error (.revert, d.withOutput childData))) :
    out.error = some .revert ∧ out.output = childData ∧
      out.state = msg.benv.state ∧
      out.transientStorage = msg.tenv.transientStorage := by
  exact rollback_revert_of_weth10_runCompiledTo
    h_pm h_fill h_bt h_prec h_code h_run

end Weth10
end Blanc
