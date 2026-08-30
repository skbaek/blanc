import Blanc.BeaconDepositAbi
import Blanc.BeaconDepositErrorModel
import Blanc.BeaconDepositEvent
import Blanc.BeaconDepositGuards
import Blanc.BeaconDepositSuccessGuards
import Jaune.MulDiv

/-!
# Beacon deposit model guard failures

Exact compiled walks for all eight source guards reached after successful ABI
decoding.  The first six precede event emission and reconstruction; the final
two compose those stages and select the reconstructed-root or capacity
auxiliary.  Every walk ends at the catalogued `Error(string)` payload.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Ninst

/-- Exact endpoint-level evidence for one catalogued model error.  The gas
witness is existential because C3 fixes the revert and payload, while the
differential lane owns public gas comparison. -/
def DepositEndpointErrorWitness
    (sevm : Sevm) (base : Devm) (G : Nat) (reason : Reason) : Prop :=
  ∃ endpointCost post,
    Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], Mem.empty, G + endpointCost⟩)
      depositEndpoint (.error (.revert, post)) ∧
    post.output = errorData (reasonString reason)

/-- Exact constant-error cost at the 768-byte post-reconstruction memory
boundary. -/
def depositPostHashErrorGuardCost (error : ReachableReason) : Nat :=
  errorGuardCost
    ((default : Devm).setMach
      ⟨[], Mem.empty.write 736 (0 : B256).toBytes, 0⟩)
    (reasonString error.reason)

private theorem depositPostHashErrorGuardCost_eq
    {base : Devm} {memory : Mem} {oldCount node : B256}
    (error : ReachableReason)
    (hmem : InsertionStartMemoryCarrier memory oldCount node) :
    errorGuardCost (base.setMach ⟨[], memory, 0⟩)
        (reasonString error.reason) =
      depositPostHashErrorGuardCost error := by
  unfold depositPostHashErrorGuardCost
  apply errorGuardCost_congr_memory_size
  simp only [Devm.memory_setMach]
  rw [hmem.size_eq, Mem.size_write_word_at]
  decide +kernel

private theorem payload_length_bound
    {data payload : Bytes} {head : Nat}
    (heq : dynamicPayload data head = payload) :
    payload.length < 2 ^ 256 := by
  have h := congrArg List.length heq
  simp only [dynamicPayload, List.length_sliceD] at h
  rw [← h]
  exact B256.toNat_lt _

/-- Lift an exact decoded-body error through the successful ABI decoder. -/
private theorem depositEndpointErrorWitness_of_body
    {sevm : Sevm} {base : Devm} {G bodyCost : Nat}
    {pubkey withdrawalCredentials signature : Bytes}
    {depositDataRoot : B256} {reason : Reason} {post : Devm}
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hdec : DepositAbiDecodable sevm.data pubkey withdrawalCredentials
      signature depositDataRoot)
    (hbody : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
      (base.setMach
        ⟨[], depositDecodedMemory sevm.data, G + bodyCost⟩)
      depositBody (.error (.revert, post)))
    (houtput : post.output = errorData (reasonString reason)) :
    DepositEndpointErrorWitness sevm base G reason := by
  unfold DepositEndpointErrorWitness
  have habi := validateDepositAbi_success_runCompiledTo
    (fs := runtime.main :: runtime.aux) (sevm := sevm) (base := base)
    (G := G + bodyCost) (body := depositBody)
    hdataBound hdec hbody
  refine ⟨bodyCost + 521, post, ?_, houtput⟩
  have hgas : (G + bodyCost) + 521 = G + (bodyCost + 521) := by
    omega
  simpa only [depositEndpoint, hgas] using habi

/-- Compose one post-reconstruction error through event staging and the six
successful pre-hash guards.  The final guard is supplied at the fixed 768-byte
memory boundary. -/
private theorem depositPostHashError_endpoint_runCompiledTo
    {sevm : Sevm} {base : Devm}
    {pubkey withdrawalCredentials signature : Bytes}
    {depositDataRoot : B256} {oldCount amount : B256}
    {G guardPrefixCost : Nat} {error : ReachableReason}
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hdec : DepositAbiDecodable sevm.data pubkey withdrawalCredentials
      signature depositDataRoot)
    (hpubkey : pubkey.length = 48)
    (hwithdrawal : withdrawalCredentials.length = 32)
    (hsignature : signature.length = 96)
    (hamount : sevm.value / Nat.toB256 oneGwei = amount)
    (hlower : Nat.toB256 oneEther ≤ sevm.value)
    (hgwei : sevm.value % Nat.toB256 oneGwei = 0)
    (hupper : amount ≤ Nat.toB256 (2 ^ 64 - 1))
    (hcountValue :
      base.getStorVal sevm.currentTarget depositCountSlot = oldCount)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hstatic : sevm.isStatic = false)
    (hbound :
      (G + depositPostHashErrorGuardCost error + guardPrefixCost) + 1762 <
        2 ^ 256)
    (hguard : ∀ {finalPost : Devm},
      InsertionStartMemoryCarrier finalPost.memory oldCount
        (depositDataNode Bytes.sha256 pubkey withdrawalCredentials signature
          (le64 amount.toNat)) →
      ∃ post,
        Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
          (finalPost.setMach ⟨[], finalPost.memory,
            G + depositPostHashErrorGuardCost error + guardPrefixCost⟩)
          depositSuccessGuards (.error (.revert, post)) ∧
        post.output = errorData (reasonString error.reason)) :
    DepositEndpointErrorWitness sevm base G error.reason := by
  let K := G + depositPostHashErrorGuardCost error + guardPrefixCost
  obtain ⟨logged, _hlogs, _hstorVal, _hstorMap, _hbal, hcode,
      _hloadedKeys, haddresses, _houtput, _herror, heventLift⟩ :=
    stageDepositEvent_runCompiledTo
      (fs := runtime.main :: runtime.aux) (sevm := sevm) (base := base)
      (amount := amount) (oldCount := oldCount) (G := K + 1779)
      (body := depositAfterEvent)
      hdec.pubkeyTail hdec.withdrawalCredentialsTail hdec.signatureTail
      hcountValue hstatic
  let stagedBase := logged.setMach
    ⟨[], depositEventMemory sevm.data amount oldCount, G⟩
  have hsource : ReconstructSourceMemoryCarrier stagedBase.memory
      (pubkey ++ zeros 16) (signature.take 64) (signature.drop 64)
      withdrawalCredentials (le64 amount.toNat ++ zeros 24)
      oldCount amount 704 := by
    simpa only [stagedBase, Devm.memory_setMach] using
      (depositEventMemory_carrier sevm.data amount oldCount
        |>.toDecodedReconstructSource
          hdec hpubkey hwithdrawal hsignature)
  have hnodeleg' : getDelegatedCodeAddress (stagedBase.getCode 2) = none := by
    change getDelegatedCodeAddress (logged.getCode 2) = none
    rw [hcode 2, Blanc.afterSload_getCode]
    exact hnodeleg
  have hwarm' : (2 : Adr) ∈ stagedBase.accessedAddresses := by
    change (2 : Adr) ∈ logged.accessedAddresses
    rw [haddresses, Blanc.afterSload_accessedAddresses]
    exact hwarm
  obtain ⟨finalPost, hregisters, _hreturn, _hmeta, hreconstructLift⟩ :=
    reconstructDepositDataNode_runCompiledTo
      (fs := runtime.main :: runtime.aux) (sevm := sevm)
      (base := stagedBase) (pubkeyInput := pubkey ++ zeros 16)
      (signatureFirst := signature.take 64)
      (signatureTail := signature.drop 64)
      (withdrawal := withdrawalCredentials)
      (amountPadded := le64 amount.toNat ++ zeros 24)
      (oldCount := oldCount) (amount := amount) (stack := [])
      (success := depositSuccessGuards) (K := K)
      hsource hnodeleg' hwarm' hpre hdepth (by
        simpa only [K] using hbound) (by simp)
  obtain ⟨hregisters⟩ := hregisters
  have hnodeEq := reconstructedDepositNode_eq_model pubkey
    withdrawalCredentials signature (le64 amount.toNat)
    hwithdrawal rfl hsignature
  have hstart : InsertionStartMemoryCarrier finalPost.memory oldCount
      (depositDataNode Bytes.sha256 pubkey withdrawalCredentials signature
        (le64 amount.toNat)) := by
    rw [← hnodeEq]
    exact hregisters.toInsertionStart
  obtain ⟨post, hguardRun, hpostOutput⟩ := hguard hstart
  have hreconstructRun : Func.RunCompiledTo
      (runtime.main :: runtime.aux) sevm
      (stagedBase.setMach ⟨[], stagedBase.memory, K + 1779⟩)
      (reconstructDepositDataNode depositSuccessGuards)
      (.error (.revert, post)) := by
    exact hreconstructLift hguardRun
  have heventRun : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
      (base.setMach
        ⟨[], depositEventInputMemory sevm.data amount,
          (K + 1779) + 5799 + sloadCost sevm base depositCountSlot⟩)
      (stageDepositEvent +++ depositAfterEvent)
      (.error (.revert, post)) := by
    apply heventLift
    rw [show depositAfterEvent =
      reconstructDepositDataNode depositSuccessGuards by rfl]
    simpa only [stagedBase, Devm.setMach_setMach, Devm.memory_setMach] using
      hreconstructRun
  have hguards := depositGuards_runCompiledTo
    (fs := runtime.main :: runtime.aux) (sevm := sevm) (base := base)
    (amount := amount)
    (G := (K + 1779) + 5799 + sloadCost sevm base depositCountSlot)
    hdec hpubkey hwithdrawal hsignature hamount hlower hgwei hupper heventRun
  let bodyCost :=
    (((depositPostHashErrorGuardCost error + guardPrefixCost + 1779) +
      5799 + sloadCost sevm base depositCountSlot) + depositGuardsGas)
  have hgas :
      (((K + 1779) + 5799 + sloadCost sevm base depositCountSlot) +
          depositGuardsGas) = G + bodyCost := by
    simp only [K, bodyCost]
    omega
  exact depositEndpointErrorWitness_of_body hdataBound hdec
    (bodyCost := bodyCost) (by simpa only [hgas] using hguards) hpostOutput

/-- One failing decoded-length guard, including its exact catalogued
`Error(string)` auxiliary. -/
private theorem depositLengthGuard_failure_runCompiledTo
    {sevm : Sevm} {base : Devm} {memory : Mem} {data : Bytes}
    {actual expected : B256} {word : B256} {index : Nat}
    {G : Nat} {otherwise : Func}
    (error : ReachableReason)
    (hmem : DepositDecodedMemoryCarrier memory data)
    (hindex : (word * 32).toNat = index)
    (hcovered : index + 32 ≤ memory.size)
    (hread : Bytes.toB256 (memory.read index 32).1 = actual)
    (hne : actual ≠ expected)
    (hwordPush : pushCost (word * 32).toBytes.sig = gVerylow)
    (hexpectedPush : pushCost expected.toBytes.sig = gVerylow) :
    let guardBase := base.setMach ⟨[], memory, 0⟩
    Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], memory,
        (G + errorGuardCost guardBase (reasonString error.reason)) + 15⟩)
      (loadWord word +++ pushB256 expected ::: eq ::: iszero :::
        ((.call error.slot) <?> otherwise))
      (.error (.revert,
        (base.setMach ⟨[],
          Mem.writeStoresRev memory
            (bytesWords (errorData (reasonString error.reason))).zipIdx,
          G⟩).withOutput (errorData (reasonString error.reason)))) := by
  dsimp only
  let guardBase := base.setMach ⟨[], memory, 0⟩
  let errorCost := errorGuardCost guardBase (reasonString error.reason)
  have hmod : memory.size % 32 = 0 := by
    rw [hmem.size_eq]
  have hmemory : (memory.read index 32).2 = memory :=
    Mem.read_snd_eq_self (memExtSize_of_le hmod hcovered)
  unfold loadWord
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (c := gVerylow) (G := (G + errorCost) + 12) hwordPush
      (by
        simp only [Devm.gasLeft_setMach, errorCost, guardBase,
          gVerylow])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_mload_of
      (i := word * 32) (v := actual) (s := [])
      (c := gVerylow) (G := (G + errorCost) + 9) (M := memory) rfl
      (by
        rw [Devm.extCost_zero_of_le hmod (by rw [hindex]; exact hcovered)]
        rfl)
      (by rw [Devm.memory_setMach, hindex, hread])
      (by rw [Devm.memory_setMach, hindex, hmemory])
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (c := gVerylow) (G := (G + errorCost) + 6) hexpectedPush
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  func_run (2) [0, 1]
  case h_val => simp [B256.eqCheck, Ne.symm hne]
  simpa only [guardBase, errorCost, Devm.setMach_setMach,
      Devm.memory_setMach, Nat.add_sub_cancel] using
    (reachableErrorGuard_exact_runCompiledTo
      (base := guardBase) (G := G) (w := (1 : B256))
      (stack := []) (img := hmem.image) (otherwise := otherwise)
      error (by decide) hmem.wf hmem.reads hmod
      (by cases error <;> decide +kernel)
      (by cases error <;> decide +kernel)
      (by decide))

/-- The lower-value comparison selects its catalogued error auxiliary. -/
private theorem depositValueLowerGuard_failure_runCompiledTo
    {sevm : Sevm} {base : Devm} {memory : Mem} {data : Bytes}
    {G : Nat} {otherwise : Func}
    (hmem : DepositDecodedMemoryCarrier memory data)
    (hlower : sevm.value < Nat.toB256 oneEther) :
    let guardBase := base.setMach ⟨[], memory, 0⟩
    Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], memory,
        (G + errorGuardCost guardBase
          (reasonString ReachableReason.valueTooLow.reason)) + 8⟩)
      (pushB256 (Nat.toB256 oneEther) ::: callvalue ::: lt :::
        ((.call valueTooLowErrorSlot) <?> otherwise))
      (.error (.revert,
        (base.setMach ⟨[],
          Mem.writeStoresRev memory
            (bytesWords (errorData (reasonString
              ReachableReason.valueTooLow.reason))).zipIdx,
          G⟩).withOutput (errorData (reasonString
            ReachableReason.valueTooLow.reason)))) := by
  dsimp only
  let guardBase := base.setMach ⟨[], memory, 0⟩
  let errorCost := errorGuardCost guardBase
    (reasonString ReachableReason.valueTooLow.reason)
  have hmod : memory.size % 32 = 0 := by
    rw [hmem.size_eq]
  func_run (3) [1]
  case h_val => simp [B256.ltCheck, hlower]
  simpa only [guardBase, errorCost, Devm.setMach_setMach,
      Devm.memory_setMach, ReachableReason.slot,
      Nat.add_sub_cancel] using
    (reachableErrorGuard_exact_runCompiledTo
      (base := guardBase) (G := G) (w := (1 : B256))
      (stack := []) (img := hmem.image) (otherwise := otherwise)
      .valueTooLow (by decide) hmem.wf hmem.reads hmod
      (by decide +kernel) (by decide +kernel) (by decide))

/-- A nonzero gwei remainder selects its catalogued error auxiliary. -/
private theorem depositGweiMultipleGuard_failure_runCompiledTo
    {sevm : Sevm} {base : Devm} {memory : Mem} {data : Bytes}
    {G : Nat} {otherwise : Func}
    (hmem : DepositDecodedMemoryCarrier memory data)
    (hremainder : sevm.value % Nat.toB256 oneGwei ≠ 0) :
    let guardBase := base.setMach ⟨[], memory, 0⟩
    Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], memory,
        (G + errorGuardCost guardBase
          (reasonString ReachableReason.valueNotGweiMultiple.reason)) + 10⟩)
      (pushB256 (Nat.toB256 oneGwei) ::: callvalue ::: mod :::
        ((.call valueNotGweiErrorSlot) <?> otherwise))
      (.error (.revert,
        (base.setMach ⟨[],
          Mem.writeStoresRev memory
            (bytesWords (errorData (reasonString
              ReachableReason.valueNotGweiMultiple.reason))).zipIdx,
          G⟩).withOutput (errorData (reasonString
            ReachableReason.valueNotGweiMultiple.reason)))) := by
  dsimp only
  let guardBase := base.setMach ⟨[], memory, 0⟩
  let errorCost := errorGuardCost guardBase
    (reasonString ReachableReason.valueNotGweiMultiple.reason)
  have hmod : memory.size % 32 = 0 := by
    rw [hmem.size_eq]
  func_run (3) [sevm.value % Nat.toB256 oneGwei]
  case h_gas => simp only [Devm.gasLeft_setMach, gLow]; omega
  simpa only [guardBase, errorCost, Devm.setMach_setMach,
      Devm.memory_setMach, ReachableReason.slot,
      Nat.add_sub_cancel] using
    (reachableErrorGuard_exact_runCompiledTo
      (base := guardBase) (G := G)
      (w := sevm.value % Nat.toB256 oneGwei)
      (stack := []) (img := hmem.image) (otherwise := otherwise)
      .valueNotGweiMultiple hremainder hmem.wf hmem.reads hmod
      (by decide +kernel) (by decide +kernel) (by decide))

/-- An amount above the uint64 bound selects its catalogued error auxiliary
after retaining the exact expanded amount-memory image. -/
private theorem depositAmountUpperGuard_failure_runCompiledTo
    {sevm : Sevm} {base : Devm} {memory : Mem} {data : Bytes}
    {amount : B256} {G : Nat} {otherwise : Func}
    (hmem : DepositDecodedMemoryCarrier memory data)
    (hamount : sevm.value / Nat.toB256 oneGwei = amount)
    (hupper : Nat.toB256 (2 ^ 64 - 1) < amount) :
    let writtenMemory := memory.write 672 amount.toBytes
    let guardBase := base.setMach ⟨[], writtenMemory, 0⟩
    Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], memory,
        (G + errorGuardCost guardBase
          (reasonString ReachableReason.valueTooHigh.reason)) + 73⟩)
      (pushB256 (Nat.toB256 oneGwei) ::: callvalue ::: div ::: dup 0 :::
        mstoreAt amountWord +++
        pushB256 (Nat.toB256 (2 ^ 64 - 1)) ::: lt :::
        ((.call valueTooHighErrorSlot) <?> otherwise))
      (.error (.revert,
        (base.setMach ⟨[],
          Mem.writeStoresRev writtenMemory
            (bytesWords (errorData (reasonString
              ReachableReason.valueTooHigh.reason))).zipIdx,
          G⟩).withOutput (errorData (reasonString
            ReachableReason.valueTooHigh.reason)))) := by
  dsimp only
  let writtenMemory := memory.write 672 amount.toBytes
  let guardBase := base.setMach ⟨[], writtenMemory, 0⟩
  let errorCost := errorGuardCost guardBase
    (reasonString ReachableReason.valueTooHigh.reason)
  have hwritten : DepositEventInputMemoryCarrier writtenMemory data amount := by
    exact hmem.writeAmount amount
  have hmod : writtenMemory.size % 32 = 0 := by
    rw [hwritten.size_eq]
  have hamountWord : (amountWord * 32 : B256).toNat = 672 := by
    decide +kernel
  func_run (8) [amount, 48, 1]
  case h_gas => simp only [Devm.gasLeft_setMach, gLow]; omega
  case h_ext =>
    rw [hamountWord]
    exact Devm.extCost_of_size hmem.size_eq (by decide +kernel)
  case h_val => rw [B256.ltCheck, if_pos hupper]
  simpa only [writtenMemory, guardBase, errorCost,
      Devm.setMach_setMach, Devm.memory_setMach,
      ReachableReason.slot, Nat.add_sub_cancel, hamountWord] using
    (reachableErrorGuard_exact_runCompiledTo
      (base := guardBase) (G := G) (w := (1 : B256))
      (stack := []) (img := hwritten.image)
      (otherwise := otherwise)
      .valueTooHigh (by decide) hwritten.wf hwritten.reads
      hmod (by decide +kernel) (by decide +kernel) (by decide))

/-- A reconstructed node unequal to calldata selects the root-mismatch
auxiliary before the capacity guard. -/
private theorem depositRootGuard_failure_runCompiledTo
    {sevm : Sevm} {base : Devm} {memory : Mem}
    {oldCount node : B256} {G : Nat}
    (hmem : InsertionStartMemoryCarrier memory oldCount node)
    (hroot : Sevm.argWord sevm 3 ≠ node) :
    let guardBase := base.setMach ⟨[], memory, 0⟩
    Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], memory,
        (G + errorGuardCost guardBase
          (reasonString ReachableReason.depositDataRootMismatch.reason)) + 18⟩)
      depositSuccessGuards
      (.error (.revert,
        (base.setMach ⟨[],
          Mem.writeStoresRev memory
            (bytesWords (errorData (reasonString
              ReachableReason.depositDataRootMismatch.reason))).zipIdx,
          G⟩).withOutput (errorData (reasonString
            ReachableReason.depositDataRootMismatch.reason)))) := by
  dsimp only
  let guardBase := base.setMach ⟨[], memory, 0⟩
  let errorCost := errorGuardCost guardBase
    (reasonString ReachableReason.depositDataRootMismatch.reason)
  have hmod : memory.size % 32 = 0 := by
    rw [hmem.size_eq]
  have hcovered : 640 + 32 ≤ memory.size := by
    rw [hmem.size_eq]
    omega
  have hread : Bytes.toB256 (memory.read 640 32).1 = node := hmem.readNode
  have hmemory : (memory.read 640 32).2 = memory := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le hmod hcovered)]
  unfold depositSuccessGuards
  func_run (6) [3, 0, 1]
  case h_cost =>
    simp only [show (nodeWord * 32 : B256).toNat = 640 by decide +kernel]
    rw [Devm.extCost_zero_of_le hmod hcovered]
    norm_num [gVerylow]
  case h_val =>
    change Sevm.argWord sevm 3 =? (memory.read 640 32).1.toB256 = 0
    rw [hread]
    simp [B256.eqCheck, hroot]
  simpa only [guardBase, errorCost, Devm.setMach_setMach,
      Devm.memory_setMach,
      show (nodeWord * 32 : B256).toNat = 640 by decide +kernel,
      hmemory, ReachableReason.slot,
      Nat.add_sub_cancel] using
    (reachableErrorGuard_exact_runCompiledTo
      (base := guardBase) (G := G) (w := (1 : B256))
      (stack := []) (img := hmem.image)
      (otherwise :=
        pushB256 (Nat.toB256 (2 ^ 32 - 1)) :::
          loadWord oldCountWord +++ lt ::: iszero :::
          ((.call treeFullErrorSlot) <?> commitDeposit))
      .depositDataRootMismatch (by decide) hmem.wf hmem.reads hmod
      (by decide +kernel) (by decide +kernel) (by decide))

/-- A non-capacity count selects the tree-full auxiliary after the root guard
has passed. -/
private theorem depositCapGuard_failure_runCompiledTo
    {sevm : Sevm} {base : Devm} {memory : Mem}
    {oldCount node : B256} {G : Nat} {otherwise : Func}
    (hmem : InsertionStartMemoryCarrier memory oldCount node)
    (hcap : ¬ oldCount < Nat.toB256 (2 ^ 32 - 1)) :
    let guardBase := base.setMach ⟨[], memory, 0⟩
    Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], memory,
        (G + errorGuardCost guardBase
          (reasonString ReachableReason.merkleTreeFull.reason)) + 15⟩)
      (pushB256 (Nat.toB256 (2 ^ 32 - 1)) :::
        loadWord oldCountWord +++ lt ::: iszero :::
        ((.call treeFullErrorSlot) <?> otherwise))
      (.error (.revert,
        (base.setMach ⟨[],
          Mem.writeStoresRev memory
            (bytesWords (errorData (reasonString
              ReachableReason.merkleTreeFull.reason))).zipIdx,
          G⟩).withOutput (errorData (reasonString
            ReachableReason.merkleTreeFull.reason)))) := by
  dsimp only
  let guardBase := base.setMach ⟨[], memory, 0⟩
  let errorCost := errorGuardCost guardBase
    (reasonString ReachableReason.merkleTreeFull.reason)
  have hmod : memory.size % 32 = 0 := by
    rw [hmem.size_eq]
  have hcovered : 576 + 32 ≤ memory.size := by
    rw [hmem.size_eq]
    omega
  have hread : Bytes.toB256 (memory.read 576 32).1 = oldCount :=
    hmem.readOldCount
  have hmemory : (memory.read 576 32).2 = memory := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le hmod hcovered)]
  func_run (5) [3, 0, 1]
  case h_cost =>
    rw [show (oldCountWord * 32 : B256).toNat = 576 by decide +kernel]
    rw [Devm.extCost_zero_of_le hmod hcovered]
    norm_num [gVerylow]
  case h_val =>
    rw [show (oldCountWord * 32 : B256).toNat = 576 by decide +kernel,
      hread]
    rw [B256.ltCheck, if_neg hcap]
  simpa only [guardBase, errorCost, Devm.setMach_setMach,
      Devm.memory_setMach,
      show (oldCountWord * 32 : B256).toNat = 576 by decide +kernel,
      hmemory, ReachableReason.slot,
      Nat.add_sub_cancel] using
    (reachableErrorGuard_exact_runCompiledTo
      (base := guardBase) (G := G) (w := (1 : B256))
      (stack := []) (img := hmem.image) (otherwise := otherwise)
      .merkleTreeFull (by decide) hmem.wf hmem.reads hmod
      (by decide +kernel) (by decide +kernel) (by decide))

/-- The model's first reachable error selects the compiled pubkey-length
guard and emits its byte-exact Solidity `Error(string)` payload. -/
theorem deposit_pubkeyLength_error_endpoint_runCompiledTo
    {sevm : Sevm} {base : Devm} {state : Acc}
    {pubkey withdrawalCredentials signature : Bytes}
    {depositDataRoot : B256} {G : Nat}
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hdec : DepositAbiDecodable sevm.data pubkey withdrawalCredentials
      signature depositDataRoot)
    (herror : deposit Bytes.sha256 state pubkey withdrawalCredentials
      signature depositDataRoot sevm.value.toNat =
        .error .pubkey_length) :
    DepositEndpointErrorWitness sevm base G .pubkey_length := by
  have hspec := deposit_error_spec Bytes.sha256 state pubkey
    withdrawalCredentials signature depositDataRoot sevm.value.toNat
    .pubkeyLength herror
  have hlength := depositLengthWord_of_payload
    hdec.pubkey_eq rfl
  let memory := depositDecodedMemory sevm.data
  have hcarrier : DepositDecodedMemoryCarrier memory sevm.data :=
    depositDecodedMemory_carrier sevm.data
  have hread : Bytes.toB256 (memory.read 96 32).1 =
      Nat.toB256 pubkey.length := by
    rw [hcarrier.read_length0, B256.toB256_toBytes, hlength]
  have hne : Nat.toB256 pubkey.length ≠ (48 : B256) := by
    intro equal
    have natural := congrArg B256.toNat equal
    rw [B256.toNat_toB256_of_lt
      (payload_length_bound hdec.pubkey_eq)] at natural
    have h48 : (48 : B256).toNat = 48 := by decide +kernel
    rw [h48] at natural
    exact hspec natural
  let guardBase := base.setMach ⟨[], memory, 0⟩
  let guardCost := errorGuardCost guardBase
    (reasonString ReachableReason.pubkeyLength.reason)
  let post := (base.setMach ⟨[],
    Mem.writeStoresRev memory
      (bytesWords (errorData
        (reasonString ReachableReason.pubkeyLength.reason))).zipIdx,
    G⟩).withOutput
      (errorData (reasonString ReachableReason.pubkeyLength.reason))
  have hguard : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], memory, (G + guardCost) + 15⟩)
      depositBody (.error (.revert, post)) := by
    unfold depositBody
    simpa only [memory, guardBase, guardCost, post,
        ReachableReason.slot] using
      (depositLengthGuard_failure_runCompiledTo
        (sevm := sevm) (base := base) (memory := memory)
        (data := sevm.data) (actual := Nat.toB256 pubkey.length)
        (expected := (48 : B256)) (word := 3) (index := 96)
        (G := G)
        .pubkeyLength hcarrier (by decide +kernel)
        (by rw [hcarrier.size_eq]; omega) hread hne
        (by decide +kernel) (by decide +kernel))
  exact depositEndpointErrorWitness_of_body hdataBound hdec
    (bodyCost := guardCost + 15) (by
      simpa only [Nat.add_assoc] using hguard) rfl

/-- The model's second reachable error passes the pubkey-length guard before
selecting the withdrawal-credentials-length auxiliary. -/
theorem deposit_withdrawalCredentialsLength_error_endpoint_runCompiledTo
    {sevm : Sevm} {base : Devm} {state : Acc}
    {pubkey withdrawalCredentials signature : Bytes}
    {depositDataRoot : B256} {G : Nat}
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hdec : DepositAbiDecodable sevm.data pubkey withdrawalCredentials
      signature depositDataRoot)
    (herror : deposit Bytes.sha256 state pubkey withdrawalCredentials
      signature depositDataRoot sevm.value.toNat =
        .error .withdrawal_credentials_length) :
    DepositEndpointErrorWitness sevm base G
      .withdrawal_credentials_length := by
  have hspec := deposit_error_spec Bytes.sha256 state pubkey
    withdrawalCredentials signature depositDataRoot sevm.value.toNat
    .withdrawalCredentialsLength herror
  obtain ⟨hpubkey, hwithdrawal⟩ := hspec
  have hlength0 : depositLengthWord sevm.data 0 = (48 : B256) :=
    depositLengthWord_of_payload hdec.pubkey_eq hpubkey
  have hlength1 := depositLengthWord_of_payload
    hdec.withdrawalCredentials_eq rfl
  let memory := depositDecodedMemory sevm.data
  have hcarrier : DepositDecodedMemoryCarrier memory sevm.data :=
    depositDecodedMemory_carrier sevm.data
  have hread0 : Bytes.toB256 (memory.read 96 32).1 = (48 : B256) := by
    rw [hcarrier.read_length0, B256.toB256_toBytes, hlength0]
  have hread1 : Bytes.toB256 (memory.read 128 32).1 =
      Nat.toB256 withdrawalCredentials.length := by
    rw [hcarrier.read_length1, B256.toB256_toBytes, hlength1]
  have hne : Nat.toB256 withdrawalCredentials.length ≠ (32 : B256) := by
    intro equal
    have natural := congrArg B256.toNat equal
    rw [B256.toNat_toB256_of_lt
      (payload_length_bound hdec.withdrawalCredentials_eq)] at natural
    have h32 : (32 : B256).toNat = 32 := by decide +kernel
    rw [h32] at natural
    exact hwithdrawal natural
  let guardBase := base.setMach ⟨[], memory, 0⟩
  let guardCost := errorGuardCost guardBase
    (reasonString ReachableReason.withdrawalCredentialsLength.reason)
  let post := (base.setMach ⟨[],
    Mem.writeStoresRev memory
      (bytesWords (errorData (reasonString
        ReachableReason.withdrawalCredentialsLength.reason))).zipIdx,
    G⟩).withOutput (errorData (reasonString
      ReachableReason.withdrawalCredentialsLength.reason))
  have hguard : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], memory, ((G + guardCost) + 15) + 28⟩)
      depositBody (.error (.revert, post)) := by
    unfold depositBody
    refine depositLengthGuard_runCompiledTo
      (word := 3) (expected := 48) (index := 96)
      (slot := pubkeyLengthErrorSlot) hcarrier (by decide +kernel)
      (by rw [hcarrier.size_eq]; omega) hread0
      (by decide +kernel) (by decide +kernel) ?_
    simpa only [memory, guardBase, guardCost, post,
        ReachableReason.slot] using
      (depositLengthGuard_failure_runCompiledTo
        (sevm := sevm) (base := base) (memory := memory)
        (data := sevm.data)
        (actual := Nat.toB256 withdrawalCredentials.length)
        (expected := (32 : B256)) (word := 4) (index := 128)
        (G := G) .withdrawalCredentialsLength hcarrier
        (by decide +kernel) (by rw [hcarrier.size_eq]; omega)
        hread1 hne (by decide +kernel) (by decide +kernel))
  exact depositEndpointErrorWitness_of_body hdataBound hdec
    (bodyCost := guardCost + 43) (by
      simpa only [Nat.add_assoc] using hguard) rfl

/-- The model's third reachable error passes both earlier dynamic-length
guards before selecting the signature-length auxiliary. -/
theorem deposit_signatureLength_error_endpoint_runCompiledTo
    {sevm : Sevm} {base : Devm} {state : Acc}
    {pubkey withdrawalCredentials signature : Bytes}
    {depositDataRoot : B256} {G : Nat}
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hdec : DepositAbiDecodable sevm.data pubkey withdrawalCredentials
      signature depositDataRoot)
    (herror : deposit Bytes.sha256 state pubkey withdrawalCredentials
      signature depositDataRoot sevm.value.toNat =
        .error .signature_length) :
    DepositEndpointErrorWitness sevm base G .signature_length := by
  have hspec := deposit_error_spec Bytes.sha256 state pubkey
    withdrawalCredentials signature depositDataRoot sevm.value.toNat
    .signatureLength herror
  obtain ⟨hpubkey, hwithdrawal, hsignature⟩ := hspec
  have hlength0 : depositLengthWord sevm.data 0 = (48 : B256) :=
    depositLengthWord_of_payload hdec.pubkey_eq hpubkey
  have hlength1 : depositLengthWord sevm.data 1 = (32 : B256) :=
    depositLengthWord_of_payload
      hdec.withdrawalCredentials_eq hwithdrawal
  have hlength2 := depositLengthWord_of_payload hdec.signature_eq rfl
  let memory := depositDecodedMemory sevm.data
  have hcarrier : DepositDecodedMemoryCarrier memory sevm.data :=
    depositDecodedMemory_carrier sevm.data
  have hread0 : Bytes.toB256 (memory.read 96 32).1 = (48 : B256) := by
    rw [hcarrier.read_length0, B256.toB256_toBytes, hlength0]
  have hread1 : Bytes.toB256 (memory.read 128 32).1 = (32 : B256) := by
    rw [hcarrier.read_length1, B256.toB256_toBytes, hlength1]
  have hread2 : Bytes.toB256 (memory.read 160 32).1 =
      Nat.toB256 signature.length := by
    rw [hcarrier.read_length2, B256.toB256_toBytes, hlength2]
  have hne : Nat.toB256 signature.length ≠ (96 : B256) := by
    intro equal
    have natural := congrArg B256.toNat equal
    rw [B256.toNat_toB256_of_lt
      (payload_length_bound hdec.signature_eq)] at natural
    have h96 : (96 : B256).toNat = 96 := by decide +kernel
    rw [h96] at natural
    exact hsignature natural
  let guardBase := base.setMach ⟨[], memory, 0⟩
  let guardCost := errorGuardCost guardBase
    (reasonString ReachableReason.signatureLength.reason)
  let post := (base.setMach ⟨[],
    Mem.writeStoresRev memory
      (bytesWords (errorData
        (reasonString ReachableReason.signatureLength.reason))).zipIdx,
    G⟩).withOutput
      (errorData (reasonString ReachableReason.signatureLength.reason))
  have hguard : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
      (base.setMach
        ⟨[], memory, (((G + guardCost) + 15) + 28) + 28⟩)
      depositBody (.error (.revert, post)) := by
    unfold depositBody
    refine depositLengthGuard_runCompiledTo
      (word := 3) (expected := 48) (index := 96)
      (slot := pubkeyLengthErrorSlot) hcarrier (by decide +kernel)
      (by rw [hcarrier.size_eq]; omega) hread0
      (by decide +kernel) (by decide +kernel) ?_
    refine depositLengthGuard_runCompiledTo
      (word := 4) (expected := 32) (index := 128)
      (slot := withdrawalLengthErrorSlot) hcarrier (by decide +kernel)
      (by rw [hcarrier.size_eq]; omega) hread1
      (by decide +kernel) (by decide +kernel) ?_
    simpa only [memory, guardBase, guardCost, post,
        ReachableReason.slot] using
      (depositLengthGuard_failure_runCompiledTo
        (sevm := sevm) (base := base) (memory := memory)
        (data := sevm.data) (actual := Nat.toB256 signature.length)
        (expected := (96 : B256)) (word := 5) (index := 160)
        (G := G) .signatureLength hcarrier (by decide +kernel)
        (by rw [hcarrier.size_eq]) hread2 hne
        (by decide +kernel) (by decide +kernel))
  exact depositEndpointErrorWitness_of_body hdataBound hdec
    (bodyCost := guardCost + 71) (by
      simpa only [Nat.add_assoc] using hguard) rfl

/-- The model's fourth reachable error passes all decoded-length guards before
selecting the lower-value auxiliary. -/
theorem deposit_valueTooLow_error_endpoint_runCompiledTo
    {sevm : Sevm} {base : Devm} {state : Acc}
    {pubkey withdrawalCredentials signature : Bytes}
    {depositDataRoot : B256} {G : Nat}
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hdec : DepositAbiDecodable sevm.data pubkey withdrawalCredentials
      signature depositDataRoot)
    (herror : deposit Bytes.sha256 state pubkey withdrawalCredentials
      signature depositDataRoot sevm.value.toNat =
        .error .value_too_low) :
    DepositEndpointErrorWitness sevm base G .value_too_low := by
  have hspec := deposit_error_spec Bytes.sha256 state pubkey
    withdrawalCredentials signature depositDataRoot sevm.value.toNat
    .valueTooLow herror
  obtain ⟨hpubkey, hwithdrawal, hsignature, hlowerNat⟩ := hspec
  let memory := depositDecodedMemory sevm.data
  have hcarrier : DepositDecodedMemoryCarrier memory sevm.data :=
    depositDecodedMemory_carrier sevm.data
  have hlowerWord : sevm.value < Nat.toB256 oneEther := by
    rw [B256.lt_iff_toNat_lt_toNat,
      B256.toNat_toB256_of_lt (by norm_num [oneEther])]
    exact hlowerNat
  let guardBase := base.setMach ⟨[], memory, 0⟩
  let guardCost := errorGuardCost guardBase
    (reasonString ReachableReason.valueTooLow.reason)
  let post := (base.setMach ⟨[],
    Mem.writeStoresRev memory
      (bytesWords (errorData
        (reasonString ReachableReason.valueTooLow.reason))).zipIdx,
    G⟩).withOutput
      (errorData (reasonString ReachableReason.valueTooLow.reason))
  have hguard : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], memory, ((G + guardCost) + 8) + 84⟩)
      depositBody (.error (.revert, post)) := by
    unfold depositBody
    refine depositLengthGuards_runCompiledTo hcarrier hdec
      hpubkey hwithdrawal hsignature ?_
    simpa only [memory, guardBase, guardCost, post] using
      (depositValueLowerGuard_failure_runCompiledTo
        (sevm := sevm) (base := base) (memory := memory)
        (data := sevm.data) (G := G) hcarrier hlowerWord)
  exact depositEndpointErrorWitness_of_body hdataBound hdec
    (bodyCost := guardCost + 92) (by
      simpa only [Nat.add_assoc] using hguard) rfl

/-- The model's fifth reachable error passes the lower bound before selecting
the non-gwei-multiple auxiliary. -/
theorem deposit_valueNotGweiMultiple_error_endpoint_runCompiledTo
    {sevm : Sevm} {base : Devm} {state : Acc}
    {pubkey withdrawalCredentials signature : Bytes}
    {depositDataRoot : B256} {G : Nat}
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hdec : DepositAbiDecodable sevm.data pubkey withdrawalCredentials
      signature depositDataRoot)
    (herror : deposit Bytes.sha256 state pubkey withdrawalCredentials
      signature depositDataRoot sevm.value.toNat =
        .error .value_not_gwei_multiple) :
    DepositEndpointErrorWitness sevm base G .value_not_gwei_multiple := by
  have hspec := deposit_error_spec Bytes.sha256 state pubkey
    withdrawalCredentials signature depositDataRoot sevm.value.toNat
    .valueNotGweiMultiple herror
  obtain ⟨hpubkey, hwithdrawal, hsignature, hlowerNat,
    hremainderNat⟩ := hspec
  let memory := depositDecodedMemory sevm.data
  have hcarrier : DepositDecodedMemoryCarrier memory sevm.data :=
    depositDecodedMemory_carrier sevm.data
  have hdenNe : Nat.toB256 oneGwei ≠ 0 := by
    intro hzero
    have natural := congrArg B256.toNat hzero
    rw [B256.toNat_toB256_of_lt (by norm_num [oneGwei]),
      B256.toNat_zero] at natural
    norm_num [oneGwei] at natural
  have hdenNat : (Nat.toB256 oneGwei).toNat = oneGwei :=
    B256.toNat_toB256_of_lt (by norm_num [oneGwei])
  have hlowerWord : Nat.toB256 oneEther ≤ sevm.value := by
    rw [B256.le_iff_toNat_le_toNat,
      B256.toNat_toB256_of_lt (by norm_num [oneEther])]
    exact hlowerNat
  have hremainderWord : sevm.value % Nat.toB256 oneGwei ≠ 0 := by
    intro hzero
    have natural := congrArg B256.toNat hzero
    rw [B256.toNat_mod hdenNe, hdenNat, B256.toNat_zero] at natural
    exact hremainderNat natural
  let guardBase := base.setMach ⟨[], memory, 0⟩
  let guardCost := errorGuardCost guardBase
    (reasonString ReachableReason.valueNotGweiMultiple.reason)
  let post := (base.setMach ⟨[],
    Mem.writeStoresRev memory
      (bytesWords (errorData (reasonString
        ReachableReason.valueNotGweiMultiple.reason))).zipIdx,
    G⟩).withOutput (errorData (reasonString
      ReachableReason.valueNotGweiMultiple.reason))
  have hguard : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
      (base.setMach
        ⟨[], memory, (((G + guardCost) + 10) + 21) + 84⟩)
      depositBody (.error (.revert, post)) := by
    unfold depositBody
    refine depositLengthGuards_runCompiledTo hcarrier hdec
      hpubkey hwithdrawal hsignature ?_
    refine depositValueLowerGuard_runCompiledTo
      (slot := valueTooLowErrorSlot) hlowerWord ?_
    simpa only [memory, guardBase, guardCost, post] using
      (depositGweiMultipleGuard_failure_runCompiledTo
        (sevm := sevm) (base := base) (memory := memory)
        (data := sevm.data) (G := G) hcarrier hremainderWord)
  exact depositEndpointErrorWitness_of_body hdataBound hdec
    (bodyCost := guardCost + 115) (by
      simpa only [Nat.add_assoc] using hguard) rfl

/-- The model's sixth reachable error passes the lower and gwei-multiple
guards, stores the amount, then selects the uint64-upper-bound auxiliary. -/
theorem deposit_valueTooHigh_error_endpoint_runCompiledTo
    {sevm : Sevm} {base : Devm} {state : Acc}
    {pubkey withdrawalCredentials signature : Bytes}
    {depositDataRoot : B256} {G : Nat}
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hdec : DepositAbiDecodable sevm.data pubkey withdrawalCredentials
      signature depositDataRoot)
    (herror : deposit Bytes.sha256 state pubkey withdrawalCredentials
      signature depositDataRoot sevm.value.toNat =
        .error .value_too_high) :
    DepositEndpointErrorWitness sevm base G .value_too_high := by
  have hspec := deposit_error_spec Bytes.sha256 state pubkey
    withdrawalCredentials signature depositDataRoot sevm.value.toNat
    .valueTooHigh herror
  obtain ⟨hpubkey, hwithdrawal, hsignature, hlowerNat, hgweiNat,
    hupperNat⟩ := hspec
  let memory := depositDecodedMemory sevm.data
  let amount := sevm.value / Nat.toB256 oneGwei
  let writtenMemory := memory.write 672 amount.toBytes
  have hcarrier : DepositDecodedMemoryCarrier memory sevm.data :=
    depositDecodedMemory_carrier sevm.data
  have hdenNe : Nat.toB256 oneGwei ≠ 0 := by
    intro hzero
    have natural := congrArg B256.toNat hzero
    rw [B256.toNat_toB256_of_lt (by norm_num [oneGwei]),
      B256.toNat_zero] at natural
    norm_num [oneGwei] at natural
  have hdenNat : (Nat.toB256 oneGwei).toNat = oneGwei :=
    B256.toNat_toB256_of_lt (by norm_num [oneGwei])
  have hamountNat : amount.toNat = sevm.value.toNat / oneGwei := by
    dsimp only [amount]
    rw [B256.toNat_div hdenNe, hdenNat]
  have hlowerWord : Nat.toB256 oneEther ≤ sevm.value := by
    rw [B256.le_iff_toNat_le_toNat,
      B256.toNat_toB256_of_lt (by norm_num [oneEther])]
    exact hlowerNat
  have hgweiWord : sevm.value % Nat.toB256 oneGwei = 0 := by
    apply B256.toNat_inj
    simpa only [B256.toNat_mod hdenNe, hdenNat, B256.toNat_zero] using
      hgweiNat
  have hupperWord : Nat.toB256 (2 ^ 64 - 1) < amount := by
    rw [B256.lt_iff_toNat_lt_toNat,
      B256.toNat_toB256_of_lt (by omega), hamountNat]
    exact hupperNat
  let guardBase := base.setMach ⟨[], writtenMemory, 0⟩
  let guardCost := errorGuardCost guardBase
    (reasonString ReachableReason.valueTooHigh.reason)
  let post := (base.setMach ⟨[],
    Mem.writeStoresRev writtenMemory
      (bytesWords (errorData
        (reasonString ReachableReason.valueTooHigh.reason))).zipIdx,
    G⟩).withOutput
      (errorData (reasonString ReachableReason.valueTooHigh.reason))
  have hguard : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], memory,
        ((((G + guardCost) + 73) + 23) + 21) + 84⟩)
      depositBody (.error (.revert, post)) := by
    unfold depositBody
    refine depositLengthGuards_runCompiledTo hcarrier hdec
      hpubkey hwithdrawal hsignature ?_
    refine depositValueLowerGuard_runCompiledTo
      (slot := valueTooLowErrorSlot) hlowerWord ?_
    refine depositGweiMultipleGuard_runCompiledTo
      (slot := valueNotGweiErrorSlot) hgweiWord ?_
    simpa only [memory, amount, writtenMemory, guardBase, guardCost,
        post] using
      (depositAmountUpperGuard_failure_runCompiledTo
        (sevm := sevm) (base := base) (memory := memory)
        (data := sevm.data) (amount := amount) (G := G)
        hcarrier rfl hupperWord)
  exact depositEndpointErrorWitness_of_body hdataBound hdec
    (bodyCost := guardCost + 201) (by
      simpa only [Nat.add_assoc] using hguard) rfl

/-- The model's seventh reachable error passes all pre-hash guards and then
selects the reconstructed-root mismatch auxiliary. -/
theorem deposit_depositDataRootMismatch_error_endpoint_runCompiledTo
    {sevm : Sevm} {base : Devm} {state : Acc}
    {pubkey withdrawalCredentials signature : Bytes}
    {depositDataRoot : B256} {G : Nat}
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hdec : DepositAbiDecodable sevm.data pubkey withdrawalCredentials
      signature depositDataRoot)
    (hcountValue :
      base.getStorVal sevm.currentTarget depositCountSlot =
        Nat.toB256 state.count)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hstatic : sevm.isStatic = false)
    (hbound :
      (G + depositPostHashErrorGuardCost .depositDataRootMismatch + 18) +
        1762 < 2 ^ 256)
    (herror : deposit Bytes.sha256 state pubkey withdrawalCredentials
      signature depositDataRoot sevm.value.toNat =
        .error .deposit_data_root_mismatch) :
    DepositEndpointErrorWitness sevm base G
      .deposit_data_root_mismatch := by
  have hspec := deposit_error_spec Bytes.sha256 state pubkey
    withdrawalCredentials signature depositDataRoot sevm.value.toNat
    .depositDataRootMismatch herror
  obtain ⟨hpubkey, hwithdrawal, hsignature, hlowerNat, hgweiNat,
      hupperNat, hrootModel⟩ := hspec
  let amount := sevm.value / Nat.toB256 oneGwei
  let oldCount := Nat.toB256 state.count
  have hdenNe : Nat.toB256 oneGwei ≠ 0 := by
    intro hzero
    have natural := congrArg B256.toNat hzero
    rw [B256.toNat_toB256_of_lt (by norm_num [oneGwei]),
      B256.toNat_zero] at natural
    norm_num [oneGwei] at natural
  have hdenNat : (Nat.toB256 oneGwei).toNat = oneGwei :=
    B256.toNat_toB256_of_lt (by norm_num [oneGwei])
  have hamountNat : amount.toNat = sevm.value.toNat / oneGwei := by
    dsimp only [amount]
    rw [B256.toNat_div hdenNe, hdenNat]
  have hlowerWord : Nat.toB256 oneEther ≤ sevm.value := by
    rw [B256.le_iff_toNat_le_toNat,
      B256.toNat_toB256_of_lt (by norm_num [oneEther])]
    exact hlowerNat
  have hgweiWord : sevm.value % Nat.toB256 oneGwei = 0 := by
    apply B256.toNat_inj
    simpa only [B256.toNat_mod hdenNe, hdenNat, B256.toNat_zero] using
      hgweiNat
  have hupperWord : amount ≤ Nat.toB256 (2 ^ 64 - 1) := by
    rw [B256.le_iff_toNat_le_toNat, hamountNat,
      B256.toNat_toB256_of_lt (by omega)]
    exact hupperNat
  have hrootArg : Sevm.argWord sevm 3 = depositDataRoot := by
    unfold Sevm.argWord
    rw [show 32 * (3 : B256) + 4 = Nat.toB256 100 by decide +kernel,
      dataWord_toB256 (by omega), hdec.root_eq]
  have hrootFail : Sevm.argWord sevm 3 ≠
      depositDataNode Bytes.sha256 pubkey withdrawalCredentials signature
        (le64 amount.toNat) := by
    rw [hrootArg, hamountNat]
    exact hrootModel.symm
  apply depositPostHashError_endpoint_runCompiledTo
    (amount := amount) (oldCount := oldCount)
    (guardPrefixCost := 18) (error := .depositDataRootMismatch)
    hdataBound hdec hpubkey hwithdrawal hsignature rfl
    hlowerWord hgweiWord hupperWord
    (by simpa only [oldCount] using hcountValue)
    hnodeleg hwarm hpre hdepth hstatic hbound
  intro finalPost hstart
  let guardBase := finalPost.setMach ⟨[], finalPost.memory, 0⟩
  let post := (finalPost.setMach ⟨[],
    Mem.writeStoresRev finalPost.memory
      (bytesWords (errorData (reasonString
        ReachableReason.depositDataRootMismatch.reason))).zipIdx,
    G⟩).withOutput (errorData (reasonString
      ReachableReason.depositDataRootMismatch.reason))
  have hcost := depositPostHashErrorGuardCost_eq
    (base := finalPost) .depositDataRootMismatch hstart
  refine ⟨post, ?_, rfl⟩
  simpa only [guardBase, post, hcost, Nat.add_assoc] using
    (depositRootGuard_failure_runCompiledTo
      (sevm := sevm) (base := finalPost) (G := G) hstart hrootFail)

/-- The model's eighth reachable error passes the reconstructed-root guard and
then selects the tree-capacity auxiliary.  The count bound states that the
model count is represented faithfully by its storage word. -/
theorem deposit_merkleTreeFull_error_endpoint_runCompiledTo
    {sevm : Sevm} {base : Devm} {state : Acc}
    {pubkey withdrawalCredentials signature : Bytes}
    {depositDataRoot : B256} {G : Nat}
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hcountBound : state.count < 2 ^ 256)
    (hdec : DepositAbiDecodable sevm.data pubkey withdrawalCredentials
      signature depositDataRoot)
    (hcountValue :
      base.getStorVal sevm.currentTarget depositCountSlot =
        Nat.toB256 state.count)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hstatic : sevm.isStatic = false)
    (hbound :
      (G + depositPostHashErrorGuardCost .merkleTreeFull + 46) + 1762 <
        2 ^ 256)
    (herror : deposit Bytes.sha256 state pubkey withdrawalCredentials
      signature depositDataRoot sevm.value.toNat =
        .error .merkle_tree_full) :
    DepositEndpointErrorWitness sevm base G .merkle_tree_full := by
  have hspec := deposit_error_spec Bytes.sha256 state pubkey
    withdrawalCredentials signature depositDataRoot sevm.value.toNat
    .merkleTreeFull herror
  obtain ⟨hpubkey, hwithdrawal, hsignature, hlowerNat, hgweiNat,
      hupperNat, hrootModel, hcapNat⟩ := hspec
  let amount := sevm.value / Nat.toB256 oneGwei
  let oldCount := Nat.toB256 state.count
  have hdenNe : Nat.toB256 oneGwei ≠ 0 := by
    intro hzero
    have natural := congrArg B256.toNat hzero
    rw [B256.toNat_toB256_of_lt (by norm_num [oneGwei]),
      B256.toNat_zero] at natural
    norm_num [oneGwei] at natural
  have hdenNat : (Nat.toB256 oneGwei).toNat = oneGwei :=
    B256.toNat_toB256_of_lt (by norm_num [oneGwei])
  have hamountNat : amount.toNat = sevm.value.toNat / oneGwei := by
    dsimp only [amount]
    rw [B256.toNat_div hdenNe, hdenNat]
  have hlowerWord : Nat.toB256 oneEther ≤ sevm.value := by
    rw [B256.le_iff_toNat_le_toNat,
      B256.toNat_toB256_of_lt (by norm_num [oneEther])]
    exact hlowerNat
  have hgweiWord : sevm.value % Nat.toB256 oneGwei = 0 := by
    apply B256.toNat_inj
    simpa only [B256.toNat_mod hdenNe, hdenNat, B256.toNat_zero] using
      hgweiNat
  have hupperWord : amount ≤ Nat.toB256 (2 ^ 64 - 1) := by
    rw [B256.le_iff_toNat_le_toNat, hamountNat,
      B256.toNat_toB256_of_lt (by omega)]
    exact hupperNat
  have hrootArg : Sevm.argWord sevm 3 = depositDataRoot := by
    unfold Sevm.argWord
    rw [show 32 * (3 : B256) + 4 = Nat.toB256 100 by decide +kernel,
      dataWord_toB256 (by omega), hdec.root_eq]
  have hrootPass : Sevm.argWord sevm 3 =
      depositDataNode Bytes.sha256 pubkey withdrawalCredentials signature
        (le64 amount.toNat) := by
    rw [hrootArg, hamountNat]
    exact hrootModel.symm
  have holdNat : oldCount.toNat = state.count := by
    dsimp only [oldCount]
    exact B256.toNat_toB256_of_lt hcountBound
  have hcapWord : ¬ oldCount < Nat.toB256 (2 ^ 32 - 1) := by
    intro hcap
    apply hcapNat
    rw [B256.lt_iff_toNat_lt_toNat, holdNat,
      B256.toNat_toB256_of_lt (by omega)] at hcap
    exact hcap
  apply depositPostHashError_endpoint_runCompiledTo
    (amount := amount) (oldCount := oldCount)
    (guardPrefixCost := 46) (error := .merkleTreeFull)
    hdataBound hdec hpubkey hwithdrawal hsignature rfl
    hlowerWord hgweiWord hupperWord
    (by simpa only [oldCount] using hcountValue)
    hnodeleg hwarm hpre hdepth hstatic hbound
  intro finalPost hstart
  let guardBase := finalPost.setMach ⟨[], finalPost.memory, 0⟩
  let post := (finalPost.setMach ⟨[],
    Mem.writeStoresRev finalPost.memory
      (bytesWords (errorData (reasonString
        ReachableReason.merkleTreeFull.reason))).zipIdx,
    G⟩).withOutput (errorData (reasonString
      ReachableReason.merkleTreeFull.reason))
  have hcost := depositPostHashErrorGuardCost_eq
    (base := finalPost) .merkleTreeFull hstart
  have hcapRun := depositCapGuard_failure_runCompiledTo
    (sevm := sevm) (base := finalPost) (G := G)
    (otherwise := commitDeposit) hstart hcapWord
  have hrootRun := depositRootGuard_runCompiledTo
    (fs := runtime.main :: runtime.aux) (sevm := sevm)
    (base := finalPost) hstart hrootPass hcapRun
  refine ⟨post, ?_, rfl⟩
  simpa only [depositSuccessGuards, guardBase, post, hcost,
      Nat.add_assoc] using hrootRun

end Blanc.BeaconDeposit
