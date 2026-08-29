import Blanc.BeaconDepositReconstructMemory

/-!
# Beacon deposit reconstruction compiled carriers

The seven-hash deposit-data reconstruction alternates direct SHA-256 windows
with pairs staged in memory words `0` and `1`.  This module first isolates the
exact-cost `MLOAD`/`MSTORE` fragment used by every staged word.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Ninst

/-- The real sequence of zero-value state transfers made by successive
successful SHA-256 precompile calls. -/
inductive ReconstructZeroTransferChain (sevm : Sevm) :
    State -> State -> Prop where
  | refl (state : State) : ReconstructZeroTransferChain sevm state state
  | step {origin before stmid after : State}
      (previous : ReconstructZeroTransferChain sevm origin before)
      (sub : before.subBal sevm.currentTarget 0 = some stmid)
      (add : after = stmid.addBal 2 0) :
      ReconstructZeroTransferChain sevm origin after

/-- Cumulative non-machine state preserved across reconstruction hashes.

`returnData` is intentionally absent: every successful precompile call replaces
it with the current digest.  The world-state field records the exact transfer
chain instead of asserting a stronger state equality than Jaune exposes.
-/
structure ReconstructMetaCarrier
    (sevm : Sevm) (origin current : Devm) : Prop where
  storage : forall a, Devm.getStor current a = Devm.getStor origin a
  code : forall a, current.getCode a = origin.getCode a
  accessedAddresses :
    current.accessedAddresses = origin.accessedAddresses
  accessedStorageKeys :
    current.accessedStorageKeys = origin.accessedStorageKeys
  logs : current.logs = origin.logs
  output : current.output = origin.output
  error : current.error = origin.error
  state : ReconstructZeroTransferChain sevm origin.state current.state

/-- Initial cumulative metadata carrier. -/
theorem ReconstructMetaCarrier.refl (sevm : Sevm) (base : Devm) :
    ReconstructMetaCarrier sevm base base :=
  ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl,
    ReconstructZeroTransferChain.refl base.state⟩

/-- Extend cumulative metadata by one successful SHA-256 call. -/
theorem ReconstructMetaCarrier.afterHash
    {sevm : Sevm} {origin base post : Devm}
    (h : ReconstructMetaCarrier sevm origin base)
    (hstorage : forall a, Devm.getStor post a = Devm.getStor base a)
    (hcode : forall a, post.getCode a = base.getCode a)
    (haddresses : post.accessedAddresses = base.accessedAddresses)
    (hkeys : post.accessedStorageKeys = base.accessedStorageKeys)
    (hlogs : post.logs = base.logs)
    (houtput : post.output = base.output)
    (herror : post.error = base.error)
    (htransfer : exists stmid,
      base.state.subBal sevm.currentTarget 0 = some stmid /\
      post.state = stmid.addBal 2 0) :
    ReconstructMetaCarrier sevm origin post := by
  obtain ⟨stmid, hsub, hstate⟩ := htransfer
  refine ⟨fun a => (hstorage a).trans (h.storage a),
    fun a => (hcode a).trans (h.code a),
    haddresses.trans h.accessedAddresses,
    hkeys.trans h.accessedStorageKeys,
    hlogs.trans h.logs, houtput.trans h.output, herror.trans h.error, ?_⟩
  exact ReconstructZeroTransferChain.step h.state hsub hstate

/-- Exact cost of loading one memory word and storing it at another word. -/
def reconstructLoadStoreCost (sourceWord targetWord : B256) : Nat :=
  pushCost ((sourceWord * 32).toBytes.sig) + 3 +
    pushCost ((targetWord * 32).toBytes.sig) + 3

/-- Execute one covered-memory `loadWord`/`mstoreAt` staging fragment. -/
theorem reconstructLoadStore_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {sourceWord targetWord value : B256}
    {stack : List B256} {K : Nat} {rest : Func} {ex : Execution}
    (hmod : memory.size % 32 = 0)
    (hsourceFit : (sourceWord * 32).toNat + 32 <= memory.size)
    (htargetFit : (targetWord * 32).toNat + 32 <= memory.size)
    (hread : Bytes.toB256
      (memory.read (sourceWord * 32).toNat 32).1 = value)
    (hroom : stack.length < 1023)
    (htail : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨stack,
          memory.write (targetWord * 32).toNat value.toBytes, K⟩)
      rest ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨stack, memory,
          K + reconstructLoadStoreCost sourceWord targetWord⟩)
      (loadWord sourceWord +++ mstoreAt targetWord +++ rest) ex := by
  let csource := pushCost ((sourceWord * 32).toBytes.sig)
  let ctarget := pushCost ((targetWord * 32).toBytes.sig)
  have hreadMemory :
      (memory.read (sourceWord * 32).toNat 32).2 = memory := by
    apply Mem.read_snd_eq_self
    exact memExtSize_of_le hmod hsourceFit
  simp only [loadWord, mstoreAt, prepend]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (w := sourceWord * 32) (c := csource)
      (G := K + 3 + ctarget + 3)
      rfl
      (by
        simp only [Devm.gasLeft_setMach, reconstructLoadStoreCost,
          csource, ctarget]
        omega)
      (by simp only [Devm.stack_setMach]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_mload_of
      (i := sourceWord * 32) (v := value) (s := stack)
      (c := 3) (G := K + ctarget + 3) (M := memory)
      rfl
      (by
        have hext :
            (base.setMach
              ⟨(sourceWord * 32) :: stack, memory,
                K + 3 + ctarget + 3⟩).extCost
              [⟨(sourceWord * 32).toNat, 32⟩] = 0 :=
          Devm.extCost_zero_of_le hmod hsourceFit
        rw [hext]
        decide)
      hread hreadMemory
      (by
        simp only [Devm.gasLeft_setMach]
        omega)
      (by omega)) ?_
  simp only [Devm.setMach_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (w := targetWord * 32) (c := ctarget) (G := K + 3)
      rfl
      (by
        simp only [Devm.gasLeft_setMach]
        omega)
      (by
        simp only [Devm.stack_setMach, List.length_cons]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_mstore_of
      (i := targetWord * 32) (v := value) (s := stack)
      (G := K) (e := 0)
      rfl
      (Devm.extCost_zero_of_le hmod htargetFit)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      rfl) ?_
  simpa only [Devm.setMach_setMach, Devm.memory_setMach] using htail

@[simp] theorem reconstructLoadStoreCost_node_zero :
    reconstructLoadStoreCost nodeWord 0 = 11 := by
  decide +kernel

@[simp] theorem reconstructLoadStoreCost_intermediate_zero :
    reconstructLoadStoreCost intermediateWord 0 = 11 := by
  decide +kernel

@[simp] theorem reconstructLoadStoreCost_intermediate_one :
    reconstructLoadStoreCost intermediateWord 1 = 12 := by
  decide +kernel

@[simp] theorem reconstructLoadStoreCost_second_one :
    reconstructLoadStoreCost secondIntermediateWord 1 = 12 := by
  decide +kernel

/-- Run the direct pubkey SHA-256 site and establish the node register. -/
theorem reconstructPubkeySha_runCompiledTo
    {fs : List Func} {sevm : Sevm} {origin base : Devm}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount : B256} {stack : List B256}
    {success : Func} {K : Nat}
    (source : ReconstructSourceMemoryCarrier base.memory pubkeyInput
      signatureFirst signatureTail withdrawal amountPadded oldCount amount 704)
    (hmetaBase : ReconstructMetaCarrier sevm origin base)
    (hnodeleg : getDelegatedCodeAddress (origin.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ origin.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound : K + 221 < 2 ^ 256)
    (hroom : stack.length < 1019) :
    ∃ callPost,
      callPost.stack = 1 :: stack ∧
      callPost.memory = base.memory.write 640
        (Bytes.sha256 pubkeyInput).toBytes ∧
      Nonempty (ReconstructNodeMemoryCarrier callPost.memory pubkeyInput
        signatureFirst signatureTail withdrawal amountPadded oldCount amount
        (Bytes.sha256 pubkeyInput) 704) ∧
      callPost.gasLeft = K + 37 ∧
      callPost.returnData = (Bytes.sha256 pubkeyInput).toBytes ∧
      ReconstructMetaCarrier sevm origin callPost ∧
      ∀ {ex : Execution},
        Func.RunCompiledTo fs sevm
          (callPost.setMach ⟨stack, callPost.memory, K⟩) success ex →
        Func.RunCompiledTo fs sevm
          (base.setMach ⟨stack, base.memory, K + 238⟩)
          (sha64 6 nodeWord success) ex := by
  have hinput : ((6 : B256) * 32).toNat = 192 := by
    decide +kernel
  have houtput : (nodeWord * 32).toNat = 640 := by
    decide +kernel
  have hcovered : memExtsSize base.memory.size
      [⟨((6 : B256) * 32).toNat, 64⟩,
        ⟨(nodeWord * 32).toNat, 32⟩] = base.memory.size := by
    rw [hinput, houtput, source.size_eq]
    decide +kernel
  have hnodelegBase :
      getDelegatedCodeAddress (base.getCode 2) = none := by
    rw [hmetaBase.code 2]
    exact hnodeleg
  have hwarmBase : (2 : Adr) ∈ base.accessedAddresses := by
    rw [hmetaBase.accessedAddresses]
    exact hwarm
  obtain ⟨callPost, hstack, hmemory, hgas, hreturn,
      hstorage, hcode, haddresses, hkeys,
      hlogs, houtputMeta, herror, htransfer, hlift⟩ :=
    sha64_success_prefix_runCompiledTo
      (fs := fs) (sevm := sevm) (base := base)
      (inputWord := 6) (outputWord := nodeWord)
      (stack := stack) (success := success) (K := K)
      hcovered hnodelegBase hwarmBase hpre hdepth hbound hroom
  have hmemory' : callPost.memory = base.memory.write 640
      (Bytes.sha256 pubkeyInput).toBytes := by
    rw [hinput, houtput, source.shaPubkeyInput] at hmemory
    exact hmemory
  have hreturn' :
      callPost.returnData = (Bytes.sha256 pubkeyInput).toBytes := by
    rw [hinput, source.shaPubkeyInput] at hreturn
    exact hreturn
  have hcarrier : ReconstructNodeMemoryCarrier callPost.memory pubkeyInput
      signatureFirst signatureTail withdrawal amountPadded oldCount amount
      (Bytes.sha256 pubkeyInput) 704 := by
    rw [hmemory']
    exact source.writeNode (Bytes.sha256 pubkeyInput) (by omega)
  have hmeta : ReconstructMetaCarrier sevm origin callPost :=
    hmetaBase.afterHash hstorage hcode haddresses hkeys hlogs houtputMeta herror
      htransfer
  refine ⟨callPost, hstack, hmemory', ⟨hcarrier⟩, hgas, hreturn', hmeta, ?_⟩
  intro ex htail
  have hwhole := hlift htail
  simpa only [sha64SuccessCost_six_node] using hwhole

end Blanc.BeaconDeposit
