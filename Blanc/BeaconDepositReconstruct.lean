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

/-- Machine-only changes preserve cumulative reconstruction metadata. -/
theorem ReconstructMetaCarrier.setMach
    {sevm : Sevm} {origin current : Devm}
    (h : ReconstructMetaCarrier sevm origin current) (mach : Mach) :
    ReconstructMetaCarrier sevm origin (current.setMach mach) :=
  ⟨h.storage, h.code, h.accessedAddresses, h.accessedStorageKeys,
    h.logs, h.output, h.error, h.state⟩

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

/-- Exact cost of pushing one word and storing it at a memory word. -/
def reconstructPushStoreCost (value targetWord : B256) : Nat :=
  pushCost value.toBytes.sig +
    pushCost ((targetWord * 32).toBytes.sig) + 3

/-- Execute one covered-memory `pushB256`/`mstoreAt` staging fragment. -/
theorem reconstructPushStore_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {value targetWord : B256}
    {stack : List B256} {K : Nat} {rest : Func} {ex : Execution}
    (hmod : memory.size % 32 = 0)
    (htargetFit : (targetWord * 32).toNat + 32 ≤ memory.size)
    (hroom : stack.length < 1023)
    (htail : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨stack,
          memory.write (targetWord * 32).toNat value.toBytes, K⟩)
      rest ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨stack, memory, K + reconstructPushStoreCost value targetWord⟩)
      (pushB256 value ::: mstoreAt targetWord +++ rest) ex := by
  let cvalue := pushCost value.toBytes.sig
  let ctarget := pushCost ((targetWord * 32).toBytes.sig)
  simp only [mstoreAt, prepend]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (w := value) (c := cvalue) (G := K + ctarget + 3)
      rfl
      (by
        simp only [Devm.gasLeft_setMach, reconstructPushStoreCost,
          cvalue, ctarget]
        omega)
      (by simp only [Devm.stack_setMach]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
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

@[simp] theorem reconstructPushStoreCost_zero_one :
    reconstructPushStoreCost 0 1 = 8 := by
  decide +kernel

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

@[simp] theorem reconstructLoadStoreCost_fifteen_zero :
    reconstructLoadStoreCost 15 0 = 11 := by
  decide +kernel

@[simp] theorem reconstructLoadStoreCost_nine_one :
    reconstructLoadStoreCost 9 1 = 12 := by
  decide +kernel

@[simp] theorem reconstructLoadStoreCost_eleven_zero :
    reconstructLoadStoreCost 11 0 = 11 := by
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

/-- Run the direct first-signature SHA-256 site, including the exact first
memory expansion, and establish the intermediate register. -/
theorem reconstructSignatureFirstSha_runCompiledTo
    {fs : List Func} {sevm : Sevm} {origin base : Devm}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount node : B256} {stack : List B256}
    {success : Func} {K : Nat}
    (hnode : ReconstructNodeMemoryCarrier base.memory pubkeyInput
      signatureFirst signatureTail withdrawal amountPadded oldCount amount
      node 704)
    (hmetaBase : ReconstructMetaCarrier sevm origin base)
    (hnodeleg : getDelegatedCodeAddress (origin.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ origin.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound : K + 225 < 2 ^ 256)
    (hroom : stack.length < 1019) :
    ∃ callPost,
      callPost.stack = 1 :: stack ∧
      callPost.memory =
        (base.memory.extends (reconstructionShaWindows 13 intermediateWord)).write
          704 (Bytes.sha256 signatureFirst).toBytes ∧
      Nonempty (ReconstructIntermediateMemoryCarrier callPost.memory
        pubkeyInput signatureFirst signatureTail withdrawal amountPadded
        oldCount amount node (Bytes.sha256 signatureFirst) 736) ∧
      callPost.gasLeft = K + 37 ∧
      callPost.returnData = (Bytes.sha256 signatureFirst).toBytes ∧
      ReconstructMetaCarrier sevm origin callPost ∧
      ∀ {ex : Execution},
        Func.RunCompiledTo fs sevm
          (callPost.setMach ⟨stack, callPost.memory, K⟩) success ex →
        Func.RunCompiledTo fs sevm
          (base.setMach ⟨stack, base.memory, K + 242⟩)
          (sha64 13 intermediateWord success) ex := by
  have hinput : ((13 : B256) * 32).toNat = 416 := by
    decide +kernel
  have houtput : (intermediateWord * 32).toNat = 704 := by
    decide +kernel
  have hext : base.extCost
      [⟨((13 : B256) * 32).toNat, 64⟩,
        ⟨(intermediateWord * 32).toNat, 32⟩] = 4 := by
    simp only [Devm.extCost, hinput, houtput, hnode.source.size_eq]
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
    sha64_success_prefix_runCompiledTo_ext
      (fs := fs) (sevm := sevm) (base := base)
      (inputWord := 13) (outputWord := intermediateWord)
      (stack := stack) (success := success) (K := K) (ext := 4)
      hext hnodelegBase hwarmBase hpre hdepth hbound hroom
  have hmemory' : callPost.memory =
      (base.memory.extends (reconstructionShaWindows 13 intermediateWord)).write
        704 (Bytes.sha256 signatureFirst).toBytes := by
    rw [hinput, houtput, hnode.source.shaSignatureFirstInput] at hmemory
    exact hmemory
  have hreturn' :
      callPost.returnData = (Bytes.sha256 signatureFirst).toBytes := by
    rw [hinput, hnode.source.shaSignatureFirstInput] at hreturn
    exact hreturn
  have hextended : ReconstructNodeMemoryCarrier
      (base.memory.extends (reconstructionShaWindows 13 intermediateWord))
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node 736 := by
    have h := hnode.extendForHash 13 intermediateWord
    have hsize : memExtsSize 704
        (reconstructionShaWindows 13 intermediateWord) = 736 := by
      decide +kernel
    rw [hsize] at h
    exact h
  have hcarrier : ReconstructIntermediateMemoryCarrier callPost.memory
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node (Bytes.sha256 signatureFirst) 736 := by
    rw [hmemory']
    exact hextended.writeIntermediate (Bytes.sha256 signatureFirst) (by omega)
  have hmeta : ReconstructMetaCarrier sevm origin callPost :=
    hmetaBase.afterHash hstorage hcode haddresses hkeys hlogs houtputMeta
      herror htransfer
  refine ⟨callPost, hstack, hmemory', ⟨hcarrier⟩, hgas, hreturn', hmeta, ?_⟩
  intro ex htail
  have hwhole := hlift htail
  simpa only [sha64SuccessCost_thirteen_intermediate] using hwhole

/-- The third SHA site's staged pair: the fixed-width signature tail followed
by one zero word. -/
def reconstructSignatureSecondStagedMemory
    (memory : Mem) (signatureTail : Bytes) : Mem :=
  (memory.write 0 (Bytes.toB256 signatureTail).toBytes).write
    32 (0 : B256).toBytes

/-- Digest produced by the third reconstruction SHA site. -/
def reconstructSignatureSecondDigest (signatureTail : Bytes) : B256 :=
  Bytes.sha256
    ((Bytes.toB256 signatureTail).toBytes ++ (0 : B256).toBytes)

/-- Stage the fixed-width signature tail and zero padding, run the exact second
memory expansion, and establish all three reconstruction registers. -/
theorem reconstructSignatureSecondSha_runCompiledTo
    {fs : List Func} {sevm : Sevm} {origin base : Devm}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount node intermediate : B256} {stack : List B256}
    {success : Func} {K : Nat}
    (hintermediate : ReconstructIntermediateMemoryCarrier base.memory
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node intermediate 736)
    (hmetaBase : ReconstructMetaCarrier sevm origin base)
    (hnodeleg : getDelegatedCodeAddress (origin.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ origin.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound : K + 224 < 2 ^ 256)
    (hroom : stack.length < 1019) :
    ∃ callPost,
      callPost.memory =
        ((reconstructSignatureSecondStagedMemory base.memory signatureTail).extends
          (reconstructionShaWindows 0 secondIntermediateWord)).write
          736 (reconstructSignatureSecondDigest signatureTail).toBytes ∧
      Nonempty (ReconstructRegistersMemoryCarrier callPost.memory
        pubkeyInput signatureFirst signatureTail withdrawal amountPadded
        oldCount amount node intermediate
        (reconstructSignatureSecondDigest signatureTail) 768) ∧
      callPost.returnData =
        (reconstructSignatureSecondDigest signatureTail).toBytes ∧
      ReconstructMetaCarrier sevm origin callPost ∧
      ∀ {ex : Execution},
        Func.RunCompiledTo fs sevm
          (callPost.setMach ⟨stack, callPost.memory, K⟩) success ex →
        Func.RunCompiledTo fs sevm
          (base.setMach ⟨stack, base.memory, K + 259⟩)
          (loadWord 15 +++ mstoreAt 0 +++
            pushB256 0 ::: mstoreAt 1 +++
            sha64 0 secondIntermediateWord success) ex := by
  let tailWord := Bytes.toB256 signatureTail
  let stagedMemory :=
    reconstructSignatureSecondStagedMemory base.memory signatureTail
  let shaBase := base.setMach ⟨stack, stagedMemory, K⟩
  have hpair : ReconstructIntermediatePairMemoryCarrier stagedMemory
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node intermediate tailWord 0 736 := by
    simpa only [stagedMemory, reconstructSignatureSecondStagedMemory,
      tailWord] using hintermediate.stagePair tailWord 0 (by omega)
  have hzero : ((0 : B256) * 32).toNat = 0 := by
    decide +kernel
  have houtput : (secondIntermediateWord * 32).toNat = 736 := by
    decide +kernel
  have hext : shaBase.extCost
      [⟨((0 : B256) * 32).toNat, 64⟩,
        ⟨(secondIntermediateWord * 32).toNat, 32⟩] = 3 := by
    simp only [shaBase, Devm.extCost, Devm.memory_setMach,
      hzero, houtput, hpair.intermediate.node.source.size_eq]
    decide +kernel
  have hmetaSha : ReconstructMetaCarrier sevm origin shaBase := by
    exact hmetaBase.setMach ⟨stack, stagedMemory, K⟩
  have hnodelegSha :
      getDelegatedCodeAddress (shaBase.getCode 2) = none := by
    rw [hmetaSha.code 2]
    exact hnodeleg
  have hwarmSha : (2 : Adr) ∈ shaBase.accessedAddresses := by
    rw [hmetaSha.accessedAddresses]
    exact hwarm
  obtain ⟨callPost, _hstack, hmemory, _hgas, hreturn,
      hstorage, hcode, haddresses, hkeys,
      hlogs, houtputMeta, herror, htransfer, hlift⟩ :=
    sha64_success_prefix_runCompiledTo_ext
      (fs := fs) (sevm := sevm) (base := shaBase)
      (inputWord := 0) (outputWord := secondIntermediateWord)
      (stack := stack) (success := success) (K := K) (ext := 3)
      hext hnodelegSha hwarmSha hpre hdepth hbound hroom
  have hmemory' : callPost.memory =
      (stagedMemory.extends
        (reconstructionShaWindows 0 secondIntermediateWord)).write
        736 (reconstructSignatureSecondDigest signatureTail).toBytes := by
    simp only [shaBase, Devm.memory_setMach] at hmemory
    rw [hzero, houtput, hpair.shaInput] at hmemory
    simpa only [reconstructionShaWindows, hzero, houtput,
      reconstructSignatureSecondDigest, tailWord] using hmemory
  have hreturn' : callPost.returnData =
      (reconstructSignatureSecondDigest signatureTail).toBytes := by
    simp only [shaBase, Devm.memory_setMach] at hreturn
    rw [hzero, hpair.shaInput] at hreturn
    simpa only [reconstructSignatureSecondDigest, tailWord] using hreturn
  have hextended : ReconstructIntermediateMemoryCarrier
      (stagedMemory.extends
        (reconstructionShaWindows 0 secondIntermediateWord))
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node intermediate 768 := by
    have h := hpair.intermediate.extendForHash 0 secondIntermediateWord
    have hsize : memExtsSize 736
        (reconstructionShaWindows 0 secondIntermediateWord) = 768 := by
      decide +kernel
    rw [hsize] at h
    exact h
  have hcarrier : ReconstructRegistersMemoryCarrier callPost.memory
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node intermediate
      (reconstructSignatureSecondDigest signatureTail) 768 := by
    rw [hmemory']
    exact hextended.writeSecond
      (reconstructSignatureSecondDigest signatureTail) (by omega)
  have hmeta : ReconstructMetaCarrier sevm origin callPost :=
    hmetaSha.afterHash hstorage hcode haddresses hkeys hlogs houtputMeta
      herror htransfer
  refine ⟨callPost, ?_, ⟨hcarrier⟩, hreturn', hmeta, ?_⟩
  · simpa only [stagedMemory] using hmemory'
  intro ex htail
  have hshaBase := hlift htail
  have hsha : Func.RunCompiledTo fs sevm
      (base.setMach ⟨stack, stagedMemory, K + 240⟩)
      (sha64 0 secondIntermediateWord success) ex := by
    simpa only [shaBase, Devm.setMach_setMach, Devm.memory_setMach,
      sha64SuccessCost_zero_secondIntermediate] using hshaBase
  let firstMemory :=
    base.memory.write 0 (Bytes.toB256 signatureTail).toBytes
  have hfirstCarrier : ReconstructIntermediateMemoryCarrier firstMemory
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node intermediate 736 := by
    simpa only [firstMemory] using
      hintermediate.writeBeforeSources 0
        (Bytes.toB256 signatureTail).toBytes
        (by rw [B256.length_toBytes]; omega)
        (by rw [B256.length_toBytes]; omega)
  have hzeroStage : Func.RunCompiledTo fs sevm
      (base.setMach ⟨stack, firstMemory, K + 248⟩)
      (pushB256 0 ::: mstoreAt 1 +++
        sha64 0 secondIntermediateWord success) ex := by
    have h := reconstructPushStore_runCompiledTo
      (base := base) (memory := firstMemory)
      (value := 0) (targetWord := 1) (stack := stack)
      (K := K + 240) (rest := sha64 0 secondIntermediateWord success)
      (by rw [hfirstCarrier.node.source.size_eq])
      (by rw [hfirstCarrier.node.source.size_eq]; decide +kernel)
      (by omega)
      (by
        simpa only [firstMemory, stagedMemory,
          reconstructSignatureSecondStagedMemory,
          show ((1 : B256) * 32).toNat = 32 by decide +kernel] using hsha)
    simpa only [reconstructPushStoreCost_zero_one] using h
  have hwhole := reconstructLoadStore_runCompiledTo
    (base := base) (memory := base.memory)
    (sourceWord := 15) (targetWord := 0)
    (value := Bytes.toB256 signatureTail) (stack := stack)
    (K := K + 248)
    (rest := pushB256 0 ::: mstoreAt 1 +++
      sha64 0 secondIntermediateWord success)
    (by rw [hintermediate.node.source.size_eq])
    (by rw [hintermediate.node.source.size_eq]; decide +kernel)
    (by rw [hintermediate.node.source.size_eq]; decide +kernel)
    hintermediate.node.source.readSignatureTail
    (by omega) hzeroStage
  simpa only [reconstructLoadStoreCost_fifteen_zero] using hwhole

/-- Two digest words staged in memory words `0` and `1`. -/
def reconstructPairStagedMemory
    (memory : Mem) (left right : B256) : Mem :=
  (memory.write 0 left.toBytes).write 32 right.toBytes

/-- Execute any covered steady-state staged-pair SHA site. -/
theorem reconstructPairSha_runCompiledTo
    {fs : List Func} {sevm : Sevm} {origin base : Devm}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount node intermediate second : B256}
    {leftWord rightWord outputWord left right : B256}
    {stack : List B256} {success : Func} {K : Nat}
    (hregisters : ReconstructRegistersMemoryCarrier base.memory
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node intermediate second 768)
    (hmetaBase : ReconstructMetaCarrier sevm origin base)
    (hnodeleg : getDelegatedCodeAddress (origin.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ origin.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound : K + 221 < 2 ^ 256)
    (hleftFit : (leftWord * 32).toNat + 32 ≤ 768)
    (hrightFit : (rightWord * 32).toNat + 32 ≤ 768)
    (houtputFit : (outputWord * 32).toNat + 32 ≤ 768)
    (hleftRead : Bytes.toB256
      (base.memory.read (leftWord * 32).toNat 32).1 = left)
    (hrightReadAfter : Bytes.toB256
      ((base.memory.write 0 left.toBytes).read
        (rightWord * 32).toNat 32).1 = right)
    (hroom : stack.length < 1019) :
    ∃ callPost,
      callPost.memory =
        (reconstructPairStagedMemory base.memory left right).write
          (outputWord * 32).toNat (hashPair Bytes.sha256 left right).toBytes ∧
      callPost.returnData = (hashPair Bytes.sha256 left right).toBytes ∧
      ReconstructMetaCarrier sevm origin callPost ∧
      ∀ {ex : Execution},
        Func.RunCompiledTo fs sevm
          (callPost.setMach ⟨stack, callPost.memory, K⟩) success ex →
        Func.RunCompiledTo fs sevm
          (base.setMach
            ⟨stack, base.memory,
              K + sha64SuccessCost 0 outputWord +
                reconstructLoadStoreCost rightWord 1 +
                reconstructLoadStoreCost leftWord 0⟩)
          (loadWord leftWord +++ mstoreAt 0 +++
            loadWord rightWord +++ mstoreAt 1 +++
            sha64 0 outputWord success) ex := by
  let stagedMemory := reconstructPairStagedMemory base.memory left right
  let shaBase := base.setMach ⟨stack, stagedMemory, K⟩
  have hpair : ReconstructPairMemoryCarrier stagedMemory
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node intermediate second left right 768 := by
    simpa only [stagedMemory, reconstructPairStagedMemory] using
      hregisters.stagePair left right (by omega)
  have hzero : ((0 : B256) * 32).toNat = 0 := by
    decide +kernel
  have hcovered : memExtsSize shaBase.memory.size
      [⟨((0 : B256) * 32).toNat, 64⟩,
        ⟨(outputWord * 32).toNat, 32⟩] = shaBase.memory.size := by
    have hinputCovered : memExtSize 768 0 64 = 768 :=
      memExtSize_of_le (by decide +kernel) (by decide +kernel)
    have houtputCovered :
        memExtSize 768 (outputWord * 32).toNat 32 = 768 :=
      memExtSize_of_le (by decide +kernel) houtputFit
    simp only [shaBase, Devm.memory_setMach, hzero,
      hpair.registers.intermediate.node.source.size_eq, memExtsSize]
    rw [hinputCovered, houtputCovered]
  have hmetaSha : ReconstructMetaCarrier sevm origin shaBase := by
    exact hmetaBase.setMach ⟨stack, stagedMemory, K⟩
  have hnodelegSha :
      getDelegatedCodeAddress (shaBase.getCode 2) = none := by
    rw [hmetaSha.code 2]
    exact hnodeleg
  have hwarmSha : (2 : Adr) ∈ shaBase.accessedAddresses := by
    rw [hmetaSha.accessedAddresses]
    exact hwarm
  obtain ⟨callPost, _hstack, hmemory, _hgas, hreturn,
      hstorage, hcode, haddresses, hkeys,
      hlogs, houtputMeta, herror, htransfer, hlift⟩ :=
    sha64_success_prefix_runCompiledTo
      (fs := fs) (sevm := sevm) (base := shaBase)
      (inputWord := 0) (outputWord := outputWord)
      (stack := stack) (success := success) (K := K)
      hcovered hnodelegSha hwarmSha hpre hdepth hbound hroom
  have hmemory' : callPost.memory = stagedMemory.write
      (outputWord * 32).toNat (hashPair Bytes.sha256 left right).toBytes := by
    simp only [shaBase, Devm.memory_setMach] at hmemory
    rw [hzero, hpair.shaInput] at hmemory
    simpa only [hashPair] using hmemory
  have hreturn' :
      callPost.returnData = (hashPair Bytes.sha256 left right).toBytes := by
    simp only [shaBase, Devm.memory_setMach] at hreturn
    rw [hzero, hpair.shaInput] at hreturn
    simpa only [hashPair] using hreturn
  have hmeta : ReconstructMetaCarrier sevm origin callPost :=
    hmetaSha.afterHash hstorage hcode haddresses hkeys hlogs houtputMeta
      herror htransfer
  refine ⟨callPost, ?_, hreturn', hmeta, ?_⟩
  · simpa only [stagedMemory] using hmemory'
  intro ex htail
  have hshaBase := hlift htail
  have hsha : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨stack, stagedMemory, K + sha64SuccessCost 0 outputWord⟩)
      (sha64 0 outputWord success) ex := by
    simpa only [shaBase, Devm.setMach_setMach, Devm.memory_setMach] using
      hshaBase
  let firstMemory := base.memory.write 0 left.toBytes
  have hfirstCarrier : ReconstructRegistersMemoryCarrier firstMemory
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node intermediate second 768 := by
    simpa only [firstMemory] using
      hregisters.writeBeforeSources 0 left.toBytes
        (by rw [B256.length_toBytes]; omega)
        (by rw [B256.length_toBytes]; omega)
  have hrightStage : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨stack, firstMemory,
          K + sha64SuccessCost 0 outputWord +
            reconstructLoadStoreCost rightWord 1⟩)
      (loadWord rightWord +++ mstoreAt 1 +++
        sha64 0 outputWord success) ex := by
    apply reconstructLoadStore_runCompiledTo
      (base := base) (memory := firstMemory)
      (sourceWord := rightWord) (targetWord := 1)
      (value := right) (stack := stack)
      (K := K + sha64SuccessCost 0 outputWord)
      (rest := sha64 0 outputWord success)
    · rw [hfirstCarrier.intermediate.node.source.size_eq]
    · rw [hfirstCarrier.intermediate.node.source.size_eq]
      exact hrightFit
    · rw [hfirstCarrier.intermediate.node.source.size_eq]
      decide +kernel
    · exact hrightReadAfter
    · omega
    · simpa only [firstMemory, stagedMemory, reconstructPairStagedMemory,
        show ((1 : B256) * 32).toNat = 32 by decide +kernel] using hsha
  exact reconstructLoadStore_runCompiledTo
    (base := base) (memory := base.memory)
    (sourceWord := leftWord) (targetWord := 0)
    (value := left) (stack := stack)
    (K := K + sha64SuccessCost 0 outputWord +
      reconstructLoadStoreCost rightWord 1)
    (rest := loadWord rightWord +++ mstoreAt 1 +++
      sha64 0 outputWord success)
    (by rw [hregisters.intermediate.node.source.size_eq])
    (by rw [hregisters.intermediate.node.source.size_eq]; exact hleftFit)
    (by rw [hregisters.intermediate.node.source.size_eq]; decide +kernel)
    hleftRead (by omega) hrightStage

/-- Combine the two signature-half digests into the signature root. -/
theorem reconstructSignatureRootSha_runCompiledTo
    {fs : List Func} {sevm : Sevm} {origin base : Devm}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount node intermediate second : B256}
    {stack : List B256} {success : Func} {K : Nat}
    (hregisters : ReconstructRegistersMemoryCarrier base.memory
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node intermediate second 768)
    (hmetaBase : ReconstructMetaCarrier sevm origin base)
    (hnodeleg : getDelegatedCodeAddress (origin.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ origin.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound : K + 221 < 2 ^ 256)
    (hroom : stack.length < 1019) :
    ∃ callPost,
      Nonempty (ReconstructRegistersMemoryCarrier callPost.memory
        pubkeyInput signatureFirst signatureTail withdrawal amountPadded
        oldCount amount node (hashPair Bytes.sha256 intermediate second)
        second 768) ∧
      callPost.returnData =
        (hashPair Bytes.sha256 intermediate second).toBytes ∧
      ReconstructMetaCarrier sevm origin callPost ∧
      ∀ {ex : Execution},
        Func.RunCompiledTo fs sevm
          (callPost.setMach ⟨stack, callPost.memory, K⟩) success ex →
        Func.RunCompiledTo fs sevm
          (base.setMach ⟨stack, base.memory, K + 260⟩)
          (loadWord intermediateWord +++ mstoreAt 0 +++
            loadWord secondIntermediateWord +++ mstoreAt 1 +++
            sha64 0 intermediateWord success) ex := by
  let firstMemory := base.memory.write 0 intermediate.toBytes
  have hfirstCarrier : ReconstructRegistersMemoryCarrier firstMemory
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node intermediate second 768 := by
    simpa only [firstMemory] using
      hregisters.writeBeforeSources 0 intermediate.toBytes
        (by rw [B256.length_toBytes]; omega)
        (by rw [B256.length_toBytes]; omega)
  obtain ⟨callPost, hmemory, hreturn, hmeta, hlift⟩ :=
    reconstructPairSha_runCompiledTo
      (fs := fs) (sevm := sevm) (origin := origin) (base := base)
      (hregisters := hregisters) (hmetaBase := hmetaBase)
      (leftWord := intermediateWord) (rightWord := secondIntermediateWord)
      (outputWord := intermediateWord) (left := intermediate) (right := second)
      (stack := stack) (success := success) (K := K)
      hnodeleg hwarm hpre hdepth hbound
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      hregisters.intermediate.readIntermediate hfirstCarrier.readSecond hroom
  have hpair := hregisters.stagePair intermediate second (by omega)
  have hcarrier : ReconstructRegistersMemoryCarrier callPost.memory
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node (hashPair Bytes.sha256 intermediate second)
      second 768 := by
    rw [hmemory]
    exact hpair.registers.writeIntermediate
      (hashPair Bytes.sha256 intermediate second) (by omega)
  refine ⟨callPost, ⟨hcarrier⟩, hreturn, hmeta, ?_⟩
  intro ex htail
  have hwhole := hlift htail
  simpa only [sha64SuccessCost_zero_intermediate,
    reconstructLoadStoreCost_second_one,
    reconstructLoadStoreCost_intermediate_zero] using hwhole

/-- Combine the pubkey root with the withdrawal-credentials word. -/
theorem reconstructPubkeyWithdrawalSha_runCompiledTo
    {fs : List Func} {sevm : Sevm} {origin base : Devm}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount node intermediate second : B256}
    {stack : List B256} {success : Func} {K : Nat}
    (hregisters : ReconstructRegistersMemoryCarrier base.memory
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node intermediate second 768)
    (hmetaBase : ReconstructMetaCarrier sevm origin base)
    (hnodeleg : getDelegatedCodeAddress (origin.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ origin.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound : K + 221 < 2 ^ 256)
    (hroom : stack.length < 1019) :
    ∃ callPost,
      Nonempty (ReconstructRegistersMemoryCarrier callPost.memory
        pubkeyInput signatureFirst signatureTail withdrawal amountPadded
        oldCount amount
        (hashPair Bytes.sha256 node (Bytes.toB256 withdrawal))
        intermediate second 768) ∧
      callPost.returnData =
        (hashPair Bytes.sha256 node (Bytes.toB256 withdrawal)).toBytes ∧
      ReconstructMetaCarrier sevm origin callPost ∧
      ∀ {ex : Execution},
        Func.RunCompiledTo fs sevm
          (callPost.setMach ⟨stack, callPost.memory, K⟩) success ex →
        Func.RunCompiledTo fs sevm
          (base.setMach ⟨stack, base.memory, K + 260⟩)
          (loadWord nodeWord +++ mstoreAt 0 +++
            loadWord 9 +++ mstoreAt 1 +++
            sha64 0 nodeWord success) ex := by
  let firstMemory := base.memory.write 0 node.toBytes
  have hfirstCarrier : ReconstructRegistersMemoryCarrier firstMemory
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node intermediate second 768 := by
    simpa only [firstMemory] using
      hregisters.writeBeforeSources 0 node.toBytes
        (by rw [B256.length_toBytes]; omega)
        (by rw [B256.length_toBytes]; omega)
  obtain ⟨callPost, hmemory, hreturn, hmeta, hlift⟩ :=
    reconstructPairSha_runCompiledTo
      (fs := fs) (sevm := sevm) (origin := origin) (base := base)
      (hregisters := hregisters) (hmetaBase := hmetaBase)
      (leftWord := nodeWord) (rightWord := 9)
      (outputWord := nodeWord) (left := node)
      (right := Bytes.toB256 withdrawal)
      (stack := stack) (success := success) (K := K)
      hnodeleg hwarm hpre hdepth hbound
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      hregisters.intermediate.node.readNode
      hfirstCarrier.intermediate.node.source.readWithdrawal hroom
  have hpair := hregisters.stagePair node (Bytes.toB256 withdrawal) (by omega)
  have hcarrier : ReconstructRegistersMemoryCarrier callPost.memory
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount (hashPair Bytes.sha256 node (Bytes.toB256 withdrawal))
      intermediate second 768 := by
    rw [hmemory]
    exact hpair.registers.writeNode
      (hashPair Bytes.sha256 node (Bytes.toB256 withdrawal)) (by omega)
  refine ⟨callPost, ⟨hcarrier⟩, hreturn, hmeta, ?_⟩
  intro ex htail
  have hwhole := hlift htail
  simpa only [sha64SuccessCost_zero_node,
    reconstructLoadStoreCost_nine_one,
    reconstructLoadStoreCost_node_zero] using hwhole

end Blanc.BeaconDeposit
