import Blanc.BeaconDepositBridge
import Blanc.BeaconDepositDeploy
import Blanc.BeaconDepositWriteSites
import Blanc.BytesWrite
import Blanc.ForwardStorageEffects
import Blanc.ForwardSha256
import Blanc.ForwardStorageAccess
import Blanc.WordArithmetic

/-!
# Beacon deposit constructor storage effects

Exact selected-path carriers for the creation-code loop that materializes the
thirty-one nonzero zero-hash slots.  The constructor uses fixed-width `PUSH2`
instructions, so its SHA wrapper is proved against that exact source rather
than identified with the runtime's compact-push wrapper.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Blanc.Ninst

/-- Exact successful cost of the fixed-width constructor SHA wrapper before
memory expansion: five `PUSH2`s cost 15 gas and the shared successful suffix
costs 223 gas. -/
def constructorSha64SuccessCost : Nat := 238

/-- Exact-effect wrapper for the constructor's fixed-width push.  The generic
walk tactic intentionally knows only the shared instruction vocabulary, so the
constructor-local encoding gets one equally local neutral-step bridge. -/
theorem Func.StorageEffectRun.next_constructorPushWord
    {fs : List Func} {sevm : Sevm} {devm : Devm}
    {word : B256} {body : Func} {out : Execution}
    {effects : List (Adr × B256 × B256)} {G : Nat}
    (gas : devm.gasLeft = G + gVerylow)
    (room : devm.stack.length < 1024)
    (tail : Func.StorageEffectRun fs sevm
      (devm.setMach ⟨word :: devm.stack, devm.memory, G⟩)
      body out effects) :
    Func.StorageEffectRun fs sevm devm
      (.next (constructorPushWord word) body) out effects := by
  exact Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_constructorPushWord (word := word) gas room)
    (by
      simp only [constructorPushWord]
      split <;> intro impossible <;> cases impossible)
    (by
      intro operation
      simp only [constructorPushWord]
      split <;> intro impossible <;> cases impossible) tail

/-- Scratch memory at a constructor loop head.  The logical image is exposed
so read-over-write facts can describe the exact two-word SHA input without
depending on `Mem`'s backing-array representation. -/
structure ConstructorLoopMemory (memory : Mem) (height : Nat) where
  image : Bytes
  wf : Mem.Wf memory
  reads : Mem.Reads memory image
  size_eq : memory.size = 96
  nodeWindow : image.sliceD 64 32 0 =
    (zeroHash Bytes.sha256 height).toBytes

/-- Scratch memory produced by the constructor's initialization prefix. -/
def constructorInitialMemory : Mem :=
  Mem.empty.write 64 (0 : B256).toBytes

def constructorInitialMemory_carrier :
    ConstructorLoopMemory constructorInitialMemory 0 := by
  let image := Bytes.writeAt [] 64 (0 : B256).toBytes
  refine ⟨image, Mem.wf_empty.write 64 _,
    Mem.reads_empty.write Mem.wf_empty 64 _, ?_, ?_⟩
  · unfold constructorInitialMemory
    rw [Mem.size_write_word_at]
    decide +kernel
  · dsimp only [image]
    change (Bytes.writeAt [] 64 (0 : B256).toBytes).sliceD
      64 32 0 = (0 : B256).toBytes
    rw [show (32 : Nat) = (0 : B256).toBytes.length by
      rw [B256.length_toBytes], Bytes.sliceD_writeAt]

/-- Scratch image after copying the current node into the two SHA input words. -/
def constructorPairMemory (memory : Mem) (node : B256) : Mem :=
  (memory.write 0 node.toBytes).write 32 node.toBytes

/-- A word written wholly below the node scratch word preserves the loop-head
memory carrier. -/
def ConstructorLoopMemory.writeBelowNode
    {memory : Mem} {height : Nat}
    (carrier : ConstructorLoopMemory memory height)
    (offset : Nat) (value : B256) (below : offset + 32 ≤ 64) :
    ConstructorLoopMemory (memory.write offset value.toBytes) height := by
  refine ⟨Bytes.writeAt carrier.image offset value.toBytes,
    carrier.wf.write offset value.toBytes,
    carrier.reads.write carrier.wf offset value.toBytes, ?_, ?_⟩
  · rw [Mem.size_write_of_le (by
      rw [B256.length_toBytes, carrier.size_eq]
      omega), carrier.size_eq]
  · rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]
      exact below)]
    exact carrier.nodeWindow

theorem ConstructorLoopMemory.readNode
    {memory : Mem} {height : Nat}
    (carrier : ConstructorLoopMemory memory height) :
    Bytes.toB256 (memory.read 64 32).1 =
      zeroHash Bytes.sha256 height := by
  rw [carrier.reads.read, carrier.nodeWindow, B256.toB256_toBytes]

theorem ConstructorLoopMemory.pairSize
    {memory : Mem} {height : Nat}
    (carrier : ConstructorLoopMemory memory height) :
    (constructorPairMemory memory
      (zeroHash Bytes.sha256 height)).size = 96 := by
  unfold constructorPairMemory
  rw [Mem.size_write_word_at, Mem.size_write_word_at, carrier.size_eq]
  decide +kernel

theorem ConstructorLoopMemory.pairInput
    {memory : Mem} {height : Nat}
    (carrier : ConstructorLoopMemory memory height) :
    (constructorPairMemory memory
        (zeroHash Bytes.sha256 height)).data.sliceD 0 64 0 =
      (zeroHash Bytes.sha256 height).toBytes ++
        (zeroHash Bytes.sha256 height).toBytes := by
  let node := zeroHash Bytes.sha256 height
  have wf0 := carrier.wf.write 0 node.toBytes
  have reads0 := carrier.reads.write carrier.wf 0 node.toBytes
  have reads1 := reads0.write wf0 32 node.toBytes
  have hread := reads1.read 0 64
  simpa only [constructorPairMemory, node, Mem.read] using
    hread.trans (Bytes.sliceD_stagedPair carrier.image node node)

theorem ConstructorLoopMemory.pairWf
    {memory : Mem} {height : Nat}
    (carrier : ConstructorLoopMemory memory height) :
    Mem.Wf (constructorPairMemory memory
      (zeroHash Bytes.sha256 height)) := by
  exact (carrier.wf.write 0 _).write 32 _

theorem ConstructorLoopMemory.pairReads
    {memory : Mem} {height : Nat}
    (carrier : ConstructorLoopMemory memory height) :
    Mem.Reads
      (constructorPairMemory memory (zeroHash Bytes.sha256 height))
      (Bytes.writeAt
        (Bytes.writeAt carrier.image 0
          (zeroHash Bytes.sha256 height).toBytes)
        32 (zeroHash Bytes.sha256 height).toBytes) := by
  exact (carrier.reads.write carrier.wf 0 _).write
    (carrier.wf.write 0 _) 32 _

/-- The successful SHA write advances the scratch-memory carrier by one model
zero-hash height. -/
def ConstructorLoopMemory.afterSha
    {memory : Mem} {height : Nat} {postMemory : Mem}
    (carrier : ConstructorLoopMemory memory height)
    (hmemory : postMemory =
      (constructorPairMemory memory (zeroHash Bytes.sha256 height)).write
        64
        (Bytes.sha256
          ((constructorPairMemory memory
            (zeroHash Bytes.sha256 height)).data.sliceD 0 64 0)).toBytes) :
    ConstructorLoopMemory postMemory (height + 1) := by
  let node := zeroHash Bytes.sha256 height
  let pair := constructorPairMemory memory node
  let digest := Bytes.sha256 (pair.data.sliceD 0 64 0)
  have pairWf : Mem.Wf pair := by
    simpa only [pair, node] using carrier.pairWf
  have pairReads : Mem.Reads pair
      (Bytes.writeAt (Bytes.writeAt carrier.image 0 node.toBytes)
        32 node.toBytes) := by
    simpa only [pair, node] using carrier.pairReads
  have digestEq : digest = zeroHash Bytes.sha256 (height + 1) := by
    dsimp only [digest, pair, node]
    rw [carrier.pairInput]
    rfl
  rw [hmemory]
  refine ⟨Bytes.writeAt
      (Bytes.writeAt (Bytes.writeAt carrier.image 0 node.toBytes)
        32 node.toBytes) 64 digest.toBytes,
    pairWf.write 64 digest.toBytes,
    pairReads.write pairWf 64 digest.toBytes, ?_, ?_⟩
  · rw [Mem.size_write_word_at, carrier.pairSize]
    decide +kernel
  · rw [show (32 : Nat) = digest.toBytes.length by
      rw [B256.length_toBytes], Bytes.sliceD_writeAt]
    exact congrArg B256.toBytes digestEq

/-- World facts needed at every constructor loop head.  The zero-value SHA
precompile call and each SSTORE preserve these facts while the target storage
advances by exactly one model height. -/
structure ConstructorLoopWorld
    (sevm : Sevm) (base : Devm) (height : Nat) : Prop where
  storage : Devm.getStor base sevm.currentTarget =
    constructorZeroHashStorage height
  shaCode : getDelegatedCodeAddress (base.getCode 2) = none
  shaWarm : (2 : Adr) ∈ base.accessedAddresses
  error : base.error = none

/-- Transfer the loop-world carrier through the storage-neutral SHA result and
the selected write of the newly computed zero hash. -/
theorem ConstructorLoopWorld.afterShaWrite
    {sevm : Sevm} {base shaPost : Devm} {height : Nat}
    (world : ConstructorLoopWorld sevm base height)
    (hstorage : ∀ address,
      Devm.getStor shaPost address = Devm.getStor base address)
    (hcode : ∀ address, shaPost.getCode address = base.getCode address)
    (haddresses : shaPost.accessedAddresses = base.accessedAddresses)
    (herror : shaPost.error = base.error) :
    ConstructorLoopWorld sevm
      (afterSstore sevm shaPost (zeroHashSlot (height + 1))
        (zeroHash Bytes.sha256 (height + 1))) (height + 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [afterSstore_getStor_self, hstorage, world.storage]
    rfl
  · rw [afterSstore_getCode, hcode]
    exact world.shaCode
  · rw [afterSstore_accessedAddresses, haddresses]
    exact world.shaWarm
  · rw [afterSstore_error, herror, world.error]

/-- The four constructor memory operations stage the current node twice as the
exact 64-byte SHA input without changing the loop-height stack word. -/
private theorem constructorPairStage_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {height : Nat} {heightWord : B256}
    {stack : List B256} {K : Nat} {rest : Func} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (carrier : ConstructorLoopMemory memory height)
    (hroom : stack.length < 1022)
    (tail : Func.StorageEffectRun fs sevm
      (base.setMach
        ⟨heightWord :: stack,
          constructorPairMemory memory (zeroHash Bytes.sha256 height), K⟩)
      rest ex effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach ⟨heightWord :: stack, memory, K + 24⟩)
      ((constructorLoadWord constructorNodeWord ++ constructorStoreWord 0 ++
        constructorLoadWord constructorNodeWord ++ constructorStoreWord 1) +++
        rest) ex effects := by
  let node := zeroHash Bytes.sha256 height
  let M0 := memory.write 0 node.toBytes
  have carrier0 : ConstructorLoopMemory M0 height := by
    dsimp only [M0, node]
    exact carrier.writeBelowNode 0 _ (by omega)
  have hmod : memory.size % 32 = 0 := by
    rw [carrier.size_eq]
  have hmod0 : M0.size % 32 = 0 := by
    rw [carrier0.size_eq]
  have hread0 : Bytes.toB256 (memory.read 64 32).1 = node := by
    simpa only [node] using carrier.readNode
  have hreadMem0 : (memory.read 64 32).2 = memory := by
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le hmod
    rw [carrier.size_eq]
  have hread1 : Bytes.toB256 (M0.read 64 32).1 = node := by
    simpa only [node] using carrier0.readNode
  have hreadMem1 : (M0.read 64 32).2 = M0 := by
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le hmod0
    rw [carrier0.size_eq]
  simp only [constructorLoadWord, constructorStoreWord, constructorNodeWord,
    show ((2 : B256) * 32) = 64 by decide +kernel,
    show ((0 : B256) * 32) = 0 by decide +kernel,
    show ((1 : B256) * 32) = 32 by decide +kernel]
  refine Func.StorageEffectRun.next_constructorPushWord
    (G := K + 21) ?_ ?_ ?_
  · simp only [Devm.gasLeft_setMach, gVerylow]
  · simp only [Devm.stack_setMach, List.length_cons]
    omega
  · simp only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach]
    have hmload0 :=
      (Ninst.runCompiled_mload_of
        (sevm := sevm)
        (devm := base.setMach
          ⟨64 :: heightWord :: stack, memory, K + 21⟩)
        (i := 64) (v := node) (s := heightWord :: stack)
        (c := 3) (G := K + 18) (M := memory) rfl
        (by
          rw [Devm.extCost_zero_of_le hmod (by
            rw [carrier.size_eq]
            decide +kernel)]
          decide)
        hread0 hreadMem0
        (by simp only [Devm.gasLeft_setMach])
        (by simp only [List.length_cons]; omega))
    apply Func.StorageEffectRun.next_effectNeutral hmload0
      (by rintro impossible; cases impossible)
      (by intro operation impossible; cases impossible)
    simp only [Devm.setMach_setMach]
    refine Func.StorageEffectRun.next_constructorPushWord
      (G := K + 15) ?_ ?_ ?_
    · simp only [Devm.gasLeft_setMach, gVerylow]
    · simp only [Devm.stack_setMach, List.length_cons]
      omega
    · simp only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach]
      apply Func.StorageEffectRun.next_effectNeutral
        (Ninst.runCompiled_mstore_of
          (i := 0) (v := node) (s := heightWord :: stack)
          (G := K + 12) (e := 0) rfl
          (Devm.extCost_zero_of_le hmod (by
            rw [carrier.size_eq]
            decide +kernel))
          (by simp only [Devm.gasLeft_setMach, gVerylow]) rfl)
        (by rintro impossible; cases impossible)
        (by intro operation impossible; cases impossible)
      simp only [Devm.setMach_setMach,
        show (0 : B256).toNat = 0 by decide +kernel]
      change Func.StorageEffectRun fs sevm
        (base.setMach ⟨heightWord :: stack, M0, K + 12⟩) _ ex effects
      refine Func.StorageEffectRun.next_constructorPushWord
        (G := K + 9) ?_ ?_ ?_
      · simp only [Devm.gasLeft_setMach, gVerylow]
      · simp only [Devm.stack_setMach, List.length_cons]
        omega
      · simp only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach]
        have hmload1 :=
          (Ninst.runCompiled_mload_of
            (sevm := sevm)
            (devm := base.setMach
              ⟨64 :: heightWord :: stack, M0, K + 9⟩)
            (i := 64) (v := node) (s := heightWord :: stack)
            (c := 3) (G := K + 6) (M := M0) rfl
            (by
              rw [Devm.extCost_zero_of_le hmod0 (by
                rw [carrier0.size_eq]
                decide +kernel)]
              decide)
            hread1 hreadMem1
            (by simp only [Devm.gasLeft_setMach])
            (by simp only [List.length_cons]; omega))
        apply Func.StorageEffectRun.next_effectNeutral hmload1
          (by rintro impossible; cases impossible)
          (by intro operation impossible; cases impossible)
        simp only [Devm.setMach_setMach]
        refine Func.StorageEffectRun.next_constructorPushWord
          (G := K + 3) ?_ ?_ ?_
        · simp only [Devm.gasLeft_setMach, gVerylow]
        · simp only [Devm.stack_setMach, List.length_cons]
          omega
        · simp only [Devm.setMach_setMach, Devm.stack_setMach,
            Devm.memory_setMach]
          apply Func.StorageEffectRun.next_effectNeutral
            (Ninst.runCompiled_mstore_of
              (i := 32) (v := node) (s := heightWord :: stack)
              (G := K) (e := 0) rfl
              (Devm.extCost_zero_of_le hmod0 (by
                rw [carrier0.size_eq]
                decide +kernel))
              (by simp only [Devm.gasLeft_setMach, gVerylow]) rfl)
            (by rintro impossible; cases impossible)
            (by intro operation impossible; cases impossible)
          simpa only [Devm.setMach_setMach, Devm.memory_setMach,
            M0, node, constructorPairMemory, prepend,
            show (32 : B256).toNat = 32 by decide +kernel] using tail

/-- Select the live constructor loop arm at any model height below thirty-one. -/
private theorem constructorZeroHashLoop_succ_dispatch_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {height runtimeOffset runtimeLength : Nat}
    {K : Nat} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (hheight : height < 31)
    (tail : Func.StorageEffectRun fs sevm
      (base.setMach ⟨[Nat.toB256 height], memory, K⟩)
      ((constructorLoadWord constructorNodeWord ++ constructorStoreWord 0 ++
        constructorLoadWord constructorNodeWord ++ constructorStoreWord 1) +++
        constructorSha64 0 constructorNodeWord
          (.call constructorZeroHashContinuationSlot)) ex effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach ⟨[Nat.toB256 height], memory, K + 26⟩)
      (constructorZeroHashLoop runtimeOffset runtimeLength) ex effects := by
  simp only [constructorZeroHashLoop]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_dup (n := 0) (w := Nat.toB256 height)
      (G := K + 23) rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega))
    (by rintro impossible; cases impossible)
    (by intro operation impossible; cases impossible)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.StorageEffectRun.next_constructorPushWord
    (G := K + 20) ?_ ?_ ?_
  · simp only [Devm.gasLeft_setMach, gVerylow]
  · simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
    omega
  · simp only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach]
    apply Func.StorageEffectRun.next_effectNeutral
      (Ninst.runCompiled_swap (n := 0)
        (S := Nat.toB256 height :: (31 : B256) ::
          Nat.toB256 height :: [])
        (G := K + 17) rfl
        (by simp only [Devm.gasLeft_setMach, gVerylow]))
      (by rintro impossible; cases impossible)
      (by intro operation impossible; cases impossible)
    simp only [Devm.setMach_setMach, Devm.memory_setMach]
    apply Func.StorageEffectRun.next_effectNeutral
      (Ninst.runCompiled_binary (r := .lt) (f := B256.ltCheck)
        (cost := gVerylow) (x := Nat.toB256 height) (y := 31)
        (v := 1) (s := [Nat.toB256 height]) (G := K + 14)
        (by rintro impossible; cases impossible) rfl rfl
        (by
          simp only [B256.ltCheck]
          rw [if_pos]
          rw [B256.lt_iff_toNat_lt_toNat,
            B256.toNat_toB256_of_lt (by omega : height < 2 ^ 256)]
          rw [show ((31 : B256).toNat) = 31 by decide +kernel]
          exact hheight)
        (by simp only [Devm.gasLeft_setMach, gVerylow])
        (by simp only [List.length_cons, List.length_nil]; omega))
      (by rintro impossible; cases impossible)
      (by intro operation impossible; cases impossible)
    simp only [Devm.setMach_setMach]
    apply Func.storageEffectRun_branch_succ
      (w := (1 : B256)) (s := [Nat.toB256 height]) (G := K)
      (by decide) rfl
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega)
      (by simp only [Devm.gasLeft_setMach, gVerylow, gHigh, gJumpdest])
    simpa only [Devm.setMach_setMach, Devm.memory_setMach] using tail

private theorem constructorZeroHashBase_add_toB256
    (height : Nat) (hheight : height < 32) :
    zeroHashBase + Nat.toB256 height = zeroHashSlot height := by
  apply B256.toNat_inj
  rw [B256.toNat_add_eq_of_nof]
  · rw [B256.toNat_toB256_of_lt (by omega : height < 2 ^ 256)]
    unfold zeroHashSlot
    rw [B256.toNat_toB256_of_lt (by omega : 0x300 + height < 2 ^ 256)]
    rfl
  · unfold B256.Nof zeroHashBase
    rw [B256.toNat_toB256_of_lt (by omega : height < 2 ^ 256)]
    change 768 + height < 2 ^ 256
    omega

/-- The constructor continuation loads the new digest, retains its exact
SSTORE effect, increments the model height, and tail-calls the loop. -/
private theorem constructorZeroHashContinuation_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {height : Nat} {K : Nat} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (hheight : height < 31)
    (carrier : ConstructorLoopMemory memory (height + 1))
    (hsentry : gCallStipend <
      K + 18 + sstoreCost sevm base (zeroHashSlot (height + 1))
        (zeroHash Bytes.sha256 (height + 1)))
    (hstatic : sevm.isStatic = false)
    (hcontinuation : fs[constructorZeroHashContinuationSlot]? =
      some constructorZeroHashContinuation)
    (hloop : fs[constructorZeroHashLoopSlot]? = some
      (constructorZeroHashLoop constructorRuntimeOffset codeSize))
    (tail : Func.StorageEffectRun fs sevm
      ((afterSstore sevm base (zeroHashSlot (height + 1))
          (zeroHash Bytes.sha256 (height + 1))).setMach
        ⟨[Nat.toB256 (height + 1)], memory, K⟩)
      (constructorZeroHashLoop constructorRuntimeOffset codeSize)
      ex effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach
        ⟨[Nat.toB256 height], memory,
          K + 45 + sstoreCost sevm base (zeroHashSlot (height + 1))
            (zeroHash Bytes.sha256 (height + 1))⟩)
      (.call constructorZeroHashContinuationSlot) ex
      ((sevm.currentTarget, zeroHashSlot (height + 1),
          zeroHash Bytes.sha256 (height + 1)) :: effects) := by
  let node := zeroHash Bytes.sha256 (height + 1)
  let key := zeroHashSlot (height + 1)
  let C := sstoreCost sevm base key node
  have hmod : memory.size % 32 = 0 := by
    rw [carrier.size_eq]
  have hread : Bytes.toB256 (memory.read 64 32).1 = node := by
    simpa only [node] using carrier.readNode
  have hreadMem : (memory.read 64 32).2 = memory := by
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le hmod
    rw [carrier.size_eq]
  have hnextWord : (1 : B256) + Nat.toB256 height =
      Nat.toB256 (height + 1) := by
    rw [B256.add_comm]
    exact Blanc.toB256_add_one_of_lt height (by omega)
  have hkey : (zeroHashBase + 1) + Nat.toB256 height = key := by
    apply B256.toNat_inj
    rw [B256.toNat_add_eq_of_nof]
    · rw [show (zeroHashBase + 1).toNat = 769 by decide +kernel,
        B256.toNat_toB256_of_lt (by omega : height < 2 ^ 256)]
      simp only [key, zeroHashSlot]
      rw [B256.toNat_toB256_of_lt (by omega : 0x300 + (height + 1) < 2 ^ 256)]
      omega
    · unfold B256.Nof
      rw [show (zeroHashBase + 1).toNat = 769 by decide +kernel,
        B256.toNat_toB256_of_lt (by omega : height < 2 ^ 256)]
      omega
  apply Func.StorageEffectRun.call hcontinuation
    (by simp only [Devm.stack_setMach, List.length_cons,
      List.length_nil]; omega)
    (Devm.burnBy_setMach_gas
      (G := K + 33 + C)
      (by simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest,
        C, key, node]; omega))
  simp only [constructorZeroHashContinuation, constructorLoadWord,
    constructorNodeWord, show ((2 : B256) * 32) = 64 by decide +kernel]
  refine Func.StorageEffectRun.next_constructorPushWord
    (G := K + 30 + C) ?_ ?_ ?_
  · simp only [Devm.gasLeft_setMach, gVerylow]
    omega
  · simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
    omega
  · simp only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach]
    have hmload := Ninst.runCompiled_mload_of
      (sevm := sevm)
      (devm := base.setMach
        ⟨[64, Nat.toB256 height], memory, K + 30 + C⟩)
      (i := 64) (v := node) (s := [Nat.toB256 height])
      (c := 3) (G := K + 27 + C) (M := memory) rfl
      (by
        rw [Devm.extCost_zero_of_le hmod (by
          rw [carrier.size_eq]
          decide +kernel)]
        decide)
      hread hreadMem
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by simp only [List.length_cons, List.length_nil]; omega)
    apply Func.StorageEffectRun.next_effectNeutral hmload
      (by rintro impossible; cases impossible)
      (by intro operation impossible; cases impossible)
    simp only [Devm.setMach_setMach]
    apply Func.StorageEffectRun.next_effectNeutral
      (Ninst.runCompiled_dup (n := 1) (w := Nat.toB256 height)
        (G := K + 24 + C) rfl
        (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)
        (by simp only [Devm.stack_setMach, List.length_cons,
          List.length_nil]; omega))
      (by rintro impossible; cases impossible)
      (by intro operation impossible; cases impossible)
    simp only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach]
    refine Func.StorageEffectRun.next_constructorPushWord
      (G := K + 21 + C) ?_ ?_ ?_
    · simp only [Devm.gasLeft_setMach, gVerylow]
      omega
    · simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega
    · simp only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach]
      apply Func.StorageEffectRun.next_effectNeutral
        (Ninst.runCompiled_binary (r := .add) (f := (· + ·))
          (cost := gVerylow) (x := zeroHashBase + 1)
          (y := Nat.toB256 height) (v := key) (s := [node, Nat.toB256 height])
          (G := K + 18 + C)
          (by rintro impossible; cases impossible) rfl rfl hkey
          (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)
          (by simp only [List.length_cons, List.length_nil]; omega))
        (by rintro impossible; cases impossible)
        (by intro operation impossible; cases impossible)
      simp only [Devm.setMach_setMach]
      apply Func.StorageEffectRun.next_of_not_exec
        (Ninst.runCompiled_sstore_selected_setMach
          (base := base) (key := key) (value := node)
          (stack := [Nat.toB256 height]) (memory := memory)
          (G := K + 18)
          (by simpa only [C, key, node] using hsentry) hstatic)
        (by intro operation impossible; cases impossible)
      refine Func.StorageEffectRun.next_constructorPushWord
        (G := K + 15) ?_ ?_ ?_
      · simp only [Devm.gasLeft_setMach, gVerylow]
      · simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega
      · simp only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach]
        apply Func.StorageEffectRun.next_effectNeutral
          (Ninst.runCompiled_binary (r := .add) (f := (· + ·))
            (cost := gVerylow) (x := 1) (y := Nat.toB256 height)
            (v := Nat.toB256 (height + 1)) (s := []) (G := K + 12)
            (by rintro impossible; cases impossible) rfl rfl hnextWord
            (by simp only [Devm.gasLeft_setMach, gVerylow])
            (by simp only [List.length_nil]; omega))
          (by rintro impossible; cases impossible)
          (by intro operation impossible; cases impossible)
        simp only [Devm.setMach_setMach]
        apply Func.StorageEffectRun.call hloop
          (by simp only [Devm.stack_setMach, List.length_cons,
            List.length_nil]; omega)
          (Devm.burnBy_setMach_gas
            (G := K)
            (by simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]))
        simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach, C, key, node] using tail

/-- The successful fixed-width constructor SHA-256 wrapper is storage-neutral
and preserves the exact effect list of its continuation. -/
theorem constructorSha64_success_storageEffectRun_ext
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {inputWord outputWord : B256} {stack : List B256}
    {success : Func} {K ext : Nat}
    (hext : base.extCost
      [⟨(inputWord * 32).toNat, 64⟩,
        ⟨(outputWord * 32).toNat, 32⟩] = ext)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound : K + 221 + ext < 2 ^ 256)
    (hroom : stack.length < 1019) :
    ∃ callPost,
      callPost.stack = 1 :: stack ∧
      callPost.memory = (base.memory.extends
        [⟨(inputWord * 32).toNat, 64⟩,
          ⟨(outputWord * 32).toNat, 32⟩]).write
        (outputWord * 32).toNat
        (Bytes.sha256
          (base.memory.data.sliceD (inputWord * 32).toNat 64 0)).toBytes ∧
      callPost.gasLeft = K + 37 ∧
      callPost.returnData =
        (Bytes.sha256
          (base.memory.data.sliceD (inputWord * 32).toNat 64 0)).toBytes ∧
      (∀ a, Devm.getStor callPost a = Devm.getStor base a) ∧
      (∀ a, callPost.getCode a = base.getCode a) ∧
      callPost.accessedAddresses = base.accessedAddresses ∧
      callPost.accessedStorageKeys = base.accessedStorageKeys ∧
      callPost.logs = base.logs ∧
      callPost.output = base.output ∧
      callPost.error = base.error ∧
      (∃ stmid,
        base.state.subBal sevm.currentTarget 0 = some stmid ∧
        callPost.state = stmid.addBal 2 0) ∧
      ∀ {ex : Execution} {effects : List (Adr × B256 × B256)},
        Func.StorageEffectRun fs sevm
          (callPost.setMach ⟨stack, callPost.memory, K⟩)
          success ex effects →
        Func.StorageEffectRun fs sevm
          (base.setMach
            ⟨stack, base.memory,
              K + constructorSha64SuccessCost + ext⟩)
          (constructorSha64 inputWord outputWord success) ex effects := by
  let callPre := base.setMach
    ⟨Nat.toB256 (K + 221 + ext) :: (2 : B256) ::
      (inputWord * 32) :: (64 : B256) ::
      (outputWord * 32) :: (32 : B256) :: stack,
      base.memory, K + 221 + ext⟩
  obtain ⟨callPost, hstat, hstack, hmemory, hgas, hreturn,
      hstorage, hcode, haddresses, hkeys,
      hlogs, houtput, herror, stmid, hsub, hstate⟩ :=
    Ninst.childlessRunCompiled_statcall_sha256_64_warm_ext
      (sevm := sevm) (devm := callPre)
      (iiw := inputWord * 32) (oiw := outputWord * 32)
      (s := stack) (G := K + 221 + ext) (ext := ext)
      (by simp only [callPre, Devm.stack_setMach])
      (by simp only [callPre, Devm.gasLeft_setMach])
      (by simpa only [callPre, Devm.extCost, Devm.memory_setMach] using hext)
      (by simpa only [callPre, Devm.getCode_setMach] using hnodeleg)
      (by
        change (2 : Adr) ∈ base.accessedAddresses
        exact hwarm)
      hpre hdepth (by omega) hbound (by omega)
  have hgas' : callPost.gasLeft = K + 37 := by omega
  have hmemory' :
      callPost.memory = (base.memory.extends
        [⟨(inputWord * 32).toNat, 64⟩,
          ⟨(outputWord * 32).toNat, 32⟩]).write
        (outputWord * 32).toNat
        (Bytes.sha256
          (base.memory.data.sliceD (inputWord * 32).toNat 64 0)).toBytes := by
    simpa only [callPre, Devm.memory_setMach] using hmemory
  have hreturn' :
      callPost.returnData =
        (Bytes.sha256
          (base.memory.data.sliceD (inputWord * 32).toNat 64 0)).toBytes := by
    simpa only [callPre, Devm.memory_setMach] using hreturn
  have hstorage' : ∀ a,
      Devm.getStor callPost a = Devm.getStor base a := by
    intro a
    calc
      Devm.getStor callPost a = Devm.getStor callPre a := hstorage a
      _ = Devm.getStor base a := by rfl
  have hcode' : ∀ a, callPost.getCode a = base.getCode a := by
    intro a
    calc
      callPost.getCode a = callPre.getCode a := hcode a
      _ = base.getCode a := by rfl
  have haddresses' :
      callPost.accessedAddresses = base.accessedAddresses := by
    calc
      callPost.accessedAddresses = callPre.accessedAddresses := haddresses
      _ = base.accessedAddresses := by rfl
  have hkeys' :
      callPost.accessedStorageKeys = base.accessedStorageKeys := by
    calc
      callPost.accessedStorageKeys = callPre.accessedStorageKeys := hkeys
      _ = base.accessedStorageKeys := by rfl
  have hlogs' : callPost.logs = base.logs := by
    calc
      callPost.logs = callPre.logs := hlogs
      _ = base.logs := by rfl
  have houtput' : callPost.output = base.output := by
    calc
      callPost.output = callPre.output := houtput
      _ = base.output := by rfl
  have herror' : callPost.error = base.error := by
    calc
      callPost.error = callPre.error := herror
      _ = base.error := by rfl
  have hsub' : base.state.subBal sevm.currentTarget 0 = some stmid := by
    change base.state.subBal sevm.currentTarget 0 = some stmid at hsub
    exact hsub
  refine ⟨callPost, hstack, hmemory', hgas', hreturn', hstorage', hcode',
    haddresses', hkeys', hlogs', houtput', herror',
    ⟨stmid, hsub', hstate⟩, ?_⟩
  intro ex effects tail
  have hge :
      (Nat.toB256 callPost.returnData.length <? (32 : B256)) = 0 := by
    rw [hreturn', B256.length_toBytes]
    decide +kernel
  have suffix : Func.StorageEffectRun fs sevm
      (callPost.setMach ⟨1 :: stack, callPost.memory, K + 37⟩)
      (iszero :::
        (.call constructorBubbleRevertSlot) <?>
        (constructorRetdataShorterThan 32 +++
          ((.call constructorEmptyRevertSlot) <?> success))) ex effects := by
    unfold constructorRetdataShorterThan
    storage_effect_run (2) [0]
    all_goals try {
      simp only [Devm.stack_setMach, List.length_cons] at *
      omega }
    all_goals try omega
    refine Func.StorageEffectRun.next_constructorPushWord
      (G := K + 18) ?_ ?_ ?_
    · simp only [Devm.gasLeft_setMach, gVerylow]
      omega
    · simp only [Devm.stack_setMach]
      omega
    · storage_effect_run (3) [0]
      all_goals try {
        simp only [Devm.stack_setMach, List.length_cons] at *
        omega }
      simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach, Devm.gasLeft_setMach,
        Nat.add_sub_cancel] using tail
  unfold constructorSha64 constructorPushWords
  refine Func.StorageEffectRun.next_constructorPushWord
    (G := K + 235 + ext) ?_ ?_ ?_
  · simp only [Devm.gasLeft_setMach, constructorSha64SuccessCost, gVerylow]
    omega
  · simp only [Devm.stack_setMach]
    omega
  · refine Func.StorageEffectRun.next_constructorPushWord
      (G := K + 232 + ext) ?_ ?_ ?_
    · simp only [Devm.gasLeft_setMach, gVerylow]
      omega
    · simp only [Devm.stack_setMach, List.length_cons]
      omega
    · refine Func.StorageEffectRun.next_constructorPushWord
        (G := K + 229 + ext) ?_ ?_ ?_
      · simp only [Devm.gasLeft_setMach, gVerylow]
        omega
      · simp only [Devm.stack_setMach, List.length_cons]
        omega
      · refine Func.StorageEffectRun.next_constructorPushWord
          (G := K + 226 + ext) ?_ ?_ ?_
        · simp only [Devm.gasLeft_setMach, gVerylow]
          omega
        · simp only [Devm.stack_setMach, List.length_cons]
          omega
        · refine Func.StorageEffectRun.next_constructorPushWord
            (G := K + 223 + ext) ?_ ?_ ?_
          · simp only [Devm.gasLeft_setMach, gVerylow]
            omega
          · simp only [Devm.stack_setMach, List.length_cons]
            omega
          · refine Func.StorageEffectRun.next_effectNeutral
              (Ninst.runCompiled_gas (G := K + 221 + ext) ?_ ?_)
              (by rintro impossible; cases impossible)
              (by intro operation impossible; cases impossible) ?_
            · simp only [Devm.gasLeft_setMach, gBase]
              omega
            · simp only [Devm.stack_setMach, List.length_cons]
              omega
            · have hpost : callPost.setMach
                  ⟨1 :: stack, callPost.memory, K + 37⟩ = callPost := by
                apply Devm.ext
                · apply Mach.ext
                  · exact hstack.symm
                  · rfl
                  · exact hgas'.symm
                · rfl
                · rfl
              rw [hpost] at suffix
              have statSuffix : Func.StorageEffectRun fs sevm callPre
                  (statcall ::: iszero :::
                    (.call constructorBubbleRevertSlot) <?>
                    (constructorRetdataShorterThan 32 +++
                      ((.call constructorEmptyRevertSlot) <?> success)))
                  ex effects := by
                apply Func.StorageEffectRun.next hstat
                exact suffix
              simpa only [callPre, constructorSha64SuccessCost,
                Devm.setMach_setMach, Devm.stack_setMach,
                Devm.memory_setMach, Devm.gasLeft_setMach] using statSuffix

/-- One live constructor iteration is exactly one model zero-hash write.  The
SHA result state is exposed so recursive composition can carry the actual
access set, refund counter, and zero-value precompile state forward. -/
theorem constructorZeroHashLoop_succ_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {height K : Nat}
    (hheight : height < 31)
    (memoryCarrier : ConstructorLoopMemory memory height)
    (world : ConstructorLoopWorld sevm base height)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hstatic : sevm.isStatic = false)
    (hcontinuation : fs[constructorZeroHashContinuationSlot]? =
      some constructorZeroHashContinuation)
    (hloop : fs[constructorZeroHashLoopSlot]? = some
      (constructorZeroHashLoop constructorRuntimeOffset codeSize))
    (hbound :
      K + 45 + sstoreCost sevm base (zeroHashSlot (height + 1))
          (zeroHash Bytes.sha256 (height + 1)) + 221 < 2 ^ 256)
    (hsentry : gCallStipend <
      K + 18 + sstoreCost sevm base (zeroHashSlot (height + 1))
        (zeroHash Bytes.sha256 (height + 1))) :
    ∃ shaPost,
      Nonempty (ConstructorLoopMemory shaPost.memory (height + 1)) ∧
      ConstructorLoopWorld sevm
        (afterSstore sevm shaPost (zeroHashSlot (height + 1))
          (zeroHash Bytes.sha256 (height + 1))) (height + 1) ∧
      ∀ {ex : Execution} {effects : List (Adr × B256 × B256)},
        Func.StorageEffectRun fs sevm
          ((afterSstore sevm shaPost (zeroHashSlot (height + 1))
              (zeroHash Bytes.sha256 (height + 1))).setMach
            ⟨[Nat.toB256 (height + 1)], shaPost.memory, K⟩)
          (constructorZeroHashLoop constructorRuntimeOffset codeSize)
          ex effects →
        Func.StorageEffectRun fs sevm
          (base.setMach
            ⟨[Nat.toB256 height], memory,
              K + 333 + sstoreCost sevm base (zeroHashSlot (height + 1))
                (zeroHash Bytes.sha256 (height + 1))⟩)
          (constructorZeroHashLoop constructorRuntimeOffset codeSize)
          ex
          ((sevm.currentTarget, zeroHashSlot (height + 1),
              zeroHash Bytes.sha256 (height + 1)) :: effects) := by
  let node := zeroHash Bytes.sha256 (height + 1)
  let key := zeroHashSlot (height + 1)
  let C := sstoreCost sevm base key node
  let pair := constructorPairMemory memory
    (zeroHash Bytes.sha256 height)
  let shaBase := base.setMach ⟨[], pair, 0⟩
  have pairSize : pair.size = 96 := by
    simpa only [pair] using memoryCarrier.pairSize
  have pairMod : pair.size % 32 = 0 := by
    rw [pairSize]
  have covered : memExtsSize pair.size
      [⟨((0 : B256) * 32).toNat, 64⟩,
        ⟨(constructorNodeWord * 32).toNat, 32⟩] = pair.size := by
    simp only [show ((0 : B256) * 32).toNat = 0 by decide +kernel,
      constructorNodeWord,
      show ((2 : B256) * 32).toNat = 64 by decide +kernel,
      pairSize]
    decide +kernel
  have hext : shaBase.extCost
      [⟨((0 : B256) * 32).toNat, 64⟩,
        ⟨(constructorNodeWord * 32).toNat, 32⟩] = 0 := by
    exact Devm.extCost_covered covered
  obtain ⟨shaPost, hstack, hmemory, hgas, hreturn,
      hstorage, hcode, haddresses, hkeys, hlogs, houtput, herror,
      hstate, shaLift⟩ :=
    constructorSha64_success_storageEffectRun_ext
      (fs := fs) (sevm := sevm) (base := shaBase)
      (inputWord := 0) (outputWord := constructorNodeWord)
      (stack := [Nat.toB256 height])
      (success := .call constructorZeroHashContinuationSlot)
      (K := K + 45 + C) (ext := 0)
      hext
      (by simpa only [shaBase, Devm.getCode_setMach] using world.shaCode)
      (by
        change (2 : Adr) ∈ base.accessedAddresses
        exact world.shaWarm)
      hpre hdepth
      (by simpa only [C, key, node] using hbound)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have hstorageBase : ∀ address,
      Devm.getStor shaPost address = Devm.getStor base address := by
    intro address
    calc
      Devm.getStor shaPost address = Devm.getStor shaBase address :=
        hstorage address
      _ = Devm.getStor base address := rfl
  have hcodeBase : ∀ address,
      shaPost.getCode address = base.getCode address := by
    intro address
    simpa only [shaBase, Devm.getCode_setMach] using hcode address
  have haddressesBase :
      shaPost.accessedAddresses = base.accessedAddresses := by
    calc
      shaPost.accessedAddresses = shaBase.accessedAddresses := haddresses
      _ = base.accessedAddresses := rfl
  have hkeysBase :
      shaPost.accessedStorageKeys = base.accessedStorageKeys := by
    calc
      shaPost.accessedStorageKeys = shaBase.accessedStorageKeys := hkeys
      _ = base.accessedStorageKeys := rfl
  have herrorBase : shaPost.error = base.error := by
    calc
      shaPost.error = shaBase.error := herror
      _ = base.error := rfl
  have hcost : sstoreCost sevm shaPost key node = C := by
    exact (sstoreCost_congr (d1 := shaPost) (d2 := base) key node
      hkeysBase (hstorageBase sevm.currentTarget)).trans rfl
  have extendsPair : pair.extends
      [⟨((0 : B256) * 32).toNat, 64⟩,
        ⟨(constructorNodeWord * 32).toNat, 32⟩] = pair :=
    Mem.extends_covered covered
  have hmemory' : shaPost.memory = pair.write 64
      (Bytes.sha256 (pair.data.sliceD 0 64 0)).toBytes := by
    change shaPost.memory =
      (pair.extends [⟨0, 64⟩, ⟨64, 32⟩]).write 64
        (Bytes.sha256 (pair.data.sliceD 0 64 0)).toBytes at hmemory
    have extendsPair' : pair.extends [⟨0, 64⟩, ⟨64, 32⟩] = pair := by
      simpa only [constructorNodeWord,
        show ((0 : B256) * 32).toNat = 0 by decide +kernel,
        show ((2 : B256) * 32).toNat = 64 by decide +kernel] using extendsPair
    rw [extendsPair'] at hmemory
    exact hmemory
  have nextMemory : ConstructorLoopMemory shaPost.memory (height + 1) := by
    apply memoryCarrier.afterSha
    simpa only [pair] using hmemory'
  have nextWorld : ConstructorLoopWorld sevm
      (afterSstore sevm shaPost key node) (height + 1) := by
    exact world.afterShaWrite hstorageBase hcodeBase haddressesBase herrorBase
  refine ⟨shaPost, ⟨nextMemory⟩, ?_, ?_⟩
  · simpa only [key, node] using nextWorld
  · intro ex effects tail
    have continuation : Func.StorageEffectRun fs sevm
        (shaPost.setMach
          ⟨[Nat.toB256 height], shaPost.memory,
            K + 45 + C⟩)
        (.call constructorZeroHashContinuationSlot) ex
        ((sevm.currentTarget, key, node) :: effects) := by
      have sentryPost : gCallStipend <
          K + 18 + sstoreCost sevm shaPost
            (zeroHashSlot (height + 1))
            (zeroHash Bytes.sha256 (height + 1)) := by
        rw [show sstoreCost sevm shaPost
          (zeroHashSlot (height + 1))
          (zeroHash Bytes.sha256 (height + 1)) = C by
            simpa only [key, node] using hcost]
        simpa only [C, key, node] using hsentry
      have contRaw := constructorZeroHashContinuation_storageEffectRun
        (fs := fs) (sevm := sevm) (base := shaPost)
        (memory := shaPost.memory) (height := height) (K := K)
        (ex := ex) (effects := effects)
        hheight nextMemory sentryPost hstatic hcontinuation hloop
        (by simpa only [key, node] using tail)
      rw [show sstoreCost sevm shaPost
        (zeroHashSlot (height + 1))
        (zeroHash Bytes.sha256 (height + 1)) = C by
          simpa only [key, node] using hcost] at contRaw
      simpa only [key, node] using contRaw
    have shaRun : Func.StorageEffectRun fs sevm
        (shaBase.setMach
          ⟨[Nat.toB256 height], pair,
            K + 45 + C + constructorSha64SuccessCost⟩)
        (constructorSha64 0 constructorNodeWord
          (.call constructorZeroHashContinuationSlot)) ex
        ((sevm.currentTarget, key, node) :: effects) := by
      exact shaLift continuation
    have pairRun : Func.StorageEffectRun fs sevm
        (base.setMach
          ⟨[Nat.toB256 height], memory, K + 307 + C⟩)
        ((constructorLoadWord constructorNodeWord ++ constructorStoreWord 0 ++
          constructorLoadWord constructorNodeWord ++ constructorStoreWord 1) +++
          constructorSha64 0 constructorNodeWord
            (.call constructorZeroHashContinuationSlot)) ex
        ((sevm.currentTarget, key, node) :: effects) := by
      have shaRun' : Func.StorageEffectRun fs sevm
          (base.setMach
            ⟨[Nat.toB256 height], pair, K + 283 + C⟩)
          (constructorSha64 0 constructorNodeWord
            (.call constructorZeroHashContinuationSlot)) ex
          ((sevm.currentTarget, key, node) :: effects) := by
        have shaState : shaBase.setMach
              ⟨[Nat.toB256 height], pair,
                K + 45 + C + constructorSha64SuccessCost⟩ =
            base.setMach
              ⟨[Nat.toB256 height], pair, K + 283 + C⟩ := by
          apply Devm.ext
          · apply Mach.ext
            · rfl
            · rfl
            · change K + 45 + C + constructorSha64SuccessCost =
                K + 283 + C
              simp only [constructorSha64SuccessCost]
              omega
          · rfl
          · rfl
        rw [shaState] at shaRun
        exact shaRun
      have pairRaw := constructorPairStage_storageEffectRun
        (base := base) (heightWord := Nat.toB256 height)
        (stack := []) (K := K + 283 + C)
        memoryCarrier (by simp only [List.length_nil]; omega) shaRun'
      rw [show K + 283 + C + 24 = K + 307 + C by omega] at pairRaw
      exact pairRaw
    have loopRun := constructorZeroHashLoop_succ_dispatch_storageEffectRun
      (runtimeOffset := constructorRuntimeOffset) (runtimeLength := codeSize)
      hheight pairRun
    rw [show K + 307 + C + 26 = K + 333 + C by omega] at loopRun
    simpa only [C, key, node] using loopRun

/-- Exact CODECOPY charge used by the constructor terminal arm. -/
def constructorFinishCopyCost (base : Devm) (memory : Mem) : Nat :=
  gVerylow + gasCopy * ceilDiv codeSize 32 +
    (base.setMach ⟨[], memory, 0⟩).extCost [⟨0, codeSize⟩]

/-- Exact gas needed from the terminal-arm entry through RETURN. -/
def constructorFinishGas (base : Devm) (memory : Mem) : Nat :=
  15 + constructorFinishCopyCost base memory

/-- Gas deliberately left after the constructor returns.  Keeping one unit
above the EIP-2200 sentry makes every preceding SSTORE admissible even when a
digest happens to be zero and the value-case charge is only the no-op cost. -/
def constructorSentryReserve : Nat := gCallStipend + 1

/-- A worst-case constructor iteration: the exact non-SSTORE prefix plus a
cold, zero-to-nonzero SSTORE.  Any unused SSTORE charge is carried forward as
terminal slack by the recursive proof. -/
def constructorIterationGasBound : Nat :=
  333 + gasColdSload + gasStorageSet

/-- Exact budget used at a constructor loop head with `remaining` live
iterations.  The terminal arm consumes 596 gas after the sentry reserve. -/
def constructorLoopGas (slack remaining : Nat) : Nat :=
  slack + constructorSentryReserve + 596 +
    remaining * constructorIterationGasBound

private theorem sstoreCost_le_constructor_bound
    (sevm : Sevm) (base : Devm) (key value : B256) :
    sstoreCost sevm base key value ≤ gasColdSload + gasStorageSet := by
  have valueBound : sstoreValueCost
      (getOrigStorVal sevm sevm.currentTarget key)
      (base.getStorVal sevm.currentTarget key) value ≤ gasStorageSet := by
    rw [sstoreValueCost]
    split_ifs <;> decide +kernel
  unfold sstoreCost
  split <;> omega

private theorem constructorFinishGas_eq
    {base : Devm} {memory : Mem}
    (carrier : ConstructorLoopMemory memory 31) :
    constructorFinishGas base memory = 571 := by
  have extCost :
      (base.setMach ⟨[], memory, 0⟩).extCost [⟨0, codeSize⟩] = 280 := by
    exact Devm.extCost_of_size carrier.size_eq (by
      rw [codeSize_exact]
      decide +kernel)
  unfold constructorFinishGas constructorFinishCopyCost
  rw [extCost, codeSize_exact]
  decide +kernel

/-- The terminal constructor arm copies and returns exactly the appended
runtime, with no storage effect. -/
theorem constructorFinish_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm} {memory : Mem}
    {K : Nat}
    (memoryCarrier : ConstructorLoopMemory memory 31)
    (hcode : sevm.code.toList = creationCode) :
    ∃ post,
      post.output = code ∧
      post.error = base.error ∧
      Devm.getStor post sevm.currentTarget =
        Devm.getStor base sevm.currentTarget ∧
      Func.StorageEffectRun fs sevm
        (base.setMach
          ⟨[Nat.toB256 31], memory, K + constructorFinishGas base memory⟩)
        (constructorFinish constructorRuntimeOffset codeSize)
        (.ok post) [] := by
  set copied := memory.write 0 code with copiedDef
  let copyCost := constructorFinishCopyCost base memory
  set returnBase := base.setMach ⟨[Nat.toB256 31], copied, K⟩ with returnBaseDef
  set post := (returnBase.memRead 0 codeSize).2.withOutput code with postDef
  have codeLength : code.length = codeSize := rfl
  have codeSizeBound : codeSize < 2 ^ 256 := by
    rw [codeSize_exact]
    omega
  have codeNonempty : code ≠ [] := by
    intro empty
    have lengths := congrArg List.length empty
    rw [codeLength, codeSize_exact] at lengths
    simp at lengths
  have copiedSize : copied.size = 2912 := by
    rw [copiedDef]
    rw [Mem.size_write_of_size memoryCarrier.size_eq
      (by decide +kernel) codeLength]
    simp only [codeSize_exact]
    decide +kernel
  have copiedMod : copied.size % 32 = 0 := by
    rw [copiedSize]
  have copiedCovers : codeSize ≤ copied.size := by
    rw [codeSize_exact, copiedSize]
    omega
  have readBytes : (copied.read 0 codeSize).1 = code := by
    rw [copiedDef]
    simpa only [codeLength] using Mem.read_write_zero memory codeNonempty
  have readMemory : (copied.read 0 codeSize).2 = copied := by
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le copiedMod
    omega
  have codeWindow : sevm.code.sliceD constructorRuntimeOffset codeSize
      (Linst.toUInt8 .stop) = code := by
    rw [ByteArray.sliceD_eq, hcode]
    exact creationCode_slice_runtime
  have copyCostEq :
      gVerylow + gasCopy * ceilDiv (Nat.toB256 codeSize).toNat 32 +
          (base.setMach
            ⟨[0, Nat.toB256 constructorRuntimeOffset,
              Nat.toB256 codeSize, Nat.toB256 31],
              memory, K + 6 + copyCost⟩).extCost
            [⟨(0 : B256).toNat, (Nat.toB256 codeSize).toNat⟩] =
        copyCost := by
    rw [B256.toNat_toB256_of_lt codeSizeBound]
    change gVerylow + gasCopy * ceilDiv codeSize 32 +
        (base.setMach ⟨[], memory, 0⟩).extCost [⟨0, codeSize⟩] = copyCost
    rfl
  have postOutput : post.output = code := by
    rw [postDef, Devm.withOutput_output]
  have postError : post.error = base.error := by
    rw [postDef, Devm.withOutput_error, Devm.memRead_error,
      returnBaseDef, Devm.setMach_error]
  have postStorage : Devm.getStor post sevm.currentTarget =
      Devm.getStor base sevm.currentTarget := by
    rw [postDef]
    rfl
  refine ⟨post, postOutput, postError, postStorage, ?_⟩
  simp only [constructorFinish, constructorPushWords]
  refine Func.StorageEffectRun.next_constructorPushWord
    (G := K + 12 + copyCost) ?_ ?_ ?_
  · simp only [constructorFinishGas, Devm.gasLeft_setMach, gVerylow,
      copyCost]
    omega
  · simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
    omega
  · refine Func.StorageEffectRun.next_constructorPushWord
      (G := K + 9 + copyCost) ?_ ?_ ?_
    · simp only [Devm.gasLeft_setMach, gVerylow]
      omega
    · simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega
    · refine Func.StorageEffectRun.next_constructorPushWord
        (G := K + 6 + copyCost) ?_ ?_ ?_
      · simp only [Devm.gasLeft_setMach, gVerylow]
        omega
      · simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega
      · simp only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach]
        have codecopyRun := Ninst.runCompiled_codecopy_of
          (sevm := sevm)
          (devm := base.setMach
            ⟨[0, Nat.toB256 constructorRuntimeOffset,
              Nat.toB256 codeSize, Nat.toB256 31],
              memory, K + 6 + copyCost⟩)
          (di := 0) (si := Nat.toB256 constructorRuntimeOffset)
          (sz := Nat.toB256 codeSize) (s := [Nat.toB256 31])
          (c := copyCost) (G := K + 6) (M := copied) rfl copyCostEq
          (by
            simp only [Devm.memory_setMach,
              show (0 : B256).toNat = 0 by decide +kernel,
              B256.toNat_toB256_of_lt
                (by rw [constructorRuntimeOffset_exact]; omega :
                  constructorRuntimeOffset < 2 ^ 256),
              B256.toNat_toB256_of_lt codeSizeBound]
            rw [codeWindow, ← copiedDef])
          (by simp only [Devm.gasLeft_setMach])
        apply Func.StorageEffectRun.next_effectNeutral codecopyRun
          (by rintro impossible; cases impossible)
          (by intro operation impossible; cases impossible)
        refine Func.StorageEffectRun.next_constructorPushWord
          (G := K + 3) ?_ ?_ ?_
        · simp only [Devm.gasLeft_setMach, gVerylow]
        · simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
          omega
        · refine Func.StorageEffectRun.next_constructorPushWord
            (G := K) ?_ ?_ ?_
          · simp only [Devm.gasLeft_setMach, gVerylow]
          · simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
            omega
          · simp only [Devm.setMach_setMach, Devm.stack_setMach,
              Devm.memory_setMach]
            have extZero :
                (base.setMach
                  ⟨[0, Nat.toB256 codeSize, Nat.toB256 31], copied, K⟩).extCost
                  [⟨0, codeSize⟩] = 0 := by
              exact Devm.extCost_zero_of_le copiedMod (by omega)
            have retRun : Func.RunCompiled fs sevm
                (base.setMach
                  ⟨[0, Nat.toB256 codeSize, Nat.toB256 31], copied, K⟩)
                (.last .ret) post := by
              have raw := Func.runCompiled_ret_word
                (fs := fs) (sevm := sevm)
                (devm := base.setMach
                  ⟨[0, Nat.toB256 codeSize, Nat.toB256 31], copied, K⟩)
                (i := 0) (sz := Nat.toB256 codeSize)
                (s := [Nat.toB256 31]) (out := code) (G := K) (e := 0)
                rfl
                (by
                  simpa only [show (0 : B256).toNat = 0 by decide +kernel,
                    B256.toNat_toB256_of_lt codeSizeBound] using extZero)
                (by simp only [Devm.gasLeft_setMach, Nat.add_zero])
                (by
                  simp only [show (0 : B256).toNat = 0 by decide +kernel,
                    B256.toNat_toB256_of_lt codeSizeBound]
                  rw [Devm.memRead_fst, Devm.memory_setMach]
                  simp only [Devm.memory_setMach]
                  rw [readBytes])
              rw [postDef, returnBaseDef]
              simpa only [Devm.memory_setMach, Devm.setMach_setMach,
                show (0 : B256).toNat = 0 by decide +kernel,
                B256.toNat_toB256_of_lt codeSizeBound] using raw
            cases retRun with
            | last terminalRun =>
                exact Func.StorageEffectRun.last terminalRun

/-- At height thirty-one the constructor loop selects its terminal arm in
exactly 25 gas and contributes no additional storage effect. -/
private theorem constructorZeroHashLoop_finish_dispatch_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm} {memory : Mem}
    {K : Nat} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (tail : Func.StorageEffectRun fs sevm
      (base.setMach ⟨[Nat.toB256 31], memory, K⟩)
      (constructorFinish constructorRuntimeOffset codeSize) ex effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach ⟨[Nat.toB256 31], memory, K + 25⟩)
      (constructorZeroHashLoop constructorRuntimeOffset codeSize) ex effects := by
  simp only [constructorZeroHashLoop]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_dup (n := 0) (w := Nat.toB256 31)
      (G := K + 22) rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega))
    (by rintro impossible; cases impossible)
    (by intro operation impossible; cases impossible)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.StorageEffectRun.next_constructorPushWord
    (G := K + 19) ?_ ?_ ?_
  · simp only [Devm.gasLeft_setMach, gVerylow]
  · simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
    omega
  · simp only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach]
    apply Func.StorageEffectRun.next_effectNeutral
      (Ninst.runCompiled_swap (n := 0)
        (S := Nat.toB256 31 :: (31 : B256) :: Nat.toB256 31 :: [])
        (G := K + 16) rfl
        (by simp only [Devm.gasLeft_setMach, gVerylow]))
      (by rintro impossible; cases impossible)
      (by intro operation impossible; cases impossible)
    simp only [Devm.setMach_setMach, Devm.memory_setMach]
    apply Func.StorageEffectRun.next_effectNeutral
      (Ninst.runCompiled_binary (r := .lt) (f := B256.ltCheck)
        (cost := gVerylow) (x := Nat.toB256 31) (y := 31)
        (v := 0) (s := [Nat.toB256 31]) (G := K + 13)
        (by rintro impossible; cases impossible) rfl rfl
        (by decide +kernel)
        (by simp only [Devm.gasLeft_setMach, gVerylow])
        (by simp only [List.length_cons, List.length_nil]; omega))
      (by rintro impossible; cases impossible)
      (by intro operation impossible; cases impossible)
    simp only [Devm.setMach_setMach]
    apply Func.storageEffectRun_branch_zero
      (s := [Nat.toB256 31]) (G := K) rfl
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega)
      (by simp only [Devm.gasLeft_setMach, gVerylow, gHigh])
    simpa only [Devm.setMach_setMach, Devm.memory_setMach] using tail

/-- Fold the exact constructor loop for an arbitrary suffix.  The budget is
fixed from the remaining iteration count; any difference between the
worst-case SSTORE allowance and the selected charge becomes terminal slack. -/
private theorem constructorZeroHashLoop_remaining_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm} {memory : Mem}
    {height remaining slack : Nat}
    (hsum : height + remaining = 31)
    (memoryCarrier : ConstructorLoopMemory memory height)
    (world : ConstructorLoopWorld sevm base height)
    (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hcontinuation : fs[constructorZeroHashContinuationSlot]? =
      some constructorZeroHashContinuation)
    (hloop : fs[constructorZeroHashLoopSlot]? = some
      (constructorZeroHashLoop constructorRuntimeOffset codeSize))
    (hcode : sevm.code.toList = creationCode)
    (hgasBound : constructorLoopGas slack remaining < 2 ^ 256) :
    ∃ post,
      post.output = code ∧
      post.error = none ∧
      Devm.getStor post sevm.currentTarget = constructorFinalStorage ∧
      Func.StorageEffectRun fs sevm
        (base.setMach
          ⟨[Nat.toB256 height], memory,
            constructorLoopGas slack remaining⟩)
        (constructorZeroHashLoop constructorRuntimeOffset codeSize)
        (.ok post)
        (constructorStorageEffectTriplesFrom
          sevm.currentTarget height remaining) := by
  induction remaining generalizing height slack base memory with
  | zero =>
      have heightEq : height = 31 := by omega
      subst height
      obtain ⟨post, postOutput, postError, postStorage, finishRun⟩ :=
        constructorFinish_storageEffectRun
          (fs := fs) (sevm := sevm) (base := base) (memory := memory)
          (K := slack + constructorSentryReserve) memoryCarrier hcode
      have loopRun :=
        constructorZeroHashLoop_finish_dispatch_storageEffectRun
          (K := slack + constructorSentryReserve +
            constructorFinishGas base memory) finishRun
      have gasEq :
          slack + constructorSentryReserve +
                constructorFinishGas base memory + 25 =
            constructorLoopGas slack 0 := by
        rw [constructorFinishGas_eq memoryCarrier]
        simp only [constructorLoopGas]
        omega
      rw [gasEq] at loopRun
      have finalStorage : Devm.getStor post sevm.currentTarget =
          constructorFinalStorage := by
        rw [postStorage, world.storage]
        rfl
      exact ⟨post, postOutput, postError.trans world.error, finalStorage,
        by
          simpa only [constructorStorageEffectTriplesFrom_zero] using
            loopRun⟩
  | succ remaining ih =>
      have heightBound : height < 31 := by omega
      let key := zeroHashSlot (height + 1)
      let node := zeroHash Bytes.sha256 (height + 1)
      set C := sstoreCost sevm base key node with CDef
      have costBound : C ≤ gasColdSload + gasStorageSet := by
        rw [CDef]
        exact sstoreCost_le_constructor_bound sevm base key node
      let nextSlack := slack + (gasColdSload + gasStorageSet - C)
      let K := constructorLoopGas nextSlack remaining
      have reclaimedCost :
          (gasColdSload + gasStorageSet - C) + C =
            gasColdSload + gasStorageSet :=
        Nat.sub_add_cancel costBound
      have gasEq : K + 333 + C =
          constructorLoopGas slack (remaining + 1) := by
        calc
          K + 333 + C =
              slack + (gasColdSload + gasStorageSet - C) +
                constructorSentryReserve + 596 +
                remaining * constructorIterationGasBound + 333 + C := by
            simp only [K, nextSlack, constructorLoopGas]
          _ = slack + constructorSentryReserve + 596 +
                remaining * constructorIterationGasBound + 333 +
                ((gasColdSload + gasStorageSet - C) + C) := by
            ac_rfl
          _ = slack + constructorSentryReserve + 596 +
                remaining * constructorIterationGasBound + 333 +
                (gasColdSload + gasStorageSet) := by
            rw [reclaimedCost]
          _ = constructorLoopGas slack (remaining + 1) := by
            unfold constructorLoopGas constructorIterationGasBound
            rw [Nat.add_mul]
            simp only [Nat.one_mul]
            ac_rfl
      have gasBound : K + 45 + C + 221 < 2 ^ 256 := by
        have currentBound : K + 333 + C < 2 ^ 256 := by
          rw [gasEq]
          exact hgasBound
        omega
      have sentry : gCallStipend < K + 18 + C := by
        simp only [K, nextSlack, constructorLoopGas,
          constructorSentryReserve]
        omega
      obtain ⟨shaPost, ⟨nextMemoryCarrier⟩, nextWorld, lift⟩ :=
        constructorZeroHashLoop_succ_storageEffectRun
          (fs := fs) (sevm := sevm) (base := base) (memory := memory)
          (height := height) (K := K) heightBound memoryCarrier world
          hpre hdepth hstatic hcontinuation hloop
          (by simpa only [CDef, key, node] using gasBound)
          (by simpa only [CDef, key, node] using sentry)
      have nextGasBound :
          constructorLoopGas nextSlack remaining < 2 ^ 256 := by
        change K < 2 ^ 256
        have currentBound : K + 333 + C < 2 ^ 256 := by
          rw [gasEq]
          exact hgasBound
        omega
      obtain ⟨post, postOutput, postError, postStorage, tailRun⟩ := ih
        (height := height + 1) (slack := nextSlack)
        (base := afterSstore sevm shaPost key node)
        (memory := shaPost.memory)
        (by omega) nextMemoryCarrier
        (by simpa only [key, node] using nextWorld)
        nextGasBound
      have currentRun := lift tailRun
      rw [gasEq] at currentRun
      refine ⟨post, postOutput, postError, postStorage, ?_⟩
      simpa only [constructorStorageEffectTriplesFrom_succ, key, node] using
        currentRun

/-- Public height-zero specialization of the exact constructor fold. -/
theorem constructorZeroHashLoop_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    (world : ConstructorLoopWorld sevm base 0)
    (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hcontinuation : fs[constructorZeroHashContinuationSlot]? =
      some constructorZeroHashContinuation)
    (hloop : fs[constructorZeroHashLoopSlot]? = some
      (constructorZeroHashLoop constructorRuntimeOffset codeSize))
    (hcode : sevm.code.toList = creationCode) :
    ∃ post,
      post.output = code ∧
      post.error = none ∧
      Devm.getStor post sevm.currentTarget = constructorFinalStorage ∧
      Func.StorageEffectRun fs sevm
        (base.setMach
          ⟨[0], constructorInitialMemory, constructorLoopGas 0 31⟩)
        (constructorZeroHashLoop constructorRuntimeOffset codeSize)
        (.ok post) (constructorStorageEffectTriples sevm.currentTarget) := by
  obtain ⟨post, postOutput, postError, postStorage, run⟩ :=
    constructorZeroHashLoop_remaining_storageEffectRun
      (fs := fs) (sevm := sevm) (base := base)
      (memory := constructorInitialMemory) (height := 0)
      (remaining := 31) (slack := 0) rfl
      constructorInitialMemory_carrier world hstatic hdepth hpre
      hcontinuation hloop hcode
      (by
        unfold constructorLoopGas constructorSentryReserve
          constructorIterationGasBound
        decide +kernel)
  exact ⟨post, postOutput, postError, postStorage, by
    simpa only [constructorStorageEffectTriplesFrom_initial,
      show Nat.toB256 0 = 0 by decide +kernel] using run⟩

/-- Initialize the constructor's scratch word and enter the exact zero-hash
loop.  The prefix costs 33 gas including the internal-call boundary. -/
theorem constructorStart_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {K : Nat} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (hloop : fs[constructorZeroHashLoopSlot]? = some
      (constructorZeroHashLoop constructorRuntimeOffset codeSize))
    (tail : Func.StorageEffectRun fs sevm
      (base.setMach ⟨[0], constructorInitialMemory, K⟩)
      (constructorZeroHashLoop constructorRuntimeOffset codeSize)
      ex effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], Mem.empty, K + 33⟩)
      constructorStart ex effects := by
  simp only [constructorStart, constructorStoreWord, constructorNodeWord]
  refine Func.StorageEffectRun.next_constructorPushWord
    (G := K + 30) ?_ ?_ ?_
  · simp only [Devm.gasLeft_setMach, gVerylow]
  · simp only [Devm.stack_setMach, List.length_nil]
    omega
  · simp only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach]
    refine Func.StorageEffectRun.next_constructorPushWord
      (G := K + 27) ?_ ?_ ?_
    · simp only [Devm.gasLeft_setMach, gVerylow]
    · simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega
    · simp only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach]
      have storeRun := Ninst.runCompiled_mstore_of
        (sevm := sevm)
        (devm := base.setMach ⟨[64, 0], Mem.empty, K + 27⟩)
        (i := 64) (v := 0) (s := []) (G := K + 15) (e := 9)
        (M := constructorInitialMemory) rfl
        (Devm.extCost_of_size (n := 0) rfl (by decide +kernel))
        (by simp only [Devm.gasLeft_setMach, gVerylow])
        (by
          simp only [Devm.memory_setMach,
            show (64 : B256).toNat = 64 by decide +kernel]
          rfl)
      apply Func.StorageEffectRun.next_effectNeutral storeRun
        (by rintro impossible; cases impossible)
        (by intro operation impossible; cases impossible)
      simp only [Devm.setMach_setMach]
      refine Func.StorageEffectRun.next_constructorPushWord
        (G := K + 12) ?_ ?_ ?_
      · simp only [Devm.gasLeft_setMach, gVerylow]
      · simp only [Devm.stack_setMach, List.length_nil]
        omega
      · simp only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach]
        apply Func.StorageEffectRun.call hloop
          (by simp only [Devm.stack_setMach, List.length_cons,
            List.length_nil]; omega)
          (Devm.burnBy_setMach_gas
            (G := K)
            (by simp only [Devm.gasLeft_setMach, gVerylow, gMid,
              gJumpdest]))
        simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using tail

end Blanc.BeaconDeposit
