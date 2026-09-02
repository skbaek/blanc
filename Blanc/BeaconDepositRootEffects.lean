import Blanc.BeaconDepositRootFold
import Blanc.BeaconDepositCountEffects
import Blanc.BeaconDepositStorageEffects
import Blanc.ForwardStorageEffects

/-!
# Beacon deposit root-view effects

Exact selector-tree routing and compiled effects for `get_deposit_root()`.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Blanc.Ninst

/-- Shift the root size, increment its height, and re-enter the root loop
without adding a retained storage effect. -/
private theorem rootContinuation_storageEffectRun
    {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount size node height : B256}
    {K : Nat} {ex : Execution}
    (hmem : RootMemoryCarrier memory oldCount size node)
    (tail : Func.StorageEffectRun (runtime.main :: runtime.aux) sevm
      (base.setMach
        ⟨[height + 1], memory.write 608 (size >>> 1).toBytes, K⟩)
      rootLoop ex []) :
    Func.StorageEffectRun (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[height], memory, K + 36⟩)
      rootContinuation ex [] := by
  have hoff : (shiftedSizeWord * 32).toNat = 608 := by
    decide +kernel
  have hpushOff :
      pushCost (shiftedSizeWord * 32).toBytes.sig = gVerylow := by
    decide +kernel
  have hmod : memory.size % 32 = 0 := by
    rw [hmem.size_eq]
  have hsize : 640 ≤ memory.size := by
    rw [hmem.size_eq]
    omega
  have hread : Bytes.toB256 (memory.read 608 32).1 = size := by
    rw [hmem.read_shiftedSize, B256.toB256_toBytes]
  unfold rootContinuation loadWord mstoreAt
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256
      (w := shiftedSizeWord * 32) (c := gVerylow) (G := K + 33)
      hpushOff
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega))
    (by rintro ⟨⟩)
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  have hmload :=
    Ninst.runCompiled_mload_of
      (sevm := sevm)
      (devm := base.setMach
        ⟨(shiftedSizeWord * 32) :: [height], memory, K + 33⟩)
      (i := shiftedSizeWord * 32) (v := size) (s := [height])
      (c := gVerylow) (G := K + 30) (M := memory) rfl
      (by
        rw [Devm.extCost_zero_of_le hmod (by rw [hoff]; omega)]
        omega)
      (by
        rw [Devm.memory_setMach, hoff]
        exact hread)
      (by
        rw [Devm.memory_setMach, hoff,
          Mem.read_snd_eq_self (memExtSize_of_le hmod (by omega))])
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_cons, List.length_nil]; omega)
  apply Func.StorageEffectRun.next_effectNeutral hmload
    (by rintro ⟨⟩)
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256
      (w := (1 : B256)) (c := gVerylow) (G := K + 27)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega))
    (by rintro ⟨⟩)
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_binary
      (r := .shr) (f := fun x y => y >>> x.toNat)
      (cost := gVerylow) (G := K + 24)
      (x := (1 : B256)) (y := size) (v := size >>> 1)
      (s := [height])
      (by rintro ⟨⟩) rfl rfl
      (by simp only [show (1 : B256).toNat = 1 by decide +kernel])
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_cons, List.length_nil]; omega))
    (by rintro ⟨⟩)
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256
      (w := shiftedSizeWord * 32) (c := gVerylow) (G := K + 21)
      hpushOff
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega))
    (by rintro ⟨⟩)
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_mstore_of
      (i := shiftedSizeWord * 32) (v := size >>> 1)
      (s := [height]) (G := K + 18) (e := 0) rfl
      (Devm.extCost_zero_of_le hmod (by rw [hoff]; omega))
      (by simp only [Devm.gasLeft_setMach, gVerylow]) rfl)
    (by rintro ⟨⟩)
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, hoff]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256
      (w := (1 : B256)) (c := gVerylow) (G := K + 15)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega))
    (by rintro ⟨⟩)
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_binary
      (r := .add) (f := (· + ·))
      (cost := gVerylow) (G := K + 12)
      (x := (1 : B256)) (y := height) (v := height + 1)
      (s := [])
      (by rintro ⟨⟩) rfl rfl
      (B256.add_comm (xs := (1 : B256)) (ys := height))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_nil]; omega))
    (by rintro ⟨⟩)
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach]
  apply Func.StorageEffectRun.call (by rfl)
    (by simp only [Devm.stack_setMach, List.length_cons,
      List.length_nil]; omega)
    (Devm.burnBy_setMach_gas (G := K)
      (by simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]))
  simpa only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach] using tail

/-- One root-fold hash plus its continuation, retaining the childless SHA
crossing and an empty exact-effect list. -/
private theorem rootShaTail_storageEffectRun
    {sevm : Sevm} {base : Devm}
    {oldCount size left right height : B256} {K : Nat}
    (pair : RootPairMemoryCarrier base.memory oldCount size left right)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound : K + 269 < 2 ^ 256) :
    ∃ callPost,
      callPost.stack = 1 :: [height] ∧
      callPost.memory = base.memory.write 640
        (Bytes.sha256 (left.toBytes ++ right.toBytes)).toBytes ∧
      Nonempty (RootMemoryCarrier callPost.memory oldCount size
        (Bytes.sha256 (left.toBytes ++ right.toBytes))) ∧
      callPost.gasLeft = K + 85 ∧
      callPost.returnData =
        (Bytes.sha256 (left.toBytes ++ right.toBytes)).toBytes ∧
      (∀ a, Devm.getStor callPost a = Devm.getStor base a) ∧
      (∀ a, callPost.getCode a = base.getCode a) ∧
      callPost.accessedAddresses = base.accessedAddresses ∧
      callPost.accessedStorageKeys = base.accessedStorageKeys ∧
      callPost.logs = base.logs ∧
      callPost.output = base.output ∧
      callPost.error = base.error ∧
      ∀ {ex : Execution},
        Func.StorageEffectRun (runtime.main :: runtime.aux) sevm
          (callPost.setMach
            ⟨[height + 1],
              callPost.memory.write 608 (size >>> 1).toBytes, K⟩)
          rootLoop ex [] →
        Func.StorageEffectRun (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[height], base.memory, K + 285⟩)
      (sha64 0 nodeWord (.call rootContinuationSlot)) ex [] := by
  have hzero : ((0 : B256) * 32).toNat = 0 := by decide +kernel
  have hnode : (nodeWord * 32).toNat = 640 := by decide +kernel
  have hcovered : memExtsSize base.memory.size
      [⟨0, 64⟩, ⟨640, 32⟩] = base.memory.size := by
    rw [pair.size_eq]
    decide +kernel
  obtain ⟨callPost, hstack, hmemory, hgas, hreturn,
      hstorage, hcode, haddresses, hkeys, hlogs, houtput, herror,
      _htransfer, hlift⟩ :=
    sha64_success_prefix_storageEffectRun
      (fs := runtime.main :: runtime.aux)
      (sevm := sevm) (inputWord := 0) (outputWord := nodeWord)
      (base := base) (stack := [height])
      (success := .call rootContinuationSlot) (K := K + 48)
      (effects := [])
      hcovered hnodeleg hwarm hpre hdepth (by omega)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have hmemory' : callPost.memory = base.memory.write 640
      (Bytes.sha256 (left.toBytes ++ right.toBytes)).toBytes := by
    simpa only [hzero, hnode, pair.shaInput] using hmemory
  have hreturn' : callPost.returnData =
      (Bytes.sha256 (left.toBytes ++ right.toBytes)).toBytes := by
    simpa only [hzero, pair.shaInput] using hreturn
  have hcarrier : RootMemoryCarrier callPost.memory oldCount size
      (Bytes.sha256 (left.toBytes ++ right.toBytes)) := by
    rw [hmemory']
    exact pair.finishHash
  refine ⟨callPost, hstack, hmemory', ⟨hcarrier⟩,
    by omega, hreturn', hstorage, hcode, haddresses, hkeys,
    hlogs, houtput, herror, ?_⟩
  intro ex htail
  have hcontinuation : Func.StorageEffectRun
      (runtime.main :: runtime.aux) sevm
      (callPost.setMach ⟨[height], callPost.memory, K + 48⟩)
      (.call rootContinuationSlot) ex [] := by
    have hroot : Func.StorageEffectRun
        (runtime.main :: runtime.aux) sevm
        (callPost.setMach ⟨[height], callPost.memory, K + 36⟩)
        rootContinuation ex [] :=
      rootContinuation_storageEffectRun hcarrier htail
    apply Func.StorageEffectRun.call (by rfl)
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega)
      (Devm.burnBy_setMach_gas (G := K + 36)
        (by simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]))
    simpa only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach] using hroot
  have hwhole := hlift hcontinuation
  simpa only [sha64SuccessCost_zero_node,
      show K + 48 + 237 = K + 285 by omega] using hwhole

/-- One selected live root iteration whose only external instruction is the
childless SHA-256 crossing supplied by `hsha`. -/
private theorem rootLoopLive_storageEffectRun
    {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount shiftedSize node height left : B256}
    {K : Nat} {ex : Execution}
    (hmem : RootMemoryCarrier memory oldCount shiftedSize node)
    (hheight : height < (32 : B256))
    (hbit : ((1 : B256) &&& shiftedSize) ≠ 0)
    (hval : base.getStorVal sevm.currentTarget
      (branchBase + height) = left)
    (hsha : Func.StorageEffectRun (runtime.main :: runtime.aux) sevm
      ((afterSload sevm base (branchBase + height)).setMach
        ⟨[height],
          (memory.write 0 left.toBytes).write 32 node.toBytes, K⟩)
      (sha64 0 nodeWord (.call rootContinuationSlot)) ex []) :
    Func.StorageEffectRun (runtime.main :: runtime.aux) sevm
      (base.setMach
        ⟨[height], memory,
          K + 78 + sloadCost sevm base (branchBase + height)⟩)
      rootLoop ex [] := by
  have harm : Func.StorageEffectRun (runtime.main :: runtime.aux) sevm
      (base.setMach
        ⟨[height], memory,
          K + 26 + sloadCost sevm base (branchBase + height)⟩)
      rootLiveStep ex [] := by
    have hafter : Func.StorageEffectRun
        (runtime.main :: runtime.aux) sevm
        ((afterSload sevm base (branchBase + height)).setMach
          ⟨left :: [height], memory, K + 17⟩)
      (mstoreAt 0 +++ loadWord nodeWord +++ mstoreAt 1 +++
          sha64 0 nodeWord (.call rootContinuationSlot)) ex [] := by
      have hsizeM1 : (memory.write 0 left.toBytes).size = 672 := by
        rw [Mem.size_write_of_le (by
          rw [B256.length_toBytes, hmem.size_eq]
          omega), hmem.size_eq]
      have hmod : memory.size % 32 = 0 := by rw [hmem.size_eq]
      have hcovered0 : 0 + 32 ≤ memory.size := by
        rw [hmem.size_eq]
        omega
      have hmodM1 : (memory.write 0 left.toBytes).size % 32 = 0 := by
        rw [hsizeM1]
      have hcoveredNode : 640 + 32 ≤
          (memory.write 0 left.toBytes).size := by
        rw [hsizeM1]
      have hcovered32 : 32 + 32 ≤
          (memory.write 0 left.toBytes).size := by
        rw [hsizeM1]
        omega
      have hz : ((0 : B256) * 32).toNat = 0 := by decide +kernel
      have hzeroNat : (0 : B256).toNat = 0 := by decide +kernel
      have hn : (nodeWord * 32).toNat = 640 := by decide +kernel
      have h1 : ((1 : B256) * 32).toNat = 32 := by decide +kernel
      have hext0 : ∀ (d : Devm) (S : List B256) (G : Nat),
          (d.setMach ⟨S, memory, G⟩).extCost
            [⟨0, 32⟩] = 0 := by
        intro d S G
        exact Devm.extCost_zero_of_le hmod
          hcovered0
      have hextNode : ∀ (d : Devm) (S : List B256) (G : Nat),
          (d.setMach
            ⟨S, memory.write 0 left.toBytes, G⟩).extCost
            [⟨640, 32⟩] = 0 := by
        intro d S G
        apply Devm.extCost_zero_of_le
        · exact hmodM1
        · exact hcoveredNode
      have hext32 : ∀ (d : Devm) (S : List B256) (G : Nat),
          (d.setMach ⟨S, memory.write 0 left.toBytes, G⟩).extCost
            [⟨32, 32⟩] = 0 := by
        intro d S G
        exact Devm.extCost_zero_of_le hmodM1
          hcovered32
      have hreadNode : Bytes.toB256
          ((memory.write 0 left.toBytes).read 640 32).1 = node :=
        hmem.read_node_after_write_zero
      have hreadMem :
          ((memory.write 0 left.toBytes).read 640 32).2 =
            memory.write 0 left.toBytes := by
        apply Mem.read_snd_eq_self
        apply memExtSize_of_le
        · rw [hsizeM1]
        · rw [hsizeM1]
      have hreadNode' : Bytes.toB256
          ((memory.write ((0 : B256) * 32).toNat left.toBytes).read
            (nodeWord * 32).toNat 32).1 = node := by
        simpa only [hz, hn] using hreadNode
      have hreadMem' :
          ((memory.write ((0 : B256) * 32).toNat left.toBytes).read
            (nodeWord * 32).toNat 32).2 = memory.write 0 left.toBytes := by
        simpa only [hz, hn] using hreadMem
      unfold loadWord mstoreAt
      apply Func.StorageEffectRun.next_effectNeutral
        (Ninst.runCompiled_pushB256
          (w := (0 : B256)) (c := gBase) (G := K + 15)
          pushCost_zero
          (by simp only [Devm.gasLeft_setMach, gBase])
          (by simp only [Devm.stack_setMach, List.length_cons,
            List.length_nil]; omega))
        (by rintro ⟨⟩)
        (by rintro operation ⟨⟩)
      simp only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach]
      apply Func.StorageEffectRun.next_effectNeutral
        (Ninst.runCompiled_mstore_of
          (i := (0 : B256)) (v := left) (s := [height])
          (G := K + 12) (e := 0) rfl
          (by
            simpa only [hzeroNat] using
              (hext0 (afterSload sevm base (branchBase + height))
                [0, left, height] (K + 15)))
          (by simp only [Devm.gasLeft_setMach, gVerylow]) rfl)
        (by rintro ⟨⟩)
        (by rintro operation ⟨⟩)
      simp only [Devm.setMach_setMach]
      apply Func.StorageEffectRun.next_effectNeutral
        (Ninst.runCompiled_pushB256
          (w := nodeWord * 32) (c := gVerylow) (G := K + 9)
          (by decide +kernel)
          (by simp only [Devm.gasLeft_setMach, gVerylow])
          (by simp only [Devm.stack_setMach, List.length_cons,
            List.length_nil]; omega))
        (by rintro ⟨⟩)
        (by rintro operation ⟨⟩)
      simp only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach]
      apply Func.StorageEffectRun.next_effectNeutral
        (Ninst.runCompiled_mload_of
          (i := nodeWord * 32) (v := node) (s := [height])
          (c := gVerylow) (G := K + 6)
          (M := memory.write 0 left.toBytes) rfl
          (by
            simp only [hzeroNat, hn,
              hextNode, Nat.add_zero])
          (by simpa only [Devm.memory_setMach, hzeroNat, hn] using hreadNode)
          (by simpa only [Devm.memory_setMach, hzeroNat, hn] using hreadMem)
          (by simp only [Devm.gasLeft_setMach, gVerylow])
          (by simp only [List.length_cons, List.length_nil]; omega))
        (by rintro ⟨⟩)
        (by rintro operation ⟨⟩)
      simp only [Devm.setMach_setMach]
      apply Func.StorageEffectRun.next_effectNeutral
        (Ninst.runCompiled_pushB256
          (w := (1 : B256) * 32) (c := gVerylow) (G := K + 3)
          (by decide +kernel)
          (by simp only [Devm.gasLeft_setMach, gVerylow])
          (by simp only [Devm.stack_setMach, List.length_cons,
            List.length_nil]; omega))
        (by rintro ⟨⟩)
        (by rintro operation ⟨⟩)
      simp only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach]
      apply Func.StorageEffectRun.next_effectNeutral
        (Ninst.runCompiled_mstore_of
          (i := (1 : B256) * 32) (v := node) (s := [height])
          (G := K) (e := 0) rfl
          (by
            simpa only [h1] using
              (hext32 (afterSload sevm base (branchBase + height))
                [(1 : B256) * 32, node, height] (K + 3)))
          (by simp only [Devm.gasLeft_setMach, gVerylow]) rfl)
        (by rintro ⟨⟩)
        (by rintro operation ⟨⟩)
      simpa only [Devm.setMach_setMach, Devm.memory_setMach, h1,
        prepend] using hsha
    unfold rootLiveStep
    apply Func.StorageEffectRun.next_effectNeutral
      (Ninst.runCompiled_dup
        (n := 0) (w := height)
        (G := K + 23 + sloadCost sevm base (branchBase + height)) rfl
        (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)
        (by simp only [Devm.stack_setMach, List.length_cons,
          List.length_nil]; omega))
      (by rintro ⟨⟩)
      (by rintro operation ⟨⟩)
    simp only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach]
    apply Func.StorageEffectRun.next_effectNeutral
      (Ninst.runCompiled_pushB256
        (w := branchBase) (c := gVerylow)
        (G := K + 20 + sloadCost sevm base (branchBase + height))
        (by decide +kernel)
        (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)
        (by simp only [Devm.stack_setMach, List.length_cons,
          List.length_nil]; omega))
      (by rintro ⟨⟩)
      (by rintro operation ⟨⟩)
    simp only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach]
    apply Func.StorageEffectRun.next_effectNeutral
      (Ninst.runCompiled_binary
        (r := .add) (f := (· + ·))
        (cost := gVerylow) (x := branchBase) (y := height)
        (v := branchBase + height) (s := [height])
        (G := K + 17 + sloadCost sevm base (branchBase + height))
        (by rintro ⟨⟩) rfl rfl rfl
        (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)
        (by simp only [List.length_cons, List.length_nil]; omega))
      (by rintro ⟨⟩)
      (by rintro operation ⟨⟩)
    simp only [Devm.setMach_setMach, Devm.memory_setMach]
    apply Func.StorageEffectRun.next_effectNeutral
      (rootSload_runCompiled hval
        (by simp only [List.length_cons, List.length_nil]; omega))
      (by rintro ⟨⟩)
      (by rintro operation ⟨⟩)
    simpa only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach] using hafter
  have hoff : (shiftedSizeWord * 32).toNat = 608 := by decide +kernel
  have hmod : memory.size % 32 = 0 := by rw [hmem.size_eq]
  have hread : Bytes.toB256
      (memory.read (shiftedSizeWord * 32).toNat 32).1 = shiftedSize := by
    rw [hoff, hmem.read_shiftedSize, B256.toB256_toBytes]
  have hreadMem :
      (memory.read (shiftedSizeWord * 32).toNat 32).2 = memory := by
    rw [hoff]
    apply Mem.read_snd_eq_self
    exact memExtSize_of_le hmod (by rw [hmem.size_eq]; omega)
  have hextLoad : ∀ (d : Devm) (S : List B256) (G : Nat),
      (d.setMach ⟨S, memory, G⟩).extCost
        [⟨(shiftedSizeWord * 32).toNat, 32⟩] = 0 := by
    intro d S G
    exact Devm.extCost_zero_of_le hmod
      (by rw [hoff, hmem.size_eq]; omega)
  unfold rootLoop loadWord
  storage_effect_run (9) [1, 3, ((1 : B256) &&& shiftedSize)]
  case h_val => simp [B256.ltCheck, hheight]
  case h_val =>
    rw [hread]
    change ((1 : B256) &&& shiftedSize) =
      ((1 : B256) &&& shiftedSize)
    rfl
  all_goals try { simp only [hextLoad, gVerylow, Nat.add_zero] }
  apply Func.storageEffectRun_branch_succ
    (G := K + 26 + sloadCost sevm base (branchBase + height)) hbit rfl
  · simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
    omega
  · simp only [Devm.gasLeft_setMach, gVerylow, gHigh, gJumpdest]
    omega
  · simpa only [Devm.setMach_setMach, Devm.memory_setMach,
      hreadMem] using harm

/-- One selected dead root iteration whose only external instruction is the
childless SHA-256 crossing supplied by `hsha`. -/
private theorem rootLoopDead_storageEffectRun
    {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount shiftedSize node height right : B256}
    {K : Nat} {ex : Execution}
    (hmem : RootMemoryCarrier memory oldCount shiftedSize node)
    (hheight : height < (32 : B256))
    (hbit : ((1 : B256) &&& shiftedSize) = 0)
    (hval : base.getStorVal sevm.currentTarget
      (zeroHashBase + height) = right)
    (hsha : Func.StorageEffectRun (runtime.main :: runtime.aux) sevm
      ((afterSload sevm base (zeroHashBase + height)).setMach
        ⟨[height],
          (memory.write 0 node.toBytes).write 32 right.toBytes, K⟩)
      (sha64 0 nodeWord (.call rootContinuationSlot)) ex []) :
    Func.StorageEffectRun (runtime.main :: runtime.aux) sevm
      (base.setMach
        ⟨[height], memory,
          K + 77 + sloadCost sevm base (zeroHashBase + height)⟩)
      rootLoop ex [] := by
  have harm : Func.StorageEffectRun (runtime.main :: runtime.aux) sevm
      (base.setMach
        ⟨[height], memory,
          K + 26 + sloadCost sevm base (zeroHashBase + height)⟩)
      rootDeadStep ex [] := by
    let M1 := memory.write 0 node.toBytes
    have hafter : Func.StorageEffectRun
        (runtime.main :: runtime.aux) sevm
        ((afterSload sevm base (zeroHashBase + height)).setMach
          ⟨right :: [height], M1, K + 6⟩)
        (mstoreAt 1 +++
          sha64 0 nodeWord (.call rootContinuationSlot)) ex [] := by
      have hsizeM1 : M1.size = 672 := by
        dsimp only [M1]
        rw [Mem.size_write_of_le (by
          rw [B256.length_toBytes, hmem.size_eq]
          omega), hmem.size_eq]
      have hmodM1 : M1.size % 32 = 0 := by rw [hsizeM1]
      have hcovered32 : 32 + 32 ≤ M1.size := by
        rw [hsizeM1]
        omega
      have h1 : ((1 : B256) * 32).toNat = 32 := by decide +kernel
      have hext32 : ∀ (d : Devm) (S : List B256) (G : Nat),
          (d.setMach ⟨S, M1, G⟩).extCost
            [⟨32, 32⟩] = 0 := by
        intro d S G
        exact Devm.extCost_zero_of_le hmodM1
          (by simpa only [h1] using hcovered32)
      unfold mstoreAt
      apply Func.StorageEffectRun.next_effectNeutral
        (Ninst.runCompiled_pushB256
          (w := (1 : B256) * 32) (c := gVerylow) (G := K + 3)
          (by decide +kernel)
          (by simp only [Devm.gasLeft_setMach, gVerylow])
          (by simp only [Devm.stack_setMach, List.length_cons,
            List.length_nil]; omega))
        (by rintro ⟨⟩)
        (by rintro operation ⟨⟩)
      simp only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach]
      apply Func.StorageEffectRun.next_effectNeutral
        (Ninst.runCompiled_mstore_of
          (i := (1 : B256) * 32) (v := right) (s := [height])
          (G := K) (e := 0) rfl
          (by
            simpa only [h1] using
              (hext32 (afterSload sevm base (zeroHashBase + height))
                [(1 : B256) * 32, right, height] (K + 3)))
          (by simp only [Devm.gasLeft_setMach, gVerylow]) rfl)
        (by rintro ⟨⟩)
        (by rintro operation ⟨⟩)
      simpa only [M1, h1, Devm.setMach_setMach, Devm.memory_setMach,
        prepend] using hsha
    have hsload : Func.StorageEffectRun
        (runtime.main :: runtime.aux) sevm
        (base.setMach
          ⟨(zeroHashBase + height) :: [height], M1,
            K + 6 + sloadCost sevm base (zeroHashBase + height)⟩)
        (sload ::: mstoreAt 1 +++
          sha64 0 nodeWord (.call rootContinuationSlot)) ex [] := by
      apply Func.StorageEffectRun.next_effectNeutral
        (rootSload_runCompiled hval
          (by simp only [List.length_cons, List.length_nil]; omega))
        (by rintro ⟨⟩)
        (by rintro operation ⟨⟩)
      simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using hafter
    have hload : Func.StorageEffectRun
        (runtime.main :: runtime.aux) sevm
        (base.setMach
          ⟨[height], M1,
            K + 15 + sloadCost sevm base (zeroHashBase + height)⟩)
        (dup 0 ::: pushB256 zeroHashBase ::: add ::: sload :::
          mstoreAt 1 +++
          sha64 0 nodeWord (.call rootContinuationSlot)) ex [] := by
      apply Func.StorageEffectRun.next_effectNeutral
        (Ninst.runCompiled_dup
          (n := 0) (w := height)
          (G := K + 12 + sloadCost sevm base (zeroHashBase + height)) rfl
          (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)
          (by simp only [Devm.stack_setMach, List.length_cons,
            List.length_nil]; omega))
        (by rintro ⟨⟩)
        (by rintro operation ⟨⟩)
      simp only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach]
      apply Func.StorageEffectRun.next_effectNeutral
        (Ninst.runCompiled_pushB256
          (w := zeroHashBase) (c := gVerylow)
          (G := K + 9 + sloadCost sevm base (zeroHashBase + height))
          (by decide +kernel)
          (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)
          (by simp only [Devm.stack_setMach, List.length_cons,
            List.length_nil]; omega))
        (by rintro ⟨⟩)
        (by rintro operation ⟨⟩)
      simp only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach]
      apply Func.StorageEffectRun.next_effectNeutral
        (Ninst.runCompiled_binary
          (r := .add) (f := (· + ·))
          (cost := gVerylow) (x := zeroHashBase) (y := height)
          (v := zeroHashBase + height) (s := [height])
          (G := K + 6 + sloadCost sevm base (zeroHashBase + height))
          (by rintro ⟨⟩) rfl rfl rfl
          (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)
          (by simp only [List.length_cons, List.length_nil]; omega))
        (by rintro ⟨⟩)
        (by rintro operation ⟨⟩)
      simpa only [Devm.setMach_setMach, Devm.memory_setMach] using hsload
    have hreadNode : Bytes.toB256 (memory.read 640 32).1 = node := by
      rw [hmem.read_node, B256.toB256_toBytes]
    have hreadMem : (memory.read 640 32).2 = memory := by
      apply Mem.read_snd_eq_self
      apply memExtSize_of_le
      · rw [hmem.size_eq]
      · rw [hmem.size_eq]
    have hmod : memory.size % 32 = 0 := by rw [hmem.size_eq]
    have hcoveredNode : 640 + 32 ≤ memory.size := by
      rw [hmem.size_eq]
    have hcovered0 : 0 + 32 ≤ memory.size := by
      rw [hmem.size_eq]
      omega
    have hn : (nodeWord * 32).toNat = 640 := by decide +kernel
    have hz : ((0 : B256) * 32).toNat = 0 := by decide +kernel
    have hzeroNat : (0 : B256).toNat = 0 := by decide +kernel
    have hreadNode' : Bytes.toB256
        (memory.read (nodeWord * 32).toNat 32).1 = node := by
      simpa only [hn] using hreadNode
    have hreadMem' : (memory.read (nodeWord * 32).toNat 32).2 = memory := by
      simpa only [hn] using hreadMem
    have hextNode : ∀ (d : Devm) (S : List B256) (G : Nat),
        (d.setMach ⟨S, memory, G⟩).extCost
          [⟨640, 32⟩] = 0 := by
      intro d S G
      exact Devm.extCost_zero_of_le hmod
        (by simpa only [hn] using hcoveredNode)
    have hext0 : ∀ (d : Devm) (S : List B256) (G : Nat),
        (d.setMach ⟨S, memory, G⟩).extCost
          [⟨0, 32⟩] = 0 := by
      intro d S G
      exact Devm.extCost_zero_of_le hmod
        (by simpa only [hz] using hcovered0)
    unfold rootDeadStep loadWord mstoreAt
    apply Func.StorageEffectRun.next_effectNeutral
      (Ninst.runCompiled_pushB256
        (w := nodeWord * 32) (c := gVerylow)
        (G := K + 23 + sloadCost sevm base (zeroHashBase + height))
        (by decide +kernel)
        (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)
        (by simp only [Devm.stack_setMach, List.length_cons,
          List.length_nil]; omega))
      (by rintro ⟨⟩)
      (by rintro operation ⟨⟩)
    simp only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach]
    apply Func.StorageEffectRun.next_effectNeutral
      (Ninst.runCompiled_mload_of
        (i := nodeWord * 32) (v := node) (s := [height])
        (c := gVerylow)
        (G := K + 20 + sloadCost sevm base (zeroHashBase + height))
        (M := memory) rfl
        (by simp only [hn, hextNode, Nat.add_zero])
        (by simpa only [Devm.memory_setMach, hn] using hreadNode)
        (by simpa only [Devm.memory_setMach, hn] using hreadMem)
        (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)
        (by simp only [List.length_cons, List.length_nil]; omega))
      (by rintro ⟨⟩)
      (by rintro operation ⟨⟩)
    simp only [Devm.setMach_setMach]
    apply Func.StorageEffectRun.next_effectNeutral
      (Ninst.runCompiled_pushB256
        (w := (0 : B256)) (c := gBase)
        (G := K + 18 + sloadCost sevm base (zeroHashBase + height))
        pushCost_zero
        (by simp only [Devm.gasLeft_setMach, gBase]; omega)
        (by simp only [Devm.stack_setMach, List.length_cons,
          List.length_nil]; omega))
      (by rintro ⟨⟩)
      (by rintro operation ⟨⟩)
    simp only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach]
    apply Func.StorageEffectRun.next_effectNeutral
      (Ninst.runCompiled_mstore_of
        (i := (0 : B256)) (v := node) (s := [height])
        (G := K + 15 + sloadCost sevm base (zeroHashBase + height))
        (e := 0) rfl
        (by simpa only [hzeroNat] using
          (hext0 base [0, node, height]
            (K + 18 + sloadCost sevm base (zeroHashBase + height))))
        (by simp only [Devm.gasLeft_setMach, gVerylow]; omega) rfl)
      (by rintro ⟨⟩)
      (by rintro operation ⟨⟩)
    simpa only [M1, hzeroNat, Devm.setMach_setMach,
      Devm.memory_setMach, mstoreAt, prepend] using hload
  have hoff : (shiftedSizeWord * 32).toNat = 608 := by decide +kernel
  have hmod : memory.size % 32 = 0 := by rw [hmem.size_eq]
  have hread : Bytes.toB256
      (memory.read (shiftedSizeWord * 32).toNat 32).1 = shiftedSize := by
    rw [hoff, hmem.read_shiftedSize, B256.toB256_toBytes]
  have hreadMem :
      (memory.read (shiftedSizeWord * 32).toNat 32).2 = memory := by
    rw [hoff]
    apply Mem.read_snd_eq_self
    exact memExtSize_of_le hmod (by rw [hmem.size_eq]; omega)
  have hextLoad : ∀ (d : Devm) (S : List B256) (G : Nat),
      (d.setMach ⟨S, memory, G⟩).extCost
        [⟨(shiftedSizeWord * 32).toNat, 32⟩] = 0 := by
    intro d S G
    exact Devm.extCost_zero_of_le hmod
      (by rw [hoff, hmem.size_eq]; omega)
  unfold rootLoop loadWord
  storage_effect_run (9) [1, 3, ((1 : B256) &&& shiftedSize)]
  case h_val => simp [B256.ltCheck, hheight]
  case h_val =>
    rw [hread]
    change ((1 : B256) &&& shiftedSize) =
      ((1 : B256) &&& shiftedSize)
    rfl
  all_goals try { simp only [hextLoad, gVerylow, Nat.add_zero] }
  apply Func.storageEffectRun_branch_zero
    (s := [height])
    (G := K + 26 + sloadCost sevm base (zeroHashBase + height))
    (by simp only [Devm.stack_setMach, hbit])
  · simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
    omega
  · simp only [Devm.gasLeft_setMach, gVerylow, gHigh]
    omega
  · simpa only [Devm.setMach_setMach, Devm.memory_setMach,
      hreadMem] using harm

/-- Any active prefix of the root fold preserves the exact empty retained
storage-effect list, including every childless SHA-256 crossing. -/
theorem rootLoop_iterations_exists_storageEffectRun
    {sevm : Sevm} {origin base : Devm}
    {memory : Mem} {oldCount : B256} {s : RootLoopState}
    {stor : Stor} {n K : Nat} {P : Execution → Prop}
    (carrier : RootLoopCarrier origin base memory oldCount s)
    (horiginStor : Devm.getStor origin sevm.currentTarget = stor)
    (hactive : RootLoopActive sevm.currentTarget stor n s)
    (hnodeleg : getDelegatedCodeAddress (origin.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ origin.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound :
      K + rootLoopGas sevm.currentTarget stor n s < 2 ^ 256)
    (htail :
      ∀ {base' : Devm} {memory' : Mem},
        RootLoopCarrier origin base' memory' oldCount
          (rootLoopIter sevm.currentTarget stor n s) →
        ∃ ex, P ex ∧
          Func.StorageEffectRun (runtime.main :: runtime.aux) sevm
            (base'.setMach
              ⟨[(rootLoopIter sevm.currentTarget stor n s).height],
                memory', K⟩)
            rootLoop ex []) :
    ∃ ex, P ex ∧
      Func.StorageEffectRun (runtime.main :: runtime.aux) sevm
        (base.setMach
          ⟨[s.height], memory,
            K + rootLoopGas sevm.currentTarget stor n s⟩)
        rootLoop ex [] := by
  induction n generalizing base memory s with
  | zero =>
      simpa only [rootLoopIter, rootLoopGas, Nat.add_zero] using
        htail carrier
  | succ n ih =>
      change s.height < (32 : B256) ∧
        RootLoopActive sevm.currentTarget stor n
          (s.step sevm.currentTarget stor) at hactive
      rcases hactive with ⟨hheight, hactiveNext⟩
      let next := s.step sevm.currentTarget stor
      let tailGas := rootLoopGas sevm.currentTarget stor n next
      have hnextBound :
          K + rootLoopGas sevm.currentTarget stor n next < 2 ^ 256 := by
        have hstep := rootLoopStepGas_ge sevm.currentTarget s
        have htotal :
            K + rootLoopStepGas sevm.currentTarget s +
              rootLoopGas sevm.currentTarget stor n next < 2 ^ 256 := by
          simpa only [rootLoopGas, Nat.add_assoc, next] using hbound
        omega
      have hshaBound : K + tailGas + 269 < 2 ^ 256 := by
        have hstep := rootLoopStepGas_ge sevm.currentTarget s
        have htotal :
            K + rootLoopStepGas sevm.currentTarget s +
              rootLoopGas sevm.currentTarget stor n next < 2 ^ 256 := by
          simpa only [rootLoopGas, Nat.add_assoc, next] using hbound
        dsimp only [tailGas]
        omega
      have hval :
          base.getStorVal sevm.currentTarget s.key = stor.get s.key := by
        change (Devm.getStor base sevm.currentTarget).get s.key =
          stor.get s.key
        rw [carrier.stor, horiginStor]
      have hnodelegBase :
          getDelegatedCodeAddress (base.getCode 2) = none := by
        rw [carrier.code]
        exact hnodeleg
      have hwarmBase : (2 : Adr) ∈ base.accessedAddresses := by
        rw [carrier.addresses]
        exact hwarm
      by_cases hlive : s.live
      · have hkey : s.key = branchBase + s.height := by
          simp only [RootLoopState.key, if_pos hlive]
        let left := stor.get s.key
        let loaded := afterSload sevm base s.key
        let staged :=
          (memory.write 0 left.toBytes).write 32 s.node.toBytes
        let shaBase := loaded.setMach ⟨[], staged, 0⟩
        have hpair : RootPairMemoryCarrier shaBase.memory
            oldCount s.size left s.node := by
          simpa only [shaBase, staged, Devm.memory_setMach] using
            (RootMemoryCarrier.stagePair
              (left := left) (right := s.node) carrier.mem)
        have hnodelegSha :
            getDelegatedCodeAddress (shaBase.getCode 2) = none := by
          simpa only [shaBase, loaded, Devm.getCode_setMach,
            rootAfterSload_getCode] using hnodelegBase
        have hwarmSha : (2 : Adr) ∈ shaBase.accessedAddresses := by
          change (2 : Adr) ∈ loaded.accessedAddresses
          dsimp only [loaded]
          rw [rootAfterSload_accessedAddresses]
          exact hwarmBase
        obtain ⟨callPost, _hstack, _hmemory, hcallMemNE,
            _hgas, _hreturn, hstorage, hcode, haddresses, hkeys,
            hlogs, houtput, herror, hlift⟩ :=
          rootShaTail_storageEffectRun
            (sevm := sevm) (base := shaBase)
            (height := s.height) (K := K + tailGas)
            hpair hnodelegSha hwarmSha hpre hdepth hshaBound
        rcases hcallMemNE with ⟨hcallMem⟩
        have hcallMem' :
            RootMemoryCarrier callPost.memory oldCount s.size
              (hashPair Bytes.sha256 (stor.get s.key) s.node) := by
          simpa only [left, hashPair] using hcallMem
        have hstorage' : ∀ a, Devm.getStor callPost a =
            Devm.getStor loaded a := by
          intro a
          calc
            Devm.getStor callPost a = Devm.getStor shaBase a := hstorage a
            _ = Devm.getStor loaded a := rfl
        have hcode' : ∀ a, callPost.getCode a = loaded.getCode a := by
          intro a
          calc
            callPost.getCode a = shaBase.getCode a := hcode a
            _ = loaded.getCode a := rfl
        have haddresses' :
            callPost.accessedAddresses = loaded.accessedAddresses := by
          calc
            callPost.accessedAddresses = shaBase.accessedAddresses :=
              haddresses
            _ = loaded.accessedAddresses := rfl
        have hkeys' :
            callPost.accessedStorageKeys = loaded.accessedStorageKeys := by
          calc
            callPost.accessedStorageKeys = shaBase.accessedStorageKeys := hkeys
            _ = loaded.accessedStorageKeys := rfl
        have hlogs' : callPost.logs = loaded.logs := by
          calc
            callPost.logs = shaBase.logs := hlogs
            _ = loaded.logs := rfl
        have houtput' : callPost.output = loaded.output := by
          calc
            callPost.output = shaBase.output := houtput
            _ = loaded.output := rfl
        have herror' : callPost.error = loaded.error := by
          calc
            callPost.error = shaBase.error := herror
            _ = loaded.error := rfl
        have nextCarrier : RootLoopCarrier origin callPost
            (callPost.memory.write 608 (s.size >>> 1).toBytes)
            oldCount next := by
          dsimp only [next, loaded]
          exact rootLoopCarrier_step_live carrier hlive hcallMem'
            hstorage' hcode' haddresses' hkeys' hlogs' houtput' herror'
        obtain ⟨ex, hP, hnextRun⟩ :=
          ih nextCarrier hactiveNext hnextBound (by
            intro base' memory' nextCarrier'
            apply htail
            simpa only [rootLoopIter, next] using nextCarrier')
        have hnextRun' : Func.StorageEffectRun
            (runtime.main :: runtime.aux) sevm
            (callPost.setMach
              ⟨[s.height + 1],
                callPost.memory.write 608 (s.size >>> 1).toBytes,
                K + tailGas⟩)
            rootLoop ex [] := by
          simpa only [tailGas, next, RootLoopState.step] using hnextRun
        have hshaRun := hlift hnextRun'
        have hvalLive :
            base.getStorVal sevm.currentTarget
              (branchBase + s.height) = left := by
          dsimp only [left]
          rw [← hkey]
          exact hval
        have hstage : Func.StorageEffectRun
            (runtime.main :: runtime.aux) sevm
            (base.setMach
              ⟨[s.height], memory,
                (K + tailGas + 285) + 78 +
                  sloadCost sevm base (branchBase + s.height)⟩)
            rootLoop ex [] := by
          apply rootLoopLive_storageEffectRun
            carrier.mem hheight hlive hvalLive
          simpa only [shaBase, loaded, staged, hkey,
            Devm.setMach_setMach, Devm.memory_setMach] using hshaRun
        have hcost :
            sloadCost sevm base (branchBase + s.height) =
              rootReadGas sevm.currentTarget s.keys s.key := by
          rw [← hkey, ← rootReadGas_eq_rootSloadCost, carrier.keys]
        have hgas :
            (K + tailGas + 285) + 78 +
                sloadCost sevm base (branchBase + s.height) =
              K + rootLoopGas sevm.currentTarget stor (n + 1) s := by
          rw [hcost]
          dsimp only [tailGas, next]
          simp only [rootLoopGas, rootLoopStepGas, if_pos hlive]
          omega
        rw [hgas] at hstage
        exact ⟨ex, hP, hstage⟩
      · have hkey : s.key = zeroHashBase + s.height := by
          simp only [RootLoopState.key, if_neg hlive]
        have hbit : ((1 : B256) &&& s.size) = 0 := by
          exact not_ne_iff.mp hlive
        let right := stor.get s.key
        let loaded := afterSload sevm base s.key
        let staged :=
          (memory.write 0 s.node.toBytes).write 32 right.toBytes
        let shaBase := loaded.setMach ⟨[], staged, 0⟩
        have hpair : RootPairMemoryCarrier shaBase.memory
            oldCount s.size s.node right := by
          simpa only [shaBase, staged, Devm.memory_setMach] using
            (RootMemoryCarrier.stagePair
              (left := s.node) (right := right) carrier.mem)
        have hnodelegSha :
            getDelegatedCodeAddress (shaBase.getCode 2) = none := by
          simpa only [shaBase, loaded, Devm.getCode_setMach,
            rootAfterSload_getCode] using hnodelegBase
        have hwarmSha : (2 : Adr) ∈ shaBase.accessedAddresses := by
          change (2 : Adr) ∈ loaded.accessedAddresses
          dsimp only [loaded]
          rw [rootAfterSload_accessedAddresses]
          exact hwarmBase
        obtain ⟨callPost, _hstack, _hmemory, hcallMemNE,
            _hgas, _hreturn, hstorage, hcode, haddresses, hkeys,
            hlogs, houtput, herror, hlift⟩ :=
          rootShaTail_storageEffectRun
            (sevm := sevm) (base := shaBase)
            (height := s.height) (K := K + tailGas)
            hpair hnodelegSha hwarmSha hpre hdepth hshaBound
        rcases hcallMemNE with ⟨hcallMem⟩
        have hcallMem' :
            RootMemoryCarrier callPost.memory oldCount s.size
              (hashPair Bytes.sha256 s.node (stor.get s.key)) := by
          simpa only [right, hashPair] using hcallMem
        have hstorage' : ∀ a, Devm.getStor callPost a =
            Devm.getStor loaded a := by
          intro a
          calc
            Devm.getStor callPost a = Devm.getStor shaBase a := hstorage a
            _ = Devm.getStor loaded a := rfl
        have hcode' : ∀ a, callPost.getCode a = loaded.getCode a := by
          intro a
          calc
            callPost.getCode a = shaBase.getCode a := hcode a
            _ = loaded.getCode a := rfl
        have haddresses' :
            callPost.accessedAddresses = loaded.accessedAddresses := by
          calc
            callPost.accessedAddresses = shaBase.accessedAddresses :=
              haddresses
            _ = loaded.accessedAddresses := rfl
        have hkeys' :
            callPost.accessedStorageKeys = loaded.accessedStorageKeys := by
          calc
            callPost.accessedStorageKeys = shaBase.accessedStorageKeys := hkeys
            _ = loaded.accessedStorageKeys := rfl
        have hlogs' : callPost.logs = loaded.logs := by
          calc
            callPost.logs = shaBase.logs := hlogs
            _ = loaded.logs := rfl
        have houtput' : callPost.output = loaded.output := by
          calc
            callPost.output = shaBase.output := houtput
            _ = loaded.output := rfl
        have herror' : callPost.error = loaded.error := by
          calc
            callPost.error = shaBase.error := herror
            _ = loaded.error := rfl
        have nextCarrier : RootLoopCarrier origin callPost
            (callPost.memory.write 608 (s.size >>> 1).toBytes)
            oldCount next := by
          dsimp only [next, loaded]
          exact rootLoopCarrier_step_dead carrier hlive hcallMem'
            hstorage' hcode' haddresses' hkeys' hlogs' houtput' herror'
        obtain ⟨ex, hP, hnextRun⟩ :=
          ih nextCarrier hactiveNext hnextBound (by
            intro base' memory' nextCarrier'
            apply htail
            simpa only [rootLoopIter, next] using nextCarrier')
        have hnextRun' : Func.StorageEffectRun
            (runtime.main :: runtime.aux) sevm
            (callPost.setMach
              ⟨[s.height + 1],
                callPost.memory.write 608 (s.size >>> 1).toBytes,
                K + tailGas⟩)
            rootLoop ex [] := by
          simpa only [tailGas, next, RootLoopState.step] using hnextRun
        have hshaRun := hlift hnextRun'
        have hvalDead :
            base.getStorVal sevm.currentTarget
              (zeroHashBase + s.height) = right := by
          dsimp only [right]
          rw [← hkey]
          exact hval
        have hstage : Func.StorageEffectRun
            (runtime.main :: runtime.aux) sevm
            (base.setMach
              ⟨[s.height], memory,
                (K + tailGas + 285) + 77 +
                  sloadCost sevm base (zeroHashBase + s.height)⟩)
            rootLoop ex [] := by
          apply rootLoopDead_storageEffectRun
            carrier.mem hheight hbit hvalDead
          simpa only [shaBase, loaded, staged, hkey,
            Devm.setMach_setMach, Devm.memory_setMach] using hshaRun
        have hcost :
            sloadCost sevm base (zeroHashBase + s.height) =
              rootReadGas sevm.currentTarget s.keys s.key := by
          rw [← hkey, ← rootReadGas_eq_rootSloadCost, carrier.keys]
        have hgas :
            (K + tailGas + 285) + 77 +
                sloadCost sevm base (zeroHashBase + s.height) =
              K + rootLoopGas sevm.currentTarget stor (n + 1) s := by
          rw [hcost]
          dsimp only [tailGas, next]
          simp only [rootLoopGas, rootLoopStepGas, if_neg hlive]
          omega
        rw [hgas] at hstage
        exact ⟨ex, hP, hstage⟩

/-- Fixed-outcome compatibility corollary of the existential exact-effect
root-fold carrier. -/
theorem rootLoop_iterations_storageEffectRun
    {sevm : Sevm} {origin base : Devm}
    {memory : Mem} {oldCount : B256} {s : RootLoopState}
    {stor : Stor} {n K : Nat} {ex : Execution}
    (carrier : RootLoopCarrier origin base memory oldCount s)
    (horiginStor : Devm.getStor origin sevm.currentTarget = stor)
    (hactive : RootLoopActive sevm.currentTarget stor n s)
    (hnodeleg : getDelegatedCodeAddress (origin.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ origin.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound :
      K + rootLoopGas sevm.currentTarget stor n s < 2 ^ 256)
    (htail :
      ∀ {base' : Devm} {memory' : Mem},
        RootLoopCarrier origin base' memory' oldCount
          (rootLoopIter sevm.currentTarget stor n s) →
        Func.StorageEffectRun (runtime.main :: runtime.aux) sevm
          (base'.setMach
            ⟨[(rootLoopIter sevm.currentTarget stor n s).height],
              memory', K⟩)
          rootLoop ex []) :
    Func.StorageEffectRun (runtime.main :: runtime.aux) sevm
      (base.setMach
        ⟨[s.height], memory,
          K + rootLoopGas sevm.currentTarget stor n s⟩)
      rootLoop ex [] := by
  obtain ⟨ex', hex, hrun⟩ :=
    rootLoop_iterations_exists_storageEffectRun
      (P := fun ex' => ex' = ex) carrier horiginStor hactive
      hnodeleg hwarm hpre hdepth hbound
      (by
        intro base' memory' hcarrier
        exact ⟨ex, rfl, htail hcarrier⟩)
  subst ex'
  exact hrun

/-- The finishing return suffix is source-local, childless, and retains no
storage effect. -/
private theorem rootFinishReturn_storageEffectRun
    {sevm : Sevm} {base : Devm}
    {memory : Mem} {digest : B256} {G : Nat}
    (hsize : memory.size = 672)
    (hread : Bytes.toB256 (memory.read 640 32).1 = digest) :
    Func.StorageEffectRun (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], memory, G + 16⟩)
      (loadWord nodeWord +++ mstoreAt 0 +++ returnMemoryRange 0 32)
      (.ok (rootFinishPost base memory digest G)) [] := by
  have hrun := rootFinishReturn_runCompiled
    (fs := runtime.main :: runtime.aux) (sevm := sevm)
    (base := base) (memory := memory) (digest := digest) (G := G)
    hsize hread
  have hrunTo := Func.RunCompiledTo.of_runCompiled hrun
  exact Func.StorageEffectRun.of_noRawSstorePath
    (Func.RunCompiledTo.NoRawSstorePath.of_entrySstoreFree_reachableExecFree
      (program := runtime) (members := []) hrunTo
      (by decide +kernel) (by decide +kernel))

private theorem rootFinishShaReturn_storageEffectRun
    {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount node : B256} {G : Nat}
    (carrier : RootFinishMemoryCarrier memory oldCount node)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound : G + 237 < 2 ^ 256) :
    ∃ post,
      Func.StorageEffectRun (runtime.main :: runtime.aux) sevm
        (base.setMach ⟨[], memory, G + 253⟩)
        (sha64 0 nodeWord
          (loadWord nodeWord +++ mstoreAt 0 +++
            returnMemoryRange 0 32))
        (.ok post) [] ∧
      post.stack = [] ∧
      post.gasLeft = G ∧
      post.output =
        (mixIn Bytes.sha256 node oldCount.toNat).toBytes ∧
      Bytes.toB256 post.output =
        mixIn Bytes.sha256 node oldCount.toNat ∧
      post.returnData =
        (mixIn Bytes.sha256 node oldCount.toNat).toBytes ∧
      (∀ a, Devm.getStor post a = Devm.getStor base a) ∧
      (∀ a, post.getCode a = base.getCode a) ∧
      post.accessedAddresses = base.accessedAddresses ∧
      post.accessedStorageKeys = base.accessedStorageKeys ∧
      post.logs = base.logs ∧
      post.error = base.error := by
  let digest := mixIn Bytes.sha256 node oldCount.toNat
  let shaBase := base.setMach ⟨[], memory, G + 253⟩
  have hzero : ((0 : B256) * 32).toNat = 0 := by decide +kernel
  have hnode : (nodeWord * 32).toNat = 640 := by decide +kernel
  have hcovered : memExtsSize shaBase.memory.size
      [⟨((0 : B256) * 32).toNat, 64⟩,
        ⟨(nodeWord * 32).toNat, 32⟩] = shaBase.memory.size := by
    rw [hzero, hnode]
    change memExtsSize memory.size [⟨0, 64⟩, ⟨640, 32⟩] = memory.size
    rw [carrier.size_eq]
    decide +kernel
  obtain ⟨callPost, _hstack, hmemory, _hgas, hreturnData,
      hstorage, hcode, haddresses, hkeys,
      hlogs, _houtput, herror, _htransfer, hlift⟩ :=
    sha64_success_prefix_storageEffectRun
      (fs := runtime.main :: runtime.aux)
      (sevm := sevm) (base := shaBase)
      (inputWord := 0) (outputWord := nodeWord)
      (stack := []) (success :=
        loadWord nodeWord +++ mstoreAt 0 +++ returnMemoryRange 0 32)
      (K := G + 16) (effects := []) hcovered
      (by simpa only [shaBase, Devm.getCode_setMach] using hnodeleg)
      (by change (2 : Adr) ∈ base.accessedAddresses; exact hwarm)
      hpre hdepth (by omega)
      (by simp only [List.length_nil]; omega)
  have hmemory' : callPost.memory = memory.write 640 digest.toBytes := by
    simpa only [shaBase, Devm.memory_setMach, hzero, hnode,
      carrier.shaInput, digest, mixIn] using hmemory
  have hreturnData' : callPost.returnData = digest.toBytes := by
    simpa only [shaBase, Devm.memory_setMach, hzero,
      carrier.shaInput, digest, mixIn] using hreturnData
  have hsizeCall : callPost.memory.size = 672 := by
    rw [hmemory']
    rw [Mem.size_write_of_le (by
      rw [B256.length_toBytes, carrier.size_eq]), carrier.size_eq]
  have hwriteReads :
      Mem.Reads (memory.write 640 digest.toBytes)
        (Bytes.writeAt carrier.image 640 digest.toBytes) :=
    Mem.Reads.write carrier.wf carrier.reads 640 digest.toBytes
  have hreadBytes :
      ((memory.write 640 digest.toBytes).read 640 32).1 =
        digest.toBytes := by
    rw [Mem.Reads.read hwriteReads]
    simpa only [B256.length_toBytes] using
      (Bytes.sliceD_writeAt carrier.image digest.toBytes 640)
  have hreadCall :
      Bytes.toB256 (callPost.memory.read 640 32).1 = digest := by
    rw [hmemory', hreadBytes, B256.toB256_toBytes]
  let post := rootFinishPost callPost callPost.memory digest G
  have htail : Func.StorageEffectRun
      (runtime.main :: runtime.aux) sevm
      (callPost.setMach ⟨[], callPost.memory, G + 16⟩)
      (loadWord nodeWord +++ mstoreAt 0 +++
        returnMemoryRange 0 32) (.ok post) [] :=
    rootFinishReturn_storageEffectRun hsizeCall hreadCall
  have hwhole : Func.StorageEffectRun
      (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], memory, G + 253⟩)
      (sha64 0 nodeWord
        (loadWord nodeWord +++ mstoreAt 0 +++
          returnMemoryRange 0 32)) (.ok post) [] := by
    have hrun := hlift htail
    simpa only [shaBase, Devm.setMach_setMach,
      Devm.memory_setMach, sha64SuccessCost_zero_node] using hrun
  refine ⟨post, hwhole, ?_⟩
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · change Bytes.toB256 digest.toBytes = digest
    exact B256.toB256_toBytes digest
  constructor
  · change callPost.returnData = digest.toBytes
    exact hreturnData'
  constructor
  · intro a
    calc
      Devm.getStor post a = Devm.getStor callPost a := rfl
      _ = Devm.getStor shaBase a := hstorage a
      _ = Devm.getStor base a := rfl
  constructor
  · intro a
    calc
      post.getCode a = callPost.getCode a := rfl
      _ = shaBase.getCode a := hcode a
      _ = base.getCode a := rfl
  constructor
  · calc
      post.accessedAddresses = callPost.accessedAddresses := rfl
      _ = shaBase.accessedAddresses := haddresses
      _ = base.accessedAddresses := rfl
  constructor
  · calc
      post.accessedStorageKeys = callPost.accessedStorageKeys := rfl
      _ = shaBase.accessedStorageKeys := hkeys
      _ = base.accessedStorageKeys := rfl
  constructor
  · calc
      post.logs = callPost.logs := rfl
      _ = shaBase.logs := hlogs
      _ = base.logs := rfl
  · calc
      post.error = callPost.error := rfl
      _ = shaBase.error := herror
      _ = base.error := rfl

private theorem rootFinish_storageEffectRun
    {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount shiftedSize node height : B256} {G : Nat}
    (hmem : RootMemoryCarrier memory oldCount shiftedSize node)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound : G + 237 < 2 ^ 256) :
    ∃ post,
      Func.StorageEffectRun (runtime.main :: runtime.aux) sevm
        (base.setMach ⟨[height], memory, G + 391⟩)
        rootFinish (.ok post) [] ∧
      post.stack = [] ∧
      post.gasLeft = G ∧
      post.output =
        (mixIn Bytes.sha256 node oldCount.toNat).toBytes ∧
      Bytes.toB256 post.output =
        mixIn Bytes.sha256 node oldCount.toNat ∧
      post.returnData =
        (mixIn Bytes.sha256 node oldCount.toNat).toBytes ∧
      (∀ a, Devm.getStor post a = Devm.getStor base a) ∧
      (∀ a, post.getCode a = base.getCode a) ∧
      post.accessedAddresses = base.accessedAddresses ∧
      post.accessedStorageKeys = base.accessedStorageKeys ∧
      post.logs = base.logs ∧
      post.error = base.error := by
  let carrier := hmem.stageFinish
  obtain ⟨post, hsha, hfacts⟩ :=
    rootFinishShaReturn_storageEffectRun
      (sevm := sevm) (base := base) (G := G)
      carrier hnodeleg hwarm hpre hdepth hbound
  have hrun : Func.StorageEffectRun
      (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[height], memory, G + 391⟩)
      rootFinish (.ok post) [] := by
    let stopPost := base.setMach
      ⟨[], rootFinishStagedMemory memory oldCount node, G + 253⟩
    have hstop : Func.RunCompiled (runtime.main :: runtime.aux) sevm
        stopPost Func.stop stopPost := Func.RunCompiled.last rfl
    have hprefixRun : Func.RunCompiledTo
        (runtime.main :: runtime.aux) sevm
        (base.setMach ⟨[height], memory, G + 391⟩)
        (pop ::: loadWord nodeWord +++ mstoreAt 0 +++
          pushB256 0 ::: mstoreAt 1 +++
          loadWord oldCountWord +++ storeLe64At 32 +++ Func.stop)
        (.ok stopPost) := by
      apply Func.RunCompiledTo.of_runCompiled
      simpa only [show G + 253 + 138 = G + 391 by omega] using
        (rootFinishPrefix_runCompiled
          (fs := runtime.main :: runtime.aux) (sevm := sevm)
          (base := base) (height := height) (G := G + 253)
          hmem hstop)
    have hprefix :
        Func.RunCompiledTo.SuccessfulStopPrefix hprefixRun := by
      apply Func.RunCompiledTo.SuccessfulStopPrefix.of_execFree hprefixRun
      · simp [loadWord, mstoreAt, storeLe64At, prepend, Func.stop,
          funcExecFree, Ninst.pushB256]
      · simp [loadWord, mstoreAt, storeLe64At, prepend, Func.stop,
          Func.LocalSstoreFree, Ninst.pushB256]
      · simp [loadWord, mstoreAt, storeLe64At, prepend, Func.stop,
          Func.SuccessStopOnly, Ninst.pushB256]
    have hspliced := hprefix.splice hsha
    simpa only [rootFinish, Func.stop, Func.replaceStopWith_prepend,
        Func.replaceStopWith] using hspliced
  exact ⟨post, hrun, hfacts⟩

/-- The selected height-32 terminal dispatch is storage-effect neutral. -/
private theorem rootLoopFinish32_dispatch_storageEffectRun
    {sevm : Sevm} {base : Devm}
    {memory : Mem}
    {stack : List B256} {K : Nat} {ex : Execution}
    (hroom : stack.length < 1022)
    (hfinish : Func.StorageEffectRun (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨(32 : B256) :: stack, memory, K⟩)
      rootFinish ex []) :
    Func.StorageEffectRun (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨(32 : B256) :: stack, memory, K + 25⟩)
      rootLoop ex [] := by
  unfold rootLoop
  storage_effect_run (4) [0]
  all_goals try {
    simp only [Devm.stack_setMach, List.length_cons]
    omega }
  apply Func.storageEffectRun_branch_zero
    (s := (32 : B256) :: stack) (G := K)
    (by simp only [Devm.stack_setMach])
  · simp only [Devm.stack_setMach, List.length_cons]
    omega
  · simp only [Devm.gasLeft_setMach, gVerylow, gHigh]
    omega
  · simpa only [Devm.setMach_setMach, Devm.memory_setMach] using hfinish

/-- Initialize the three root registers and enter the root loop without
retaining a storage effect. -/
private theorem getDepositRootEndpoint_prefix_storageEffectRun
    {sevm : Sevm} {base : Devm} {count : B256} {K : Nat}
    {ex : Execution}
    (hvalue : base.getStorVal sevm.currentTarget depositCountSlot = count)
    (htail : Func.StorageEffectRun (runtime.main :: runtime.aux) sevm
      ((afterSload sevm base depositCountSlot).setMach
        ⟨[0], rootInitialMemory count, K⟩)
      rootLoop ex []) :
    Func.StorageEffectRun (runtime.main :: runtime.aux) sevm
      (base.setMach
        ⟨[], Mem.empty, K + getDepositRootPrefixGas sevm base⟩)
      getDepositRootEndpoint ex [] := by
  let loaded := afterSload sevm base depositCountSlot
  let M1 := Mem.empty.write 576 count.toBytes
  let M2 := M1.write 608 count.toBytes
  have hsize1 : M1.size = 608 := by
    dsimp only [M1]
    rw [Mem.size_write_word_at]
    decide +kernel
  have hsize2 : M2.size = 640 := by
    dsimp only [M2]
    rw [Mem.size_write_word_at, hsize1]
    decide +kernel
  unfold getDepositRootEndpoint
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256
      (w := depositCountSlot) (c := gVerylow)
      (G := K + 100 + sloadCost sevm base depositCountSlot)
      (by unfold depositCountSlot; decide +kernel)
      (by simp only [Devm.gasLeft_setMach, getDepositRootPrefixGas,
        gVerylow]; omega)
      (by simp only [Devm.stack_setMach, List.length_nil]; omega))
    (by rintro ⟨⟩)
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (rootSload_runCompiled
      (stack := []) (memory := Mem.empty) (G := K + 100)
      hvalue (by simp only [List.length_nil]; omega))
    (by rintro ⟨⟩)
    (by rintro operation ⟨⟩)
  change Func.StorageEffectRun (runtime.main :: runtime.aux) sevm
    (loaded.setMach ⟨[count], Mem.empty, K + 100⟩) _ ex []
  storage_effect_run (9) [57, 3, 3]
  case h_ext =>
    exact Devm.extCost_of_size (N := Mem.empty)
      (i := (oldCountWord * 32).toNat) (sz := 32)
      rfl (by unfold oldCountWord; decide +kernel)
  case h_ext =>
    exact Devm.extCost_of_size (N := M1)
      (i := (shiftedSizeWord * 32).toNat) (sz := 32)
      hsize1 (by unfold shiftedSizeWord; decide +kernel)
  case h_ext =>
    exact Devm.extCost_of_size (N := M2)
      (i := (nodeWord * 32).toNat) (sz := 32)
      hsize2 (by unfold nodeWord; decide +kernel)
  case tail =>
    apply Func.StorageEffectRun.call (by rfl)
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega)
      (Devm.burnBy_setMach_gas (G := K)
        (by simp only [Devm.gasLeft_setMach, gVerylow, gMid,
          gJumpdest]; omega))
    simpa only [loaded, rootInitialMemory,
        show (oldCountWord * 32).toNat = 576 by decide +kernel,
        show (shiftedSizeWord * 32).toNat = 608 by decide +kernel,
        show (nodeWord * 32).toNat = 640 by decide +kernel,
        Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using htail

/-- Exact successful internal execution of `get_deposit_root`. -/
theorem getDepositRootEndpoint_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {stor : Stor} {count G : Nat}
    (hstor : Devm.getStor base sevm.currentTarget = stor)
    (hcountValue :
      base.getStorVal sevm.currentTarget depositCountSlot =
        Nat.toB256 count)
    (hcount : count < 2 ^ 32)
    (hzero : ZeroHashesCorrect stor)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound :
      G + 416 +
          rootLoopGas sevm.currentTarget stor 32
            (rootInitialLoopState
              (afterSload sevm base depositCountSlot)
              (Nat.toB256 count)) <
        2 ^ 256)
    (hrootContinuation :
      fs[rootContinuationSlot]? = some rootContinuation)
    (hrootLoop : fs[rootLoopSlot]? = some rootLoop) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach
          ⟨[], Mem.empty,
            G + 416 +
                rootLoopGas sevm.currentTarget stor 32
                  (rootInitialLoopState
                    (afterSload sevm base depositCountSlot)
                    (Nat.toB256 count)) +
              getDepositRootPrefixGas sevm base⟩)
        getDepositRootEndpoint post ∧
      post.stack = [] ∧
      post.gasLeft = G ∧
      post.output =
        (mixIn Bytes.sha256
          (climb Bytes.sha256 (accOfStor stor).branch 32 0 count 0)
          count).toBytes ∧
      Bytes.toB256 post.output =
        mixIn Bytes.sha256
          (climb Bytes.sha256 (accOfStor stor).branch 32 0 count 0)
          count ∧
      post.returnData =
        (mixIn Bytes.sha256
          (climb Bytes.sha256 (accOfStor stor).branch 32 0 count 0)
          count).toBytes ∧
      (∀ a, Devm.getStor post a = Devm.getStor base a) ∧
      (∀ a, post.getCode a = base.getCode a) ∧
      post.accessedAddresses = base.accessedAddresses ∧
      post.accessedStorageKeys =
        (rootLoopIter sevm.currentTarget stor 32
          (rootInitialLoopState
            (afterSload sevm base depositCountSlot)
            (Nat.toB256 count))).keys ∧
      post.logs = base.logs ∧
      post.error = base.error := by
  let loaded := afterSload sevm base depositCountSlot
  let initial := rootInitialLoopState loaded (Nat.toB256 count)
  let final := rootLoopIter sevm.currentTarget stor 32 initial
  let node :=
    climb Bytes.sha256 (accOfStor stor).branch 32 0 count 0
  let Good : Devm → Prop := fun post =>
    post.stack = [] ∧
    post.gasLeft = G ∧
    post.output = (mixIn Bytes.sha256 node count).toBytes ∧
    Bytes.toB256 post.output = mixIn Bytes.sha256 node count ∧
    post.returnData = (mixIn Bytes.sha256 node count).toBytes ∧
    (∀ a, Devm.getStor post a = Devm.getStor base a) ∧
    (∀ a, post.getCode a = base.getCode a) ∧
    post.accessedAddresses = base.accessedAddresses ∧
    post.accessedStorageKeys = final.keys ∧
    post.logs = base.logs ∧
    post.error = base.error
  let P : Execution → Prop := fun ex =>
    ∃ post, ex = .ok post ∧ Good post
  have hloadedStor :
      Devm.getStor loaded sevm.currentTarget = stor := by
    simpa only [loaded, rootAfterSload_getStor] using hstor
  have hloadedNodeleg :
      getDelegatedCodeAddress (loaded.getCode 2) = none := by
    simpa only [loaded, rootAfterSload_getCode] using hnodeleg
  have hloadedWarm : (2 : Adr) ∈ loaded.accessedAddresses := by
    simpa only [loaded, rootAfterSload_accessedAddresses] using hwarm
  have hactive : RootLoopActive sevm.currentTarget stor 32 initial := by
    simpa only [initial] using
      rootLoopActive_32_initial sevm.currentTarget stor loaded count
        hcount hzero
  have htrace :=
    rootLoopIter_32_initial_eq_climb
      sevm.currentTarget stor loaded count hcount hzero
  have hfinalSize : final.size = 0 := by
    dsimp only [final, initial]
    rw [htrace]
    rfl
  have hfinalNode : final.node = node := by
    dsimp only [final, initial, node]
    rw [htrace]
    rfl
  have hfinalHeight : final.height = (32 : B256) := by
    dsimp only [final, initial]
    rw [htrace]
    rfl
  have hfinishBound : G + 237 < 2 ^ 256 := by
    omega
  obtain ⟨ex, hGood, hloop⟩ :=
    rootLoop_iterations_exists_runCompiledTo
      (P := P)
      (rootInitialLoopCarrier loaded (Nat.toB256 count))
      hloadedStor hactive hloadedNodeleg hloadedWarm hpre hdepth
      (by simpa only [initial] using hbound)
      hrootContinuation hrootLoop
      (by
        intro base' memory' carrier
        have hmem :
            RootMemoryCarrier memory' (Nat.toB256 count) 0 node := by
          have hm := carrier.mem
          change RootMemoryCarrier memory' (Nat.toB256 count)
            final.size final.node at hm
          rw [hfinalSize, hfinalNode] at hm
          exact hm
        have hnodeleg' :
            getDelegatedCodeAddress (base'.getCode 2) = none := by
          rw [carrier.code]
          exact hloadedNodeleg
        have hwarm' : (2 : Adr) ∈ base'.accessedAddresses := by
          rw [carrier.addresses]
          exact hloadedWarm
        obtain ⟨post, hfinish, hstack, hgas, houtput, houtputWord,
            hreturnData, hpostStor, hpostCode, hpostAddresses,
            hpostKeys, hpostLogs, hpostError⟩ :=
          rootFinish_runCompiled
            (fs := fs) (sevm := sevm) (base := base')
            (memory := memory') (oldCount := Nat.toB256 count)
            (shiftedSize := 0) (node := node) (height := (32 : B256))
            (G := G) hmem hnodeleg' hwarm' hpre hdepth hfinishBound
        have hterminal :
            Func.RunCompiledTo fs sevm
              (base'.setMach
                ⟨[(32 : B256)], memory', G + 416⟩)
              rootLoop (.ok post) := by
          apply rootLoopFinish32_dispatch_runCompiledTo
            (stack := []) (K := G + 391) hmem
            (by simp only [List.length_nil]; omega)
          simpa only [show G + 391 + 25 = G + 416 by omega] using
            Func.RunCompiledTo.of_runCompiled hfinish
        refine ⟨.ok post, ?_, ?_⟩
        · refine ⟨post, rfl, ?_⟩
          dsimp only [Good]
          refine ⟨hstack, hgas, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simpa only [
              B256.toNat_toB256_of_lt (by omega : count < 2 ^ 256)]
              using houtput
          · simpa only [
              B256.toNat_toB256_of_lt (by omega : count < 2 ^ 256)]
              using houtputWord
          · simpa only [
              B256.toNat_toB256_of_lt (by omega : count < 2 ^ 256)]
              using hreturnData
          · intro a
            rw [hpostStor, carrier.stor]
            simp only [loaded, rootAfterSload_getStor]
          · intro a
            rw [hpostCode, carrier.code]
            simp only [loaded, rootAfterSload_getCode]
          · rw [hpostAddresses, carrier.addresses]
            simp only [loaded, rootAfterSload_accessedAddresses]
          · rw [hpostKeys, carrier.keys]
          · rw [hpostLogs, carrier.logs]
            simp only [loaded, rootAfterSload_logs]
          · rw [hpostError, carrier.error]
            simp only [loaded, rootAfterSload_error]
        · change Func.RunCompiledTo fs sevm
            (base'.setMach ⟨[final.height], memory', G + 416⟩)
            rootLoop (.ok post)
          simpa only [hfinalHeight] using hterminal)
  have hloop' : Func.RunCompiledTo fs sevm
      (loaded.setMach
        ⟨[0], rootInitialMemory (Nat.toB256 count),
          G + 416 + rootLoopGas sevm.currentTarget stor 32 initial⟩)
      rootLoop ex := by
    simpa only [initial, rootInitialLoopState] using hloop
  have hendpoint :=
    getDepositRootEndpoint_prefix_runCompiledTo
      (K := G + 416 + rootLoopGas sevm.currentTarget stor 32 initial)
      hcountValue hrootLoop hloop'
  dsimp only [P] at hGood
  rcases hGood with ⟨post, rfl, hpost⟩
  refine ⟨post, Func.RunCompiled.of_runCompiledTo_ok ?_, ?_⟩
  · simpa only [loaded, initial] using hendpoint
  · simpa only [Good, node, final, initial, loaded] using hpost

/-- Exact successful internal root execution with an empty retained
storage-effect list across all 33 childless SHA-256 calls. -/
theorem getDepositRootEndpoint_storageEffectRun
    {sevm : Sevm} {base : Devm}
    {stor : Stor} {count G : Nat}
    (hstor : Devm.getStor base sevm.currentTarget = stor)
    (hcountValue :
      base.getStorVal sevm.currentTarget depositCountSlot =
        Nat.toB256 count)
    (hcount : count < 2 ^ 32)
    (hzero : ZeroHashesCorrect stor)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound :
      G + 416 +
          rootLoopGas sevm.currentTarget stor 32
            (rootInitialLoopState
              (afterSload sevm base depositCountSlot)
              (Nat.toB256 count)) <
        2 ^ 256) :
    ∃ post,
      Func.StorageEffectRun (runtime.main :: runtime.aux) sevm
        (base.setMach
          ⟨[], Mem.empty,
            G + 416 +
                rootLoopGas sevm.currentTarget stor 32
                  (rootInitialLoopState
                    (afterSload sevm base depositCountSlot)
                    (Nat.toB256 count)) +
              getDepositRootPrefixGas sevm base⟩)
        getDepositRootEndpoint (.ok post) [] ∧
      post.stack = [] ∧
      post.gasLeft = G ∧
      post.output =
        (mixIn Bytes.sha256
          (climb Bytes.sha256 (accOfStor stor).branch 32 0 count 0)
          count).toBytes ∧
      Bytes.toB256 post.output =
        mixIn Bytes.sha256
          (climb Bytes.sha256 (accOfStor stor).branch 32 0 count 0)
          count ∧
      post.returnData =
        (mixIn Bytes.sha256
          (climb Bytes.sha256 (accOfStor stor).branch 32 0 count 0)
          count).toBytes ∧
      (∀ a, Devm.getStor post a = Devm.getStor base a) ∧
      (∀ a, post.getCode a = base.getCode a) ∧
      post.accessedAddresses = base.accessedAddresses ∧
      post.accessedStorageKeys =
        (rootLoopIter sevm.currentTarget stor 32
          (rootInitialLoopState
            (afterSload sevm base depositCountSlot)
            (Nat.toB256 count))).keys ∧
      post.logs = base.logs ∧
      post.error = base.error := by
  let loaded := afterSload sevm base depositCountSlot
  let initial := rootInitialLoopState loaded (Nat.toB256 count)
  let final := rootLoopIter sevm.currentTarget stor 32 initial
  let node :=
    climb Bytes.sha256 (accOfStor stor).branch 32 0 count 0
  let Good : Devm → Prop := fun post =>
    post.stack = [] ∧
    post.gasLeft = G ∧
    post.output = (mixIn Bytes.sha256 node count).toBytes ∧
    Bytes.toB256 post.output = mixIn Bytes.sha256 node count ∧
    post.returnData = (mixIn Bytes.sha256 node count).toBytes ∧
    (∀ a, Devm.getStor post a = Devm.getStor base a) ∧
    (∀ a, post.getCode a = base.getCode a) ∧
    post.accessedAddresses = base.accessedAddresses ∧
    post.accessedStorageKeys = final.keys ∧
    post.logs = base.logs ∧
    post.error = base.error
  let P : Execution → Prop := fun ex =>
    ∃ post, ex = .ok post ∧ Good post
  have hloadedStor :
      Devm.getStor loaded sevm.currentTarget = stor := by
    simpa only [loaded, rootAfterSload_getStor] using hstor
  have hloadedNodeleg :
      getDelegatedCodeAddress (loaded.getCode 2) = none := by
    simpa only [loaded, rootAfterSload_getCode] using hnodeleg
  have hloadedWarm : (2 : Adr) ∈ loaded.accessedAddresses := by
    simpa only [loaded, rootAfterSload_accessedAddresses] using hwarm
  have hactive : RootLoopActive sevm.currentTarget stor 32 initial := by
    simpa only [initial] using
      rootLoopActive_32_initial sevm.currentTarget stor loaded count
        hcount hzero
  have htrace :=
    rootLoopIter_32_initial_eq_climb
      sevm.currentTarget stor loaded count hcount hzero
  have hfinalSize : final.size = 0 := by
    dsimp only [final, initial]
    rw [htrace]
    rfl
  have hfinalNode : final.node = node := by
    dsimp only [final, initial, node]
    rw [htrace]
    rfl
  have hfinalHeight : final.height = (32 : B256) := by
    dsimp only [final, initial]
    rw [htrace]
    rfl
  have hfinishBound : G + 237 < 2 ^ 256 := by
    omega
  obtain ⟨ex, hGood, hloop⟩ :=
    rootLoop_iterations_exists_storageEffectRun
      (P := P)
      (rootInitialLoopCarrier loaded (Nat.toB256 count))
      hloadedStor hactive hloadedNodeleg hloadedWarm hpre hdepth
      (by simpa only [initial] using hbound)
      (by
        intro base' memory' carrier
        have hmem :
            RootMemoryCarrier memory' (Nat.toB256 count) 0 node := by
          have hm := carrier.mem
          change RootMemoryCarrier memory' (Nat.toB256 count)
            final.size final.node at hm
          rw [hfinalSize, hfinalNode] at hm
          exact hm
        have hnodeleg' :
            getDelegatedCodeAddress (base'.getCode 2) = none := by
          rw [carrier.code]
          exact hloadedNodeleg
        have hwarm' : (2 : Adr) ∈ base'.accessedAddresses := by
          rw [carrier.addresses]
          exact hloadedWarm
        obtain ⟨post, hfinish, hstack, hgas, houtput, houtputWord,
            hreturnData, hpostStor, hpostCode, hpostAddresses,
            hpostKeys, hpostLogs, hpostError⟩ :=
          rootFinish_storageEffectRun
            (sevm := sevm) (base := base')
            (memory := memory') (oldCount := Nat.toB256 count)
            (shiftedSize := 0) (node := node) (height := (32 : B256))
            (G := G) hmem hnodeleg' hwarm' hpre hdepth hfinishBound
        have hterminal :
            Func.StorageEffectRun (runtime.main :: runtime.aux) sevm
              (base'.setMach
                ⟨[(32 : B256)], memory', G + 416⟩)
              rootLoop (.ok post) [] := by
          have hrun := rootLoopFinish32_dispatch_storageEffectRun
            (stack := []) (K := G + 391)
            (by simp only [List.length_nil]; omega) hfinish
          simpa only [show G + 391 + 25 = G + 416 by omega] using hrun
        refine ⟨.ok post, ?_, ?_⟩
        · refine ⟨post, rfl, ?_⟩
          dsimp only [Good]
          refine ⟨hstack, hgas, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simpa only [
              B256.toNat_toB256_of_lt (by omega : count < 2 ^ 256)]
              using houtput
          · simpa only [
              B256.toNat_toB256_of_lt (by omega : count < 2 ^ 256)]
              using houtputWord
          · simpa only [
              B256.toNat_toB256_of_lt (by omega : count < 2 ^ 256)]
              using hreturnData
          · intro a
            rw [hpostStor, carrier.stor]
            simp only [loaded, rootAfterSload_getStor]
          · intro a
            rw [hpostCode, carrier.code]
            simp only [loaded, rootAfterSload_getCode]
          · rw [hpostAddresses, carrier.addresses]
            simp only [loaded, rootAfterSload_accessedAddresses]
          · rw [hpostKeys, carrier.keys]
          · rw [hpostLogs, carrier.logs]
            simp only [loaded, rootAfterSload_logs]
          · rw [hpostError, carrier.error]
            simp only [loaded, rootAfterSload_error]
        · change Func.StorageEffectRun (runtime.main :: runtime.aux) sevm
            (base'.setMach ⟨[final.height], memory', G + 416⟩)
            rootLoop (.ok post) []
          simpa only [hfinalHeight] using hterminal)
  have hloop' : Func.StorageEffectRun (runtime.main :: runtime.aux) sevm
      (loaded.setMach
        ⟨[0], rootInitialMemory (Nat.toB256 count),
          G + 416 + rootLoopGas sevm.currentTarget stor 32 initial⟩)
      rootLoop ex [] := by
    simpa only [initial, rootInitialLoopState] using hloop
  have hendpoint :=
    getDepositRootEndpoint_prefix_storageEffectRun
      (K := G + 416 + rootLoopGas sevm.currentTarget stor 32 initial)
      hcountValue hloop'
  dsimp only [P] at hGood
  rcases hGood with ⟨post, rfl, hpost⟩
  refine ⟨post, ?_, ?_⟩
  · simpa only [loaded, initial] using hendpoint
  · simpa only [Good, node, final, initial, loaded] using hpost

private def getDepositRootLeafRoute : Func :=
  pushB256 getDepositRootSelector ::: eq :::
    ((nonpayableEndpoint getDepositRootEndpoint) <?> Func.revert)

private def getDepositRootInnerRoute : Func :=
  dup 0 ::: pushB256 getDepositRootSelector ::: gt :::
    ((pushB256 getDepositCountSelector ::: eq :::
        ((nonpayableEndpoint getDepositCountEndpoint) <?> Func.revert)) <?>
      getDepositRootLeafRoute)

private def getDepositRootMiddleRoute : Func :=
  dup 0 ::: pushB256 getDepositCountSelector ::: gt :::
    (dispatch (.leaf depositSelector depositEndpoint) <?>
      getDepositRootInnerRoute)

private def getDepositRootRootRoute : Func :=
  dup 0 ::: pushB256 depositSelector ::: gt :::
    (dispatch
      (.leaf supportsInterfaceSelector
        (nonpayableEndpoint supportsInterfaceEndpoint)) <?>
      getDepositRootMiddleRoute)

private def getDepositRootMainRoute : Func :=
  fsig +++ getDepositRootRootRoute

private theorem getDepositRootMainRoute_eq :
    Func.main tree = getDepositRootMainRoute := by
  rfl

private theorem getDepositRootLeafRoute_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {out : Execution} {G : Nat}
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G⟩)
      (nonpayableEndpoint getDepositRootEndpoint) out) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[getDepositRootSelector], Mem.empty, G + 20⟩)
      getDepositRootLeafRoute out := by
  unfold getDepositRootLeafRoute
  have hpushCost :
      pushCost getDepositRootSelector.toBytes.sig = gVerylow := by
    rw [getDepositRootSelector_eq]
    decide +kernel
  have hpushGas :
      (base.setMach
        ⟨[getDepositRootSelector], Mem.empty, G + 20⟩).gasLeft =
          G + 17 + gVerylow := by
    simp only [Devm.gasLeft_setMach, gVerylow]
  have hpushRoom :
      (base.setMach
        ⟨[getDepositRootSelector], Mem.empty, G + 20⟩).stack.length <
          1024 := by
    simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
    omega
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 hpushCost hpushGas hpushRoom) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_binary (r := .eq) (f := B256.eqCheck)
      (cost := gVerylow) (G := G + 14) (v := 1)
      (by rintro ⟨⟩) rfl rfl (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by decide)) ?_
  simp only [Devm.setMach_setMach]
  exact Func.runCompiledTo_branch_succ
    (w := (1 : B256)) (s := []) (G := G)
    (by decide) rfl
    (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    (by
      simp only [Devm.gasLeft_setMach, gVerylow, gHigh, gJumpdest])
    hbody

private theorem getDepositRootInnerRoute_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {out : Execution} {G : Nat}
    (hleaf : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[getDepositRootSelector], Mem.empty, G + 20⟩)
      getDepositRootLeafRoute out) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[getDepositRootSelector], Mem.empty, G + 42⟩)
      getDepositRootInnerRoute out := by
  unfold getDepositRootInnerRoute
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_dup
      (n := 0) (w := getDepositRootSelector) (G := G + 39) rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  have hpushCost :
      pushCost getDepositRootSelector.toBytes.sig = gVerylow := by
    rw [getDepositRootSelector_eq]
    decide +kernel
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (G := G + 36) hpushCost
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_binary (r := .gt) (f := B256.gtCheck)
      (cost := gVerylow) (G := G + 33) (v := 0)
      (by rintro ⟨⟩) rfl rfl
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach]
  exact Func.runCompiledTo_branch_zero
    (s := [getDepositRootSelector]) (G := G + 20)
    rfl
    (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    (by simp only [Devm.gasLeft_setMach, gVerylow, gHigh])
    (by
      simpa only [Devm.setMach_setMach, Devm.memory_setMach] using hleaf)

private theorem getDepositRootMiddleRoute_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {out : Execution} {G : Nat}
    (hinner : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[getDepositRootSelector], Mem.empty, G + 42⟩)
      getDepositRootInnerRoute out) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[getDepositRootSelector], Mem.empty, G + 64⟩)
      getDepositRootMiddleRoute out := by
  unfold getDepositRootMiddleRoute
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_dup
      (n := 0) (w := getDepositRootSelector) (G := G + 61) rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  have hpushCost :
      pushCost getDepositCountSelector.toBytes.sig = gVerylow := by
    rw [getDepositCountSelector_eq]
    decide +kernel
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (G := G + 58) hpushCost
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_binary (r := .gt) (f := B256.gtCheck)
      (cost := gVerylow) (G := G + 55) (v := 0)
      (by rintro ⟨⟩) rfl rfl
      (by
        rw [getDepositCountSelector_eq, getDepositRootSelector_eq]
        decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach]
  exact Func.runCompiledTo_branch_zero
    (s := [getDepositRootSelector]) (G := G + 42)
    rfl
    (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    (by simp only [Devm.gasLeft_setMach, gVerylow, gHigh])
    (by
      simpa only [Devm.setMach_setMach, Devm.memory_setMach] using hinner)

private theorem getDepositRootRootRoute_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {out : Execution} {G : Nat}
    (hmiddle : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[getDepositRootSelector], Mem.empty, G + 64⟩)
      getDepositRootMiddleRoute out) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[getDepositRootSelector], Mem.empty, G + 86⟩)
      getDepositRootRootRoute out := by
  unfold getDepositRootRootRoute
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_dup
      (n := 0) (w := getDepositRootSelector) (G := G + 83) rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  have hpushCost : pushCost depositSelector.toBytes.sig = gVerylow := by
    rw [depositSelector_eq]
    decide +kernel
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (G := G + 80) hpushCost
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_binary (r := .gt) (f := B256.gtCheck)
      (cost := gVerylow) (G := G + 77) (v := 0)
      (by rintro ⟨⟩) rfl rfl
      (by
        rw [depositSelector_eq, getDepositRootSelector_eq]
        decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach]
  exact Func.runCompiledTo_branch_zero
    (s := [getDepositRootSelector]) (G := G + 64)
    rfl
    (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    (by simp only [Devm.gasLeft_setMach, gVerylow, gHigh])
    (by
      simpa only [Devm.setMach_setMach, Devm.memory_setMach] using hmiddle)

private theorem getDepositRootMainRoute_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {out : Execution} {G : Nat}
    (hselector : Sevm.selector sevm = getDepositRootSelector)
    (hroot : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[getDepositRootSelector], Mem.empty, G + 86⟩)
      getDepositRootRootRoute out) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 97⟩)
      (Func.main tree) out := by
  rw [getDepositRootMainRoute_eq]
  unfold getDepositRootMainRoute fsig shiftRight cdl
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (c := gBase) (G := G + 95)
      pushCost_zero
      (by simp only [Devm.gasLeft_setMach, gBase])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_calldataload
      (v := Sevm.dataWord sevm 0) (G := G + 92) rfl rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by decide)) ?_
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
  have hpush224 : pushCost (224 : B256).toBytes.sig = gVerylow := by
    decide +kernel
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (G := G + 89) hpush224
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  have h224 : (224 : B256).toNat = 224 := by
    decide +kernel
  have hselector' :
      Sevm.dataWord sevm 0 >>> (224 : B256).toNat =
        getDepositRootSelector := by
    rw [h224]
    exact hselector
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_binary (r := .shr)
      (f := fun x y => y >>> x.toNat)
      (cost := gVerylow) (G := G + 86)
      (v := getDepositRootSelector)
      (by rintro ⟨⟩) rfl rfl hselector'
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by decide)) ?_
  simp only [Devm.setMach_setMach]
  simpa only [Devm.memory_setMach, prepend] using hroot

private theorem getDepositRootLeafRoute_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {out : Execution} {effects : List (Adr × B256 × B256)} {G : Nat}
    (hbody : Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], Mem.empty, G⟩)
      (nonpayableEndpoint getDepositRootEndpoint) out effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach
        ⟨[getDepositRootSelector], Mem.empty, G + 20⟩)
      getDepositRootLeafRoute out effects := by
  unfold getDepositRootLeafRoute
  have hpushCost :
      pushCost getDepositRootSelector.toBytes.sig = gVerylow := by
    rw [getDepositRootSelector_eq]
    decide +kernel
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256 (G := G + 17) hpushCost
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega))
    (by intro impossible; cases impossible)
    (by intro operation impossible; cases impossible)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_binary (r := .eq) (f := B256.eqCheck)
      (cost := gVerylow) (G := G + 14) (v := 1)
      (by rintro ⟨⟩) rfl rfl (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by decide))
    (by intro impossible; cases impossible)
    (by intro operation impossible; cases impossible)
  simp only [Devm.setMach_setMach]
  exact Func.StorageEffectRun.succ
    (word := (1 : B256)) (by decide)
    (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    (by
      simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using
        Devm.popBurnBy_setMach
          (devm := base.setMach ⟨[(1 : B256)], Mem.empty, G + 14⟩)
          (G := G) rfl
          (by simp only [Devm.gasLeft_setMach, gVerylow, gHigh,
            gJumpdest]))
    hbody

private theorem getDepositRootInnerRoute_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {out : Execution} {effects : List (Adr × B256 × B256)} {G : Nat}
    (hleaf : Func.StorageEffectRun fs sevm
      (base.setMach
        ⟨[getDepositRootSelector], Mem.empty, G + 20⟩)
      getDepositRootLeafRoute out effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach
        ⟨[getDepositRootSelector], Mem.empty, G + 42⟩)
      getDepositRootInnerRoute out effects := by
  unfold getDepositRootInnerRoute
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_dup
      (n := 0) (w := getDepositRootSelector) (G := G + 39) rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega))
    (by intro impossible; cases impossible)
    (by intro operation impossible; cases impossible)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  have hpushCost :
      pushCost getDepositRootSelector.toBytes.sig = gVerylow := by
    rw [getDepositRootSelector_eq]
    decide +kernel
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256 (G := G + 36) hpushCost
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega))
    (by intro impossible; cases impossible)
    (by intro operation impossible; cases impossible)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_binary (r := .gt) (f := B256.gtCheck)
      (cost := gVerylow) (G := G + 33) (v := 0)
      (by rintro ⟨⟩) rfl rfl (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_cons, List.length_nil]; omega))
    (by intro impossible; cases impossible)
    (by intro operation impossible; cases impossible)
  simp only [Devm.setMach_setMach]
  exact Func.StorageEffectRun.zero
    (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    (by
      simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using
        Devm.popBurnBy_setMach
          (devm := base.setMach
            ⟨[(0 : B256), getDepositRootSelector], Mem.empty, G + 33⟩)
          (G := G + 20) rfl
          (by simp only [Devm.gasLeft_setMach, gVerylow, gHigh]))
    (by simpa only [Devm.setMach_setMach, Devm.memory_setMach] using hleaf)

private theorem getDepositRootMiddleRoute_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {out : Execution} {effects : List (Adr × B256 × B256)} {G : Nat}
    (hinner : Func.StorageEffectRun fs sevm
      (base.setMach
        ⟨[getDepositRootSelector], Mem.empty, G + 42⟩)
      getDepositRootInnerRoute out effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach
        ⟨[getDepositRootSelector], Mem.empty, G + 64⟩)
      getDepositRootMiddleRoute out effects := by
  unfold getDepositRootMiddleRoute
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_dup
      (n := 0) (w := getDepositRootSelector) (G := G + 61) rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega))
    (by intro impossible; cases impossible)
    (by intro operation impossible; cases impossible)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  have hpushCost :
      pushCost getDepositCountSelector.toBytes.sig = gVerylow := by
    rw [getDepositCountSelector_eq]
    decide +kernel
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256 (G := G + 58) hpushCost
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega))
    (by intro impossible; cases impossible)
    (by intro operation impossible; cases impossible)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_binary (r := .gt) (f := B256.gtCheck)
      (cost := gVerylow) (G := G + 55) (v := 0)
      (by rintro ⟨⟩) rfl rfl
      (by
        rw [getDepositCountSelector_eq, getDepositRootSelector_eq]
        decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_cons, List.length_nil]; omega))
    (by intro impossible; cases impossible)
    (by intro operation impossible; cases impossible)
  simp only [Devm.setMach_setMach]
  exact Func.StorageEffectRun.zero
    (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    (by
      simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using
        Devm.popBurnBy_setMach
          (devm := base.setMach
            ⟨[(0 : B256), getDepositRootSelector], Mem.empty, G + 55⟩)
          (G := G + 42) rfl
          (by simp only [Devm.gasLeft_setMach, gVerylow, gHigh]))
    (by simpa only [Devm.setMach_setMach, Devm.memory_setMach] using hinner)

private theorem getDepositRootRootRoute_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {out : Execution} {effects : List (Adr × B256 × B256)} {G : Nat}
    (hmiddle : Func.StorageEffectRun fs sevm
      (base.setMach
        ⟨[getDepositRootSelector], Mem.empty, G + 64⟩)
      getDepositRootMiddleRoute out effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach
        ⟨[getDepositRootSelector], Mem.empty, G + 86⟩)
      getDepositRootRootRoute out effects := by
  unfold getDepositRootRootRoute
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_dup
      (n := 0) (w := getDepositRootSelector) (G := G + 83) rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega))
    (by intro impossible; cases impossible)
    (by intro operation impossible; cases impossible)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  have hpushCost : pushCost depositSelector.toBytes.sig = gVerylow := by
    rw [depositSelector_eq]
    decide +kernel
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256 (G := G + 80) hpushCost
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega))
    (by intro impossible; cases impossible)
    (by intro operation impossible; cases impossible)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_binary (r := .gt) (f := B256.gtCheck)
      (cost := gVerylow) (G := G + 77) (v := 0)
      (by rintro ⟨⟩) rfl rfl
      (by
        rw [depositSelector_eq, getDepositRootSelector_eq]
        decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_cons, List.length_nil]; omega))
    (by intro impossible; cases impossible)
    (by intro operation impossible; cases impossible)
  simp only [Devm.setMach_setMach]
  exact Func.StorageEffectRun.zero
    (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    (by
      simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using
        Devm.popBurnBy_setMach
          (devm := base.setMach
            ⟨[(0 : B256), getDepositRootSelector], Mem.empty, G + 77⟩)
          (G := G + 64) rfl
          (by simp only [Devm.gasLeft_setMach, gVerylow, gHigh]))
    (by simpa only [Devm.setMach_setMach, Devm.memory_setMach] using hmiddle)

private theorem getDepositRootMainRoute_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {out : Execution} {effects : List (Adr × B256 × B256)} {G : Nat}
    (hselector : Sevm.selector sevm = getDepositRootSelector)
    (hroot : Func.StorageEffectRun fs sevm
      (base.setMach
        ⟨[getDepositRootSelector], Mem.empty, G + 86⟩)
      getDepositRootRootRoute out effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], Mem.empty, G + 97⟩)
      (Func.main tree) out effects := by
  rw [getDepositRootMainRoute_eq]
  unfold getDepositRootMainRoute fsig shiftRight cdl
  have h224 : (224 : B256).toNat = 224 := by
    decide +kernel
  have hselector' :
      Sevm.dataWord sevm 0 >>> (224 : B256).toNat =
        getDepositRootSelector := by
    rw [h224]
    exact hselector
  storage_effect_run (4) [getDepositRootSelector]
  simpa only [Devm.setMach_setMach, Devm.memory_setMach, prepend,
      show G + 97 - 11 = G + 86 by omega] using hroot

def getDepositRootRouteGas : Nat := 114

/-- Exact-effect analogue of the public root selector route.  The selector
prefix is childless and storage-neutral, so it preserves the endpoint's
retained effect list while exposing the runtime entry burn used by the
execution bridge. -/
theorem getDepositRoot_route_storageEffectRun
    {sevm : Sevm} {base : Devm} {out : Execution}
    {effects : List (Adr × B256 × B256)} {K : Nat}
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hselector : Sevm.selector sevm = getDepositRootSelector)
    (hbody : Func.StorageEffectRun
      (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], Mem.empty, K⟩)
      (nonpayableEndpoint getDepositRootEndpoint) out effects) :
    ∃ mid : Devm,
      Devm.BurnBy gJumpdest
        (base.setMach
          ⟨[], Mem.empty, K + getDepositRootRouteGas⟩) mid ∧
      Func.StorageEffectRun (runtime.main :: runtime.aux)
        sevm mid runtime.main out effects := by
  have hleaf :=
    getDepositRootLeafRoute_storageEffectRun (G := K) hbody
  have hinner :=
    getDepositRootInnerRoute_storageEffectRun (G := K) hleaf
  have hmiddle :=
    getDepositRootMiddleRoute_storageEffectRun (G := K) hinner
  have hroot :=
    getDepositRootRootRoute_storageEffectRun (G := K) hmiddle
  have hmain :=
    getDepositRootMainRoute_storageEffectRun (G := K) hselector hroot
  let pre := base.setMach
    ⟨[], Mem.empty, K + getDepositRootRouteGas⟩
  let mid := base.setMach ⟨[], Mem.empty, K + 113⟩
  let afterSize := base.setMach
    ⟨[sevm.data.length.toB256], Mem.empty, K + 111⟩
  let afterBranch := base.setMach ⟨[], Mem.empty, K + 97⟩
  have hsize : Ninst.RunCompiled sevm mid calldatasize afterSize := by
    simpa only [mid, afterSize, Devm.setMach_setMach,
        Devm.stack_setMach, Devm.memory_setMach] using
      (Ninst.runCompiled_pushItem (sevm := sevm) (devm := mid)
        (r := .calldatasize) (x := Nat.toB256 sevm.data.length)
        (cost := gBase) (G := K + 111) (by rintro ⟨⟩) rfl
        (by simp only [mid, Devm.gasLeft_setMach, gBase])
        (by simp only [mid, Devm.stack_setMach, List.length_nil]; omega))
  have hroom : afterSize.stack.length < 1024 := by
    simp only [afterSize, Devm.stack_setMach, List.length_cons,
      List.length_nil]
    omega
  have hpop : Devm.PopBurnBy [sevm.data.length.toB256]
      (gVerylow + gHigh + gJumpdest) afterSize afterBranch := by
    simpa only [afterSize, afterBranch, Devm.setMach_setMach,
        Devm.stack_setMach, Devm.memory_setMach] using
      Devm.popBurnBy_setMach (devm := afterSize) (G := K + 97)
        (by simp only [afterSize, Devm.stack_setMach])
        (by simp only [afterSize, Devm.gasLeft_setMach,
          gVerylow, gHigh, gJumpdest])
  have hbranch : Func.StorageEffectRun
      (runtime.main :: runtime.aux) sevm afterSize
      (Func.main tree <?> Func.revert) out effects :=
    .succ hnonempty hroom hpop (by
      simpa only [afterBranch] using hmain)
  have hmainEffects : Func.StorageEffectRun
      (runtime.main :: runtime.aux) sevm mid runtime.main out effects := by
    unfold runtime
    exact Func.StorageEffectRun.next_effectNeutral hsize
      (by intro impossible; cases impossible)
      (by intro operation impossible; cases impossible)
      hbranch
  have hentry : Devm.BurnBy gJumpdest pre mid := by
    simpa only [pre, mid, Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach, getDepositRootRouteGas, gJumpdest] using
      Devm.burnBy_setMach_gas
        (devm := pre) (G := K + 113)
        (by simp only [pre, Devm.gasLeft_setMach,
          getDepositRootRouteGas])
  exact ⟨mid, hentry, hmainEffects⟩

/-- Translate the exact empty-effect root selector walk to a bytecode
execution with no raw SSTORE occurrence. -/
theorem getDepositRoot_route_noRawSstore
    {sevm : Sevm} {base : Devm} {out : Execution} {K : Nat}
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hselector : Sevm.selector sevm = getDepositRootSelector)
    (hcode : sevm.code.toList = code)
    (hbody : Func.StorageEffectRun
      (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], Mem.empty, K⟩)
      (nonpayableEndpoint getDepositRootEndpoint) out []) :
    ∃ execution : Exec 0 sevm
        (base.setMach
          ⟨[], Mem.empty, K + getDepositRootRouteGas⟩) out,
      Prog.RunCompiledTo sevm
          (base.setMach
            ⟨[], Mem.empty, K + getDepositRootRouteGas⟩)
          runtime out ∧
      Exec.NoRawSstore execution ∧
      Exec.retainedStorageWrites execution = [] ∧
      Exec.retainedStorageEffectTriples execution = [] ∧
      some sevm.code.toList = Prog.compile runtime := by
  obtain ⟨mid, hentry, hmain⟩ :=
    getDepositRoot_route_storageEffectRun
      hnonempty hselector hbody
  have hprogram : Prog.RunCompiledTo sevm
      (base.setMach
        ⟨[], Mem.empty, K + getDepositRootRouteGas⟩)
      runtime out := ⟨mid, hentry, hmain.run⟩
  have hcompiled : some sevm.code.toList = Prog.compile runtime := by
    rw [hcode, code_compile]
  obtain ⟨execution, executionSafe⟩ :=
    Prog.exists_exec_noRawSstore
      hentry hmain.run hmain.noRawSstorePath hcompiled
  exact ⟨execution, hprogram, executionSafe,
    executionSafe.retainedStorageWrites_eq_nil,
    executionSafe.retainedStorageEffectTriples_eq_nil, hcompiled⟩

/-- The zero-value nonpayable guard preserves the exact retained effects of
the selected root endpoint. -/
theorem getDepositRootEndpoint_nonpayable_zero_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {out : Execution} {effects : List (Adr × B256 × B256)} {G : Nat}
    (hvalue : sevm.value = 0)
    (hroom : base.stack.length < 1023)
    (hbody : Func.StorageEffectRun fs sevm
      (base.setMach ⟨base.stack, base.memory, G⟩)
      getDepositRootEndpoint out effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach
        ⟨base.stack, base.memory, G + nonpayableEndpointZeroGas⟩)
      (nonpayableEndpoint getDepositRootEndpoint) out effects := by
  unfold nonpayableEndpoint nonpayableEndpointZeroGas
  storage_effect_run (1)
  · simp only [Devm.stack_setMach]
    omega
  · rw [hvalue]
    storage_effect_run (1)
    · simp only [Devm.stack_setMach, List.length_cons]
      omega
    case h_arm =>
      simpa only [Devm.setMach_setMach,
          show G + 15 - 15 = G by omega] using hbody

/-- A nonzero-value root call selects the empty-revert arm without entering
the endpoint, and that selected arm has an empty exact effect list. -/
theorem getDepositRootEndpoint_nonpayable_nonzero_storageEffectRun
    {sevm : Sevm} {base : Devm} {G : Nat}
    (hvalue : sevm.value ≠ 0)
    (hroom : base.stack.length < 1023) :
    Func.StorageEffectRun (runtime.main :: runtime.aux) sevm
      (base.setMach
        ⟨base.stack, base.memory, G + nonpayableEndpointRevertGas⟩)
      (nonpayableEndpoint getDepositRootEndpoint)
      (.error (.revert,
        (base.setMach ⟨base.stack, base.memory, G⟩).withOutput [])) [] := by
  unfold nonpayableEndpoint nonpayableEndpointRevertGas
  storage_effect_run (1)
  · simp only [Devm.stack_setMach]
    omega
  · apply Func.StorageEffectRun.succ hvalue
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)
      (by
        simpa only [Devm.setMach_setMach, Devm.stack_setMach,
            Devm.memory_setMach,
            show G + 20 - 2 = G + 18 by omega] using
          Devm.popBurnBy_setMach
            (devm := base.setMach
              ⟨sevm.value :: base.stack, base.memory, G + 18⟩)
            (G := G + 4) rfl
            (by
              simp only [Devm.gasLeft_setMach, gVerylow, gHigh,
                gJumpdest]))
    have hrev : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
        (base.setMach ⟨base.stack, base.memory, G + 4⟩) Func.revert
        (.error (.revert,
          (base.setMach ⟨base.stack, base.memory, G⟩).withOutput [])) := by
      simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using
        (Func.runCompiledTo_revert_func
          (fs := runtime.main :: runtime.aux) (sevm := sevm)
          (devm := base.setMach ⟨base.stack, base.memory, G + 4⟩)
          (G := G) (by simp only [Devm.gasLeft_setMach, gBase])
          (by simp only [Devm.stack_setMach]; exact hroom))
    exact Func.StorageEffectRun.of_noRawSstorePath
      (Func.RunCompiledTo.NoRawSstorePath.of_entrySstoreFree_reachableExecFree
        (program := runtime) (members := []) hrev (by rfl) (by rfl))

/-- Exact compiled selector-tree cost through the root nonpayable wrapper. -/
theorem getDepositRoot_route_runCompiledTo
    {sevm : Sevm} {base : Devm} {out : Execution} {K : Nat}
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hselector : Sevm.selector sevm = getDepositRootSelector)
    (hbody : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], Mem.empty, K⟩)
      (nonpayableEndpoint getDepositRootEndpoint) out) :
    Prog.RunCompiledTo sevm
      (base.setMach ⟨[], Mem.empty, K + getDepositRootRouteGas⟩)
      runtime out := by
  have hleaf :=
    getDepositRootLeafRoute_runCompiledTo (G := K) hbody
  have hinner :=
    getDepositRootInnerRoute_runCompiledTo (G := K) hleaf
  have hmiddle :=
    getDepositRootMiddleRoute_runCompiledTo (G := K) hinner
  have hroot :=
    getDepositRootRootRoute_runCompiledTo (G := K) hmiddle
  have hmain :=
    getDepositRootMainRoute_runCompiledTo (G := K) hselector hroot
  refine Prog.runCompiledTo_intro
    (mid := base.setMach ⟨[], Mem.empty, K + 113⟩)
    (G := K + 113) ?_ rfl ?_
  · simp only [Devm.gasLeft_setMach, getDepositRootRouteGas,
      gJumpdest]
  · unfold runtime
    func_run (1) []
    exact Func.runCompiledTo_branch_succ
      (w := sevm.data.length.toB256) (s := []) (G := K + 97)
      hnonempty rfl
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)
      (by
        simp only [Devm.gasLeft_setMach, gVerylow, gHigh, gJumpdest]
        omega)
      (by
        simpa only [runtime, Devm.setMach_setMach, Devm.memory_setMach]
          using hmain)

/-- Successful specialization of the exact public root route. -/
theorem getDepositRoot_route_runCompiled
    {sevm : Sevm} {base post : Devm} {K : Nat}
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hselector : Sevm.selector sevm = getDepositRootSelector)
    (hbody : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], Mem.empty, K⟩)
      (nonpayableEndpoint getDepositRootEndpoint) post) :
    Prog.RunCompiled sevm
      (base.setMach ⟨[], Mem.empty, K + getDepositRootRouteGas⟩)
      runtime post := by
  rcases getDepositRoot_route_runCompiledTo hnonempty hselector
      (Func.RunCompiledTo.of_runCompiled hbody) with
    ⟨mid, hburn, hmain⟩
  exact ⟨mid, hburn, Func.RunCompiled.of_runCompiledTo_ok hmain⟩

def getDepositRootRuntimeGas
    (sevm : Sevm) (base : Devm) (stor : Stor) (count : Nat) : Nat :=
  416 +
    rootLoopGas sevm.currentTarget stor 32
      (rootInitialLoopState
        (afterSload sevm base depositCountSlot)
        (Nat.toB256 count)) +
    getDepositRootPrefixGas sevm base +
    nonpayableEndpointZeroGas +
    getDepositRootRouteGas

def getDepositRootNonzeroValueRuntimeGas : Nat := 134

/-- A value-carrying root query is rejected before the endpoint reads the
count slot or invokes SHA-256. -/
theorem getDepositRoot_nonzero_value_runCompiledTo
    (sevm : Sevm) (base : Devm) (G : Nat)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hvalue : sevm.value ≠ 0)
    (hselector : Sevm.selector sevm = getDepositRootSelector)
    (hcode : sevm.code.toList = code) :
    Prog.RunCompiledTo sevm
      (base.setMach
        ⟨[], Mem.empty, G + getDepositRootNonzeroValueRuntimeGas⟩)
      runtime
      (.error (.revert,
        (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])) ∧
    some sevm.code.toList = Prog.compile runtime := by
  let routeBase := base.setMach ⟨[], Mem.empty, base.gasLeft⟩
  have hbody := nonpayableEndpoint_nonzero_runCompiledTo
    (fs := runtime.main :: runtime.aux) (sevm := sevm)
    (base := routeBase) (G := G)
    (body := getDepositRootEndpoint) hvalue
    (by simp only [routeBase, Devm.stack_setMach, List.length_nil]; omega)
  have hroute := getDepositRoot_route_runCompiledTo
    (base := base) (K := G + nonpayableEndpointRevertGas)
    hnonempty hselector (by
      simpa only [routeBase, Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using hbody)
  constructor
  · have hboundary :
        G + nonpayableEndpointRevertGas + getDepositRootRouteGas =
          G + getDepositRootNonzeroValueRuntimeGas := by
      simp only [nonpayableEndpointRevertGas, getDepositRootRouteGas,
        getDepositRootNonzeroValueRuntimeGas]
    simpa only [hboundary] using hroute
  · rw [hcode, code_compile]

/-- The selected value-rejecting root route has no raw SSTORE and retains no
storage effect. -/
theorem getDepositRoot_nonzero_value_runCompiledTo_noRawSstore
    (sevm : Sevm) (base : Devm) (G : Nat)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hvalue : sevm.value ≠ 0)
    (hselector : Sevm.selector sevm = getDepositRootSelector)
    (hcode : sevm.code.toList = code) :
    ∃ execution : Exec 0 sevm
        (base.setMach
          ⟨[], Mem.empty, G + getDepositRootNonzeroValueRuntimeGas⟩)
        (.error (.revert,
          (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])),
      Prog.RunCompiledTo sevm
          (base.setMach
            ⟨[], Mem.empty, G + getDepositRootNonzeroValueRuntimeGas⟩)
          runtime
          (.error (.revert,
            (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])) ∧
      Exec.NoRawSstore execution ∧
      Exec.retainedStorageWrites execution = [] ∧
      Exec.retainedStorageEffectTriples execution = [] ∧
      some sevm.code.toList = Prog.compile runtime := by
  let routeBase := base.setMach ⟨[], Mem.empty, base.gasLeft⟩
  have hbodyEffects : Func.StorageEffectRun
      (runtime.main :: runtime.aux) sevm
      (base.setMach
        ⟨[], Mem.empty, G + nonpayableEndpointRevertGas⟩)
      (nonpayableEndpoint getDepositRootEndpoint)
      (.error (.revert,
        (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])) [] := by
    simpa only [routeBase, Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
      (getDepositRootEndpoint_nonpayable_nonzero_storageEffectRun
        (sevm := sevm) (base := routeBase) (G := G) hvalue
        (by
          simp only [routeBase, Devm.stack_setMach, List.length_nil]
          omega))
  obtain ⟨execution, hrun, executionSafe, hwrites, htriples,
      hcompiled⟩ :=
    getDepositRoot_route_noRawSstore
      (base := base) (K := G + nonpayableEndpointRevertGas)
      hnonempty hselector hcode
      hbodyEffects
  have hboundary :
      G + nonpayableEndpointRevertGas + getDepositRootRouteGas =
        G + getDepositRootNonzeroValueRuntimeGas := by
    simp only [nonpayableEndpointRevertGas, getDepositRootRouteGas,
      getDepositRootNonzeroValueRuntimeGas]
  rw [← hboundary]
  exact ⟨execution, hrun, executionSafe, hwrites, htriples, hcompiled⟩

end Blanc.BeaconDeposit
