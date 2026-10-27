import Blanc.Lift.Usdc.InitV1KeyBounds
import Blanc.Lift.Usdc.ProxyWritesHistory
import Blanc.Lift.Usdc.HistoricalMappingKeys

/-!
# Initializer writes at the Pair's rows, from the prefix walks

Every raw `SSTORE` node of an initializer frame (`UsdcInitFrame`) is the end of a reach of its
implementation code from entry `0` (`Reach.sstoreNode_pot`), so the prefix walks classify its
key: `KeysInit06` under `initialize` (V1 `InitReachV1.initV1_reach`, V2-line
`Init06.init_reach_V2`/`V2_1`/`V2_2`), `KeysInitV2` under `initializeV2`
(`InitReachV2.initV2_reach` and its V2_1/V2_2 twins), `KeysInitV2_2` under `initializeV2_2`
(`InitReachV2_2.initV2_2_reach`), or the stored word is zero. The classification holds at
every node of the frame, whatever its outcome.

`InitRowsApart` states, per initializer frame at `P`, that no tracked Pair row is a key of
these classes for that frame's own calldata: fixed slots, payload keys `keccak(slot) + j`
below the frame's decoded lengths, and `initializeV2_2`'s blacklist mapping keys. From it,
`ConfiguredHistoryTraceIn.initRowWritesNonInc` gives `InitRowWritesNonInc`, and
`usdc_pairAllowance_noIncrease_deployed_apart` is `usdc_pairAllowance_noIncrease_deployed`
with that premise in place of `InitRowWritesNonInc`.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- The keys an initializer frame's code writes under its selector, read from the frame's
own calldata: `initialize`'s fixed slots and string payload keys, `initializeV2`'s, and
`initializeV2_2`'s (with its blacklist mapping keys), each under its own selector. Each decoded
length is capped at a bound the walks prove for any reached store: `2 ^ 32` from the solc 0.6
ABI decoders, `2 ^ 160` for `initialize` from V1's memory potential. -/
def InitKeys (sevm : Sevm) (key : B256) : Prop :=
  (initSelWord sevm = 0x3357162b ∧ Init06.KeysInit06 sevm key) ∨
    (initSelWord sevm = 0xd608ea64 ∧ KeysInitV2 sevm key) ∨
    (initSelWord sevm = 0x430239b4 ∧ InitReachV2_2.KeysInitV2_2 sevm key)

/-- **Initializer keys apart from the tracked rows (stated, frame-local).** For every raw
initializer frame at `P`, no tracked Pair row is one of the frame's `InitKeys`.

It is meant for a finite, explicit `Tr`. The fixed slots and mapping keys are apart from a
tracked row unless Keccak collides. The payload keys `keccak(s) + j` (`s ∈ {4, 5, 7}`) form
intervals from three constant bases, of at most `2 ^ 155` words under `initialize` and
`2 ^ 27` under the solc 0.6 decoders; keeping a tracked row out of them is interval
avoidance, decidable by arithmetic for an explicit `Tr`, not a hash-collision fact. -/
def InitRowsApart (P pair : Adr) (Tr : Adr → Prop) (frames : List Exec.Deriv) : Prop :=
  ∀ G ∈ frames, G.sevm.currentTarget = P → UsdcInitFrame G →
    ∀ g, Tr g → ¬ InitKeys G.sevm (allowSlot pair g)

/-- Decide initializer key membership from the original calldata. String payloads
use modular distance from their hash base, not enumeration of their word ranges.
Only the capped blacklist account array is traversed. -/
def checkInitKeys (sevm : Sevm) (key : B256) : Bool :=
  let payload (slot : B256) (length : Nat) :=
    decide ((key - slot.toBytes.keccak).toNat < (length + 31) / 32)
  (decide (initSelWord sevm = 0x3357162b) &&
    (decide (key ∈ ([0, 1, 2, 4, 5, 6, 7, 8] : List B256)) ||
      payload 4 (min (Init06.len06 sevm 4) (2 ^ 160)) ||
      payload 5 (min (Init06.len06 sevm (4 + 32)) (2 ^ 160)) ||
      payload 7 (min (Init06.len06 sevm (4 + 32 + 32)) (2 ^ 160)))) ||
  (decide (initSelWord sevm = 0xd608ea64) &&
    (decide (key = 4 ∨ key = 15 ∨ key = 18) ||
      payload 4 (min (CdStrWrap.cdLen sevm) (2 ^ 32)))) ||
  (decide (initSelWord sevm = 0x430239b4) &&
    (decide (key = 5) || payload 5 (min (InitReachV2_2.strLen sevm) (2 ^ 32)) ||
      (List.range (min (InitReachV2_2.arrLen sevm).toNat (2 ^ 32))).any (fun j =>
        decide (key = mapSlot (InitReachV2_2.acctAt sevm (InitReachV2_2.arrPtr sevm) j) 3 ∨
          key = mapSlot (InitReachV2_2.acctAt sevm (InitReachV2_2.arrPtr sevm) j &&& InitReachV2_2.addrMask) 9)) ||
      @decide (InitReachV2_2.AfterKeys sevm key) (by unfold InitReachV2_2.AfterKeys; infer_instance)))

/-- The check is exact, including modular wraparound and the original decoder caps. -/
theorem checkInitKeys_eq_true (sevm : Sevm) (key : B256) :
    checkInitKeys sevm key = true ↔ InitKeys sevm key := by
  have payload (slot : B256) (length : Nat) (bound : length ≤ 2 ^ 160) :
      (key - slot.toBytes.keccak).toNat < (length + 31) / 32 ↔
        ∃ j : Nat, j < (length + 31) / 32 ∧ key = slot.toBytes.keccak + j.toB256 := by
    constructor
    · intro member
      refine ⟨(key - slot.toBytes.keccak).toNat, member, ?_⟩
      rw [toB256_toNat, B256.add_comm, B256.sub_add_cancel]
    · rintro ⟨j, member, rfl⟩
      have small : j < 2 ^ 256 := by omega
      have base := B256.toNat_lt slot.toBytes.keccak
      simp only [B256.toNat_sub, B256.toNat_add, B256.toNat_toB256_of_lt small, Nat.lo]
      omega
  have capped (length : Nat) : min length (2 ^ 160) ≤ 2 ^ 160 := Nat.min_le_right _ _
  have modern (length : Nat) : min length (2 ^ 32) ≤ 2 ^ 160 := by
    have := Nat.min_le_right length (2 ^ 32)
    omega
  simp only [checkInitKeys, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.any_eq_true, List.mem_range, InitKeys, Init06.KeysInit06, Init06.KeysInit,
    KeysInitV2, KeysV2Len, InitReachV2_2.KeysInitV2_2, InitReachV2_2.BodyKeys,
    InitReachV2_2.LoopKeys]
  rw [payload _ _ (capped _), payload _ _ (capped _), payload _ _ (capped _),
    payload _ _ (modern _), payload _ _ (modern _)]
  simp only [or_assoc, show Bytes.toB256 [4] = (4 : B256) from rfl,
    show Bytes.toB256 [32] = (32 : B256) from rfl]

/-- Finite initializer separation for the exact frame and spender populations.
Frames at other targets or outside the initializer families impose no condition. -/
def checkInitRowsApart (P pair : Adr) (spenders : List Adr) (frames : List Exec.Deriv) : Bool :=
  frames.all fun G =>
    letI : Decidable (UsdcInitFrame G) := by unfold UsdcInitFrame; infer_instance
    if G.sevm.currentTarget = P ∧ UsdcInitFrame G then
      spenders.all fun g => !(checkInitKeys G.sevm (allowSlot pair g))
    else true

theorem checkInitRowsApart_eq_true {P pair : Adr} {spenders : List Adr}
    {frames : List Exec.Deriv} :
    checkInitRowsApart P pair spenders frames = true ↔
      InitRowsApart P pair (fun g => g ∈ spenders) frames := by
  simp only [checkInitRowsApart, List.all_eq_true, InitRowsApart]
  constructor
  · intro checked G member target init g tracked
    have atFrame := checked G member
    simp only [target, init, and_self, ↓reduceIte, List.all_eq_true,
      Bool.not_eq_true', Bool.eq_false_iff, ne_eq, checkInitKeys_eq_true] at atFrame
    exact atFrame g tracked
  · intro apart G member
    split
    · next selected =>
        simp only [List.all_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, checkInitKeys_eq_true]
        exact apart G member selected.1 selected.2
    · rfl

/-- Use an explicit finite spender superset without narrowing the tracked predicate. -/
theorem initRowsApart_of_check {P pair : Adr} {Tr : Adr → Prop}
    {spenders : List Adr} {frames : List Exec.Deriv}
    (included : ∀ g, Tr g → g ∈ spenders)
    (checked : checkInitRowsApart P pair spenders frames = true) :
    InitRowsApart P pair Tr frames := by
  intro G member target init g tracked
  exact (checkInitRowsApart_eq_true.mp checked) G member target init g (included g tracked)

theorem selV1T_root (sevm : Sevm) :
    selV1T.eval (WriteSite.Env.root sevm) = Blanc.Sevm.selector sevm := by
  rw [← dispatchWord_eq_selector]
  unfold Proxy.dispatchWord
  rw [B256.and_comm]
  simp only [selV1T, WriteSite.Term.eval, WriteSite.Op2.eval, WriteSite.Env.root, Sevm.dataWord]
  rfl

theorem selWord_eq_selector (sevm : Sevm) : initSelWord sevm = Blanc.Sevm.selector sevm := by
  unfold initSelWord Blanc.Sevm.selector
  rw [show Bytes.toB256 [0] = (0 : B256) from by decide,
    show (Bytes.toB256 [0xe0]).toNat = 224 from by decide]

theorem selV2T_root_selWord (sevm : Sevm) :
    selV2T.eval (WriteSite.Env.root sevm) = initSelWord sevm := by
  simp only [selV2T, WriteSite.Term.eval, WriteSite.Op2.eval, WriteSite.Env.root, initSelWord,
    Sevm.dataWord]
  rfl

/-- **Every `SSTORE` node of an initializer frame, classified.** At a node under a raw
initializer frame entered at pc `0` without state gas, with empty stack and memory and gas
below `2 ^ 256`, a successful `SSTORE` writes one of the frame's `InitKeys` or zero. -/
theorem initFrame_sstore {G N : Exec.Deriv} (hpc : G.pc = 0)
    (hsg : G.sevm.benvStat.rules.stateGas = none) (fresh : Exec.FreshEntry G.sevm G.devm)
    (gas : G.devm.gasMeasure < 2 ^ 256) (init : UsdcInitFrame G)
    (chain : Exec.Deriv.ParentPrefix G N) {w : Exec.StorageWrite}
    (found : Exec.Deriv.successfulSstore? N = some w) :
    InitKeys G.sevm w.key ∨ w.value = 0 := by
  obtain ⟨hat, rest, hstack⟩ := successfulSstore?_decoded found
  obtain ⟨stack, memory⟩ := fresh
  have erase : ∀ {s d n d'}, StepIn G s d n d' → Ninst.Run s d n d' := fun h => StepIn.toRun h
  have eraseP : ∀ {s d n d'}, FreePtr.PotStep (StepIn G) s d n d' → Ninst.Run s d n d' :=
    fun h => StepIn.toRun h.1
  have use : ∀ {K : B256 → Prop} {T : Conf}, InitStore K T → T.d = N.devm →
      ∀ {L : B256 → Prop}, (∀ k, K k → L k) → L w.key ∨ w.value = 0 := by
    intro K T h e L hL
    rw [← e] at hstack
    exact (h _ _ _ hstack).imp_left (hL _)
  rcases init with ⟨code, sel⟩ | ⟨code, sel⟩ | ⟨code, sel⟩ | ⟨code, sel⟩
  · obtain ⟨T, run, hT, e⟩ := Reach.sstoreNode_pot ImplV1.cert_check hpc code hsg stack memory
      gas chain hat
    have hs : Blanc.Sevm.selector G.sevm = 0x3357162b := by
      rw [← selV1T_root]
      exact List.mem_singleton.mp sel
    exact use (InitReachV1.initV1_reach erase hs run hT) e
      fun _ h => .inl ⟨(selWord_eq_selector _).trans hs, h⟩
  · obtain ⟨T, run, hT, e⟩ := Reach.sstoreNode_pot ImplV2.cert_check hpc code hsg stack memory
      gas chain hat
    change selV2T.eval _ ∈ [0x3357162b, 0xd608ea64] at sel
    rw [selV2T_root_selWord] at sel
    rcases List.mem_cons.mp sel with hs | hs
    · exact use (Init06.init_reach_V2 erase hs run hT) e fun _ h => .inl ⟨hs, h⟩
    · rw [List.mem_singleton] at hs
      exact use (InitReachV2.initV2_reach eraseP hs run hT) e fun _ h => .inr (.inl ⟨hs, h⟩)
  · obtain ⟨T, run, hT, e⟩ := Reach.sstoreNode_pot ImplV2_1.cert_check hpc code hsg stack
      memory gas chain hat
    change selV2T.eval _ ∈ [0x3357162b, 0xd608ea64] at sel
    rw [selV2T_root_selWord] at sel
    rcases List.mem_cons.mp sel with hs | hs
    · exact use (Init06.init_reach_V2_1 erase hs run hT) e fun _ h => .inl ⟨hs, h⟩
    · rw [List.mem_singleton] at hs
      exact use (InitReachV2_1.initV2_reach eraseP hs run hT) e fun _ h => .inr (.inl ⟨hs, h⟩)
  · obtain ⟨T, run, hT, e⟩ := Reach.sstoreNode_pot Impl.cert_check hpc code hsg stack memory
      gas chain hat
    change selV2T.eval _ ∈ [0x3357162b, 0x430239b4, 0xd608ea64] at sel
    rw [selV2T_root_selWord] at sel
    rcases List.mem_cons.mp sel with hs | hs
    · exact use (Init06.init_reach_V2_2 erase hs run hT) e fun _ h => .inl ⟨hs, h⟩
    rcases List.mem_cons.mp hs with hs | hs
    · exact use (InitReachV2_2.initV2_2_reach eraseP hs run hT) e
        fun _ h => .inr (.inr ⟨hs, h⟩)
    · rw [List.mem_singleton] at hs
      exact use (InitReachV2_2.initV2_reach eraseP hs run hT) e fun _ h => .inr (.inl ⟨hs, h⟩)

/-- Every actual initializer store avoids the implementation slot, except possibly
the explicitly identified mapping writes of `initializeV2_2`. No separation of
unexecuted calldata keys is assumed. -/
theorem initFrame_sstore_ne_implSlot_or_migration {G N : Exec.Deriv} (hpc : G.pc = 0)
    (hsg : G.sevm.benvStat.rules.stateGas = none) (fresh : Exec.FreshEntry G.sevm G.devm)
    (gas : G.devm.gasMeasure < 2 ^ 256) (init : UsdcInitFrame G)
    (chain : Exec.Deriv.ParentPrefix G N) {w : Exec.StorageWrite}
    (found : Exec.Deriv.successfulSstore? N = some w) :
    w.key ≠ implSlot ∨ G.sevm.code = Impl.code ∧ initSelWord G.sevm = 0x430239b4 ∧
      InitReachV2_2.MigrationKey G.sevm w.key := by
  obtain ⟨hat, rest, hstack⟩ := successfulSstore?_decoded found
  obtain ⟨stack, memory⟩ := fresh
  have erase : ∀ {s d n d'}, StepIn G s d n d' → Ninst.Run s d n d' := fun h => StepIn.toRun h
  have eraseP : ∀ {s d n d'}, FreePtr.PotStep (StepIn G) s d n d' → Ninst.Run s d n d' :=
    fun h => StepIn.toRun h.1
  have use : ∀ {T : Conf},
      (∀ key value S, T.d.stack = key :: value :: S → key ≠ implSlot) →
      T.d = N.devm → w.key ≠ implSlot := by
    intro T safe e
    exact safe w.key w.value rest (e ▸ hstack)
  rcases init with ⟨code, sel⟩ | ⟨code, sel⟩ | ⟨code, sel⟩ | ⟨code, sel⟩
  · obtain ⟨T, run, hT, e⟩ := Reach.sstoreNode_pot ImplV1.cert_check hpc code hsg stack memory
      gas chain hat
    have hs : Blanc.Sevm.selector G.sevm = 0x3357162b := by
      rw [← selV1T_root]
      exact List.mem_singleton.mp sel
    exact .inl (use (InitV1KeyBounds.initV1_reach_ne_implSlot_concrete erase hs run hT) e)
  · obtain ⟨T, run, hT, e⟩ := Reach.sstoreNode_pot ImplV2.cert_check hpc code hsg stack memory
      gas chain hat
    change selV2T.eval _ ∈ [0x3357162b, 0xd608ea64] at sel
    rw [selV2T_root_selWord] at sel
    rcases List.mem_cons.mp sel with hs | hs
    · exact .inl (use (Init06.init_reach_V2_ne_implSlot erase hs run hT) e)
    · rw [List.mem_singleton] at hs
      exact .inl (use (InitReachV2.initV2_reach_ne_implSlot eraseP hs run hT) e)
  · obtain ⟨T, run, hT, e⟩ := Reach.sstoreNode_pot ImplV2_1.cert_check hpc code hsg stack
      memory gas chain hat
    change selV2T.eval _ ∈ [0x3357162b, 0xd608ea64] at sel
    rw [selV2T_root_selWord] at sel
    rcases List.mem_cons.mp sel with hs | hs
    · exact .inl (use (Init06.init_reach_V2_1_ne_implSlot erase hs run hT) e)
    · rw [List.mem_singleton] at hs
      exact .inl (use (InitReachV2_1.initV2_reach_ne_implSlot eraseP hs run hT) e)
  · obtain ⟨T, run, hT, e⟩ := Reach.sstoreNode_pot Impl.cert_check hpc code hsg stack memory
      gas chain hat
    change selV2T.eval _ ∈ [0x3357162b, 0x430239b4, 0xd608ea64] at sel
    rw [selV2T_root_selWord] at sel
    rcases List.mem_cons.mp sel with hs | hs
    · exact .inl (use (Init06.init_reach_V2_2_ne_implSlot erase hs run hT) e)
    rcases List.mem_cons.mp hs with hs | hs
    · rcases InitReachV2_2.initV2_2_reach_ne_implSlot_or_mapping eraseP hs run hT
          w.key w.value rest (e ▸ hstack) with safe | mapping
      · exact .inl safe
      · exact .inr ⟨code, hs, mapping⟩
    · rw [List.mem_singleton] at hs
      exact .inl (use (InitReachV2_2.initV2_reach_ne_implSlot eraseP hs run hT) e)

section History

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
  {P : Adr} {W : List UsdcDeployedEntry} {pair : Adr} {Tr : Adr → Prop}

/-- History admission supplies the entry conditions for the exact initializer
classifier, at every raw store and without requiring the frame to succeed. -/
theorem ConfiguredHistoryTraceIn.initializer_write_ne_implSlot_or_migration
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (init : UsdcInitFrame node)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key ≠ implSlot ∨ node.sevm.code = Impl.code ∧
      initSelWord node.sevm = 0x430239b4 ∧ InitReachV2_2.MigrationKey node.sevm write.key := by
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, fresh, gas⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  have rootInit : UsdcInitFrame root := by
    simpa only [UsdcInitFrame, same] using init
  rw [same]
  exact initFrame_sstore_ne_implSlot_or_migration pc hsg fresh gas rootInit chain found


/-- Every actual initializer write is numerically off the implementation slot or
has an original successful migration mapping hash before that same write. -/
theorem ConfiguredHistoryTraceIn.initializer_write_ne_implSlot_or_hash
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (init : UsdcInitFrame node)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key ≠ implSlot ∨ ∃ root ∈ history.rawFrames,
      Exec.Deriv.ParentPrefix root node ∧ root.sevm.code = Impl.code ∧
        initSelWord root.sevm = 0x430239b4 ∧ ∃ (account : Adr) (base : B256),
          (base = 3 ∨ base = 9) ∧ write.key = mapSlot account.toB256 base ∧
            ∃ hashPc, KeccakBefore root node (account.toB256.toBytes ++ base.toBytes) hashPc := by
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, fresh, gas⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  have rootInit : UsdcInitFrame root := by
    simpa only [UsdcInitFrame, same] using init
  rcases initFrame_sstore_ne_implSlot_or_migration pc hsg fresh gas rootInit chain found with
    safe | ⟨code, selected, _⟩
  · exact .inl safe
  rcases InitReachV2_2.initV2_2_successfulSstore_source pc code hsg fresh.1 selected chain found with
    safe | source
  · exact .inl safe
  · exact .inr ⟨root, inFrames, chain, code, selected, source⟩

/-- Decode only the two canonical mapping preimages used by V2.2 migration.
The address comes from the input bytes, never from a comparison of digests. -/
def v22MigrationInputKey? (input : Bytes) : Option HistoricalMappingKey :=
  let account := (Bytes.toB256 (input.take 32)).toAdr
  if input = account.toB256.toBytes ++ (3 : B256).toBytes then
    some (.oldBlacklist3 account)
  else if input = account.toB256.toBytes ++ (9 : B256).toBytes then
    some (.modern (.bal account))
  else none

theorem v22MigrationInputKey?_complete (account : Adr) (base : B256)
    (migration : base = 3 ∨ base = 9) :
    ∃ key, v22MigrationInputKey? (account.toB256.toBytes ++ base.toBytes) = some key ∧
      key.slot = mapSlot account.toB256 base := by
  have address : (Bytes.toB256 ((account.toB256.toBytes ++ base.toBytes).take 32)).toAdr = account := by
    rw [List.take_length_append' (B256.length_toBytes _).symm,
      B256.toB256_toBytes, toAdr_toB256]
  unfold v22MigrationInputKey?
  dsimp only
  rw [address]
  rcases migration with rfl | rfl
  · exact ⟨.oldBlacklist3 account, ite_eq_left rfl, rfl⟩
  · have different : account.toB256.toBytes ++ (9 : B256).toBytes ≠
        account.toB256.toBytes ++ (3 : B256).toBytes := by
      intro equal
      have words := congrArg Bytes.toB256 (List.append_cancel_left equal)
      simp only [B256.toB256_toBytes] at words
      exact (by decide : (9 : B256) ≠ 3) words
    exact ⟨.modern (.bal account), by rw [ite_eq_right different, ite_eq_left rfl], rfl⟩

theorem v22MigrationInputKey?_sound {input : Bytes} {key : HistoricalMappingKey}
    (recognized : v22MigrationInputKey? input = some key) :
    ∃ (account : Adr) (base : B256), (base = 3 ∨ base = 9) ∧
      input = account.toB256.toBytes ++ base.toBytes ∧ key.slot = mapSlot account.toB256 base := by
  unfold v22MigrationInputKey? at recognized
  dsimp only at recognized
  split at recognized
  next at3 => cases recognized; exact ⟨_, 3, .inl rfl, at3, rfl⟩
  next =>
    split at recognized
    next at9 => cases recognized; exact ⟨_, 9, .inr rfl, at9, rfl⟩
    next => cases recognized

/-- Successful original hash inputs in the migration selector, including inputs
whose subsequent writes clear a slot. No unexecuted calldata row is collected. -/
def v22MigrationHashKey? (P : Adr) (node : Exec.Deriv) : Option HistoricalMappingKey :=
  if node.sevm.currentTarget = P ∧ node.sevm.code = Impl.code ∧
      initSelWord node.sevm = 0x430239b4 ∧
      node.devm.stack.take 2 = [0, 64] then
    match node.sevm.code.getInst node.pc with
    | some (.next (.reg .keccak256)) =>
        match Rinst.run ⟨node.pc, node.sevm, node.devm⟩ .keccak256 with
        | .ok _ => v22MigrationInputKey? (node.devm.memory.read 0 64).1
        | .error _ => none
    | _ => none
  else none

def actualV22MigrationHashKeys (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  history.rawNodes.filterMap (v22MigrationHashKey? P)

theorem v22MigrationHashKey?_complete {P : Adr} {root : Exec.Deriv}
    (occurrence : Exec.NinstOccurrence root) {post : Devm}
    (target : occurrence.node.sevm.currentTarget = P)
    (code : occurrence.node.sevm.code = Impl.code)
    (selected : initSelWord occurrence.node.sevm = 0x430239b4)
    (instruction : occurrence.instruction = .reg .keccak256)
    (success : occurrence.stepResult = .ok post)
    (stack : ∃ rest, occurrence.node.devm.stack = 0 :: 64 :: rest)
    {input : Bytes} (read : (occurrence.node.devm.memory.read 0 64).1 = input)
    {key : HistoricalMappingKey} (recognized : v22MigrationInputKey? input = some key) :
    v22MigrationHashKey? P occurrence.node = some key := by
  have decoded := occurrence.decoded
  rw [instruction] at decoded
  have run := occurrence.stepRun
  rw [instruction, success] at run
  simp only [Ninst.StepRun, Ninst.step_reg] at run
  have executed := (Step.run_ofExecution.mp run).2.symm
  obtain ⟨rest, stack⟩ := stack
  have shape : occurrence.node.devm.stack.take 2 = [0, 64] := by
    rw [stack]; rfl
  rw [v22MigrationHashKey?, ite_eq_left ⟨target, code, selected, shape⟩,
    decoded, executed, read]
  exact recognized


theorem v22MigrationHashKey?_sound {P : Adr} {node : Exec.Deriv}
    {key : HistoricalMappingKey} (recognized : v22MigrationHashKey? P node = some key) :
    node.sevm.currentTarget = P ∧ node.sevm.code = Impl.code ∧
      initSelWord node.sevm = 0x430239b4 ∧
      Ninst.At node.sevm.code node.pc (.reg .keccak256) ∧
      node.devm.stack.take 2 = [0, 64] ∧ ∃ post,
        Rinst.run ⟨node.pc, node.sevm, node.devm⟩ .keccak256 = .ok post ∧
        v22MigrationInputKey? (node.devm.memory.read 0 64).1 = some key := by
  unfold v22MigrationHashKey? at recognized
  split at recognized
  next scope =>
    split at recognized
    next decoded =>
      split at recognized
      next post executed =>
        exact ⟨scope.1, scope.2.1, scope.2.2.1, decoded, scope.2.2.2,
          post, executed, recognized⟩
      next => cases recognized
    next => cases recognized
  next => cases recognized

/-- Every collected key has its successful original hash occurrence and exact
canonical input, even if the enclosing frame later reverts. -/
theorem ConfiguredHistoryTraceIn.actualV22MigrationHashKeys_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    {key : HistoricalMappingKey} (member : key ∈ actualV22MigrationHashKeys P history) :
    ∃ root ∈ history.rawFrames, ∃ occurrence : Exec.NinstOccurrence root,
      occurrence.node ∈ history.rawNodes ∧ occurrence.node.sevm.currentTarget = P ∧
      occurrence.node.sevm.code = Impl.code ∧
      initSelWord occurrence.node.sevm = 0x430239b4 ∧
      occurrence.node.devm.stack.take 2 = [0, 64] ∧
      occurrence.instruction = .reg .keccak256 ∧ ∃ post,
        occurrence.stepResult = .ok post ∧ ∃ (account : Adr) (base : B256),
          (base = 3 ∨ base = 9) ∧
          (occurrence.node.devm.memory.read 0 64).1 = account.toB256.toBytes ++ base.toBytes ∧
          key.slot = mapSlot account.toB256 base := by
  obtain ⟨node, inNodes, recognized⟩ := List.mem_filterMap.mp member
  obtain ⟨target, code, selected, decoded, shape, post, executed, input⟩ :=
    v22MigrationHashKey?_sound recognized
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp inNodes
  have reached : node ∈ Exec.rawNodes root.exc := by
    obtain ⟨earlier, decomposition⟩ := Exec.Deriv.ParentPrefix.rawNodes_decomposition chain
    rw [decomposition]
    exact List.mem_append_right earlier (Exec.mem_rawNodes_self node.exc)
  obtain ⟨occurrence, same, instruction⟩ :=
    Exec.exists_ninstOccurrence_of_mem_rawNodes reached decoded
  have step : Ninst.StepRun occurrence.node.pc occurrence.node.sevm occurrence.node.devm
      occurrence.instruction .none (.ok post) := by
    rw [same, instruction]
    simp only [Ninst.StepRun, Ninst.step_reg]
    exact Step.run_ofExecution.mpr ⟨rfl, executed.symm⟩
  have success := (occurrence_stepRun_unique occurrence (slot := .none) trivial step).2
  obtain ⟨account, base, migration, read, slot⟩ := v22MigrationInputKey?_sound input
  refine ⟨root, inFrames, occurrence, ?_⟩
  rw [same]
  exact ⟨inNodes, target, code, selected, shape, instruction, post, success,
    account, base, migration, read, slot⟩

/-- Every initializer write is numerically separated or its mapping key is
collected from the original successful hash before that same write. -/
theorem ConfiguredHistoryTraceIn.initializer_write_ne_implSlot_or_collected
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (target : node.sevm.currentTarget = P)
    (init : UsdcInitFrame node) {write : Exec.StorageWrite}
    (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key ≠ implSlot ∨ ∃ key ∈ actualV22MigrationHashKeys P history, write.key = key.slot := by
  rcases ConfiguredHistoryTraceIn.initializer_write_ne_implSlot_or_hash history capabilities member init found with
    safe | ⟨root, inFrames, chain, code, selected, account, base, migration, slot, pc, source⟩
  · exact .inl safe
  obtain ⟨occurrence, next, _, instruction, success, before, _, _, stack, read⟩ := source
  have same := Exec.Deriv.ParentPrefix.sevm_eq before
  have targetRoot : root.sevm.currentTarget = P := by
    rw [← Exec.Deriv.ParentPrefix.sevm_eq chain]
    exact target
  have inNodes := (history.mem_rawNodes_iff_rawFrame_parentPrefix occurrence.node).mpr
    ⟨root, inFrames, before⟩
  obtain ⟨key, recognized, keySlot⟩ := v22MigrationInputKey?_complete account base migration
  have collected := v22MigrationHashKey?_complete (P := P) occurrence
    (by rw [same]; exact targetRoot) (by rw [same]; exact code)
    (by rw [same]; exact selected) instruction success stack read recognized
  exact .inr ⟨key, List.mem_filterMap.mpr ⟨occurrence.node, inNodes, collected⟩,
    slot.trans keySlot.symm⟩

/-- Trace-local freshness of actually hashed migration keys discharges every
initializer's implementation-slot separation, including zero-clearing writes. -/
theorem ConfiguredHistoryTraceIn.initializer_write_ne_implSlot
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {initial : HistoricalMappingKey → Prop}
    (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
    (fresh : SlotFootprint.FreshKeys HistoricalMappingKey.slot fixedSlots initial
      (actualV22MigrationHashKeys P history))
    {node : Exec.Deriv} (member : node ∈ history.rawNodes)
    (target : node.sevm.currentTarget = P) (init : UsdcInitFrame node)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key ≠ implSlot := by
  rcases ConfiguredHistoryTraceIn.initializer_write_ne_implSlot_or_collected history capabilities member target init found with
    safe | ⟨key, collected, slot⟩
  · exact safe
  · rw [slot]
    exact HistoricalMappingKey.slot_ne_implSlot initialApart fresh collected


/-- **`InitRowWritesNonInc` from the frame-local key separation.** -/
theorem ConfiguredHistoryTraceIn.initRowWritesNonInc
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (apart : InitRowsApart P pair Tr history.rawFrames) :
    InitRowWritesNonInc P pair Tr history.rawFrames := by
  intro G hG target init m chain w found tracked
  obtain ⟨hpc, -, hsg, fresh, gas⟩ := history.rawFrame_entryFacts capabilities G hG
  rcases initFrame_sstore hpc hsg fresh gas init chain found with keys | zero
  · obtain ⟨g, hg, hk⟩ := tracked
    exact (apart G hG target init g hg (hk ▸ keys)).elim
  · rw [zero]
    exact Nat.zero_le _

/-- **P1 with the initializers' writes discharged.** `usdc_pairAllowance_noIncrease_deployed`
with `InitRowsApart` (frame-local key separation of the initializer frames) in place of
`InitRowWritesNonInc`; every other premise is the same. -/
theorem ConfiguredHistoryTraceIn.usdc_pairAllowance_noIncrease_deployed_apart
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    (world : UsdcDeployedWorld history.BoundaryAt P W checkpoint.state)
    (admin : AdminUpgradesWithinFrom P W history.rawFrames history.rawNodes)
    (apartSlot : ImplSlotApart P history.rawNodes)
    (slotsApart : ProxySlotsApart pair Tr)
    (rowSep : UsdcRowSep P pair Tr history.rawFrames)
    (noPairException : NoPairExceptionWrites P pair Tr history.rawFrames history.rawNodes)
    (initApart : InitRowsApart P pair Tr history.rawFrames)
    {k : B256} (tracked : ∃ g, Tr g ∧ allowSlot pair g = k) :
    (∀ n ∈ history.rawNodes,
        ((n.devm.getStor P).get k).toNat ≤ ((checkpoint.state.getStor P).get k).toNat) ∧
      ((future.state.getStor P).get k).toNat ≤ ((checkpoint.state.getStor P).get k).toNat :=
  ConfiguredHistoryTraceIn.usdc_pairAllowance_noIncrease_deployed history capabilities bal world
    admin apartSlot slotsApart rowSep noPairException
    (ConfiguredHistoryTraceIn.initRowWritesNonInc history capabilities initApart) tracked

end History

end Blanc.Lift.Usdc
