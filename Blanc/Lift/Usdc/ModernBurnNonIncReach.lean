import Blanc.Lift.Usdc.OldBurnNonIncBodies
import Blanc.Lift.Usdc.V22BurnNonIncReach

/-! Every actual burn store in all three modern runtimes is non-increasing at its own node. -/
namespace Blanc.Lift.Usdc.ModernBurnNonIncReach

open Jaune Blanc Blanc.Lift

def wrapper : ModernVersion → SFunc
  | .v2 => ImplV2.t_07e8_c133
  | .v2_1 => ImplV2_1.t_07fd_c131
  | .v2_2 => Impl.t_0834_c161

/-- Each public burn wrapper reaches its original body after its ABI bound check. -/
theorem wrapper_source {version : ModernVersion}
    {Q : Sevm → Devm → Ninst → Devm → Prop} {observe : Conf → Conf → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {selector : B256}
    {M : Mem} {G : Nat} {T : Conf}
    (run : ObservedReach Q observe version.cert.prog sevm
      ⟨St b (selector :: S) M G, wrapper version, []⟩ T) (hT : AtSstore T) :
    ModernBurnStores.StoreSource Q observe sevm T := by
  cases version with
  | v2_2 => exact V22BurnNonIncReach.wrapper_source erase run hT
  | v2 | v2_1 =>
    simp only [wrapper] at run
    first | unfold ImplV2.t_07e8_c133 at run | unfold ImplV2_1.t_07fd_c131 at run
    orsd
    iterate 10 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
        (fun _ h => by cases h)).elim
    first | unfold ImplV2.t_07fe_c133 at run | unfold ImplV2_1.t_0813_c131 at run
    orsd
    iterate 3 orsx
    obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
    first
    | change some ImplV2.t_2178_c45 = some g at hg
    | change some ImplV2_1.t_20ee_c47 = some g at hg
    cases hg
    first
    | apply OldBurnNonIncBodies.body_source (version := .v2) (by decide) erase run hT
    | apply OldBurnNonIncBodies.body_source (version := .v2_1) (by decide) erase run hT
    all_goals
      intro f member
      have same := List.mem_singleton.mp member
      subst f
      decide +kernel

/-- Compatibility projection of the observed source proof. -/
theorem wrapper_nonInc {version : ModernVersion}
    {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {selector : B256}
    {M : Mem} {G : Nat} {T : Conf}
    (run : Reach Q version.cert.prog sevm
      ⟨St b (selector :: S) M G, wrapper version, []⟩ T) (hT : AtSstore T) :
    ∃ key value rest, T.d.stack = key :: value :: rest ∧
      value.toNat ≤ (T.d.getStorVal sevm.currentTarget key).toNat := by
  obtain ⟨key, value, rest, stack, bound, _⟩ := wrapper_source erase (ObservedReach.of_reach run) hT
  exact ⟨key, value, rest, stack, bound⟩

def entry : ModernVersion → Nat
  | .v2 => 133
  | .v2_1 => 131
  | .v2_2 => 161

/-- The original entry and selector dispatcher reach only the burn wrapper. -/
theorem reach_source {version : ModernVersion}
    {Q : Sevm → Devm → Ninst → Devm → Prop} {observe : Conf → Conf → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0x42966c68)
    (run : ObservedReach Q observe version.cert.prog sevm
      ⟨St b S M G, ModernCallerReach.start version, []⟩ T) (hT : AtSstore T) :
    ModernBurnStores.StoreSource Q observe sevm T := by
  have routing : SFunc.selWalk (Blanc.Sevm.selector sevm) (ModernCallerReach.dispatch version) =
      .inl (Blanc.Sevm.selector sevm, entry version) := by
    rw [selected]
    cases version <;> decide +kernel
  have wrapperAt : version.cert.prog[entry version]? = some (wrapper version) := by
    cases version <;> rfl
  have word : Sevm.dataWord sevm (Bytes.toB256 [0]) >>> (Bytes.toB256 [0xe0]).toNat =
      Blanc.Sevm.selector sevm := rfl
  cases version
  all_goals
    simp only [ModernCallerReach.start] at run
    first
    | unfold ImplV2.t_0000_c0 at run
    | unfold ImplV2_1.t_0000_c0 at run
    | unfold Impl.t_0000_c0 at run
    iterate 7 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
        (fun _ h => by cases h)).elim
    first
    | unfold ImplV2.t_0010_c0 at run
    | unfold ImplV2_1.t_0010_c0 at run
    | unfold Impl.t_0010_c0 at run
    orsd
    iterate 5 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    swap
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
        (fun _ h => by cases h)).elim
    first
    | unfold ImplV2.t_001a_c0 at run
    | unfold ImplV2_1.t_001a_c0 at run
    | unfold Impl.t_001a_c0 at run
    iterate 4 orsx
    rw [word] at run
    obtain ⟨-, g, _, hg, run⟩ := ObservedReach.selWalk_inlS erase routing run hT
    rw [wrapperAt] at hg
    cases hg
    first
    | exact wrapper_source (version := .v2) erase run hT
    | exact wrapper_source (version := .v2_1) erase run hT
    | exact wrapper_source (version := .v2_2) erase run hT

/-- Compatibility projection of the observed source proof. -/
theorem reach_nonInc {version : ModernVersion}
    {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0x42966c68)
    (run : Reach Q version.cert.prog sevm
      ⟨St b S M G, ModernCallerReach.start version, []⟩ T) (hT : AtSstore T) :
    ∃ key value rest, T.d.stack = key :: value :: rest ∧
      value.toNat ≤ (T.d.getStorVal sevm.currentTarget key).toNat := by
  obtain ⟨key, value, rest, stack, bound, _⟩ := reach_source erase selected (ObservedReach.of_reach run) hT
  exact ⟨key, value, rest, stack, bound⟩

/-- Every original successful burn store is bounded by its own pre-state cell. -/
theorem successfulSstore_source (version : ModernVersion) {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = version.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x42966c68)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.value.toNat ≤ (node.devm.getStorVal node.sevm.currentTarget write.key).toNat ∧
      (write.key = 11 ∨ ∃ account : Adr, write.key = mapSlot account.toB256 9 ∧
        ∃ hashPc, KeccakBefore root node (account.toB256.toBytes ++ (9 : B256).toBytes) hashPc) := by
  obtain ⟨decoded, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, observed, ok⟩ :=
    observed_reach_of_parentPrefix_noStateGas version.cert_check pc code hsg chain
  have reach := observed
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have target : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  have begin : (Cursor.start version.cert).conf root.devm =
      ⟨root.devm, ModernCallerReach.start version, []⟩ := by
    cases version <;> rfl
  rw [begin, St.self' root.devm] at reach
  obtain ⟨key, value, other, shape, bound, source⟩ :=
    reach_source (fun h => StepIn.toRun h) selected reach target
  have same := List.cons.inj (stack.symm.trans shape)
  have keyEq := same.1
  have valueEq := (List.cons.inj same.2).1
  rw [← keyEq, ← valueEq] at bound
  rw [← Exec.Deriv.ParentPrefix.sevm_eq chain] at bound
  refine ⟨bound, ?_⟩
  rcases source with supply | ⟨account, slot, hash⟩
  · exact .inl (keyEq.trans supply)
  · obtain ⟨occurrence, next, here, instruction, success, before, edge, after,
      _, _, hashStack, input⟩ := hash.actual
    exact .inr ⟨account, keyEq.trans slot, occurrence.node.pc,
      occurrence, next, rfl, instruction, success, before, edge, after, hashStack, input⟩

/-- Compatibility projection retaining the original nonincrease statement. -/
theorem successfulSstore_nonInc (version : ModernVersion) {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = version.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x42966c68)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.value.toNat ≤ (node.devm.getStorVal node.sevm.currentTarget write.key).toNat := by
  exact (successfulSstore_source version pc code hsg chain selected found).1

end Blanc.Lift.Usdc.ModernBurnNonIncReach

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- Raw-history membership supplies the original entry for the same-node nonincrease law. -/
theorem ConfiguredHistoryTraceIn.modernBurn_nonInc
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {version : ModernVersion} {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (code : node.sevm.code = version.code)
    (selected : Sevm.selector node.sevm = 0x42966c68)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.value.toNat ≤ (node.devm.getStorVal node.sevm.currentTarget write.key).toNat := by
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  have rootCode : root.sevm.code = version.code := by rw [← same]; exact code
  have rootSelected : Sevm.selector root.sevm = 0x42966c68 := by rw [← same]; exact selected
  exact ModernBurnNonIncReach.successfulSstore_nonInc version pc rootCode hsg chain rootSelected found

/-- Every original burn store is literal supply11 or a balance mapping
with its exact successful original hash before that same store. -/
theorem ConfiguredHistoryTraceIn.modernBurn_write_source
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {version : ModernVersion} {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (code : node.sevm.code = version.code)
    (selected : Sevm.selector node.sevm = 0x42966c68)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key = 11 ∨ ∃ root ∈ history.rawFrames, Exec.Deriv.ParentPrefix root node ∧
      root.sevm.code = version.code ∧ Sevm.selector root.sevm = 0x42966c68 ∧
      ∃ account : Adr, write.key = mapSlot account.toB256 9 ∧
        ∃ hashPc, KeccakBefore root node (account.toB256.toBytes ++ (9 : B256).toBytes) hashPc := by
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  have rootCode : root.sevm.code = version.code := by rw [← same]; exact code
  have rootSelected : Sevm.selector root.sevm = 0x42966c68 := by rw [← same]; exact selected
  rcases (ModernBurnNonIncReach.successfulSstore_source version pc rootCode hsg chain rootSelected found).2 with
    supply | source
  · exact .inl supply
  · exact .inr ⟨root, inFrames, chain, rootCode, rootSelected, source⟩

section BurnHashKeys

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
  {version : ModernVersion} {P : Adr}

/-- Recognize the exact balance preimage; the account is decoded from bytes. -/
def modernBurnInputKey? (input : Bytes) : Option HistoricalMappingKey :=
  let account := (Bytes.toB256 (input.take 32)).toAdr
  if input = account.toB256.toBytes ++ (9 : B256).toBytes then
    some (.modern (.bal account))
  else none

theorem modernBurnInputKey?_complete (account : Adr) :
    modernBurnInputKey? (account.toB256.toBytes ++ (9 : B256).toBytes) =
      some (.modern (.bal account)) := by
  have address : (Bytes.toB256 ((account.toB256.toBytes ++ (9 : B256).toBytes).take 32)).toAdr = account := by
    rw [List.take_length_append' (B256.length_toBytes _).symm,
      B256.toB256_toBytes, toAdr_toB256]
  unfold modernBurnInputKey?
  dsimp only
  rw [address, ite_eq_left rfl]

theorem modernBurnInputKey?_sound {input : Bytes} {key : HistoricalMappingKey}
    (recognized : modernBurnInputKey? input = some key) :
    ∃ (account : Adr) (base : B256), base = 9 ∧
      input = account.toB256.toBytes ++ base.toBytes ∧ key.slot = mapSlot account.toB256 base := by
  unfold modernBurnInputKey? at recognized
  dsimp only at recognized
  split at recognized
  next inputEq => cases recognized; exact ⟨_, 9, rfl, inputEq, rfl⟩
  next => cases recognized

/-- Successful original hash inputs in the burn selector, including inputs
whose subsequent writes clear a slot. No unexecuted calldata row is collected. -/
def modernBurnHashKey? (version : ModernVersion) (P : Adr) (node : Exec.Deriv) : Option HistoricalMappingKey :=
  if node.sevm.currentTarget = P ∧ node.sevm.code = version.code ∧
      Sevm.selector node.sevm = 0x42966c68 ∧
      node.devm.stack.take 2 = [0, 64] then
    match node.sevm.code.getInst node.pc with
    | some (.next (.reg .keccak256)) =>
        match Rinst.run ⟨node.pc, node.sevm, node.devm⟩ .keccak256 with
        | .ok _ => modernBurnInputKey? (node.devm.memory.read 0 64).1
        | .error _ => none
    | _ => none
  else none

def actualModernBurnHashKeys (version : ModernVersion) (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  history.rawNodes.filterMap (modernBurnHashKey? version P)

theorem modernBurnHashKey?_complete {P : Adr} {root : Exec.Deriv}
    (occurrence : Exec.NinstOccurrence root) {post : Devm}
    (target : occurrence.node.sevm.currentTarget = P)
    (code : occurrence.node.sevm.code = version.code)
    (selected : Sevm.selector occurrence.node.sevm = 0x42966c68)
    (instruction : occurrence.instruction = .reg .keccak256)
    (success : occurrence.stepResult = .ok post)
    (stack : ∃ rest, occurrence.node.devm.stack = 0 :: 64 :: rest)
    {input : Bytes} (read : (occurrence.node.devm.memory.read 0 64).1 = input)
    {key : HistoricalMappingKey} (recognized : modernBurnInputKey? input = some key) :
    modernBurnHashKey? version P occurrence.node = some key := by
  have decoded := occurrence.decoded
  rw [instruction] at decoded
  have run := occurrence.stepRun
  rw [instruction, success] at run
  simp only [Ninst.StepRun, Ninst.step_reg] at run
  have executed := (Step.run_ofExecution.mp run).2.symm
  obtain ⟨rest, stack⟩ := stack
  have shape : occurrence.node.devm.stack.take 2 = [0, 64] := by
    rw [stack]; rfl
  rw [modernBurnHashKey?, ite_eq_left ⟨target, code, selected, shape⟩,
    decoded, executed, read]
  exact recognized


theorem modernBurnHashKey?_sound {P : Adr} {node : Exec.Deriv}
    {key : HistoricalMappingKey} (recognized : modernBurnHashKey? version P node = some key) :
    node.sevm.currentTarget = P ∧ node.sevm.code = version.code ∧
      Sevm.selector node.sevm = 0x42966c68 ∧
      Ninst.At node.sevm.code node.pc (.reg .keccak256) ∧
      node.devm.stack.take 2 = [0, 64] ∧ ∃ post,
        Rinst.run ⟨node.pc, node.sevm, node.devm⟩ .keccak256 = .ok post ∧
        modernBurnInputKey? (node.devm.memory.read 0 64).1 = some key := by
  unfold modernBurnHashKey? at recognized
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
theorem ConfiguredHistoryTraceIn.actualModernBurnHashKeys_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    {key : HistoricalMappingKey} (member : key ∈ actualModernBurnHashKeys version P history) :
    ∃ root ∈ history.rawFrames, ∃ occurrence : Exec.NinstOccurrence root,
      occurrence.node ∈ history.rawNodes ∧ occurrence.node.sevm.currentTarget = P ∧
      occurrence.node.sevm.code = version.code ∧
      Sevm.selector occurrence.node.sevm = 0x42966c68 ∧
      occurrence.node.devm.stack.take 2 = [0, 64] ∧
      occurrence.instruction = .reg .keccak256 ∧ ∃ post,
        occurrence.stepResult = .ok post ∧ ∃ (account : Adr) (base : B256),
          base = 9 ∧
          (occurrence.node.devm.memory.read 0 64).1 = account.toB256.toBytes ++ base.toBytes ∧
          key.slot = mapSlot account.toB256 base := by
  obtain ⟨node, inNodes, recognized⟩ := List.mem_filterMap.mp member
  obtain ⟨target, code, selected, decoded, shape, post, executed, input⟩ :=
    modernBurnHashKey?_sound recognized
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
  obtain ⟨account, base, balanceBase, read, slot⟩ := modernBurnInputKey?_sound input
  refine ⟨root, inFrames, occurrence, ?_⟩
  rw [same]
  exact ⟨inNodes, target, code, selected, shape, instruction, post, success,
    account, base, balanceBase, read, slot⟩

/-- Every burn write is literal supply11 or has an actually hashed balance key. -/
theorem ConfiguredHistoryTraceIn.modernBurn_write_collected
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = version.code)
    (selected : Sevm.selector node.sevm = 0x42966c68)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key = 11 ∨ ∃ key ∈ actualModernBurnHashKeys version P history, write.key = key.slot := by
  rcases ConfiguredHistoryTraceIn.modernBurn_write_source history capabilities member code selected found with
    supply | ⟨root, inFrames, chain, code, selected, account, slot, pc, source⟩
  · exact .inl supply
  obtain ⟨occurrence, next, _, instruction, success, before, _, _, stack, read⟩ := source
  have same := Exec.Deriv.ParentPrefix.sevm_eq before
  have targetRoot : root.sevm.currentTarget = P := by
    rw [← Exec.Deriv.ParentPrefix.sevm_eq chain]
    exact target
  have inNodes := (history.mem_rawNodes_iff_rawFrame_parentPrefix occurrence.node).mpr
    ⟨root, inFrames, before⟩
  have collected := modernBurnHashKey?_complete (P := P) (version := version) occurrence
    (by rw [same]; exact targetRoot) (by rw [same]; exact code)
    (by rw [same]; exact selected) instruction success stack read
    (modernBurnInputKey?_complete account)
  exact .inr ⟨.modern (.bal account),
    List.mem_filterMap.mpr ⟨occurrence.node, inNodes, collected⟩, slot⟩

/-- Actual balance-hash freshness excludes the implementation slot for every
modern burn store; the supply word is numerically distinct. -/
theorem ConfiguredHistoryTraceIn.modernBurn_write_ne_implSlot
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {initial : HistoricalMappingKey → Prop}
    (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
    (fresh : SlotFootprint.FreshKeys HistoricalMappingKey.slot fixedSlots initial
      (actualModernBurnHashKeys version P history))
    {node : Exec.Deriv} (member : node ∈ history.rawNodes)
    (target : node.sevm.currentTarget = P) (code : node.sevm.code = version.code)
    (selected : Sevm.selector node.sevm = 0x42966c68)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key ≠ implSlot := by
  rcases ConfiguredHistoryTraceIn.modernBurn_write_collected history capabilities
      member target code selected found with supply | ⟨key, collected, slot⟩
  · rw [supply]
    decide +kernel
  · rw [slot]
    exact HistoricalMappingKey.slot_ne_implSlot initialApart fresh collected

end BurnHashKeys

end Blanc.Lift.Usdc
