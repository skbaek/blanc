import Blanc.Lift.Usdc.ModernCallerReach
import Blanc.Lift.Usdc.ModernCancelMappingTouches

/-! Ordered successful authorization-state hashes on the original cancellation prefix. -/
namespace Blanc.Lift.Usdc.ModernCancelReach

open Jaune Blanc Blanc.Lift

def unused : ModernVersion → SFunc
  | .v2 => ImplV2.t_4c93_c89
  | .v2_1 => ImplV2_1.t_4627_c87
  | .v2_2 => Impl.t_524e_c110

/-- The unused-authorization guard reads exactly the owner/nonce mapping, in order. -/
theorem unused_hashes {version : ModernVersion}
    {Q : Sevm → Devm → Ninst → Devm → Prop} {observe : Conf → Conf → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {a : Adr} {nonce : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe version.cert.prog sevm
      ⟨St b (nonce :: a.toB256 :: S) M G, unused version, K⟩ T)
    (hT : AtSstore T) :
    ObservedKeccakPair Q observe version.cert.prog sevm
      (a.toB256.toBytes ++ (16 : B256).toBytes)
      (nonce.toBytes ++ (mapSlot a.toB256 16).toBytes) := by
  cases version
  all_goals
    simp only [unused] at run
    first
    | unfold ImplV2.t_4c93_c89 at run
    | unfold ImplV2_1.t_4627_c87 at run
    | unfold Impl.t_524e_c110 at run
    orsd
    iterate 3 orsx
    rw [B256.and_comm, ff20_and_adr] at run
    iterate 12 orsx
    obtain ⟨_, firstHash, run⟩ := ObservedKeccak.of_next_linked erase run hT
      (input := a.toB256.toBytes ++ (16 : B256).toBytes) (shape := fun _ => True)
      (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
    simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
      show (Bytes.toB256 [32]).toNat = 32 from rfl] at run firstHash
    rw [Mem.read_two_word_writes_at_raw] at run firstHash
    have run := run.withPrefix
    iterate 7 orsx
    obtain ⟨_, secondHash, _⟩ := ObservedKeccak.of_next erase run hT
      (input := nonce.toBytes ++ (mapSlot a.toB256 16).toBytes) (shape := fun _ => True)
      (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
    exact ⟨_, firstHash, secondHash⟩

def vrsWrapper : ModernVersion → SFunc
  | .v2 => ImplV2.t_0879_c131
  | .v2_1 => ImplV2_1.t_088e_c122
  | .v2_2 => Impl.t_0987_c159

def vrsStop : ModernVersion → SFunc
  | .v2 => ImplV2.t_0470_c131
  | .v2_1 => ImplV2_1.t_0452_c122
  | .v2_2 => Impl.t_0489_c159

/-- ABI decoding and the pause guard preserve the original VRS owner and nonce. -/
theorem vrs_hashes {version : ModernVersion}
    {Q : Sevm → Devm → Ninst → Devm → Prop} {observe : Conf → Conf → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {selector : B256}
    {M : Mem} {G : Nat} {T : Conf}
    (run : ObservedReach Q observe version.cert.prog sevm
      ⟨St b (selector :: S) M G, vrsWrapper version, []⟩ T) (hT : AtSstore T) :
    ObservedKeccakPair Q observe version.cert.prog sevm
      ((Sevm.dataWord sevm 4).toAdr.toB256.toBytes ++ (16 : B256).toBytes)
      ((Sevm.dataWord sevm 36).toBytes ++ (mapSlot (Sevm.dataWord sevm 4).toAdr.toB256 16).toBytes) := by
  have cont : ∀ f ∈ [vrsStop version], f.sstoreFreeIn [] = true := by
    intro f member
    have same := List.mem_singleton.mp member
    subst f
    cases version <;> decide +kernel
  cases version
  all_goals
    simp only [vrsWrapper] at run
    first
    | unfold ImplV2.t_0879_c131 at run
    | unfold ImplV2_1.t_088e_c122 at run
    | unfold Impl.t_0987_c159 at run
    orsd
    iterate 10 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
        (fun _ h => by cases h)).elim
    first
    | unfold ImplV2.t_088f_c131 at run
    | unfold ImplV2_1.t_08a4_c122 at run
    | unfold Impl.t_099d_c159 at run
    orsd
    iterate 27 orsx
    rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
        0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
      B256.and_comm (Sevm.dataWord sevm (Bytes.toB256 [4])) ff20, ff20_and_word] at run
    obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
    have bodyAt := hg
    first
    | change some ImplV2.t_2750_c43 = some g at bodyAt
    | change some ImplV2_1.t_26d9_c37 = some g at bodyAt
    | change some Impl.t_2a20_c52 = some g at bodyAt
    cases bodyAt
    first
    | unfold ImplV2.t_2750_c43 at run
    | unfold ImplV2_1.t_26d9_c37 at run
    | unfold Impl.t_2a20_c52 at run
    orsd
    orsx
    orsld
    iterate 7 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
    first
    | unfold ImplV2.t_27da_c43 at run
    | unfold ImplV2_1.t_2763_c37 at run
    | unfold Impl.t_2aaa_c52 at run
    orsd
    iterate 7 orsx
    obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
    first
    | change some ImplV2.t_4271_c76 = some g at hg
    | change some ImplV2_1.t_3e9a_c74 = some g at hg
    | change some Impl.t_4531_c97 = some g at hg
    cases hg
    first
    | unfold ImplV2.t_4271_c76 at run
    | unfold ImplV2_1.t_3e9a_c74 at run
    | unfold Impl.t_4531_c97 at run
    orsd
    repeat orsx
    obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
    first
    | change some ImplV2.t_4c93_c89 = some g at hg
    | change some ImplV2_1.t_4627_c87 = some g at hg
    | change some Impl.t_4a3f_c89 = some g at hg
    cases hg
    try
      unfold Impl.t_4a3f_c89 at run
      orsd
      iterate 4 orsx
      obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
      change some Impl.t_524e_c110 = some g at hg
      cases hg
    first
    | exact unused_hashes (version := .v2) erase run hT
    | exact unused_hashes (version := .v2_1) erase run hT
    | exact unused_hashes (version := .v2_2) erase run hT

/-- The bytes overload keeps its ABI-decoded authorizer and nonce through all bounds checks. -/
theorem bytes_hashes
    {Q : Sevm → Devm → Ninst → Devm → Prop} {observe : Conf → Conf → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {selector : B256}
    {M : Mem} {G : Nat} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (selector :: S) M G, Impl.t_0db0_c136, []⟩ T) (hT : AtSstore T) :
    ObservedKeccakPair Q observe Impl.cert.prog sevm
      ((Sevm.dataWord sevm 4).toAdr.toB256.toBytes ++ (16 : B256).toBytes)
      ((Sevm.dataWord sevm 36).toBytes ++ (mapSlot (Sevm.dataWord sevm 4).toAdr.toB256 16).toBytes) := by
  unfold Impl.t_0db0_c136 at run
  orsd
  repeat orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold Impl.t_0dc6_c136 at run
  orsd
  repeat orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    B256.and_comm (Sevm.dataWord sevm (Bytes.toB256 [4])) ff20, ff20_and_word] at run
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold Impl.t_0e03_c136 at run
  orsd
  repeat orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold Impl.t_0e15_c136 at run
  orsd
  repeat orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold Impl.t_0e37_c136 at run
  orsd
  repeat orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  change some Impl.t_3498_c28 = some g at hg
  cases hg
  unfold Impl.t_3498_c28 at run
  orsd
  orsx
  orsld
  iterate 7 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (by intro f member; have same := List.mem_singleton.mp member; subst f; decide +kernel)).elim
  unfold Impl.t_3522_c28 at run
  orsd
  iterate 5 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  change some Impl.t_4a3f_c89 = some g at hg
  cases hg
  unfold Impl.t_4a3f_c89 at run
  orsd
  iterate 4 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  change some Impl.t_524e_c110 = some g at hg
  cases hg
  exact unused_hashes (version := .v2_2) erase run hT

def entry (version : ModernVersion) (selector : B256) : Nat :=
  match version with
  | .v2 => 131
  | .v2_1 => 122
  | .v2_2 => if selector = 0xb7b72899 then 136 else 159

def wrapper (version : ModernVersion) (selector : B256) : SFunc :=
  match version with
  | .v2 => vrsWrapper .v2
  | .v2_1 => vrsWrapper .v2_1
  | .v2_2 => if selector = 0xb7b72899 then Impl.t_0db0_c136 else vrsWrapper .v2_2

/-- The original entry and dispatcher select one of the four proved cancellation paths. -/
theorem reach_hashes {version : ModernVersion}
    {Q : Sevm → Devm → Ninst → Devm → Prop} {observe : Conf → Conf → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm ∈ modernCancelSelectors version)
    (run : ObservedReach Q observe version.cert.prog sevm
      ⟨St b S M G, ModernCallerReach.start version, []⟩ T) (hT : AtSstore T) :
    ObservedKeccakPair Q observe version.cert.prog sevm
      ((Sevm.dataWord sevm 4).toAdr.toB256.toBytes ++ (16 : B256).toBytes)
      ((Sevm.dataWord sevm 36).toBytes ++ (mapSlot (Sevm.dataWord sevm 4).toAdr.toB256 16).toBytes) := by
  have routing : SFunc.selWalk (Blanc.Sevm.selector sevm) (ModernCallerReach.dispatch version) =
      .inl (Blanc.Sevm.selector sevm, entry version (Blanc.Sevm.selector sevm)) := by
    cases version <;> simp only [modernCancelSelectors, List.mem_cons, List.not_mem_nil, or_false] at selected
    · rw [selected]; decide +kernel
    · rw [selected]; decide +kernel
    · rcases selected with selected | selected <;> rw [selected] <;> decide +kernel
  have wrapperAt : version.cert.prog[entry version (Blanc.Sevm.selector sevm)]? =
      some (wrapper version (Blanc.Sevm.selector sevm)) := by
    cases version
    · rfl
    · rfl
    · simp only [entry, wrapper]; split <;> rfl
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
    simp only [wrapper] at run
  · exact vrs_hashes (version := .v2) erase run hT
  · exact vrs_hashes (version := .v2_1) erase run hT
  · split at run
    · exact bytes_hashes erase run hT
    · exact vrs_hashes (version := .v2_2) erase run hT

/-- Both original successful hashes precede the same actual successful cancellation store. -/
theorem successfulSstore_ordered_hashes (version : ModernVersion) {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = version.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm ∈ modernCancelSelectors version)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    KeccakPairBefore root node
      ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (16 : B256).toBytes)
      ((Sevm.dataWord root.sevm 36).toBytes ++
        (mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 16).toBytes) := by
  obtain ⟨decoded, _, _⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, reach, ok⟩ :=
    observed_reach_of_parentPrefix_noStateGas version.cert_check pc code hsg chain
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have target : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  have begin : (Cursor.start version.cert).conf root.devm =
      ⟨root.devm, ModernCallerReach.start version, []⟩ := by
    cases version <;> rfl
  rw [begin, St.self' root.devm] at reach
  exact (reach_hashes (fun h => StepIn.toRun h) selected reach target).actual

end Blanc.Lift.Usdc.ModernCancelReach

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
  {version : ModernVersion} {P : Adr}

/-- Recognized cancellation keys carry ordered successful hashes in their original frame prefix. -/
theorem ConfiguredHistoryTraceIn.modernCancelKey?_ordered_hashes
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : modernCancelKey? version P node = some key) :
    ∃ root ∈ history.rawFrames, Exec.Deriv.ParentPrefix root node ∧
      ∃ write, Exec.Deriv.successfulSstore? node = some write ∧
        write.owner = P ∧ write.key = key.slot ∧ KeccakPairBefore root node
          ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (16 : B256).toBytes)
          ((Sevm.dataWord root.sevm 36).toBytes ++
            (mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 16).toBytes) := by
  obtain ⟨target, code, selected, ⟨write, found⟩, keyEq⟩ := modernCancelKey?_eq_some_iff.mp collected
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  rw [same] at code selected keyEq
  have hashes := ModernCancelReach.successfulSstore_ordered_hashes version pc code hsg chain selected found
  have slot := modernCancel_store_key version pc code hsg chain selected found
  refine ⟨root, inFrames, chain, write, found,
    (successfulSstore?_node_owner found).2.trans target, ?_, hashes⟩
  rw [keyEq]
  exact slot

/-- Every member of the unchanged exact collector retains its original ordered hash pair. -/
theorem ConfiguredHistoryTraceIn.actualModernCancelKeys_ordered_hashes
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {key : HistoricalMappingKey}
    (member : key ∈ actualModernCancelKeys version P history) :
    ∃ node ∈ history.rawNodes, modernCancelKey? version P node = some key ∧
      ∃ root ∈ history.rawFrames, Exec.Deriv.ParentPrefix root node ∧
        ∃ write, Exec.Deriv.successfulSstore? node = some write ∧
          write.owner = P ∧ write.key = key.slot ∧ KeccakPairBefore root node
            ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (16 : B256).toBytes)
            ((Sevm.dataWord root.sevm 36).toBytes ++
              (mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 16).toBytes) := by
  obtain ⟨node, inNodes, collected⟩ := (mem_actualModernCancelKeys history).mp member
  exact ⟨node, inNodes, collected,
    ConfiguredHistoryTraceIn.modernCancelKey?_ordered_hashes history capabilities inNodes collected⟩

end Blanc.Lift.Usdc
