import Blanc.Lift.Usdc.ModernCallerHashBodies

/-! Original dispatcher-to-store hash provenance for all modern caller allowance methods. -/
namespace Blanc.Lift.Usdc.ModernCallerReach

open Jaune Blanc Blanc.Lift

def start : ModernVersion → SFunc
  | .v2 => ImplV2.t_0000_c0
  | .v2_1 => ImplV2_1.t_0000_c0
  | .v2_2 => Impl.t_0000_c0

def dispatch : ModernVersion → SFunc
  | .v2 => .next (.reg (.dup 0)) (.next (.push [0x8a,0x6d,0xb9,0xc3] (by decide))
      (.next (.reg .gt) (.next (.push [0x01,0xbd] (by decide))
        (.branch ImplV2.t_002b_c0 ImplV2.t_01bd_c0))))
  | .v2_1 => .next (.reg (.dup 0)) (.next (.push [0x7f,0x2e,0xec,0xc3] (by decide))
      (.next (.reg .gt) (.next (.push [0x01,0xb2] (by decide))
        (.branch ImplV2_1.t_002b_c0 ImplV2_1.t_01b2_c0))))
  | .v2_2 => .next (.reg (.dup 0)) (.next (.push [0x84,0x56,0xcb,0x59] (by decide))
      (.next (.reg .gt) (.next (.push [0x01,0xd3] (by decide))
        (.branch Impl.t_002b_c0 Impl.t_01d3_c0))))

def entry : ModernVersion → Action → Nat
  | .v2, .approve => 149 | .v2, .increase => 136 | .v2, .decrease => 121
  | .v2_1, .approve => 145 | .v2_1, .increase => 134 | .v2_1, .decrease => 114
  | .v2_2, .approve => 178 | .v2_2, .increase => 165 | .v2_2, .decrease => 144

def wrapper : ModernVersion → Action → SFunc
  | .v2, .approve => ImplV2.t_03ce_c149
  | .v2, .increase => ImplV2.t_076e_c136
  | .v2, .decrease => ImplV2.t_0990_c121
  | .v2_1, .approve => ImplV2_1.t_03b8_c145
  | .v2_1, .increase => ImplV2_1.t_0783_c134
  | .v2_1, .decrease => ImplV2_1.t_09ad_c114
  | .v2_2, .approve => Impl.t_03ef_c178
  | .v2_2, .increase => Impl.t_07ba_c165
  | .v2_2, .decrease => Impl.t_0c62_c144

def wrapperStop : ModernVersion → Action → SFunc
  | .v2, .approve => ImplV2.t_0407_c149
  | .v2, .increase => ImplV2.t_0407_c136
  | .v2, .decrease => ImplV2.t_0407_c121
  | .v2_1, .approve => ImplV2_1.t_03f1_c145
  | .v2_1, .increase => ImplV2_1.t_03f1_c134
  | .v2_1, .decrease => ImplV2_1.t_03f1_c114
  | .v2_2, .approve => Impl.t_0428_c178
  | .v2_2, .increase => Impl.t_0428_c165
  | .v2_2, .decrease => Impl.t_0428_c144

def guardedEntry : ModernVersion → Action → Nat
  | .v2, .approve => 61 | .v2, .increase => 48 | .v2, .decrease => 33
  | .v2_1, .approve => 61 | .v2_1, .increase => 50 | .v2_1, .decrease => 29
  | .v2_2, .approve => 71 | .v2_2, .increase => 58 | .v2_2, .decrease => 36

def guarded : ModernVersion → Action → SFunc
  | .v2, .approve => ImplV2.t_0f56_c61
  | .v2, .increase => ImplV2.t_1afe_c48
  | .v2, .decrease => ImplV2.t_2a36_c33
  | .v2_1, .approve => ImplV2_1.t_0e72_c61
  | .v2_1, .increase => ImplV2_1.t_1a74_c50
  | .v2_1, .decrease => ImplV2_1.t_29e3_c29
  | .v2_2, .approve => Impl.t_12d3_c71
  | .v2_2, .increase => Impl.t_1d6a_c58
  | .v2_2, .decrease => Impl.t_2f0e_c36

def coreEntry : ModernVersion → Action → Nat
  | .v2, .approve => 81 | .v2, .increase => 79 | .v2, .decrease => 75
  | .v2_1, .approve => 79 | .v2_1, .increase => 77 | .v2_1, .decrease => 72
  | .v2_2, .approve => 81 | .v2_2, .increase => 102 | .v2_2, .decrease => 92

def bodyStop : ModernVersion → Action → SFunc
  | .v2, .approve => ImplV2.t_10d8_c61
  | .v2, .increase => ImplV2.t_10d8_c48
  | .v2, .decrease => ImplV2.t_10d8_c33
  | .v2_1, .approve => ImplV2_1.t_0ff4_c61
  | .v2_1, .increase => ImplV2_1.t_0ff4_c50
  | .v2_1, .decrease => ImplV2_1.t_0ff4_c29
  | .v2_2, .approve => Impl.t_136b_c71
  | .v2_2, .increase => Impl.t_136b_c58
  | .v2_2, .decrease => Impl.t_136b_c36

theorem route (version : ModernVersion) (action : Action) :
    SFunc.selWalk action.selector (dispatch version) = .inl (action.selector, entry version action) := by
  cases version <;> cases action <;> decide +kernel

theorem action_of_selected (version : ModernVersion) {selector : B256}
    (selected : selector ∈ version.selectors.callers) :
    ∃ action : Action, selector = action.selector := by
  have callers : version.selectors.callers = [0x095ea7b3, 0x39509351, 0xa457c2d7] := by
    cases version <;> rfl
  rw [callers] at selected
  simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
  rcases selected with selected | selected | selected
  · exact ⟨.approve, selected⟩
  · exact ⟨.increase, selected⟩
  · exact ⟨.decrease, selected⟩

/-- Follow the original ABI/guard prefix into the two actual successful hashes. -/
theorem reach_hashes {version : ModernVersion} {action : Action}
    {Q : Sevm → Devm → Ninst → Devm → Prop} {observe : Conf → Conf → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = action.selector)
    (run : ObservedReach Q observe version.cert.prog sevm
      ⟨St b S M G, start version, []⟩ T) (hT : AtSstore T) :
    ObservedKeccakPair Q observe version.cert.prog sevm
      (sevm.caller.toB256.toBytes ++ (10 : B256).toBytes)
      ((Sevm.dataWord sevm 4).toAdr.toB256.toBytes ++ (mapSlot sevm.caller.toB256 10).toBytes) := by
  have routing := route version action
  have wrapperAt : version.cert.prog[entry version action]? = some (wrapper version action) := by
    cases version <;> cases action <;> rfl
  have guardedAt : version.cert.prog[guardedEntry version action]? = some (guarded version action) := by
    cases version <;> cases action <;> rfl
  have coreAt : version.cert.prog[coreEntry version action]? = some (core version action) := by
    cases version <;> cases action <;> rfl
  have cont : ∀ f ∈ [wrapperStop version action], f.sstoreFreeIn [] = true := by
    intro f member
    have same := List.mem_singleton.mp member
    subst f
    cases version <;> cases action <;> decide +kernel
  have cont2 : ∀ f ∈ [bodyStop version action, wrapperStop version action], f.sstoreFreeIn [] = true := by
    intro f member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> cases version <;> cases action <;> decide +kernel
  have word : Sevm.dataWord sevm (Bytes.toB256 [0]) >>> (Bytes.toB256 [0xe0]).toNat =
      action.selector := selected
  cases version <;> cases action
  all_goals
    simp only [start] at run
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
    first
    | unfold ImplV2.t_03ce_c149 at run
    | unfold ImplV2.t_076e_c136 at run
    | unfold ImplV2.t_0990_c121 at run
    | unfold ImplV2_1.t_03b8_c145 at run
    | unfold ImplV2_1.t_0783_c134 at run
    | unfold ImplV2_1.t_09ad_c114 at run
    | unfold Impl.t_03ef_c178 at run
    | unfold Impl.t_07ba_c165 at run
    | unfold Impl.t_0c62_c144 at run
    orsd
    iterate 10 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
        (fun _ h => by cases h)).elim
    first
    | unfold ImplV2.t_03e4_c149 at run
    | unfold ImplV2.t_0784_c136 at run
    | unfold ImplV2.t_09a6_c121 at run
    | unfold ImplV2_1.t_03ce_c145 at run
    | unfold ImplV2_1.t_0799_c134 at run
    | unfold ImplV2_1.t_09c3_c114 at run
    | unfold Impl.t_0405_c178 at run
    | unfold Impl.t_07d0_c165 at run
    | unfold Impl.t_0c78_c144 at run
    orsd
    iterate 10 orsx
    rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
        0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
      B256.and_comm (Sevm.dataWord sevm (Bytes.toB256 [4])) ff20, ff20_and_word] at run
    obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
    simp only [guardedEntry] at guardedAt
    rw [guardedAt] at hg
    cases hg
    simp only [guarded] at run
    first
    | unfold ImplV2.t_0f56_c61 at run
    | unfold ImplV2.t_1afe_c48 at run
    | unfold ImplV2.t_2a36_c33 at run
    | unfold ImplV2_1.t_0e72_c61 at run
    | unfold ImplV2_1.t_1a74_c50 at run
    | unfold ImplV2_1.t_29e3_c29 at run
    | unfold Impl.t_12d3_c71 at run
    | unfold Impl.t_1d6a_c58 at run
    | unfold Impl.t_2f0e_c36 at run
    orsd
    orsx
    orsld
    iterate 9 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
    -- V2 and V2_1 have two legacy-blacklist guards here; V2_2 calls the core directly.
    try
      first
      | unfold ImplV2.t_0fe3_c61 at run
      | unfold ImplV2.t_1b8b_c48 at run
      | unfold ImplV2.t_2ac3_c33 at run
      | unfold ImplV2_1.t_0eff_c61 at run
      | unfold ImplV2_1.t_1b01_c50 at run
      | unfold ImplV2_1.t_2a70_c29 at run
      orsd
      iterate 11 orsx
      orsld
      iterate 4 orsx
      rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
      · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
      first
      | unfold ImplV2.t_104c_c61 at run
      | unfold ImplV2.t_1bf4_c48 at run
      | unfold ImplV2.t_2b2c_c33 at run
      | unfold ImplV2_1.t_0f68_c61 at run
      | unfold ImplV2_1.t_1b6a_c50 at run
      | unfold ImplV2_1.t_2ad9_c29 at run
      orsd
      iterate 13 orsx
      orsld
      iterate 6 orsx
      rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
      · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
    first
    | unfold ImplV2.t_10cd_c61 at run
    | unfold ImplV2.t_1c75_c48 at run
    | unfold ImplV2.t_2bad_c33 at run
    | unfold ImplV2_1.t_0fe9_c61 at run
    | unfold ImplV2_1.t_1beb_c50 at run
    | unfold ImplV2_1.t_2b5a_c29 at run
    | unfold Impl.t_1360_c71 at run
    | unfold Impl.t_1df7_c58 at run
    | unfold Impl.t_2f9b_c36 at run
    orsd
    iterate 5 orsx
    obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
    simp only [coreEntry] at coreAt
    rw [coreAt] at hg
    cases hg
    first
    | exact core_hashes (version := .v2) (action := .approve) erase run hT cont2
    | exact core_hashes (version := .v2) (action := .increase) erase run hT cont2
    | exact core_hashes (version := .v2) (action := .decrease) erase run hT cont2
    | exact core_hashes (version := .v2_1) (action := .approve) erase run hT cont2
    | exact core_hashes (version := .v2_1) (action := .increase) erase run hT cont2
    | exact core_hashes (version := .v2_1) (action := .decrease) erase run hT cont2
    | exact core_hashes (version := .v2_2) (action := .approve) erase run hT cont2
    | exact core_hashes (version := .v2_2) (action := .increase) erase run hT cont2
    | exact core_hashes (version := .v2_2) (action := .decrease) erase run hT cont2

/-- Both original successful hashes precede the same actual successful store. -/
theorem successfulSstore_ordered_hashes (version : ModernVersion) {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = version.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm ∈ version.selectors.callers)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    KeccakPairBefore root node
      (root.sevm.caller.toB256.toBytes ++ (10 : B256).toBytes)
      ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++
        (mapSlot root.sevm.caller.toB256 10).toBytes) := by
  obtain ⟨action, selected⟩ := action_of_selected version selected
  obtain ⟨decoded, _, _⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, reach, ok⟩ :=
    observed_reach_of_parentPrefix_noStateGas version.cert_check pc code hsg chain
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have target : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  have begin : (Cursor.start version.cert).conf root.devm = ⟨root.devm, start version, []⟩ := by
    cases version <;> rfl
  rw [begin, St.self' root.devm] at reach
  exact (reach_hashes (fun h => StepIn.toRun h) selected reach target).actual

end Blanc.Lift.Usdc.ModernCallerReach

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
  {version : ModernVersion} {P : Adr}

/-- Recognized caller keys carry ordered successful hashes in their original frame prefix. -/
theorem ConfiguredHistoryTraceIn.modernCallerKey?_ordered_hashes
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : modernCallerKey? version P node = some key) :
    ∃ root ∈ history.rawFrames, Exec.Deriv.ParentPrefix root node ∧
      ∃ write, Exec.Deriv.successfulSstore? node = some write ∧
        write.owner = P ∧ write.key = key.slot ∧ KeccakPairBefore root node
          (root.sevm.caller.toB256.toBytes ++ (10 : B256).toBytes)
          ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++
            (mapSlot root.sevm.caller.toB256 10).toBytes) := by
  obtain ⟨target, code, selected, ⟨write, found⟩, keyEq⟩ := modernCallerKey?_eq_some_iff.mp collected
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  rw [same] at code selected keyEq
  have hashes := ModernCallerReach.successfulSstore_ordered_hashes version pc code hsg chain selected found
  have slot := modernCaller_store_key version pc code hsg chain selected found
  refine ⟨root, inFrames, chain, write, found,
    (successfulSstore?_node_owner found).2.trans target, ?_, hashes⟩
  rw [keyEq]
  exact slot

/-- Every member of the unchanged exact collector retains its original ordered hash pair. -/
theorem ConfiguredHistoryTraceIn.actualModernCallerKeys_ordered_hashes
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {key : HistoricalMappingKey}
    (member : key ∈ actualModernCallerKeys version P history) :
    ∃ node ∈ history.rawNodes, modernCallerKey? version P node = some key ∧
      ∃ root ∈ history.rawFrames, Exec.Deriv.ParentPrefix root node ∧
        ∃ write, Exec.Deriv.successfulSstore? node = some write ∧
          write.owner = P ∧ write.key = key.slot ∧ KeccakPairBefore root node
            (root.sevm.caller.toB256.toBytes ++ (10 : B256).toBytes)
            ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++
              (mapSlot root.sevm.caller.toB256 10).toBytes) := by
  obtain ⟨node, inNodes, collected⟩ := (mem_actualModernCallerKeys history).mp member
  exact ⟨node, inNodes, collected,
    ConfiguredHistoryTraceIn.modernCallerKey?_ordered_hashes history capabilities inNodes collected⟩

end Blanc.Lift.Usdc
