import Blanc.Lift.CursorKeccak
import Blanc.Lift.Usdc.V2BlacklistMappingTouches
import Blanc.Lift.WalkCutKit

/-! Original successful hashes for both legacy-blacklist modern runtimes. -/
namespace Blanc.Lift.Usdc.V2BlacklistReach

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

variable {observe : Conf → Conf → Prop}

def selector (blocked : Bool) : B256 := if blocked then 0xf9f92be4 else 0x1a895266

def body : V2BlacklistVersion → Bool → SFunc
  | .v2, false => ImplV2.t_117d_c58
  | .v2, true => ImplV2.t_3d0f_c11
  | .v2_1, false => ImplV2_1.t_1075_c57
  | .v2_1, true => ImplV2_1.t_3938_c12

/-- The same original body prefix writes the address and base before hashing. -/
theorem body_reach_observed {version : V2BlacklistVersion} {blocked : Bool}
    {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {a : Adr} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe version.cert.prog sevm
      ⟨St b (a.toB256 :: S) M G, body version blocked, K⟩ T)
    (hT : AtSstore T) :
    ObservedKeccak Q observe sevm (a.toB256.toBytes ++ (3 : B256).toBytes) (fun _ => True) := by
  cases version <;> cases blocked
  all_goals
    simp only [body] at run
    first
    | unfold ImplV2.t_117d_c58 at run
    | unfold ImplV2.t_3d0f_c11 at run
    | unfold ImplV2_1.t_1075_c57 at run
    | unfold ImplV2_1.t_3938_c12 at run
    orsd
    iterate 3 orsx
    rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
        0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
      B256.and_comm, ff20_and_adr] at run
    iterate 10 orsx
    obtain ⟨_, hash, _⟩ := ObservedKeccak.of_next erase run hT
      (input := a.toB256.toBytes ++ (3 : B256).toBytes) (shape := fun _ => True)
      (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
    exact hash

def start : V2BlacklistVersion → SFunc
  | .v2 => ImplV2.t_0000_c0
  | .v2_1 => ImplV2_1.t_0000_c0

def dispatch : V2BlacklistVersion → SFunc
  | .v2 => .next (.reg (.dup 0)) (.next (.push [0x8a,0x6d,0xb9,0xc3] (by decide))
      (.next (.reg .gt) (.next (.push [0x01,0xbd] (by decide))
        (.branch ImplV2.t_002b_c0 ImplV2.t_01bd_c0))))
  | .v2_1 => .next (.reg (.dup 0)) (.next (.push [0x7f,0x2e,0xec,0xc3] (by decide))
      (.next (.reg .gt) (.next (.push [0x01,0xb2] (by decide))
        (.branch ImplV2_1.t_002b_c0 ImplV2_1.t_01b2_c0))))

def entry : V2BlacklistVersion → Bool → Nat
  | .v2, false => 146
  | .v2, true => 101
  | .v2_1, false => 141
  | .v2_1, true => 99

def wrapper : V2BlacklistVersion → Bool → SFunc
  | .v2, false => ImplV2.t_043d_c146
  | .v2, true => ImplV2.t_0e44_c101
  | .v2_1, false => ImplV2_1.t_041f_c141
  | .v2_1, true => ImplV2_1.t_0d60_c99

def internalEntry : V2BlacklistVersion → Bool → Nat
  | .v2, false => 58
  | .v2, true => 11
  | .v2_1, false => 57
  | .v2_1, true => 12

def guarded : V2BlacklistVersion → Bool → SFunc
  | .v2, false => ImplV2.t_110d_c58
  | .v2, true => ImplV2.t_3c9f_c11
  | .v2_1, false => ImplV2_1.t_1005_c57
  | .v2_1, true => ImplV2_1.t_38c8_c12

theorem route (version : V2BlacklistVersion) (blocked : Bool) :
    SFunc.selWalk (selector blocked) (dispatch version) =
      .inl (selector blocked, entry version blocked) := by
  cases version <;> cases blocked <;> decide +kernel

/-- Original dispatcher, ABI wrapper and role guard lead to the successful hash.
The eventual frame outcome is unrestricted. -/
theorem reach_observed {version : V2BlacklistVersion} {blocked : Bool}
    {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = selector blocked)
    (run : ObservedReach Q observe version.cert.prog sevm
      ⟨St b S M G, start version, []⟩ T) (hT : AtSstore T) :
    ObservedKeccak Q observe sevm
      ((Sevm.dataWord sevm 4).toAdr.toB256.toBytes ++ (3 : B256).toBytes) (fun _ => True) := by
  have routing := route version blocked
  have wrapperAt : version.cert.prog[entry version blocked]? = some (wrapper version blocked) := by
    cases version <;> cases blocked <;> rfl
  have guardedAt : version.cert.prog[internalEntry version blocked]? = some (guarded version blocked) := by
    cases version <;> cases blocked <;> rfl
  have word : Sevm.dataWord sevm (Bytes.toB256 [0]) >>> (Bytes.toB256 [0xe0]).toNat =
      selector blocked := selected
  cases version <;> cases blocked
  all_goals
    simp only [start] at run
    first
    | unfold ImplV2.t_0000_c0 at run
    | unfold ImplV2_1.t_0000_c0 at run
    iterate 7 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
        (fun _ h => by cases h)).elim
    first
    | unfold ImplV2.t_0010_c0 at run
    | unfold ImplV2_1.t_0010_c0 at run
    orsd
    iterate 5 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    swap
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
        (fun _ h => by cases h)).elim
    first
    | unfold ImplV2.t_001a_c0 at run
    | unfold ImplV2_1.t_001a_c0 at run
    iterate 4 orsx
    rw [word] at run
    obtain ⟨-, g, _, hg, run⟩ := ObservedReach.selWalk_inlS erase routing run hT
    rw [wrapperAt] at hg
    cases hg
    simp only [wrapper] at run
    first
    | unfold ImplV2.t_043d_c146 at run
    | unfold ImplV2.t_0e44_c101 at run
    | unfold ImplV2_1.t_041f_c141 at run
    | unfold ImplV2_1.t_0d60_c99 at run
    orsd
    iterate 10 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
        (fun _ h => by cases h)).elim
    first
    | unfold ImplV2.t_0453_c146 at run
    | unfold ImplV2.t_0e5a_c101 at run
    | unfold ImplV2_1.t_0435_c141 at run
    | unfold ImplV2_1.t_0d76_c99 at run
    orsd
    iterate 4 orsx
    rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
        0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
      ff20_and_word] at run
    orsx
    obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
    simp only [internalEntry] at guardedAt
    rw [guardedAt] at hg
    cases hg
    simp only [guarded] at run
    first
    | unfold ImplV2.t_110d_c58 at run
    | unfold ImplV2.t_3c9f_c11 at run
    | unfold ImplV2_1.t_1005_c57 at run
    | unfold ImplV2_1.t_38c8_c12 at run
    orsd
    orsx
    orsld
    iterate 5 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
        (by intro f member; have same := List.mem_singleton.mp member; subst f; decide +kernel)).elim
    first
    | exact body_reach_observed (version := .v2) (blocked := false) erase run hT
    | exact body_reach_observed (version := .v2) (blocked := true) erase run hT
    | exact body_reach_observed (version := .v2_1) (blocked := false) erase run hT
    | exact body_reach_observed (version := .v2_1) (blocked := true) erase run hT

/-- The same actual prefix contains a successful base-3 hash before its store. -/
theorem successfulSstore_hash (version : V2BlacklistVersion) {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = version.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x1a895266 ∨
      Blanc.Sevm.selector root.sevm = 0xf9f92be4)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    ∃ hashPc, KeccakBefore root node
      ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (3 : B256).toBytes) hashPc := by
  obtain ⟨decoded, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, reach, ok⟩ :=
    observed_reach_of_parentPrefix_noStateGas version.cert_check pc code hsg chain
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have target : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  have begin : (Cursor.start version.cert).conf root.devm = ⟨root.devm, start version, []⟩ := by
    cases version <;> rfl
  rw [begin, St.self' root.devm] at reach
  have hash : ObservedKeccak (StepIn root)
      (Cursor.RawEdgeAt version.code version.cert root node) root.sevm
      ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (3 : B256).toBytes) (fun _ => True) := by
    rcases selected with selected | selected
    · exact reach_observed (blocked := false) (fun h => StepIn.toRun h) selected reach target
    · exact reach_observed (blocked := true) (fun h => StepIn.toRun h) selected reach target
  obtain ⟨occurrence, next, here, instruction, result, reached, edge, suffix,
    _, _, hashStack, read⟩ := hash.actual
  exact ⟨occurrence.node.pc, occurrence, next, rfl, instruction, result,
    reached, edge, suffix, hashStack, read⟩

end Blanc.Lift.Usdc.V2BlacklistReach

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
  {version : V2BlacklistVersion} {P : Adr}

/-- A recognized key has its successful hash and store in the same original prefix. -/
theorem ConfiguredHistoryTraceIn.v2OldBlacklistKey?_hash
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) {key : HistoricalMappingKey}
    (collected : v2OldBlacklistKey? version P node = some key) :
    ∃ root ∈ history.rawFrames, Exec.Deriv.ParentPrefix root node ∧
      ∃ write, Exec.Deriv.successfulSstore? node = some write ∧
        write.owner = P ∧ write.key = key.slot ∧
        ∃ hashPc, KeccakBefore root node
          ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (3 : B256).toBytes) hashPc := by
  obtain ⟨target, code, selected, ⟨write, found⟩, keyEq⟩ :=
    v2OldBlacklistKey?_eq_some_iff.mp collected
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  rw [same] at code selected keyEq
  have hash := V2BlacklistReach.successfulSstore_hash version pc code hsg chain selected found
  have slot := v2OldBlacklist_store_key version pc code hsg chain selected found
  refine ⟨root, inFrames, chain, write, found,
    (successfulSstore?_node_owner found).2.trans target, ?_, hash⟩
  rw [keyEq]
  exact slot

/-- Every member of the exact collector carries original successful hash provenance. -/
theorem ConfiguredHistoryTraceIn.actualV2OldBlacklistKeys_hash
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {key : HistoricalMappingKey}
    (member : key ∈ actualV2OldBlacklistKeys version P history) :
    ∃ node ∈ history.rawNodes, v2OldBlacklistKey? version P node = some key ∧
      ∃ root ∈ history.rawFrames, Exec.Deriv.ParentPrefix root node ∧
        ∃ write, Exec.Deriv.successfulSstore? node = some write ∧
          write.owner = P ∧ write.key = key.slot ∧
          ∃ hashPc, KeccakBefore root node
            ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (3 : B256).toBytes) hashPc := by
  obtain ⟨node, inNodes, collected⟩ := (mem_actualV2OldBlacklistKeys history).mp member
  exact ⟨node, inNodes, collected,
    ConfiguredHistoryTraceIn.v2OldBlacklistKey?_hash history capabilities inNodes collected⟩

end Blanc.Lift.Usdc
