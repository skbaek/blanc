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
theorem wrapper_nonInc {version : ModernVersion}
    {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {selector : B256}
    {M : Mem} {G : Nat} {T : Conf}
    (run : Reach Q version.cert.prog sevm
      ⟨St b (selector :: S) M G, wrapper version, []⟩ T) (hT : AtSstore T) :
    ∃ key value rest, T.d.stack = key :: value :: rest ∧
      value.toNat ≤ (T.d.getStorVal sevm.currentTarget key).toNat := by
  cases version with
  | v2_2 => exact V22BurnNonIncReach.wrapper_nonInc erase run hT
  | v2 | v2_1 =>
    simp only [wrapper] at run
    first | unfold ImplV2.t_07e8_c133 at run | unfold ImplV2_1.t_07fd_c131 at run
    rsd
    iterate 10 rsx
    rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run hT (by decide +kernel)
        (fun _ h => by cases h)).elim
    first | unfold ImplV2.t_07fe_c133 at run | unfold ImplV2_1.t_0813_c131 at run
    rsd
    iterate 3 rsx
    obtain ⟨g, _, hg, run⟩ := rs_callIn run hT
    first
    | change some ImplV2.t_2178_c45 = some g at hg
    | change some ImplV2_1.t_20ee_c47 = some g at hg
    cases hg
    first
    | apply OldBurnNonIncBodies.body_nonInc (version := .v2) (by decide) erase run hT
    | apply OldBurnNonIncBodies.body_nonInc (version := .v2_1) (by decide) erase run hT
    all_goals
      intro f member
      have same := List.mem_singleton.mp member
      subst f
      decide +kernel

def entry : ModernVersion → Nat
  | .v2 => 133
  | .v2_1 => 131
  | .v2_2 => 161

/-- The original entry and selector dispatcher reach only the burn wrapper. -/
theorem reach_nonInc {version : ModernVersion}
    {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0x42966c68)
    (run : Reach Q version.cert.prog sevm
      ⟨St b S M G, ModernCallerReach.start version, []⟩ T) (hT : AtSstore T) :
    ∃ key value rest, T.d.stack = key :: value :: rest ∧
      value.toNat ≤ (T.d.getStorVal sevm.currentTarget key).toNat := by
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
    iterate 7 rsx
    rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run hT (by decide +kernel)
        (fun _ h => by cases h)).elim
    first
    | unfold ImplV2.t_0010_c0 at run
    | unfold ImplV2_1.t_0010_c0 at run
    | unfold Impl.t_0010_c0 at run
    rsd
    iterate 5 rsx
    rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    swap
    · exact (Reach.false_of_sstoreFree (E := []) rfl run hT (by decide +kernel)
        (fun _ h => by cases h)).elim
    first
    | unfold ImplV2.t_001a_c0 at run
    | unfold ImplV2_1.t_001a_c0 at run
    | unfold Impl.t_001a_c0 at run
    iterate 4 rsx
    rw [word] at run
    obtain ⟨-, g, _, hg, run⟩ := Reach.selWalk_inlS erase routing run hT
    rw [wrapperAt] at hg
    cases hg
    first
    | exact wrapper_nonInc (version := .v2) erase run hT
    | exact wrapper_nonInc (version := .v2_1) erase run hT
    | exact wrapper_nonInc (version := .v2_2) erase run hT

/-- Every original successful burn store is bounded by its own pre-state cell. -/
theorem successfulSstore_nonInc (version : ModernVersion) {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = version.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x42966c68)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.value.toNat ≤ (node.devm.getStorVal node.sevm.currentTarget write.key).toNat := by
  obtain ⟨decoded, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, observed, ok⟩ :=
    observed_reach_of_parentPrefix_noStateGas version.cert_check pc code hsg chain
  have reach := observed.forget
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have target : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  have begin : (Cursor.start version.cert).conf root.devm =
      ⟨root.devm, ModernCallerReach.start version, []⟩ := by
    cases version <;> rfl
  rw [begin, St.self' root.devm] at reach
  obtain ⟨key, value, other, shape, bound⟩ :=
    reach_nonInc (fun h => StepIn.toRun h) selected reach target
  have same := List.cons.inj (stack.symm.trans shape)
  have keyEq := same.1
  have valueEq := (List.cons.inj same.2).1
  rw [← keyEq, ← valueEq] at bound
  rw [← Exec.Deriv.ParentPrefix.sevm_eq chain] at bound
  exact bound

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

end Blanc.Lift.Usdc
