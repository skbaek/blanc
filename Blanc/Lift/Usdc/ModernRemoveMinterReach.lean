import Blanc.Lift.Usdc.ModernCallerReach

/-! Actual modern removeMinter writes never increase their own current storage word. -/
namespace Blanc.Lift.Usdc.ModernRemoveMinterReach

open Jaune Blanc Blanc.Lift

def core : ModernVersion → SFunc
  | .v2 => ImplV2.t_16cb_c55
  | .v2_1 => ImplV2_1.t_1641_c55
  | .v2_2 => Impl.t_192e_c65

/-- The flag write clears bits of its same-key reload; the allowance write stores zero.
Neither case needs distinct hash outputs or a successful enclosing frame. -/
theorem core_nonInc {version : ModernVersion}
    {Q : Sevm → Devm → Ninst → Devm → Prop} {observe : Conf → Conf → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {arg : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe version.cert.prog sevm
      ⟨St b (0 :: arg :: S) M G, core version, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ∃ key value rest, T.d.stack = key :: value :: rest ∧
      value.toNat ≤ (T.d.getStorVal sevm.currentTarget key).toNat := by
  cases version
  all_goals
    simp only [core] at run
    first
    | unfold ImplV2.t_16cb_c55 at run
    | unfold ImplV2_1.t_1641_c55 at run
    | unfold Impl.t_192e_c65 at run
    orsd
    iterate 17 orsx
    obtain ⟨loadedPost, loadStep, run⟩ := ObservedReach.rs_next run hT
    have loadRun := erase loadStep
    obtain ⟨key, rest, pop, push⟩ := of_run_sload loadRun
    simp only [Stack.Pop, Stack.Push, Split, St.stack, List.cons_append, List.nil_append,
      List.cons.injEq] at pop push
    obtain ⟨rfl, rfl⟩ := pop
    have storage := fun k => Devm.getStorVal_of_state (of_run_sload_state loadRun)
      sevm.currentTarget k
    simp only [St.getStorVal] at storage
    rw [St.self push (SolcStorageReturn.sload_memory loadRun), St.getStorVal, storage] at run
    simp only [St.memory] at run
    iterate 3 orsx
    rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
    · refine ⟨_, _, _, rfl, ?_⟩
      simp only [St.getStorVal, B256.toNat_and]
      exact Nat.and_le_right
    obtain ⟨b', G1, rfl⟩ := SolcStorageReturn.ri_sstore_any (erase step)
    iterate 9 orsx
    rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
    · exact ⟨_, _, _, rfl, Nat.zero_le _⟩
    exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim

def wrapper : ModernVersion → SFunc
  | .v2 => ImplV2.t_04e8_c143
  | .v2_1 => ImplV2_1.t_04fd_c139
  | .v2_2 => Impl.t_0534_c172

def stop : ModernVersion → SFunc
  | .v2 => ImplV2.t_0407_c143
  | .v2_1 => ImplV2_1.t_03f1_c139
  | .v2_2 => Impl.t_0428_c172

/-- ABI bounds and the master-minter guard lead to the same non-increasing stores. -/
theorem wrapper_nonInc {version : ModernVersion}
    {Q : Sevm → Devm → Ninst → Devm → Prop} {observe : Conf → Conf → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {selector : B256}
    {M : Mem} {G : Nat} {T : Conf}
    (run : ObservedReach Q observe version.cert.prog sevm
      ⟨St b (selector :: S) M G, wrapper version, []⟩ T) (hT : AtSstore T) :
    ∃ key value rest, T.d.stack = key :: value :: rest ∧
      value.toNat ≤ (T.d.getStorVal sevm.currentTarget key).toNat := by
  have cont : ∀ f ∈ [stop version], f.sstoreFreeIn [] = true := by
    intro f member
    have same := List.mem_singleton.mp member
    subst f
    cases version <;> decide +kernel
  cases version
  all_goals
    simp only [wrapper] at run
    first
    | unfold ImplV2.t_04e8_c143 at run
    | unfold ImplV2_1.t_04fd_c139 at run
    | unfold Impl.t_0534_c172 at run
    orsd
    iterate 10 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
        (fun _ h => by cases h)).elim
    first
    | unfold ImplV2.t_04fe_c143 at run
    | unfold ImplV2_1.t_0513_c139 at run
    | unfold Impl.t_054a_c172 at run
    orsd
    iterate 5 orsx
    obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
    first
    | change some ImplV2.t_1658_c55 = some g at hg
    | change some ImplV2_1.t_15ce_c55 = some g at hg
    | change some Impl.t_18bb_c65 = some g at hg
    cases hg
    first
    | unfold ImplV2.t_1658_c55 at run
    | unfold ImplV2_1.t_15ce_c55 at run
    | unfold Impl.t_18bb_c65 at run
    orsd
    orsx
    orsld
    iterate 7 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
    first
    | exact core_nonInc (version := .v2) erase run hT cont
    | exact core_nonInc (version := .v2_1) erase run hT cont
    | exact core_nonInc (version := .v2_2) erase run hT cont

def entry : ModernVersion → Nat
  | .v2 => 143
  | .v2_1 => 139
  | .v2_2 => 172

/-- The original entry and selector dispatcher reach only the removeMinter wrapper. -/
theorem reach_nonInc {version : ModernVersion}
    {Q : Sevm → Devm → Ninst → Devm → Prop} {observe : Conf → Conf → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0x3092afd5)
    (run : ObservedReach Q observe version.cert.prog sevm
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
    | exact wrapper_nonInc (version := .v2) erase run hT
    | exact wrapper_nonInc (version := .v2_1) erase run hT
    | exact wrapper_nonInc (version := .v2_2) erase run hT

/-- Every original successful removeMinter store is bounded by its own pre-state cell. -/
theorem successfulSstore_nonInc (version : ModernVersion) {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = version.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x3092afd5)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.value.toNat ≤ (node.devm.getStorVal node.sevm.currentTarget write.key).toNat := by
  obtain ⟨decoded, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, reach, ok⟩ :=
    observed_reach_of_parentPrefix_noStateGas version.cert_check pc code hsg chain
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

end Blanc.Lift.Usdc.ModernRemoveMinterReach

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- Raw-history membership supplies the original entry for the same-node nonincrease law. -/
theorem ConfiguredHistoryTraceIn.modernRemoveMinter_nonInc
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {version : ModernVersion} {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (code : node.sevm.code = version.code)
    (selected : Sevm.selector node.sevm = 0x3092afd5)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.value.toNat ≤ (node.devm.getStorVal node.sevm.currentTarget write.key).toNat := by
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  have rootCode : root.sevm.code = version.code := by rw [← same]; exact code
  have rootSelected : Sevm.selector root.sevm = 0x3092afd5 := by rw [← same]; exact selected
  exact ModernRemoveMinterReach.successfulSstore_nonInc version pc rootCode hsg chain rootSelected found

end Blanc.Lift.Usdc
