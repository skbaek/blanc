import Blanc.Lift.Usdc.V22BurnNonIncBodies

/-! Original entry-to-store nonincrease for V2_2 burn, with no key-separation premise. -/
namespace Blanc.Lift.Usdc.V22BurnNonIncReach

open Jaune Blanc Blanc.Lift

/-- Pause, minter and blacklist checks lead to the bounded balance read and two stores. -/
theorem body_source {Q : Sevm → Devm → Ninst → Devm → Prop} {observe : Conf → Conf → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {amount : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (amount :: S) M G, Impl.t_2296_c54, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ModernBurnStores.StoreSource Q observe sevm T := by
  unfold Impl.t_2296_c54 at run
  orsd
  orsx
  orsld
  iterate 7 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold Impl.t_2320_c54 at run
  orsd
  iterate 11 orsx
  orsld
  iterate 3 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold Impl.t_2388_c54 at run
  orsd
  iterate 4 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  change some Impl.t_3f6a_c83 = some g at hg
  cases hg
  unfold Impl.t_3f6a_c83 at run
  orsd
  iterate 12 orsx
  orsld
  iterate 5 orsx
  obtain ⟨f, K', G', same, run⟩ := ObservedReach.rs_retBase run hT
  obtain ⟨rfl, rfl⟩ := List.cons.inj same
  unfold Impl.t_2392_c54 at run
  orsd
  iterate 2 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  exact V22BurnNonIncBodies.read_source erase run hT cont

/-- Compatibility projection of the observed source proof. -/
theorem body_nonInc {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {amount : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : Reach Q Impl.cert.prog sevm
      ⟨St b (amount :: S) M G, Impl.t_2296_c54, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ∃ key value rest, T.d.stack = key :: value :: rest ∧
      value.toNat ≤ (T.d.getStorVal sevm.currentTarget key).toNat := by
  obtain ⟨key, value, rest, stack, bound, _⟩ := body_source erase (ObservedReach.of_reach run) hT cont
  exact ⟨key, value, rest, stack, bound⟩

/-- The public ABI wrapper enters the original burn body with its decoded amount. -/
theorem wrapper_source {Q : Sevm → Devm → Ninst → Devm → Prop} {observe : Conf → Conf → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {selector : B256} {S : List B256}
    {M : Mem} {G : Nat} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (selector :: S) M G, Impl.t_0834_c161, []⟩ T) (hT : AtSstore T) :
    ModernBurnStores.StoreSource Q observe sevm T := by
  unfold Impl.t_0834_c161 at run
  orsd
  iterate 10 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold Impl.t_084a_c161 at run
  orsd
  iterate 3 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  change some Impl.t_2296_c54 = some g at hg
  cases hg
  apply body_source erase run hT
  intro f member
  have same := List.mem_singleton.mp member
  subst f
  decide +kernel

/-- Compatibility projection of the observed source proof. -/
theorem wrapper_nonInc {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {selector : B256} {S : List B256}
    {M : Mem} {G : Nat} {T : Conf}
    (run : Reach Q Impl.cert.prog sevm
      ⟨St b (selector :: S) M G, Impl.t_0834_c161, []⟩ T) (hT : AtSstore T) :
    ∃ key value rest, T.d.stack = key :: value :: rest ∧
      value.toNat ≤ (T.d.getStorVal sevm.currentTarget key).toNat := by
  obtain ⟨key, value, rest, stack, bound, _⟩ := wrapper_source erase (ObservedReach.of_reach run) hT
  exact ⟨key, value, rest, stack, bound⟩

/-- The original pc-zero dispatcher selects the same public burn wrapper. -/
theorem reach_nonInc {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0x42966c68)
    (run : Reach Q Impl.cert.prog sevm ⟨St b S M G, Impl.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    ∃ key value rest, T.d.stack = key :: value :: rest ∧
      value.toNat ≤ (T.d.getStorVal sevm.currentTarget key).toNat := by
  have routing : SFunc.selWalk (Blanc.Sevm.selector sevm) (ModernCallerReach.dispatch .v2_2) =
      .inl (Blanc.Sevm.selector sevm, 161) := by
    rw [selected]
    decide +kernel
  have word : Sevm.dataWord sevm (Bytes.toB256 [0]) >>> (Bytes.toB256 [0xe0]).toNat =
      Blanc.Sevm.selector sevm := rfl
  unfold Impl.t_0000_c0 at run
  iterate 7 rsx
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold Impl.t_0010_c0 at run
  rsd
  iterate 5 rsx
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold Impl.t_001a_c0 at run
  iterate 4 rsx
  rw [word] at run
  obtain ⟨-, g, _, hg, run⟩ := Reach.selWalk_inlS erase routing run hT
  change some Impl.t_0834_c161 = some g at hg
  cases hg
  exact wrapper_nonInc erase run hT

/-- Every actual successful burn store is bounded at that original node's pre-state. -/
theorem successfulSstore_nonInc {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = Impl.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x42966c68)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.value.toNat ≤ (node.devm.getStorVal node.sevm.currentTarget write.key).toNat := by
  obtain ⟨decoded, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, observed, ok⟩ :=
    observed_reach_of_parentPrefix_noStateGas Impl.cert_check pc code hsg chain
  have reach := observed.forget
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have target : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  change Reach (StepIn root) Impl.cert.prog root.sevm
    ⟨root.devm, Impl.t_0000_c0, []⟩ (κ.conf node.devm) at reach
  rw [St.self' root.devm] at reach
  obtain ⟨key, value, other, shape, bound⟩ :=
    reach_nonInc (fun h => StepIn.toRun h) selected reach target
  have same := List.cons.inj (stack.symm.trans shape)
  have keyEq := same.1
  have valueEq := (List.cons.inj same.2).1
  rw [← keyEq, ← valueEq, ← Exec.Deriv.ParentPrefix.sevm_eq chain] at bound
  exact bound

end Blanc.Lift.Usdc.V22BurnNonIncReach

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- Raw-history entry facts discharge the same-node burn law without a new hash population. -/
theorem ConfiguredHistoryTraceIn.v22Burn_nonInc
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (code : node.sevm.code = Impl.code)
    (selected : Sevm.selector node.sevm = 0x42966c68)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.value.toNat ≤ (node.devm.getStorVal node.sevm.currentTarget write.key).toNat := by
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  have rootCode : root.sevm.code = Impl.code := by rw [← same]; exact code
  have rootSelected : Sevm.selector root.sevm = 0x42966c68 := by rw [← same]; exact selected
  exact V22BurnNonIncReach.successfulSstore_nonInc pc rootCode hsg chain rootSelected found

end Blanc.Lift.Usdc
