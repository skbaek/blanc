import Blanc.Lift.CursorKeccakOrder
import Blanc.Lift.Usdc.ImplV1.Check
import Blanc.Lift.Usdc.ProxyForward
import Blanc.Lift.CursorOccurrenceNoStateGas
import Blanc.Lift.WalkCutKit

/-! Actual V1 approve stores and their earlier nested mapping hashes. -/
namespace Blanc.Lift.Usdc.V1ApproveReach

open Jaune Blanc Blanc.Lift

variable {observe : Conf → Conf → Prop}

/-- The actual allowance key and both of the hash inputs that compute it. -/
def ObservedSource (Q : Sevm → Devm → Ninst → Devm → Prop)
    (observe : Conf → Conf → Prop) (sevm : Sevm) (spender : Adr) (T : Conf) : Prop :=
  (∃ rest, T.d.stack = mapSlot spender.toB256 (mapSlot sevm.caller.toB256 10) :: rest) ∧
  ObservedKeccak Q observe sevm (sevm.caller.toB256.toBytes ++ (10 : B256).toBytes)
    (fun _ => True) ∧
  ObservedKeccak Q observe sevm
    (spender.toB256.toBytes ++ (mapSlot sevm.caller.toB256 10).toBytes) (fun _ => True)

/-- The same allowance key, retaining the segment from the inner hash to the outer hash. -/
def OrderedObservedSource (Q : Sevm → Devm → Ninst → Devm → Prop)
    (observe : Conf → Conf → Prop) (sevm : Sevm) (spender : Adr) (T : Conf) : Prop :=
  (∃ rest, T.d.stack = mapSlot spender.toB256 (mapSlot sevm.caller.toB256 10) :: rest) ∧
  ObservedKeccakPair Q observe ImplV1.cert.prog sevm
    (sevm.caller.toB256.toBytes ++ (10 : B256).toBytes)
    (spender.toB256.toBytes ++ (mapSlot sevm.caller.toB256 10).toBytes)

theorem OrderedObservedSource.forget {Q : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {spender : Adr} {T : Conf}
    (source : OrderedObservedSource Q observe sevm spender T) :
    ObservedSource Q observe sevm spender T :=
  ⟨source.1, source.2.forget⟩

/-- Abstract the guard memory before following the two nested hashes. -/
theorem body_reach_ordered {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {a : Adr} {x z value : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV1.cert.prog sevm
      ⟨St b (a.toB256 :: x :: z :: value :: a.toB256 :: S) M G, ImplV1.t_0e61_c10, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    OrderedObservedSource Q observe sevm a T := by
  unfold ImplV1.t_0e61_c10 at run
  orsd
  iterate 8 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ff20_and_adr, ff20_and_adr] at run
  iterate 10 orsx
  rw [show Bytes.toB256 [32] + Bytes.toB256 [0] = (Bytes.toB256 [32] : B256) from by decide +kernel,
    show Bytes.toB256 [32] + Bytes.toB256 [32] = (Bytes.toB256 [64] : B256) from by decide +kernel] at run
  obtain ⟨_, firstHash, run⟩ := ObservedKeccak.of_next_linked erase run hT
    (input := sevm.caller.toB256.toBytes ++ (10 : B256).toBytes)
    (shape := fun _ => True)
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from by decide +kernel,
    show (Bytes.toB256 [32]).toNat = 32 from by decide +kernel] at run firstHash
  rw [Mem.read_two_word_writes_at_raw] at run firstHash
  have run := run.withPrefix
  iterate 6 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ff20_and_adr, ff20_and_adr] at run
  iterate 10 orsx
  rw [show Bytes.toB256 [32] + Bytes.toB256 [0] = (Bytes.toB256 [32] : B256) from by decide +kernel,
    show Bytes.toB256 [32] + Bytes.toB256 [32] = (Bytes.toB256 [64] : B256) from by decide +kernel] at run
  obtain ⟨_, secondHash, run⟩ := ObservedKeccak.of_next erase run hT
    (input := a.toB256.toBytes ++ (mapSlot sevm.caller.toB256 10).toBytes)
    (shape := fun _ => True)
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from by decide +kernel,
    show (Bytes.toB256 [32]).toNat = 32 from by decide +kernel] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  iterate 2 orsx
  rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
  · exact ⟨⟨_, rfl⟩, _, firstHash, secondHash⟩
  exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim

/-- Project the individual observations from the ordered body proof. -/
theorem body_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {a : Adr} {x z value : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV1.cert.prog sevm
      ⟨St b (a.toB256 :: x :: z :: value :: a.toB256 :: S) M G, ImplV1.t_0e61_c10, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ObservedSource Q observe sevm a T :=
  (body_reach_ordered erase run hT cont).forget

/-- V1's checked dispatcher selects its original approve wrapper. -/
theorem route_approve : SFunc.selWalk 0x095ea7b3
    (.next (.reg (.dup 0)) (.next (.push [0x06, 0xfd, 0xde, 0x03] (by decide)) (.next (.reg .eq)
      (.next (.push [0x01, 0x90] (by decide)) (.branchTo ImplV1.t_0041_c0 53))))) =
    .inl (Bytes.toB256 [0x09, 0x5e, 0xa7, 0xb3], 54) := by
  decide +kernel

/-- Follow the actual selected prefix, preserving observations at its reached store. -/
theorem approve_reach_ordered {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0x095ea7b3)
    (run : ObservedReach Q observe ImplV1.cert.prog sevm
      ⟨St b S M G, ImplV1.t_0000_c0, []⟩ T)
    (hT : AtSstore T) : OrderedObservedSource Q observe sevm (Sevm.dataWord sevm 4).toAdr T := by
  unfold ImplV1.t_0000_c0 at run
  iterate 7 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold ImplV1.t_000d_c0 at run
  iterate 7 orsx
  have word := (dispatchWord_eq_selector sevm).trans selected
  unfold Proxy.dispatchWord at word
  rw [word] at run
  obtain ⟨-, g, G1, hg, run⟩ := ObservedReach.selWalk_inlS erase route_approve run hT
  rw [show ImplV1.cert.prog[54]? = some ImplV1.t_0220_c54 from rfl] at hg
  cases hg
  unfold ImplV1.t_0220_c54 at run
  orsd
  iterate 4 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold ImplV1.t_022c_c54 at run
  orsd
  iterate 14 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ff20_and_word] at run
  iterate 20 orsx
  obtain ⟨g, G2, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV1.cert.prog[10]? = some ImplV1.t_0d83_c10 from rfl] at hg
  cases hg
  have cont : ∀ f ∈ [ImplV1.t_026b_c54], f.sstoreFreeIn [] = true := by
    intro f hf
    have same := List.mem_singleton.mp hf
    subst f
    decide +kernel
  unfold ImplV1.t_0d83_c10 at run
  orsd
  iterate 4 orsx
  orsld
  iterate 11 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV1.t_0da1_c10 at run
  orsd
  iterate 24 orsx
  orsld
  iterate 13 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV1.t_0e01_c10 at run
  orsd
  iterate 24 orsx
  orsld
  iterate 13 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  exact body_reach_ordered erase run hT cont

/-- Project the individual observations from the ordered dispatcher proof. -/
theorem approve_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0x095ea7b3)
    (run : ObservedReach Q observe ImplV1.cert.prog sevm
      ⟨St b S M G, ImplV1.t_0000_c0, []⟩ T)
    (hT : AtSstore T) : ObservedSource Q observe sevm (Sevm.dataWord sevm 4).toAdr T :=
  (approve_reach_ordered erase selected run hT).forget

/-- Both successful hashes belong to the same actual raw prefix before the store. -/
def HashSource (root node : Exec.Deriv) : Prop :=
  ∃ innerPc outerPc,
    KeccakBefore root node (root.sevm.caller.toB256.toBytes ++ (10 : B256).toBytes) innerPc ∧
    KeccakBefore root node
      ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++
        (mapSlot root.sevm.caller.toB256 10).toBytes) outerPc

/-- The successful inner hash finishes before the successful outer hash begins. -/
def OrderedHashSource (root node : Exec.Deriv) : Prop :=
  KeccakPairBefore root node
    (root.sevm.caller.toB256.toBytes ++ (10 : B256).toBytes)
    ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++
      (mapSlot root.sevm.caller.toB256 10).toBytes)

/-- An actual recognized store supplies its key and both successful earlier hash occurrences. -/
theorem successfulSstore_ordered_hashes {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV1.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x095ea7b3)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key = mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256
      (mapSlot root.sevm.caller.toB256 10) ∧ OrderedHashSource root node := by
  obtain ⟨decoded, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, reach, ok⟩ :=
    observed_reach_of_parentPrefix_noStateGas ImplV1.cert_check pc code hsg chain
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have target : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  have walk := reach
  change ObservedReach (StepIn root) (Cursor.RawEdgeAt ImplV1.code ImplV1.cert root node)
    ImplV1.cert.prog root.sevm ⟨root.devm, ImplV1.t_0000_c0, []⟩ (κ.conf node.devm) at walk
  rw [St.self' root.devm] at walk
  obtain ⟨⟨other, keyStack⟩, hashes⟩ :=
    approve_reach_ordered (fun h => StepIn.toRun h) selected walk target
  have keyEq := (List.cons.inj (stack.symm.trans keyStack)).1
  exact ⟨keyEq, hashes.actual⟩

/-- Compatibility projection retaining the two individual earlier-occurrence witnesses. -/
theorem successfulSstore_hashes {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV1.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x095ea7b3)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key = mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256
      (mapSlot root.sevm.caller.toB256 10) ∧ HashSource root node := by
  obtain ⟨key, hashes⟩ := successfulSstore_ordered_hashes pc code hsg chain selected found
  exact ⟨key, KeccakPairBefore.forget hashes⟩

end Blanc.Lift.Usdc.V1ApproveReach
