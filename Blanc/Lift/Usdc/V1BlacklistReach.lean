import Blanc.Lift.CursorKeccak
import Blanc.Lift.Usdc.ImplV1.Check
import Blanc.Lift.Usdc.ProxyForward
import Blanc.Lift.CursorOccurrenceNoStateGas
import Blanc.Lift.WalkCutKit

/-! Successful original V1 blacklist hashes before the actual packed-boolean store. -/
namespace Blanc.Lift.Usdc.V1BlacklistReach

open Jaune Blanc Blanc.Lift

variable {observe : Conf → Conf → Prop}

def body (blocked : Bool) : SFunc :=
  if blocked then ImplV1.t_2d1e_c40 else ImplV1.t_0fb9_c12

def ObservedSource (Q : Sevm → Devm → Ninst → Devm → Prop)
    (observe : Conf → Conf → Prop) (sevm : Sevm) (account : Adr) (T : Conf) : Prop :=
  (∃ rest, T.d.stack = mapSlot account.toB256 3 :: rest) ∧
    ObservedKeccak Q observe sevm (account.toB256.toBytes ++ (3 : B256).toBytes)
      (fun _ => True)

/-- Both Boolean updates compute the same account/base-3 input before their store. -/
theorem body_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {blocked : Bool} {sevm : Sevm} {b : Devm} {a : Adr} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV1.cert.prog sevm
      ⟨St b (a.toB256 :: S) M G, body blocked, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ObservedSource Q observe sevm a T := by
  cases blocked <;> unfold body at run
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at run
    first | unfold ImplV1.t_0fb9_c12 at run | unfold ImplV1.t_2d1e_c40 at run
    orsd
    iterate 8 orsx
    rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
        0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
      ff20_and_adr, ff20_and_adr] at run
    iterate 10 orsx
    rw [show Bytes.toB256 [32] + Bytes.toB256 [0] = (Bytes.toB256 [32] : B256) from by decide +kernel,
      show Bytes.toB256 [32] + Bytes.toB256 [32] = (Bytes.toB256 [64] : B256) from by decide +kernel] at run
    obtain ⟨_, hash, run⟩ := ObservedKeccak.of_next erase run hT
      (input := a.toB256.toBytes ++ (3 : B256).toBytes) (shape := fun _ => True)
      (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
    simp only [show (Bytes.toB256 [0]).toNat = 0 from by decide +kernel,
      show (Bytes.toB256 [32]).toNat = 32 from by decide +kernel] at run
    rw [Mem.read_two_word_writes_at_raw] at run
    iterate 4 orsx
    orsld
    iterate 12 orsx
    rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
    · exact ⟨⟨_, rfl⟩, hash⟩
    exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim

/-- V1's own dispatcher sends unblacklist to its original wrapper. -/
theorem route_unblacklist : SFunc.selWalk 0x1a895266
    (.next (.reg (.dup 0)) (.next (.push [0x06, 0xfd, 0xde, 0x03] (by decide)) (.next (.reg .eq)
      (.next (.push [0x01, 0x90] (by decide)) (.branchTo ImplV1.t_0041_c0 53))))) =
    .inl (Bytes.toB256 [0x1a, 0x89, 0x52, 0x66], 56) := by
  decide +kernel

/-- Actual V1 selector, wrapper and guarded body, stopping at its reached store. -/
theorem unblacklist_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0x1a895266)
    (run : ObservedReach Q observe ImplV1.cert.prog sevm
      ⟨St b S M G, ImplV1.t_0000_c0, []⟩ T)
    (hT : AtSstore T) : ObservedSource Q observe sevm (Sevm.dataWord sevm 4).toAdr T := by
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
  obtain ⟨-, g, G1, hg, run⟩ := ObservedReach.selWalk_inlS erase route_unblacklist run hT
  rw [show ImplV1.cert.prog[56]? = some ImplV1.t_02b0_c56 from rfl] at hg
  cases hg
  unfold ImplV1.t_02b0_c56 at run
  orsd
  iterate 4 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold ImplV1.t_02bc_c56 at run
  orsd
  iterate 14 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ff20_and_word] at run
  iterate 11 orsx
  obtain ⟨g, G2, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV1.cert.prog[12]? = some ImplV1.t_0f5d_c12 from rfl] at hg
  cases hg
  have cont : ∀ f ∈ [ImplV1.t_02f1_c56], f.sstoreFreeIn [] = true := by
    intro f hf
    have same := List.mem_singleton.mp hf
    subst f
    decide +kernel
  unfold ImplV1.t_0f5d_c12 at run
  orsd
  iterate 3 orsx
  orsld
  iterate 16 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  exact body_reach_observed (blocked := false) erase run hT cont

/-- V1's own dispatcher sends blacklist to its original wrapper. -/
theorem route_blacklist : SFunc.selWalk 0xf9f92be4
    (.next (.reg (.dup 0)) (.next (.push [0x06, 0xfd, 0xde, 0x03] (by decide)) (.next (.reg .eq)
      (.next (.push [0x01, 0x90] (by decide)) (.branchTo ImplV1.t_0041_c0 53))))) =
    .inl (Bytes.toB256 [0xf9, 0xf9, 0x2b, 0xe4], 82) := by
  decide +kernel

/-- Actual V1 selector, wrapper and guarded body, stopping at its reached store. -/
theorem blacklist_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0xf9f92be4)
    (run : ObservedReach Q observe ImplV1.cert.prog sevm
      ⟨St b S M G, ImplV1.t_0000_c0, []⟩ T)
    (hT : AtSstore T) : ObservedSource Q observe sevm (Sevm.dataWord sevm 4).toAdr T := by
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
  obtain ⟨-, g, G1, hg, run⟩ := ObservedReach.selWalk_inlS erase route_blacklist run hT
  rw [show ImplV1.cert.prog[82]? = some ImplV1.t_0c47_c82 from rfl] at hg
  cases hg
  unfold ImplV1.t_0c47_c82 at run
  orsd
  iterate 4 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold ImplV1.t_0c53_c82 at run
  orsd
  iterate 14 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ff20_and_word] at run
  iterate 11 orsx
  obtain ⟨g, G2, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV1.cert.prog[40]? = some ImplV1.t_2cc2_c40 from rfl] at hg
  cases hg
  have cont : ∀ f ∈ [ImplV1.t_0c88_c82], f.sstoreFreeIn [] = true := by
    intro f hf
    have same := List.mem_singleton.mp hf
    subst f
    decide +kernel
  unfold ImplV1.t_2cc2_c40 at run
  orsd
  iterate 3 orsx
  orsld
  iterate 16 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  exact body_reach_observed (blocked := true) erase run hT cont

/-- Every actual blacklist write retains its successful earlier base-3 hash. -/
theorem successfulSstore_hash {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV1.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x1a895266 ∨
      Blanc.Sevm.selector root.sevm = 0xf9f92be4)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key = mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 3 ∧
      ∃ hashPc, KeccakBefore root node
        ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (3 : B256).toBytes) hashPc := by
  obtain ⟨decoded, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, reach, ok⟩ :=
    observed_reach_of_parentPrefix_noStateGas ImplV1.cert_check pc code hsg chain
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have target : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  have walk := reach
  change ObservedReach (StepIn root) (Cursor.RawEdgeAt ImplV1.code ImplV1.cert root node)
    ImplV1.cert.prog root.sevm ⟨root.devm, ImplV1.t_0000_c0, []⟩ (κ.conf node.devm) at walk
  rw [St.self' root.devm] at walk
  have source : ObservedSource (StepIn root)
      (Cursor.RawEdgeAt ImplV1.code ImplV1.cert root node) root.sevm
      (Sevm.dataWord root.sevm 4).toAdr (κ.conf node.devm) := by
    rcases selected with selected | selected
    · exact unblacklist_reach_observed (fun h => StepIn.toRun h) selected walk target
    · exact blacklist_reach_observed (fun h => StepIn.toRun h) selected walk target
  obtain ⟨⟨other, keyStack⟩, hash⟩ := source
  have keyEq := (List.cons.inj (stack.symm.trans keyStack)).1
  obtain ⟨occurrence, next, here, instruction, result, reached, edge, suffix,
    _, _, hashStack, read⟩ := hash.actual
  exact ⟨keyEq, occurrence.node.pc, occurrence, next, rfl, instruction, result,
    reached, edge, suffix, hashStack, read⟩

end Blanc.Lift.Usdc.V1BlacklistReach
