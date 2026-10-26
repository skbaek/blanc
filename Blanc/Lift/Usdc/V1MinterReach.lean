import Blanc.Lift.CursorKeccak
import Blanc.Lift.Usdc.ImplV1.MinterPcSources
import Blanc.Lift.Usdc.ImplV1.Check
import Blanc.Lift.Usdc.ProxyForward
import Blanc.Lift.ReachSstoreLoops
import Blanc.Lift.CursorOccurrenceNoStateGas
import Blanc.Lift.WalkCutKit

/-! Actual V1 removeMinter stores, preserving their final checked source tail. -/
namespace Blanc.Lift.Usdc.V1MinterReach

open Jaune Blanc Blanc.Lift

variable {observe : Conf → Conf → Prop}

/-- Source alternatives at the actual endpoint, before either store is executed. -/
private def firstSource (a : Adr) (T : Conf) : Prop :=
  ((∃ tail, T.f = .next (.reg .sstore) (.next (.reg .pop)
      (.next (.push [0x00] (by decide)) tail))) ∧
    ∃ rest, T.d.stack = mapSlot a.toB256 12 :: rest)

private def secondSource (a : Adr) (T : Conf) : Prop :=
  ((∃ (tail : SFunc) (bs : Bytes) (fits : bs.length ≤ 32), bs.length = 20 ∧
    T.f = .next (.reg .sstore) (.next (.reg .pop)
      (.next (.reg (.dup 1)) (.next (.push bs fits) tail)))) ∧
    ∃ rest, T.d.stack = mapSlot a.toB256 13 :: rest)

def RemoveSource (a : Adr) (T : Conf) : Prop :=
  firstSource a T ∨ secondSource a T

/-- The same source alternative together with its own earlier observed hash. -/
def ObservedSource (P : Sevm → Devm → Ninst → Devm → Prop)
    (observe : Conf → Conf → Prop) (sevm : Sevm) (a : Adr) (T : Conf) : Prop :=
  (firstSource a T ∧ ObservedKeccak P observe sevm (a.toB256.toBytes ++ (12 : B256).toBytes)
    (fun f => ∃ tail, f = packedBoolHashLead.foldr SFunc.next (.next (.reg .sstore) (.next (.reg .pop) (.next (.push [0x00] (by decide)) tail))))) ∨
  (secondSource a T ∧ ObservedKeccak P observe sevm (a.toB256.toBytes ++ (13 : B256).toBytes)
    (fun f => ∃ (tail : SFunc) (bs : Bytes) (fits : bs.length ≤ 32), bs.length = 20 ∧ f = wordStoreHashLead.foldr SFunc.next (.next (.reg .sstore) (.next (.reg .pop) (.next (.reg (.dup 1)) (.next (.push bs fits) tail))))))

theorem ObservedSource.source {P : Sevm → Devm → Ninst → Devm → Prop}
    {observe : Conf → Conf → Prop} {sevm : Sevm} {a : Adr} {T : Conf}
    (h : ObservedSource P observe sevm a T) : RemoveSource a T := by
  rcases h with ⟨source, _⟩ | ⟨source, _⟩
  · exact .inl source
  · exact .inr source

/-- Stop at the first store before considering the continuation to the second hash. -/
theorem body_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {a : Adr} {z t : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV1.cert.prog sevm
      ⟨St b (z :: a.toB256 :: t :: S) M G, ImplV1.t_15b4_c14, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) : ObservedSource Q observe sevm a T := by
  unfold ImplV1.t_15b4_c14 at run
  orsd
  iterate 8 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ff20_and_adr, ff20_and_adr] at run
  iterate 10 orsx
  rw [show Bytes.toB256 [32] + Bytes.toB256 [0] = (Bytes.toB256 [32] : B256) from by decide +kernel,
    show Bytes.toB256 [32] + Bytes.toB256 [32] = (Bytes.toB256 [64] : B256) from by decide +kernel] at run
  obtain ⟨_, firstHash, run⟩ := ObservedKeccak.of_next erase run hT
    (input := a.toB256.toBytes ++ (12 : B256).toBytes)
    (shape := (fun f => ∃ tail, f = packedBoolHashLead.foldr SFunc.next (.next (.reg .sstore) (.next (.reg .pop) (.next (.push [0x00] (by decide)) tail)))))
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _)
    (by exact ⟨_, rfl⟩)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from by decide +kernel,
    show (Bytes.toB256 [32]).toNat = 32 from by decide +kernel] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  iterate 4 orsx
  orsld
  iterate 12 orsx
  rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
  · exact .inl ⟨⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩, firstHash⟩
  obtain ⟨b', G', rfl⟩ := SolcStorageReturn.ri_sstore_any (erase step)
  iterate 9 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ff20_and_adr, ff20_and_adr] at run
  iterate 10 orsx
  rw [show Bytes.toB256 [32] + Bytes.toB256 [0] = (Bytes.toB256 [32] : B256) from by decide +kernel,
    show Bytes.toB256 [32] + Bytes.toB256 [32] = (Bytes.toB256 [64] : B256) from by decide +kernel] at run
  obtain ⟨_, secondHash, run⟩ := ObservedKeccak.of_next erase run hT
    (input := a.toB256.toBytes ++ (13 : B256).toBytes)
    (shape := (fun f => ∃ (tail : SFunc) (bs : Bytes) (fits : bs.length ≤ 32), bs.length = 20 ∧ f = wordStoreHashLead.foldr SFunc.next (.next (.reg .sstore) (.next (.reg .pop) (.next (.reg (.dup 1)) (.next (.push bs fits) tail))))))
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _)
    (by exact ⟨_, _, _, rfl, rfl⟩)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from by decide +kernel,
    show (Bytes.toB256 [32]).toNat = 32 from by decide +kernel] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  iterate 2 orsx
  rcases ObservedReach.sstoreS run with rfl | ⟨d'', step', _, run⟩
  · exact .inr ⟨⟨⟨_, _, _, rfl, rfl⟩, ⟨_, rfl⟩⟩, secondHash⟩
  exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim

theorem body_reach {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {a : Adr} {z t : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : Reach Q ImplV1.cert.prog sevm
      ⟨St b (z :: a.toB256 :: t :: S) M G, ImplV1.t_15b4_c14, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) : RemoveSource a T := by
  exact (body_reach_observed erase (ObservedReach.of_reach run) hT cont).source

/-- V1's own dispatcher sends removeMinter to its original entry 58. -/
theorem route_remove : SFunc.selWalk 0x3092afd5
    (.next (.reg (.dup 0)) (.next (.push [0x06, 0xfd, 0xde, 0x03] (by decide)) (.next (.reg .eq)
      (.next (.push [0x01, 0x90] (by decide)) (.branchTo ImplV1.t_0041_c0 53))))) =
    .inl (Bytes.toB256 [0x30, 0x92, 0xaf, 0xd5], 58) := by
  decide +kernel

/-- Actual V1 selector, wrapper and guarded body, stopping at either reached store. -/
theorem remove_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0x3092afd5)
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
  obtain ⟨-, g, G1, hg, run⟩ := ObservedReach.selWalk_inlS erase route_remove run hT
  rw [show ImplV1.cert.prog[58]? = some ImplV1.t_0378_c58 from rfl] at hg
  cases hg
  unfold ImplV1.t_0378_c58 at run
  orsd
  iterate 4 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold ImplV1.t_0384_c58 at run
  orsd
  iterate 14 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ff20_and_word] at run
  iterate 11 orsx
  obtain ⟨g, G2, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV1.cert.prog[14]? = some ImplV1.t_1556_c14 from rfl] at hg
  cases hg
  have cont : ∀ f ∈ [ImplV1.t_03b9_c58], f.sstoreFreeIn [] = true := by
    intro f hf
    have same := List.mem_singleton.mp hf
    subst f
    decide +kernel
  unfold ImplV1.t_1556_c14 at run
  orsd
  iterate 4 orsx
  orsld
  iterate 16 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  exact body_reach_observed erase run hT cont

theorem remove_reach {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0x3092afd5)
    (run : Reach Q ImplV1.cert.prog sevm
      ⟨St b S M G, ImplV1.t_0000_c0, []⟩ T)
    (hT : AtSstore T) : RemoveSource (Sevm.dataWord sevm 4).toAdr T := by
  exact (remove_reach_observed erase selected (ObservedReach.of_reach run) hT).source

/-- Paired source pc, actual key and tail of one same checked cursor. -/
def ActualRemoveSource (a : Adr) (node : Exec.Deriv) (κ : Cursor) (key : B256) : Prop :=
  (node.pc = 0x160b ∧ key = mapSlot a.toB256 12 ∧
    ∃ tail, κ.f = .next (.reg .sstore) (.next (.reg .pop)
      (.next (.push [0x00] (by decide)) tail))) ∨
  (node.pc = 0x1650 ∧ key = mapSlot a.toB256 13 ∧
    ∃ (tail : SFunc) (bs : Bytes) (fits : bs.length ≤ 32), bs.length = 20 ∧
      κ.f = .next (.reg .sstore) (.next (.reg .pop)
        (.next (.reg (.dup 1)) (.next (.push bs fits) tail))))

/-- Apply pc uniqueness to the very cursor and key produced by the family walk. -/
theorem source_at_cursor {a : Adr} {node : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK ImplV1.code ImplV1.cert node κ)
    (source : RemoveSource a (κ.conf node.devm))
    {key value : B256} {rest : List B256}
    (stack : node.devm.stack = key :: value :: rest) : ActualRemoveSource a node κ key := by
  rcases source with ⟨⟨tail, tree⟩, ⟨other, keyStack⟩⟩ | ⟨⟨tail, bs, fits, width, tree⟩, ⟨other, keyStack⟩⟩
  · have keyEq : key = mapSlot a.toB256 12 := (List.cons.inj (stack.symm.trans keyStack)).1
    exact .inl ⟨ImplV1.pc_eq_160b_of_store_tail ok tree, keyEq, tail, tree⟩
  · have keyEq : key = mapSlot a.toB256 13 := (List.cons.inj (stack.symm.trans keyStack)).1
    exact .inr ⟨ImplV1.pc_eq_1650_of_store_tail ok fits width tree, keyEq, tail, bs, fits, width, tree⟩

/-- At an actual raw SSTORE prefix, derive both source alternatives from its root's code and selector. -/
theorem raw_store_source {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV1.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x3092afd5)
    (decoded : Ninst.At node.sevm.code node.pc (.reg .sstore))
    {key value : B256} {rest : List B256}
    (stack : node.devm.stack = key :: value :: rest) :
    ∃ κ, CursorOK ImplV1.code ImplV1.cert node κ ∧
      Reach (StepIn root) ImplV1.cert.prog root.sevm
        ((Cursor.start ImplV1.cert).conf root.devm) (κ.conf node.devm) ∧
      ActualRemoveSource (Sevm.dataWord root.sevm 4).toAdr node κ key := by
  obtain ⟨κ, reach, ok⟩ := reach_of_parentPrefix_noStateGas ImplV1.cert_check pc code hsg chain
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have target : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  have walk := reach
  change Reach (StepIn root) ImplV1.cert.prog root.sevm
    ⟨root.devm, ImplV1.t_0000_c0, []⟩ (κ.conf node.devm) at walk
  rw [St.self' root.devm] at walk
  have source := remove_reach (fun h => StepIn.toRun h) selected walk target
  exact ⟨κ, ok, reach, source_at_cursor ok source stack⟩


/-- The executable successful-store recognizer feeds the same raw-prefix source theorem. -/
theorem successfulSstore_source {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV1.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x3092afd5)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    ∃ κ, CursorOK ImplV1.code ImplV1.cert node κ ∧
      Reach (StepIn root) ImplV1.cert.prog root.sevm
        ((Cursor.start ImplV1.cert).conf root.devm) (κ.conf node.devm) ∧
      ActualRemoveSource (Sevm.dataWord root.sevm 4).toAdr node κ write.key := by
  obtain ⟨decoded, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  exact raw_store_source pc code hsg chain selected decoded stack

end Blanc.Lift.Usdc.V1MinterReach
