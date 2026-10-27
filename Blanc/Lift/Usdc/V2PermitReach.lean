import Blanc.Lift.Usdc.V2TransferWithAuthorizationReach
import Blanc.Lift.Usdc.ModernCallerHashBodies
import Blanc.Lift.Usdc.V2_1PermitReach

/-! Original nonce and allowance stores of V2 permit. -/
namespace Blanc.Lift.Usdc.V2PermitReach

open Jaune Blanc Blanc.Lift
open V2_1PermitReach (NonceSource nonceLine)

variable {observe : Conf → Conf → Prop}

/-- The checked dispatcher routes permit through its original ABI wrapper. -/
theorem route_permit : SFunc.selWalk 0xd505accf
    (.next (.reg (.dup 0)) (.next (.push [0x8a, 0x6d, 0xb9, 0xc3] (by decide))
      (.next (.reg .gt) (.next (.push [0x01, 0xbd] (by decide))
        (.branch ImplV2.t_002b_c0 ImplV2.t_01bd_c0))))) =
    .inl (Bytes.toB256 [0xd5, 0x05, 0xac, 0xcf], 111) := by
  decide +kernel

/-- The ABI-decoded permit arguments in the order used by the runtime. -/
def args (sevm : Sevm) : List B256 :=
  [Sevm.dataWord sevm 196, Sevm.dataWord sevm 164, Sevm.dataWord sevm 132 &&& 255,
    Sevm.dataWord sevm 100, Sevm.dataWord sevm 68,
    (Sevm.dataWord sevm 36).toAdr.toB256, (Sevm.dataWord sevm 4).toAdr.toB256]

/-- Original dispatcher, ABI and public guards reach the internal permit body. -/
theorem entry_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0xd505accf)
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b S M G, ImplV2.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    ∃ b' S' M' G', ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b' (args sevm ++ S') M' G', ImplV2.t_475b_c71,
        [ImplV2.t_35eb_c23, ImplV2.t_0470_c111]⟩ T := by
  unfold ImplV2.t_0000_c0 at run
  iterate 7 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold ImplV2.t_0010_c0 at run
  orsd
  iterate 5 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold ImplV2.t_001a_c0 at run
  iterate 4 orsx
  have word : Sevm.dataWord sevm (Bytes.toB256 [0]) >>> (Bytes.toB256 [0xe0]).toNat =
      0xd505accf := selected
  rw [word] at run
  obtain ⟨-, g, _, hg, run⟩ := ObservedReach.selWalk_inlS erase route_permit run hT
  rw [show ImplV2.cert.prog[111]? = some ImplV2.t_0bc6_c111 from rfl] at hg
  cases hg
  unfold ImplV2.t_0bc6_c111 at run
  orsd
  iterate 10 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold ImplV2.t_0bdc_c111 at run
  orsd
  iterate 41 orsx
  simp only [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
    0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ] at run
  simp only [ff20_and_word] at run
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2.cert.prog[23]? = some ImplV2.t_3450_c23 from rfl] at hg
  cases hg
  have cont : ∀ f ∈ [ImplV2.t_0470_c111], f.sstoreFreeIn [] = true := by
    intro f member
    have same := List.mem_singleton.mp member
    subst f
    decide +kernel
  unfold ImplV2.t_3450_c23 at run
  orsd
  orsx
  orsld
  iterate 7 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2.t_34da_c23 at run
  orsd
  iterate 13 orsx
  orsld
  iterate 6 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2.t_355b_c23 at run
  orsd
  iterate 13 orsx
  orsld
  iterate 6 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2.t_35dc_c23 at run
  orsd
  iterate 9 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2.cert.prog[71]? = some ImplV2.t_475b_c71 from rfl] at hg
  cases hg
  exact ⟨_, _, _, _, run⟩


/-- The nonce increment precedes the actual returning recovery helper; a later
store is the approval setter for the unchanged decoded owner and spender. -/
theorem body_source {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} (hsg : sevm.benvStat.rules.stateGas = none)
    {b : Devm} {owner spender : Adr} {sigS sigR sigV deadline value : B256}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b (sigS :: sigR :: sigV :: deadline :: value :: spender.toB256 ::
        owner.toB256 :: S) M G, ImplV2.t_475b_c71, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    NonceSource Q observe sevm owner T ∨
      ModernCallerReach.ApprovalSource Q observe .v2 sevm owner spender T := by
  unfold ImplV2.t_475b_c71 at run
  orsd
  obtain ⟨d', step, run⟩ := ObservedReach.rs_next run hT
  obtain ⟨_, rfl⟩ := ri_timestamp (erase step)
  iterate 4 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT
      (by decide +kernel) cont).elim
  unfold ImplV2.t_47ca_c71 at run
  orsd
  iterate 4 orsx
  rw [B256.and_comm, ff20_and_adr] at run
  iterate 13 orsx
  obtain ⟨_, hash, run⟩ := ObservedKeccak.of_next erase run hT
    (input := owner.toB256.toBytes ++ (17 : B256).toBytes)
    (shape := fun _ => True)
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [32]).toNat = 32 from rfl] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  orsx
  orsld
  iterate 5 orsx
  rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
  · exact .inl ⟨⟨_, rfl⟩, ⟨_, rfl⟩, hash⟩
  obtain ⟨b', G', rfl⟩ := SolcStorageReturn.ri_sstore_any (erase step)
  iterate 60 orsx
  rw [B256.and_comm spender.toB256 ff20, ff20_and_adr] at run
  orsld
  iterate 7 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2.cert.prog[84]? = some ImplV2.t_4d2c_c84 from rfl] at hg
  cases hg
  obtain ⟨D, returned, _, run⟩ := ObservedReach.return_of_sstoreFree
    V2TransferWithAuthorizationReach.signature_sstoreFree (by decide +kernel) run hT
  obtain ⟨result, stack⟩ :=
    V2TransferWithAuthorizationReach.signature_return_stack erase hsg returned
  rw [St.self' D, stack] at run
  unfold ImplV2.t_486d_c71 at run
  orsd
  iterate 4 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT
      (by decide +kernel) cont).elim
  unfold ImplV2.t_48ef_c71 at run
  orsd
  iterate 5 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2.cert.prog[81]? = some ImplV2.t_3db1_c81 from rfl] at hg
  cases hg
  apply Or.inr
  exact ModernCallerReach.approval_core_source erase run hT (by
    intro f member
    rcases List.mem_cons.mp member with rfl | member
    · decide +kernel
    exact cont f member)

theorem noncePattern_occurrences :
    BytePattern.occurrences (nonceLine.flatMap Ninst.toBytes) ImplV2.code.toList =
      [0x47fd] := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

theorem approval_pc_ne_nonce {node : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK ImplV2.code ImplV2.cert node κ) {tail : SFunc}
    (tree : κ.f = ModernCallerReach.approvalLine.foldr SFunc.next tail) :
    node.pc ≠ 0x47fd := by
  have bytes := ok.bytesAt_of_prefix ModernCallerReach.approvalLine tail tree
  intro bad
  rw [bad] at bytes
  have actual : bytesAt ImplV2.code 0x47fd
      (ModernCallerReach.approvalLine.flatMap Ninst.toBytes) = false := by decide +kernel
  rw [actual] at bytes
  contradiction


def ActualSource (root node : Exec.Deriv) (owner spender : Adr) (key : B256) : Prop :=
  (node.pc = 0x47fd ∧ key = nonceSlot owner ∧
    ∃ hashPc, KeccakBefore root node (owner.toB256.toBytes ++ (17 : B256).toBytes) hashPc) ∨
  (node.pc ≠ 0x47fd ∧ key = allowSlot owner spender ∧
    KeccakPairBefore root node (owner.toB256.toBytes ++ (10 : B256).toBytes)
      (spender.toB256.toBytes ++ (mapSlot owner.toB256 10).toBytes))

/-- Every original selected store retains its actual nonce or allowance hash
source, even if the enclosing frame subsequently reverts. -/
theorem successfulSstore_source {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV2.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Sevm.selector root.sevm = 0xd505accf)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    ActualSource root node (Sevm.dataWord root.sevm 4).toAdr
      (Sevm.dataWord root.sevm 36).toAdr write.key := by
  obtain ⟨decoded, rest, targetStack⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, reach, ok⟩ :=
    observed_reach_of_parentPrefix_noStateGas ImplV2.cert_check pc code hsg chain
  obtain ⟨g, tree, _⟩ := ok.tree_of_sstore decoded
  have atStore : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  change ObservedReach (StepIn root) (Cursor.RawEdgeAt ImplV2.code ImplV2.cert root node)
    ImplV2.cert.prog root.sevm ⟨root.devm, ImplV2.t_0000_c0, []⟩ (κ.conf node.devm) at reach
  rw [St.self' root.devm] at reach
  obtain ⟨b, S, M, G, run⟩ := entry_reach_observed (fun h => StepIn.toRun h) selected reach atStore
  have source := body_source (fun h => StepIn.toRun h) hsg run atStore (by
    intro f member
    rcases List.mem_cons.mp member with rfl | member
    · decide +kernel
    have same := List.mem_singleton.mp member
    subst f
    decide +kernel)
  rcases source with ⟨⟨other, keyStack⟩, ⟨tail, shape⟩, hash⟩ |
      ⟨⟨other, keyStack⟩, ⟨tail, shape⟩, hashes⟩
  · have location := ok.pc_eq_of_prefix_singleton nonceLine tail shape
      (suffix := []) (by simp only [List.append_nil]) (by decide) noncePattern_occurrences
    obtain ⟨occ, next, here, instruction, result, before, edge, after, _, _, hashStack, read⟩ :=
      hash.actual
    exact .inl ⟨location, (List.cons.inj (targetStack.symm.trans keyStack)).1,
      _, occ, next, rfl, instruction, result, before, edge, after, hashStack, read⟩
  · exact .inr ⟨approval_pc_ne_nonce ok shape,
      (List.cons.inj (targetStack.symm.trans keyStack)).1, hashes.actual⟩

end Blanc.Lift.Usdc.V2PermitReach
