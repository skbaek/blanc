import Blanc.Lift.CursorObservedCut
import Blanc.Lift.Usdc.PermitRowPrefixV2_1
import Blanc.Lift.Usdc.ModernCallerHashBodies
import Blanc.Lift.Usdc.V2_1TransferWithAuthorizationReach

/-! Original nonce and allowance stores of V2.1 permit. -/
namespace Blanc.Lift.Usdc.V2_1PermitReach

open Jaune Blanc Blanc.Lift

variable {observe : Conf → Conf → Prop}

def nonceLine : List Ninst := [.reg .sstore, .reg (.dup 2), .reg .mload]

def NonceSource (Q : Sevm → Devm → Ninst → Devm → Prop)
    (observe : Conf → Conf → Prop) (sevm : Sevm) (owner : Adr) (T : Conf) : Prop :=
  (∃ rest, T.d.stack = nonceSlot owner :: rest) ∧
  (∃ tail, T.f = nonceLine.foldr SFunc.next tail) ∧
  ObservedKeccak Q observe sevm (owner.toB256.toBytes ++ (17 : B256).toBytes)
    (fun _ => True)

/-- The nonce increment precedes the actual returning recovery helper; a later
store is the approval setter for the unchanged decoded owner and spender. -/
theorem body_source {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} (hsg : sevm.benvStat.rules.stateGas = none)
    {b : Devm} {owner spender : Adr} {sigS sigR sigV deadline value : B256}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV2_1.cert.prog sevm
      ⟨St b (sigS :: sigR :: sigV :: deadline :: value :: spender.toB256 ::
        owner.toB256 :: S) M G, ImplV2_1.t_417b_c71, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    NonceSource Q observe sevm owner T ∨
      ModernCallerReach.ApprovalSource Q observe .v2_1 sevm owner spender T := by
  unfold ImplV2_1.t_417b_c71 at run
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
  rw [show ImplV2_1.cert.prog[83]? = some ImplV2_1.t_46b5_c83 from rfl] at hg
  cases hg
  obtain ⟨D, returned, _, run⟩ := ObservedReach.return_of_sstoreFree
    V2_1TransferWithAuthorizationReach.signature_sstoreFree (by decide +kernel) run hT
  obtain ⟨result, stack⟩ :=
    V2_1TransferWithAuthorizationReach.signature_return_stack erase hsg returned
  rw [St.self' D, stack] at run
  unfold ImplV2_1.t_421e_c71 at run
  orsd
  iterate 4 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT
      (by decide +kernel) cont).elim
  unfold ImplV2_1.t_42a0_c71 at run
  orsd
  iterate 5 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2_1.cert.prog[79]? = some ImplV2_1.t_39da_c79 from rfl] at hg
  cases hg
  apply Or.inr
  exact ModernCallerReach.approval_core_source erase run hT (by
    intro f member
    rcases List.mem_cons.mp member with rfl | member
    · decide +kernel
    exact cont f member)

theorem noncePattern_occurrences :
    BytePattern.occurrences (nonceLine.flatMap Ninst.toBytes) ImplV2_1.code.toList =
      [0x41ae] := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

theorem approval_pc_ne_nonce {node : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK ImplV2_1.code ImplV2_1.cert node κ) {tail : SFunc}
    (tree : κ.f = ModernCallerReach.approvalLine.foldr SFunc.next tail) :
    node.pc ≠ 0x41ae := by
  have bytes := ok.bytesAt_of_prefix ModernCallerReach.approvalLine tail tree
  intro bad
  rw [bad] at bytes
  have actual : bytesAt ImplV2_1.code 0x41ae
      (ModernCallerReach.approvalLine.flatMap Ninst.toBytes) = false := by decide +kernel
  rw [actual] at bytes
  contradiction


def ActualSource (root node : Exec.Deriv) (owner spender : Adr) (key : B256) : Prop :=
  (node.pc = 0x41ae ∧ key = nonceSlot owner ∧
    ∃ hashPc, KeccakBefore root node (owner.toB256.toBytes ++ (17 : B256).toBytes) hashPc) ∨
  (node.pc ≠ 0x41ae ∧ key = allowSlot owner spender ∧
    KeccakPairBefore root node (owner.toB256.toBytes ++ (10 : B256).toBytes)
      (spender.toB256.toBytes ++ (mapSlot owner.toB256 10).toBytes))

/-- Every original selected successful store has its actual nonce or allowance
hash source, including stores in a frame that subsequently reverts. -/
theorem successfulSstore_source {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV2_1.code)
    (stack : root.devm.stack = []) (memory : root.devm.memory = Mem.empty)
    (fork : NeutralFork root.sevm.benvStat.fork)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Sevm.selector root.sevm = 0xd505accf)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    ActualSource root node (Sevm.dataWord root.sevm 4).toAdr
      (Sevm.dataWord root.sevm 36).toAdr write.key := by
  obtain ⟨decoded, rest, targetStack⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨b, M, _, _, ⟨cut⟩⟩ :=
    permitV2_1_root_nonce_toward_sstore pc code stack memory selected chain decoded fork
  obtain ⟨κ, run, ok⟩ := cut.placed.observedReach_from_cut
    ImplV2_1.cert_check cut.free.1 cut.toward fork.stateGas
  obtain ⟨gas, state⟩ := cut.state
  simp only [Cursor.conf, state, cut.tree, cut.continuations] at run
  obtain ⟨g, tree, _⟩ := ok.tree_of_sstore decoded
  have atStore : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  have source := body_source (fun h => StepIn.toRun h) fork.stateGas run atStore (by
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

end Blanc.Lift.Usdc.V2_1PermitReach
