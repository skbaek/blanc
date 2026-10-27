import Blanc.Lift.Usdc.V2TransferWithAuthorizationReach
import Blanc.Lift.Usdc.V22TransferReach
import Blanc.Lift.ObservedReachSplit

/-! V2.2 signed-transfer stores and their original successful hash observations. -/
namespace Blanc.Lift.Usdc.V22TransferWithAuthorizationReach
open Jaune Blanc Blanc.Lift
variable {observe : Conf → Conf → Prop}

/-- The auth writer retains observations in the actual V2.2 program. -/
abbrev AuthSource (Q : Sevm → Devm → Ninst → Devm → Prop)
    (observe : Conf → Conf → Prop) :=
  V2TransferWithAuthorizationReach.AuthSourceFor Q observe Impl.cert.prog

/-- V2.2 preserves the checked authorization writer instruction tree. -/
theorem auth_writer_eq : Impl.t_5006_c113 = ImplV2.t_4e5e_c85 := rfl

/-- Every store after signature validation is an auth flag or an actual balance writer. -/
theorem writes_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {nonce amount ptr before after : B256}
    {b : Devm} {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (ptr :: nonce :: before :: after :: amount ::
        recipient.toB256 :: owner.toB256 :: S) M G, Impl.t_467d_c90, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    AuthSource Q observe sevm owner nonce T ∨
      V22TransferReach.ObservedSource Q observe sevm owner recipient T := by
  unfold Impl.t_467d_c90 at run
  orsd
  iterate 4 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[113]? = some Impl.t_5006_c113 from rfl] at hg
  cases hg
  rcases V2TransferWithAuthorizationReach.auth_reach_observed erase run hT with found | ⟨b', M', G', run⟩
  · exact .inl found
  unfold Impl.t_4687_c90 at run
  orsd
  iterate 5 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[93]? = some Impl.t_3f98_c93 from rfl] at hg
  cases hg
  apply Or.inr
  apply V22TransferReach.body_reach_observed erase run hT
  intro f member
  rcases List.mem_cons.mp member with rfl | member
  · decide +kernel
  exact cont f member

/-- The internal entry passes the original arguments below the validity helper's frame. -/
theorem validity_call_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {nonce amount signature before after : B256}
    {b : Devm} {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (signature :: nonce :: before :: after :: amount ::
        recipient.toB256 :: owner.toB256 :: S) M G, Impl.t_4b49_c90, K⟩ T)
    (hT : AtSstore T) :
    ∃ b' M' G', ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b' (before :: after :: nonce :: owner.toB256 :: 0x4b55 ::
        signature :: nonce :: before :: after :: amount ::
        recipient.toB256 :: owner.toB256 :: S) M' G', Impl.t_4dc8_c112,
        Impl.t_4b55_c90 :: K⟩ T := by
  unfold Impl.t_4b49_c90 at run
  orsd
  iterate 6 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[112]? = some Impl.t_4dc8_c112 from rfl] at hg
  cases hg
  exact ⟨_, _, _, run⟩

/-- A returning validity check preserves all signed-transfer arguments below its frame. -/
theorem validity_return_stack {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} (hsg : sevm.benvStat.rules.stateGas = none)
    {b D : Devm} {a c n o tag : B256} {S : List B256} {M : Mem} {G : Nat}
    (run : SFunc.RunP Q Impl.cert.prog sevm
      (St b (a :: c :: n :: o :: tag :: S) M G) Impl.t_4dc8_c112 (.returned D)) :
    D.stack = S := by
  obtain ⟨Y, stack, len⟩ := run.entry_stack_below_noStateGas erase Impl.cert_check hsg
    (k := 112) (e := ⟨0x4dc8, [.unk, .unk, .unk, .unk, .ret], 0⟩) rfl rfl
    (ρ := tag) (X := [a, c, n, o, tag]) (R := S) rfl
    (.cons trivial (.cons trivial (.cons trivial (.cons trivial (.cons rfl .nil)))))
  have empty : Y = [] := List.eq_nil_of_length_eq_zero len
  simpa only [empty, List.nil_append] using stack

/-- Neither validity helper can write in the original frame. -/
theorem validity_sstoreFree : SstoreFreeSet Impl.cert.prog [110, 112] = true := by
  decide +kernel

/-- The full recovery and signature-validation helper closure has no own-frame store. -/
theorem signature_sstoreFree :
    SstoreFreeSet Impl.cert.prog [4, 6, 11, 76, 77, 78, 79, 106, 107, 111, 117] = true := by
  decide +kernel

/-- A returning signature validator preserves the original arguments below its frame. -/
theorem signature_return_stack {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} (hsg : sevm.benvStat.rules.stateGas = none)
    {b D : Devm} {signature hash owner tag : B256} {S : List B256} {M : Mem} {G : Nat}
    (run : SFunc.RunP Q Impl.cert.prog sevm
      (St b (signature :: hash :: owner :: tag :: S) M G) Impl.t_4e88_c111 (.returned D)) :
    D.stack = S := by
  obtain ⟨Y, stack, len⟩ := run.entry_stack_below_noStateGas erase Impl.cert_check hsg
    (k := 111) (e := ⟨0x4e88, [.unk, .unk, .unk, .ret], 0⟩) rfl rfl
    (ρ := tag) (X := [signature, hash, owner, tag]) (R := S) rfl
    (.cons trivial (.cons trivial (.cons trivial (.cons rfl .nil))))
  have empty : Y = [] := List.eq_nil_of_length_eq_zero len
  simpa only [empty, List.nil_append] using stack

/-- Signature preparation preserves the original transfer arguments below validation. -/
theorem signature_call_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {signature nonce amount before after : B256}
    {b : Devm} {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (signature :: nonce :: before :: after :: amount ::
        recipient.toB256 :: owner.toB256 :: S) M G, Impl.t_4b55_c90, K⟩ T)
    (hT : AtSstore T) :
    ∃ b' hash M' G', ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b' (signature :: hash :: owner.toB256 :: 0x467d ::
        signature :: nonce :: before :: after :: amount ::
        recipient.toB256 :: owner.toB256 :: S) M' G', Impl.t_4e88_c111,
        Impl.t_467d_c90 :: K⟩ T := by
  unfold Impl.t_4b55_c90 at run
  orsd
  iterate 79 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[111]? = some Impl.t_4e88_c111 from rfl] at hg
  cases hg
  exact ⟨_, _, _, _, run⟩

/-- Both helpers return on the original observed path before its selected writer. -/
theorem body_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} (hsg : sevm.benvStat.rules.stateGas = none)
    {owner recipient : Adr} {nonce amount signature before after : B256}
    {b : Devm} {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (signature :: nonce :: before :: after :: amount ::
        recipient.toB256 :: owner.toB256 :: S) M G, Impl.t_4b49_c90, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    AuthSource Q observe sevm owner nonce T ∨
      V22TransferReach.ObservedSource Q observe sevm owner recipient T := by
  obtain ⟨b', M', G', run⟩ := validity_call_reach_observed erase run hT
  obtain ⟨D, returned, _, run⟩ := ObservedReach.return_of_sstoreFree
    validity_sstoreFree (by decide +kernel) run hT
  have stack := validity_return_stack erase hsg returned
  rw [St.self' D, stack] at run
  obtain ⟨b'', hash, M'', G'', run⟩ := signature_call_reach_observed erase run hT
  obtain ⟨D, returned, _, run⟩ := ObservedReach.return_of_sstoreFree
    signature_sstoreFree (by decide +kernel) run hT
  have stack := signature_return_stack erase hsg returned
  rw [St.self' D, stack] at run
  exact writes_reach_observed erase run hT cont

/-- The original ABI's signature words are packed without losing the six transfer fields. -/
theorem pack_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {nonce amount sigS sigR sigV before after : B256}
    {b : Devm} {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (sigS :: sigR :: sigV :: nonce :: before :: after :: amount ::
        recipient.toB256 :: owner.toB256 :: S) M G, Impl.t_4c3f_c87, K⟩ T)
    (hT : AtSstore T) :
    ∃ b' signature S' M' G', ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b' (signature :: nonce :: before :: after :: amount ::
        recipient.toB256 :: owner.toB256 :: S') M' G', Impl.t_4b49_c90,
        Impl.t_2d6f_c87 :: K⟩ T := by
  unfold Impl.t_4c3f_c87 at run
  orsd
  iterate 52 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[90]? = some Impl.t_4b49_c90 from rfl] at hg
  cases hg
  exact ⟨_, _, _, _, _, run⟩


/-- The checked dispatcher routes transfer through its original ABI wrapper. -/
theorem route_authorization : SFunc.selWalk 0xe3ee160e
    (.next (.reg (.dup 0)) (.next (.push [0x84, 0x56, 0xcb, 0x59] (by decide))
      (.next (.reg .gt) (.next (.push [0x01, 0xd3] (by decide))
        (.branch Impl.t_002b_c0 Impl.t_01d3_c0))))) =
    .inl (Bytes.toB256 [0xe3, 0xee, 0x16, 0x0e], 129) := by
  decide +kernel

/-- The original static signature ABI is unchanged. -/
abbrev args := V2TransferWithAuthorizationReach.args

/-- Original dispatcher, ABI and public guards reach the internal signed-transfer body. -/
theorem entry_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0xe3ee160e)
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b S M G, Impl.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    ∃ b' S' M' G', ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b' (args sevm ++ S') M' G', Impl.t_4c3f_c87,
        [Impl.t_39e4_c20, Impl.t_0489_c129]⟩ T := by
  unfold Impl.t_0000_c0 at run
  iterate 7 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold Impl.t_0010_c0 at run
  orsd
  iterate 5 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold Impl.t_001a_c0 at run
  iterate 4 orsx
  have word : Sevm.dataWord sevm (Bytes.toB256 [0]) >>> (Bytes.toB256 [0xe0]).toNat =
      0xe3ee160e := selected
  rw [word] at run
  obtain ⟨-, g, _, hg, run⟩ := ObservedReach.selWalk_inlS erase route_authorization run hT
  rw [show Impl.cert.prog[129]? = some Impl.t_1075_c129 from rfl] at hg
  cases hg
  unfold Impl.t_1075_c129 at run
  orsd
  iterate 10 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold Impl.t_108c_c129 at run
  orsd
  iterate 51 orsx
  simp only [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
    0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ] at run
  simp only [ff20_and_word] at run
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[20]? = some Impl.t_3889_c20 from rfl] at hg
  cases hg
  have cont : ∀ f ∈ [Impl.t_0489_c129], f.sstoreFreeIn [] = true := by
    intro f member
    have same := List.mem_singleton.mp member
    subst f
    decide +kernel
  unfold Impl.t_3889_c20 at run
  orsd
  orsx
  orsld
  iterate 7 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold Impl.t_3913_c20 at run
  orsd
  iterate 4 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[83]? = some Impl.t_3f6a_c83 from rfl] at hg
  cases hg
  obtain ⟨_, _, _, _, run⟩ := V22TransferReach.blacklist_reach_observed erase run hT
  unfold Impl.t_391d_c20 at run
  orsd
  iterate 2 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold Impl.t_3973_c20 at run
  orsd
  iterate 4 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[83]? = some Impl.t_3f6a_c83 from rfl] at hg
  cases hg
  obtain ⟨_, _, _, _, run⟩ := V22TransferReach.blacklist_reach_observed erase run hT
  unfold Impl.t_397d_c20 at run
  orsd
  iterate 2 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold Impl.t_39d3_c20 at run
  orsd
  iterate 11 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[87]? = some Impl.t_4c3f_c87 from rfl] at hg
  cases hg
  exact ⟨_, _, _, _, run⟩

abbrev authLine := V2TransferWithAuthorizationReach.authLine

/-- The authorization writer has one occurrence in the actual V2.2 runtime. -/
theorem authPattern_occurrences :
    BytePattern.occurrences (authLine.flatMap Ninst.toBytes) Impl.code.toList = [0x5060] := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

/-- The balance setter's immediate return excludes the authorization flag store. -/
theorem setter_pc_ne_auth {node : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK Impl.code Impl.cert node κ)
    (tree : κ.f = .next (.reg .sstore) .ret) : node.pc ≠ 0x5060 := by
  have checked := ok.check
  rw [tree] at checked
  obtain ⟨_, a, later⟩ := checkNode_nexts [.reg .sstore] .ret checked
  have byte : byteAt Impl.code (κ.pc + 1) = some (Jinst.toUInt8 .jump) := by
    rcases a with _ | ⟨_ | _ | _, a⟩ <;>
      simp only [checkNode, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq] at later
    exact later.1
  intro bad
  rw [← ok.pc_eq, bad] at byte
  have actual : byteAt Impl.code (0x5060 + 1) = some 0x51 := by decide +kernel
  rw [actual] at byte
  contradiction

/-- Actual store discrimination retains the authorization pair or the tagged balance hash. -/
def ActualSource (root node : Exec.Deriv) (owner recipient : Adr) (nonce key : B256) : Prop :=
  (node.pc = 0x5060 ∧ key = mapSlot nonce (mapSlot owner.toB256 16) ∧
    KeccakPairBefore root node (owner.toB256.toBytes ++ (16 : B256).toBytes)
      (nonce.toBytes ++ (mapSlot owner.toB256 16).toBytes)) ∨
  (node.pc ≠ 0x5060 ∧ node.devm.stack[2]? = some 0x40e8 ∧
    key = mapSlot owner.toB256 9 ∧
    ∃ hashPc, KeccakBefore root node (owner.toB256.toBytes ++ (9 : B256).toBytes) hashPc) ∨
  (node.pc ≠ 0x5060 ∧ node.devm.stack[2]? = some 0x40f9 ∧
    key = mapSlot recipient.toB256 9 ∧
    ∃ hashPc, KeccakBefore root node (recipient.toB256.toBytes ++ (9 : B256).toBytes) hashPc)

/-- Convert each selected writer's own observed hashes at the same actual cursor. -/
theorem actualSource_of_observed {root node : Exec.Deriv} {κ : Cursor}
    {owner recipient : Adr} {nonce : B256} {write : Exec.StorageWrite}
    (ok : CursorOK Impl.code Impl.cert node κ)
    (found : Exec.Deriv.successfulSstore? node = some write)
    (source : AuthSource (StepIn root) (Cursor.RawEdgeAt Impl.code Impl.cert root node)
        root.sevm owner nonce (κ.conf node.devm) ∨
      V22TransferReach.ObservedSource (StepIn root)
        (Cursor.RawEdgeAt Impl.code Impl.cert root node)
        root.sevm owner recipient (κ.conf node.devm)) :
    ActualSource root node owner recipient nonce write.key := by
  obtain ⟨_, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  rcases source with ⟨⟨other, keyStack⟩, ⟨tail, shape⟩, hashes⟩ | balance
  · have location := ok.pc_eq_of_prefix_singleton authLine tail shape
      (suffix := []) (by simp only [List.append_nil]) (by decide) authPattern_occurrences
    exact .inl ⟨location, (List.cons.inj (stack.symm.trans keyStack)).1, hashes.actual⟩
  apply Or.inr
  rcases balance with ⟨⟨value, other, keyStack⟩, tree, hash⟩ |
      ⟨⟨value, other, keyStack⟩, tree, hash⟩
  · obtain ⟨occ, next, here, instruction, result, before, edge, after, _, _, hashStack, read⟩ :=
      hash.actual
    exact .inl ⟨setter_pc_ne_auth ok tree,
      by change node.devm.stack = _ at keyStack; rw [keyStack]; rfl,
      (List.cons.inj (stack.symm.trans keyStack)).1,
      _, occ, next, rfl, instruction, result, before, edge, after, hashStack, read⟩
  · obtain ⟨occ, next, here, instruction, result, before, edge, after, _, _, hashStack, read⟩ :=
      hash.actual
    exact .inr ⟨setter_pc_ne_auth ok tree,
      by change node.devm.stack = _ at keyStack; rw [keyStack]; rfl,
      (List.cons.inj (stack.symm.trans keyStack)).1,
      _, occ, next, rfl, instruction, result, before, edge, after, hashStack, read⟩

/-- Every successful signed-transfer store retains its original entry and successful hashes. -/
theorem successfulSstore_source {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = Impl.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0xe3ee160e)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    ActualSource root node (Sevm.dataWord root.sevm 4).toAdr
      (Sevm.dataWord root.sevm 36).toAdr (Sevm.dataWord root.sevm 164) write.key := by
  obtain ⟨decoded, _, _⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, reach, ok⟩ :=
    observed_reach_of_parentPrefix_noStateGas Impl.cert_check pc code hsg chain
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have target : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  change ObservedReach (StepIn root) (Cursor.RawEdgeAt Impl.code Impl.cert root node)
    Impl.cert.prog root.sevm ⟨root.devm, Impl.t_0000_c0, []⟩ (κ.conf node.devm) at reach
  rw [St.self' root.devm] at reach
  obtain ⟨b, S, M, G, run⟩ := entry_reach_observed (fun h => StepIn.toRun h) selected reach target
  obtain ⟨b', signature, S', M', G', run⟩ := pack_reach_observed (fun h => StepIn.toRun h) run target
  have source := body_reach_observed (fun h => StepIn.toRun h) hsg run target
    (by intro f member
        rcases List.mem_cons.mp member with rfl | member
        · decide +kernel
        rcases List.mem_cons.mp member with rfl | member
        · decide +kernel
        have same := List.mem_singleton.mp member
        subst f
        decide +kernel)
  exact actualSource_of_observed ok found source

end Blanc.Lift.Usdc.V22TransferWithAuthorizationReach
