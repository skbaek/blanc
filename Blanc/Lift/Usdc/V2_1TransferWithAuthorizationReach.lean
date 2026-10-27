import Blanc.Lift.Usdc.V2TransferWithAuthorizationReach
import Blanc.Lift.Usdc.V2_1TransferReach
import Blanc.Lift.ObservedReachSplit

/-! V2.1 signed-transfer stores and their original successful hash observations. -/
namespace Blanc.Lift.Usdc.V2_1TransferWithAuthorizationReach
open Jaune Blanc Blanc.Lift
variable {observe : Conf → Conf → Prop}

/-- V2.1 uses the same authorization flag writer with its own observed program. -/
abbrev AuthSource (Q : Sevm → Devm → Ninst → Devm → Prop)
    (observe : Conf → Conf → Prop) :=
  V2TransferWithAuthorizationReach.AuthSourceFor Q observe ImplV2_1.cert.prog

/-- Equality of the checked instruction trees permits reuse of the auth writer proof. -/
theorem auth_writer_eq : ImplV2_1.t_48bf_c84 = ImplV2.t_4e5e_c85 := rfl

/-- Every store after signature validation is an auth flag or an actual balance writer. -/
theorem writes_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {nonce amount ptr sigS sigR sigV before after : B256}
    {b : Devm} {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV2_1.cert.prog sevm
      ⟨St b (ptr :: sigS :: sigR :: sigV :: nonce :: before :: after :: amount ::
        recipient.toB256 :: owner.toB256 :: S) M G, ImplV2_1.t_4448_c69, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    AuthSource Q observe sevm owner nonce T ∨
      V2_1TransferReach.ObservedSource Q observe sevm owner recipient T := by
  unfold ImplV2_1.t_4448_c69 at run
  orsd
  iterate 4 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2_1.cert.prog[84]? = some ImplV2_1.t_48bf_c84 from rfl] at hg
  cases hg
  rcases V2TransferWithAuthorizationReach.auth_reach_observed erase run hT with found | ⟨b', M', G', run⟩
  · exact .inl found
  unfold ImplV2_1.t_4452_c69 at run
  orsd
  iterate 5 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2_1.cert.prog[73]? = some ImplV2_1.t_3b21_c73 from rfl] at hg
  cases hg
  apply Or.inr
  apply V2_1TransferReach.body_reach_observed erase run hT
  intro f member
  rcases List.mem_cons.mp member with rfl | member
  · decide +kernel
  exact cont f member

/-- The internal entry passes the original arguments below the validity helper's frame. -/
theorem validity_call_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {nonce amount sigS sigR sigV before after : B256}
    {b : Devm} {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV2_1.cert.prog sevm
      ⟨St b (sigS :: sigR :: sigV :: nonce :: before :: after :: amount ::
        recipient.toB256 :: owner.toB256 :: S) M G, ImplV2_1.t_4327_c69, K⟩ T)
    (hT : AtSstore T) :
    ∃ b' M' G', ObservedReach Q observe ImplV2_1.cert.prog sevm
      ⟨St b' (before :: after :: nonce :: owner.toB256 :: 0x4333 ::
        sigS :: sigR :: sigV :: nonce :: before :: after :: amount ::
        recipient.toB256 :: owner.toB256 :: S) M' G', ImplV2_1.t_47ff_c82,
        ImplV2_1.t_4333_c69 :: K⟩ T := by
  unfold ImplV2_1.t_4327_c69 at run
  orsd
  iterate 6 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2_1.cert.prog[82]? = some ImplV2_1.t_47ff_c82 from rfl] at hg
  cases hg
  exact ⟨_, _, _, run⟩

/-- A selected storage writer rules out the recovery guard's reverting branch. -/
theorem signature_result_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr}
    {result nonce amount ptr sigS sigR sigV before after : B256}
    {b : Devm} {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV2_1.cert.prog sevm
      ⟨St b (result :: owner.toB256 :: ptr :: sigS :: sigR :: sigV :: nonce ::
        before :: after :: amount :: recipient.toB256 :: owner.toB256 :: S) M G,
        ImplV2_1.t_43c6_c69, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    AuthSource Q observe sevm owner nonce T ∨
      V2_1TransferReach.ObservedSource Q observe sevm owner recipient T := by
  unfold ImplV2_1.t_43c6_c69 at run
  orsd
  iterate 4 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT
      (by decide +kernel) cont).elim
  exact writes_reach_observed erase run hT cont

/-- The validity helper and its authorization-state check contain no storage writer. -/
theorem validity_sstoreFree : SstoreFreeSet ImplV2_1.cert.prog [82, 87] = true := by
  decide +kernel

/-- The recovery helper's own-frame closure contains no storage writer. -/
theorem signature_sstoreFree : SstoreFreeSet ImplV2_1.cert.prog [7, 83, 89] = true := by
  decide +kernel

/-- A returning validity check preserves all signed-transfer arguments below its frame. -/
theorem validity_return_stack {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} (hsg : sevm.benvStat.rules.stateGas = none)
    {b D : Devm} {a c n o tag : B256} {S : List B256} {M : Mem} {G : Nat}
    (run : SFunc.RunP Q ImplV2_1.cert.prog sevm
      (St b (a :: c :: n :: o :: tag :: S) M G) ImplV2_1.t_47ff_c82 (.returned D)) :
    D.stack = S := by
  obtain ⟨Y, stack, len⟩ := run.entry_stack_below_noStateGas erase ImplV2_1.cert_check hsg
    (k := 82) (e := ⟨0x47ff, [.unk, .unk, .unk, .unk, .ret], 0⟩) rfl rfl
    (ρ := tag) (X := [a, c, n, o, tag]) (R := S) rfl
    (.cons trivial (.cons trivial (.cons trivial (.cons trivial (.cons rfl .nil)))))
  have empty : Y = [] := List.eq_nil_of_length_eq_zero len
  simpa only [empty, List.nil_append] using stack

/-- A returning recovery helper leaves one word above the untouched signed-transfer arguments. -/
theorem signature_return_stack {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} (hsg : sevm.benvStat.rules.stateGas = none)
    {b D : Devm} {ptr s r v domain tag : B256} {S : List B256} {M : Mem} {G : Nat}
    (run : SFunc.RunP Q ImplV2_1.cert.prog sevm
      (St b (ptr :: s :: r :: v :: domain :: tag :: S) M G) ImplV2_1.t_46b5_c83 (.returned D)) :
    ∃ result, D.stack = result :: S := by
  obtain ⟨Y, stack, len⟩ := run.entry_stack_below_noStateGas erase ImplV2_1.cert_check hsg
    (k := 83) (e := ⟨0x46b5, [.unk, .unk, .unk, .unk, .unk, .ret], 1⟩) rfl rfl
    (ρ := tag) (X := [ptr, s, r, v, domain, tag]) (R := S) rfl
    (.cons trivial (.cons trivial (.cons trivial (.cons trivial (.cons trivial (.cons rfl .nil))))))
  cases Y with
  | nil => cases len
  | cons result rest =>
    have empty : rest = [] := List.eq_nil_of_length_eq_zero (by
      simp only [List.length_cons] at len
      omega)
    subst rest
    exact ⟨result, stack⟩

/-- Signature preparation keeps the original arguments below the recovery helper's frame. -/
theorem signature_call_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {nonce amount sigS sigR sigV before after : B256}
    {b : Devm} {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV2_1.cert.prog sevm
      ⟨St b (sigS :: sigR :: sigV :: nonce :: before :: after :: amount ::
        recipient.toB256 :: owner.toB256 :: S) M G, ImplV2_1.t_4333_c69, K⟩ T)
    (hT : AtSstore T) :
    ∃ b' ptr domain M' G', ObservedReach Q observe ImplV2_1.cert.prog sevm
      ⟨St b' (ptr :: sigS :: sigR :: sigV :: domain :: 0x43c6 :: owner.toB256 ::
        ptr :: sigS :: sigR :: sigV :: nonce :: before :: after :: amount ::
        recipient.toB256 :: owner.toB256 :: S) M' G', ImplV2_1.t_46b5_c83,
        ImplV2_1.t_43c6_c69 :: K⟩ T := by
  unfold ImplV2_1.t_4333_c69 at run
  orsd
  iterate 68 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    B256.and_comm owner.toB256 ff20, ff20_and_adr] at run
  orsld
  iterate 10 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2_1.cert.prog[83]? = some ImplV2_1.t_46b5_c83 from rfl] at hg
  cases hg
  exact ⟨_, _, _, _, _, run⟩


/-- Both store-free helpers return on the same observed path before the selected writer. -/
theorem body_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} (hsg : sevm.benvStat.rules.stateGas = none)
    {owner recipient : Adr} {nonce amount sigS sigR sigV before after : B256}
    {b : Devm} {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV2_1.cert.prog sevm
      ⟨St b (sigS :: sigR :: sigV :: nonce :: before :: after :: amount ::
        recipient.toB256 :: owner.toB256 :: S) M G, ImplV2_1.t_4327_c69, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    AuthSource Q observe sevm owner nonce T ∨
      V2_1TransferReach.ObservedSource Q observe sevm owner recipient T := by
  obtain ⟨b', M', G', run⟩ := validity_call_reach_observed erase run hT
  obtain ⟨D, returned, _, run⟩ := ObservedReach.return_of_sstoreFree
    validity_sstoreFree (by decide +kernel) run hT
  have stack := validity_return_stack erase hsg returned
  rw [St.self' D, stack] at run
  obtain ⟨b'', ptr, domain, M'', G'', run⟩ := signature_call_reach_observed erase run hT
  obtain ⟨D, returned, _, run⟩ := ObservedReach.return_of_sstoreFree
    signature_sstoreFree (by decide +kernel) run hT
  obtain ⟨result, stack⟩ := signature_return_stack erase hsg returned
  rw [St.self' D, stack] at run
  exact signature_result_reach_observed erase run hT cont

/-- The checked dispatcher routes transfer through its original ABI wrapper. -/
theorem route_authorization : SFunc.selWalk 0xe3ee160e
    (.next (.reg (.dup 0)) (.next (.push [0x7f, 0x2e, 0xec, 0xc3] (by decide))
      (.next (.reg .gt) (.next (.push [0x01, 0xb2] (by decide))
        (.branch ImplV2_1.t_002b_c0 ImplV2_1.t_01b2_c0))))) =
    .inl (Bytes.toB256 [0xe3, 0xee, 0x16, 0x0e], 101) := by
  decide +kernel

/-- The two runtimes decode the same signed-transfer ABI words. -/
abbrev args := V2TransferWithAuthorizationReach.args

/-- Original dispatcher, ABI and public guards reach the internal signed-transfer body. -/
theorem entry_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0xe3ee160e)
    (run : ObservedReach Q observe ImplV2_1.cert.prog sevm
      ⟨St b S M G, ImplV2_1.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    ∃ b' S' M' G', ObservedReach Q observe ImplV2_1.cert.prog sevm
      ⟨St b' (args sevm ++ S') M' G', ImplV2_1.t_4327_c69,
        [ImplV2_1.t_351a_c15, ImplV2_1.t_0452_c101]⟩ T := by
  unfold ImplV2_1.t_0000_c0 at run
  iterate 7 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold ImplV2_1.t_0010_c0 at run
  orsd
  iterate 5 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold ImplV2_1.t_001a_c0 at run
  iterate 4 orsx
  have word : Sevm.dataWord sevm (Bytes.toB256 [0]) >>> (Bytes.toB256 [0xe0]).toNat =
      0xe3ee160e := selected
  rw [word] at run
  obtain ⟨-, g, _, hg, run⟩ := ObservedReach.selWalk_inlS erase route_authorization run hT
  rw [show ImplV2_1.cert.prog[101]? = some ImplV2_1.t_0c14_c101 from rfl] at hg
  cases hg
  unfold ImplV2_1.t_0c14_c101 at run
  orsd
  iterate 10 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold ImplV2_1.t_0c2b_c101 at run
  orsd
  iterate 51 orsx
  simp only [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
    0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ] at run
  simp only [ff20_and_word] at run
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2_1.cert.prog[15]? = some ImplV2_1.t_337d_c15 from rfl] at hg
  cases hg
  have cont : ∀ f ∈ [ImplV2_1.t_0452_c101], f.sstoreFreeIn [] = true := by
    intro f member
    have same := List.mem_singleton.mp member
    subst f
    decide +kernel
  unfold ImplV2_1.t_337d_c15 at run
  orsd
  orsx
  orsld
  iterate 7 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2_1.t_3407_c15 at run
  orsd
  iterate 13 orsx
  orsld
  iterate 6 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2_1.t_3488_c15 at run
  orsd
  iterate 13 orsx
  orsld
  iterate 6 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2_1.t_3509_c15 at run
  orsd
  iterate 11 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2_1.cert.prog[69]? = some ImplV2_1.t_4327_c69 from rfl] at hg
  cases hg
  exact ⟨_, _, _, _, run⟩


abbrev authLine := V2TransferWithAuthorizationReach.authLine

/-- The auth writer's three-instruction prefix has one occurrence in the actual runtime. -/
theorem authPattern_occurrences :
    BytePattern.occurrences (authLine.flatMap Ninst.toBytes) ImplV2_1.code.toList = [0x4919] := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

/-- The source alternatives retain precisely the selected writer's own original hashes. -/
def ActualSource (root node : Exec.Deriv) (owner recipient : Adr) (nonce key : B256) : Prop :=
  (node.pc = 0x4919 ∧ key = mapSlot nonce (mapSlot owner.toB256 16) ∧
    KeccakPairBefore root node (owner.toB256.toBytes ++ (16 : B256).toBytes)
      (nonce.toBytes ++ (mapSlot owner.toB256 16).toBytes)) ∨
  V2_1TransferReach.ActualSource root node owner recipient key

/-- Convert the observed writer alternative at the same checked cursor to raw provenance. -/
theorem actualSource_of_observed {root node : Exec.Deriv} {κ : Cursor}
    {owner recipient : Adr} {nonce : B256} {write : Exec.StorageWrite}
    (ok : CursorOK ImplV2_1.code ImplV2_1.cert node κ)
    (found : Exec.Deriv.successfulSstore? node = some write)
    (source : AuthSource (StepIn root) (Cursor.RawEdgeAt ImplV2_1.code ImplV2_1.cert root node)
        root.sevm owner nonce (κ.conf node.devm) ∨
      V2_1TransferReach.ObservedSource (StepIn root)
        (Cursor.RawEdgeAt ImplV2_1.code ImplV2_1.cert root node)
        root.sevm owner recipient (κ.conf node.devm)) :
    ActualSource root node owner recipient nonce write.key := by
  obtain ⟨_, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  rcases source with ⟨⟨other, keyStack⟩, ⟨tail, shape⟩, hashes⟩ | balance
  · have location := ok.pc_eq_of_prefix_singleton authLine tail shape
      (suffix := []) (by simp only [List.append_nil]) (by decide) authPattern_occurrences
    exact .inl ⟨location, (List.cons.inj (stack.symm.trans keyStack)).1, hashes.actual⟩
  apply Or.inr
  rcases balance with ⟨⟨other, keyStack⟩, ⟨tail, shape⟩, hash⟩ |
      ⟨⟨other, keyStack⟩, ⟨tail, shape⟩, hash⟩
  · have location := ok.pc_eq_of_prefix_singleton V2_1TransferReach.ownerLine tail shape
      (suffix := []) (by simp only [List.append_nil]) (by decide)
      V2_1TransferReach.ownerPattern_occurrences
    obtain ⟨occ, next, here, instruction, result, before, edge, after, _, _, hashStack, read⟩ :=
      hash.actual
    exact .inl ⟨location, (List.cons.inj (stack.symm.trans keyStack)).1,
      _, occ, next, rfl, instruction, result, before, edge, after, hashStack, read⟩
  · have location := ok.pc_eq_of_prefix_singleton V2_1TransferReach.recipientLine tail shape
      (suffix := []) (by simp only [List.append_nil]) (by decide)
      V2_1TransferReach.recipientPattern_occurrences
    obtain ⟨occ, next, here, instruction, result, before, edge, after, _, _, hashStack, read⟩ :=
      hash.actual
    exact .inr ⟨location, (List.cons.inj (stack.symm.trans keyStack)).1,
      _, occ, next, rfl, instruction, result, before, edge, after, hashStack, read⟩

/-- Every successful signed-transfer store is attributed to its original entry and hashes. -/
theorem successfulSstore_source {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV2_1.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0xe3ee160e)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    ActualSource root node (Sevm.dataWord root.sevm 4).toAdr
      (Sevm.dataWord root.sevm 36).toAdr (Sevm.dataWord root.sevm 164) write.key := by
  obtain ⟨decoded, _, _⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, reach, ok⟩ :=
    observed_reach_of_parentPrefix_noStateGas ImplV2_1.cert_check pc code hsg chain
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have target : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  change ObservedReach (StepIn root) (Cursor.RawEdgeAt ImplV2_1.code ImplV2_1.cert root node)
    ImplV2_1.cert.prog root.sevm ⟨root.devm, ImplV2_1.t_0000_c0, []⟩ (κ.conf node.devm) at reach
  rw [St.self' root.devm] at reach
  obtain ⟨b, S, M, G, run⟩ := entry_reach_observed (fun h => StepIn.toRun h) selected reach target
  have source := body_reach_observed (fun h => StepIn.toRun h) hsg run target
    (by intro f member; rcases List.mem_cons.mp member with rfl | member
        · decide +kernel
        have same := List.mem_singleton.mp member
        subst f
        decide +kernel)
  exact actualSource_of_observed ok found source

end Blanc.Lift.Usdc.V2_1TransferWithAuthorizationReach
