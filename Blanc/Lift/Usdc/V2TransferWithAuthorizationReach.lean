import Blanc.Lift.Usdc.V2TransferReach
import Blanc.Lift.CursorKeccakOrder
import Blanc.Lift.FrameSkip

/-! Original successful authorization and balance hashes for V2 signed transfers. -/
namespace Blanc.Lift.Usdc.V2TransferWithAuthorizationReach
open Jaune Blanc Blanc.Lift
variable {observe : Conf → Conf → Prop}

def authLine : List Ninst := [.reg .sstore, .reg .mload, .reg (.dup 3)]

/-- The authorization flag's actual key and ordered original hash pair. -/
def AuthSourceFor (Q : Sevm → Devm → Ninst → Devm → Prop)
    (observe : Conf → Conf → Prop) (fs : List SFunc) (sevm : Sevm) (owner : Adr) (nonce : B256)
    (T : Conf) : Prop :=
  (∃ rest, T.d.stack = mapSlot nonce (mapSlot owner.toB256 16) :: rest) ∧
  (∃ tail, T.f = authLine.foldr SFunc.next tail) ∧
  ObservedKeccakPair Q observe fs sevm
    (owner.toB256.toBytes ++ (16 : B256).toBytes)
    (nonce.toBytes ++ (mapSlot owner.toB256 16).toBytes)

/-- V2 specializes the authorization writer's original observed program. -/
abbrev AuthSource (Q : Sevm → Devm → Ninst → Devm → Prop)
    (observe : Conf → Conf → Prop) := AuthSourceFor Q observe ImplV2.cert.prog

/-- The auth writer either reaches its own store or returns through the same observed path. -/
theorem auth_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {fs : List SFunc} {sevm : Sevm} {owner : Adr} {nonce tag : B256} {b : Devm}
    {S : List B256} {M : Mem} {G : Nat} {f : SFunc} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe fs sevm
      ⟨St b (nonce :: owner.toB256 :: tag :: S) M G, ImplV2.t_4e5e_c85, f :: K⟩ T)
    (hT : AtSstore T) :
    AuthSourceFor Q observe fs sevm owner nonce T ∨
      ∃ b' M' G', ObservedReach Q observe fs sevm
        ⟨St b' S M' G', f, K⟩ T := by
  unfold ImplV2.t_4e5e_c85 at run
  orsd
  iterate 3 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    B256.and_comm owner.toB256 ff20, ff20_and_adr] at run
  iterate 12 orsx
  obtain ⟨_, firstHash, run⟩ := ObservedKeccak.of_next_linked erase run hT
    (input := owner.toB256.toBytes ++ (16 : B256).toBytes) (shape := fun _ => True)
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [32]).toNat = 32 from rfl] at run firstHash
  rw [Mem.read_two_word_writes_at_raw] at run firstHash
  have run := run.withPrefix
  iterate 8 orsx
  obtain ⟨_, secondHash, run⟩ := ObservedKeccak.of_next erase run hT
    (input := nonce.toBytes ++ (mapSlot owner.toB256 16).toBytes) (shape := fun _ => True)
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [32]).toNat = 32 from rfl] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  orsx
  orsld
  iterate 5 orsx
  rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
  · exact .inl ⟨⟨_, rfl⟩, ⟨_, rfl⟩, _, firstHash, secondHash⟩
  obtain ⟨b', G', rfl⟩ := SolcStorageReturn.ri_sstore_any (erase step)
  iterate 6 orsx
  obtain ⟨d', step, run⟩ := ObservedReach.rs_next run hT
  obtain ⟨_, rfl⟩ := ri_log3 (erase step)
  iterate 2 orsx
  obtain ⟨_, _, b'', G'', same, run⟩ := ObservedReach.rs_retM run hT
  cases same
  exact .inr ⟨_, _, _, Relation.ReflTransGen.mono (fun _ _ h => ⟨h.1, h.2.1⟩) _ _ run⟩

/-- Every store after signature validation is an auth flag or an actual balance writer. -/
theorem writes_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {nonce amount ptr sigS sigR sigV before after : B256}
    {b : Devm} {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b (ptr :: sigS :: sigR :: sigV :: nonce :: before :: after :: amount ::
        recipient.toB256 :: owner.toB256 :: S) M G, ImplV2.t_4bcd_c67, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    AuthSource Q observe sevm owner nonce T ∨
      V2TransferReach.ObservedSource Q observe sevm owner recipient T := by
  unfold ImplV2.t_4bcd_c67 at run
  orsd
  iterate 4 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2.cert.prog[85]? = some ImplV2.t_4e5e_c85 from rfl] at hg
  cases hg
  rcases auth_reach_observed erase run hT with found | ⟨b', M', G', run⟩
  · exact .inl found
  unfold ImplV2.t_4bd7_c67 at run
  orsd
  iterate 5 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2.cert.prog[74]? = some ImplV2.t_3ef8_c74 from rfl] at hg
  cases hg
  apply Or.inr
  apply V2TransferReach.body_reach_observed erase run hT
  intro f member
  rcases List.mem_cons.mp member with rfl | member
  · decide +kernel
  exact cont f member

/-- The checked dispatcher routes transfer through its original ABI wrapper. -/
theorem route_authorization : SFunc.selWalk 0xe3ee160e
    (.next (.reg (.dup 0)) (.next (.push [0x8a, 0x6d, 0xb9, 0xc3] (by decide))
      (.next (.reg .gt) (.next (.push [0x01, 0xbd] (by decide))
        (.branch ImplV2.t_002b_c0 ImplV2.t_01bd_c0))))) =
    .inl (Bytes.toB256 [0xe3, 0xee, 0x16, 0x0e], 104) := by
  decide +kernel

/-- The ABI-decoded signed-transfer arguments in the order used by the runtime. -/
def args (sevm : Sevm) : List B256 :=
  [Sevm.dataWord sevm 260, Sevm.dataWord sevm 228, Sevm.dataWord sevm 196 &&& 255,
    Sevm.dataWord sevm 164, Sevm.dataWord sevm 132, Sevm.dataWord sevm 100,
    Sevm.dataWord sevm 68, (Sevm.dataWord sevm 36).toAdr.toB256,
    (Sevm.dataWord sevm 4).toAdr.toB256]

/-- Original dispatcher, ABI and public guards reach the internal signed-transfer body. -/
theorem entry_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0xe3ee160e)
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b S M G, ImplV2.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    ∃ b' S' M' G', ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b' (args sevm ++ S') M' G', ImplV2.t_4aac_c67,
        [ImplV2.t_31d0_c15, ImplV2.t_0470_c104]⟩ T := by
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
      0xe3ee160e := selected
  rw [word] at run
  obtain ⟨-, g, _, hg, run⟩ := ObservedReach.selWalk_inlS erase route_authorization run hT
  rw [show ImplV2.cert.prog[104]? = some ImplV2.t_0d43_c104 from rfl] at hg
  cases hg
  unfold ImplV2.t_0d43_c104 at run
  orsd
  iterate 10 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold ImplV2.t_0d5a_c104 at run
  orsd
  iterate 51 orsx
  simp only [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
    0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ] at run
  simp only [ff20_and_word] at run
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2.cert.prog[15]? = some ImplV2.t_38fe_c15 from rfl] at hg
  cases hg
  have cont : ∀ f ∈ [ImplV2.t_0470_c104], f.sstoreFreeIn [] = true := by
    intro f member
    have same := List.mem_singleton.mp member
    subst f
    decide +kernel
  unfold ImplV2.t_38fe_c15 at run
  orsd
  orsx
  orsld
  iterate 7 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2.t_3988_c15 at run
  orsd
  iterate 13 orsx
  orsld
  iterate 6 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2.t_3a09_c15 at run
  orsd
  iterate 13 orsx
  orsld
  iterate 6 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2.t_3a8a_c15 at run
  orsd
  iterate 11 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2.cert.prog[67]? = some ImplV2.t_4aac_c67 from rfl] at hg
  cases hg
  exact ⟨_, _, _, _, run⟩


/-- The internal entry passes the original arguments below the validity helper's frame. -/
theorem validity_call_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {nonce amount sigS sigR sigV before after : B256}
    {b : Devm} {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b (sigS :: sigR :: sigV :: nonce :: before :: after :: amount ::
        recipient.toB256 :: owner.toB256 :: S) M G, ImplV2.t_4aac_c67, K⟩ T)
    (hT : AtSstore T) :
    ∃ b' M' G', ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b' (before :: after :: nonce :: owner.toB256 :: 0x4ab8 ::
        sigS :: sigR :: sigV :: nonce :: before :: after :: amount ::
        recipient.toB256 :: owner.toB256 :: S) M' G', ImplV2.t_4d9e_c83,
        ImplV2.t_4ab8_c67 :: K⟩ T := by
  unfold ImplV2.t_4aac_c67 at run
  orsd
  iterate 6 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2.cert.prog[83]? = some ImplV2.t_4d9e_c83 from rfl] at hg
  cases hg
  exact ⟨_, _, _, run⟩

/-- A selected storage writer rules out the recovery guard's reverting branch. -/
theorem signature_result_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr}
    {result nonce amount ptr sigS sigR sigV before after : B256}
    {b : Devm} {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b (result :: owner.toB256 :: ptr :: sigS :: sigR :: sigV :: nonce ::
        before :: after :: amount :: recipient.toB256 :: owner.toB256 :: S) M G,
        ImplV2.t_4b4b_c67, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    AuthSource Q observe sevm owner nonce T ∨
      V2TransferReach.ObservedSource Q observe sevm owner recipient T := by
  unfold ImplV2.t_4b4b_c67 at run
  orsd
  iterate 4 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT
      (by decide +kernel) cont).elim
  exact writes_reach_observed erase run hT cont

/-- The validity helper and its authorization-state check contain no storage writer. -/
theorem validity_sstoreFree : SstoreFreeSet ImplV2.cert.prog [83, 89] = true := by
  decide +kernel

/-- The recovery helper's own-frame closure contains no storage writer. -/
theorem signature_sstoreFree : SstoreFreeSet ImplV2.cert.prog [6, 84, 91] = true := by
  decide +kernel

/-- A returning validity check preserves all signed-transfer arguments below its frame. -/
theorem validity_return_stack {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} (hsg : sevm.benvStat.rules.stateGas = none)
    {b D : Devm} {a c n o tag : B256} {S : List B256} {M : Mem} {G : Nat}
    (run : SFunc.RunP Q ImplV2.cert.prog sevm
      (St b (a :: c :: n :: o :: tag :: S) M G) ImplV2.t_4d9e_c83 (.returned D)) :
    D.stack = S := by
  obtain ⟨Y, stack, len⟩ := run.entry_stack_below_noStateGas erase ImplV2.cert_check hsg
    (k := 83) (e := ⟨0x4d9e, [.unk, .unk, .unk, .unk, .ret], 0⟩) rfl rfl
    (ρ := tag) (X := [a, c, n, o, tag]) (R := S) rfl
    (.cons trivial (.cons trivial (.cons trivial (.cons trivial (.cons rfl .nil)))))
  have empty : Y = [] := List.eq_nil_of_length_eq_zero len
  simpa only [empty, List.nil_append] using stack

/-- A returning recovery helper leaves one word above the untouched signed-transfer arguments. -/
theorem signature_return_stack {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} (hsg : sevm.benvStat.rules.stateGas = none)
    {b D : Devm} {ptr s r v domain tag : B256} {S : List B256} {M : Mem} {G : Nat}
    (run : SFunc.RunP Q ImplV2.cert.prog sevm
      (St b (ptr :: s :: r :: v :: domain :: tag :: S) M G) ImplV2.t_4d2c_c84 (.returned D)) :
    ∃ result, D.stack = result :: S := by
  obtain ⟨Y, stack, len⟩ := run.entry_stack_below_noStateGas erase ImplV2.cert_check hsg
    (k := 84) (e := ⟨0x4d2c, [.unk, .unk, .unk, .unk, .unk, .ret], 1⟩) rfl rfl
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
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b (sigS :: sigR :: sigV :: nonce :: before :: after :: amount ::
        recipient.toB256 :: owner.toB256 :: S) M G, ImplV2.t_4ab8_c67, K⟩ T)
    (hT : AtSstore T) :
    ∃ b' ptr domain M' G', ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b' (ptr :: sigS :: sigR :: sigV :: domain :: 0x4b4b :: owner.toB256 ::
        ptr :: sigS :: sigR :: sigV :: nonce :: before :: after :: amount ::
        recipient.toB256 :: owner.toB256 :: S) M' G', ImplV2.t_4d2c_c84,
        ImplV2.t_4b4b_c67 :: K⟩ T := by
  unfold ImplV2.t_4ab8_c67 at run
  orsd
  iterate 68 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    B256.and_comm owner.toB256 ff20, ff20_and_adr] at run
  orsld
  iterate 10 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2.cert.prog[84]? = some ImplV2.t_4d2c_c84 from rfl] at hg
  cases hg
  exact ⟨_, _, _, _, _, run⟩


/-- The auth writer's three-instruction prefix has one occurrence in the actual runtime. -/
theorem authPattern_occurrences :
    BytePattern.occurrences (authLine.flatMap Ninst.toBytes) ImplV2.code.toList = [0x4eb8] := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

/-- The source alternatives retain precisely the selected writer's own original hashes. -/
def ActualSource (root node : Exec.Deriv) (owner recipient : Adr) (nonce key : B256) : Prop :=
  (node.pc = 0x4eb8 ∧ key = mapSlot nonce (mapSlot owner.toB256 16) ∧
    KeccakPairBefore root node (owner.toB256.toBytes ++ (16 : B256).toBytes)
      (nonce.toBytes ++ (mapSlot owner.toB256 16).toBytes)) ∨
  V2TransferReach.ActualSource root node owner recipient key

/-- Convert the observed writer alternative at the same checked cursor to raw provenance. -/
theorem actualSource_of_observed {root node : Exec.Deriv} {κ : Cursor}
    {owner recipient : Adr} {nonce : B256} {write : Exec.StorageWrite}
    (ok : CursorOK ImplV2.code ImplV2.cert node κ)
    (found : Exec.Deriv.successfulSstore? node = some write)
    (source : AuthSource (StepIn root) (Cursor.RawEdgeAt ImplV2.code ImplV2.cert root node)
        root.sevm owner nonce (κ.conf node.devm) ∨
      V2TransferReach.ObservedSource (StepIn root)
        (Cursor.RawEdgeAt ImplV2.code ImplV2.cert root node)
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
  · have location := ok.pc_eq_of_prefix_singleton V2TransferReach.ownerLine tail shape
      (suffix := []) (by simp only [List.append_nil]) (by decide)
      V2TransferReach.ownerPattern_occurrences
    obtain ⟨occ, next, here, instruction, result, before, edge, after, _, _, hashStack, read⟩ :=
      hash.actual
    exact .inl ⟨location, (List.cons.inj (stack.symm.trans keyStack)).1,
      _, occ, next, rfl, instruction, result, before, edge, after, hashStack, read⟩
  · have location := ok.pc_eq_of_prefix_singleton V2TransferReach.recipientLine tail shape
      (suffix := []) (by simp only [List.append_nil]) (by decide)
      V2TransferReach.recipientPattern_occurrences
    obtain ⟨occ, next, here, instruction, result, before, edge, after, _, _, hashStack, read⟩ :=
      hash.actual
    exact .inr ⟨location, (List.cons.inj (stack.symm.trans keyStack)).1,
      _, occ, next, rfl, instruction, result, before, edge, after, hashStack, read⟩

end Blanc.Lift.Usdc.V2TransferWithAuthorizationReach
