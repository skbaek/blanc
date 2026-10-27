import Blanc.Lift.Usdc.V2_1TransferWithAuthorizationReach
import Blanc.Lift.CursorReturnToward

/-! The original V2.1 receive-authorization prefix and its shared writer suffix. -/
namespace Blanc.Lift.Usdc.V2_1ReceiveWithAuthorizationReach
open Jaune Blanc Blanc.Lift
variable {observe : Conf → Conf → Prop}

/-- The receive path reaches the same checked recovery guard and writer suffix. -/
theorem signature_result_eq : ImplV2_1.t_43c6_c67 = ImplV2_1.t_43c6_c69 := rfl

/-- Only the additional caller guard precedes this validity/signature path. -/
theorem caller_guard_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {nonce amount sigS sigR sigV before after : B256}
    {b : Devm} {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV2_1.cert.prog sevm
      ⟨St b (sigS :: sigR :: sigV :: nonce :: before :: after :: amount ::
        recipient.toB256 :: owner.toB256 :: S) M G, ImplV2_1.t_4469_c67, K⟩ T)
    (hT : AtSstore T) :
    ∃ b' M' G', ObservedReach Q observe ImplV2_1.cert.prog sevm
      ⟨St b' (sigS :: sigR :: sigV :: nonce :: before :: after :: amount ::
        recipient.toB256 :: owner.toB256 :: S) M' G', ImplV2_1.t_44d7_c67, K⟩ T := by
  unfold ImplV2_1.t_4469_c67 at run
  orsd
  iterate 6 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree_halting run.forget hT
      (by decide +kernel) (by decide +kernel)).elim
  exact ⟨_, _, _, run⟩

/-- The internal entry passes the original arguments below the validity helper's frame. -/
theorem validity_call_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {nonce amount sigS sigR sigV before after : B256}
    {b : Devm} {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV2_1.cert.prog sevm
      ⟨St b (sigS :: sigR :: sigV :: nonce :: before :: after :: amount ::
        recipient.toB256 :: owner.toB256 :: S) M G, ImplV2_1.t_44d7_c67, K⟩ T)
    (hT : AtSstore T) :
    ∃ b' M' G', ObservedReach Q observe ImplV2_1.cert.prog sevm
      ⟨St b' (before :: after :: nonce :: owner.toB256 :: 0x44e3 ::
        sigS :: sigR :: sigV :: nonce :: before :: after :: amount ::
        recipient.toB256 :: owner.toB256 :: S) M' G', ImplV2_1.t_47ff_c82,
        ImplV2_1.t_44e3_c67 :: K⟩ T := by
  unfold ImplV2_1.t_44d7_c67 at run
  orsd
  iterate 6 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2_1.cert.prog[82]? = some ImplV2_1.t_47ff_c82 from rfl] at hg
  cases hg
  exact ⟨_, _, _, run⟩

/-- Signature preparation keeps the original arguments below the recovery helper's frame. -/
theorem signature_call_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {nonce amount sigS sigR sigV before after : B256}
    {b : Devm} {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV2_1.cert.prog sevm
      ⟨St b (sigS :: sigR :: sigV :: nonce :: before :: after :: amount ::
        recipient.toB256 :: owner.toB256 :: S) M G, ImplV2_1.t_44e3_c67, K⟩ T)
    (hT : AtSstore T) :
    ∃ b' ptr domain M' G', ObservedReach Q observe ImplV2_1.cert.prog sevm
      ⟨St b' (ptr :: sigS :: sigR :: sigV :: domain :: 0x43c6 :: owner.toB256 ::
        ptr :: sigS :: sigR :: sigV :: nonce :: before :: after :: amount ::
        recipient.toB256 :: owner.toB256 :: S) M' G', ImplV2_1.t_46b5_c83,
        ImplV2_1.t_43c6_c67 :: K⟩ T := by
  unfold ImplV2_1.t_44e3_c67 at run
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
        recipient.toB256 :: owner.toB256 :: S) M G, ImplV2_1.t_4469_c67, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    V2_1TransferWithAuthorizationReach.AuthSource Q observe sevm owner nonce T ∨
      V2_1TransferReach.ObservedSource Q observe sevm owner recipient T := by
  obtain ⟨b₀, M₀, G₀, run⟩ := caller_guard_reach_observed erase run hT
  obtain ⟨b', M', G', run⟩ := validity_call_reach_observed erase run hT
  obtain ⟨D, returned, _, run⟩ := ObservedReach.return_of_sstoreFree
    V2_1TransferWithAuthorizationReach.validity_sstoreFree (by decide +kernel) run hT
  have stack := V2_1TransferWithAuthorizationReach.validity_return_stack erase hsg returned
  rw [St.self' D, stack] at run
  obtain ⟨b'', ptr, domain, M'', G'', run⟩ := signature_call_reach_observed erase run hT
  obtain ⟨D, returned, _, run⟩ := ObservedReach.return_of_sstoreFree
    V2_1TransferWithAuthorizationReach.signature_sstoreFree (by decide +kernel) run hT
  obtain ⟨result, stack⟩ := V2_1TransferWithAuthorizationReach.signature_return_stack erase hsg returned
  rw [St.self' D, stack] at run
  exact V2_1TransferWithAuthorizationReach.signature_result_reach_observed erase run hT cont

/-- The checked dispatcher routes receive through its original ABI wrapper. -/
theorem route_receive : SFunc.selWalk 0xef55bec6
    (.next (.reg (.dup 0)) (.next (.push [0x7f, 0x2e, 0xec, 0xc3] (by decide))
      (.next (.reg .gt) (.next (.push [0x01, 0xb2] (by decide))
        (.branch ImplV2_1.t_002b_c0 ImplV2_1.t_01b2_c0))))) =
    .inl (Bytes.toB256 [0xef, 0x55, 0xbe, 0xc6], 97) := by
  decide +kernel

/-- Both authorization selectors decode the same ABI words. -/
abbrev args := V2_1TransferWithAuthorizationReach.args

/-- Original dispatcher, ABI and public guards reach the internal signed-transfer body. -/
theorem entry_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0xef55bec6)
    (run : ObservedReach Q observe ImplV2_1.cert.prog sevm
      ⟨St b S M G, ImplV2_1.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    ∃ b' S' M' G', ObservedReach Q observe ImplV2_1.cert.prog sevm
      ⟨St b' (args sevm ++ S') M' G', ImplV2_1.t_4469_c67,
        [ImplV2_1.t_351a_c10, ImplV2_1.t_0452_c97]⟩ T := by
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
      0xef55bec6 := selected
  rw [word] at run
  obtain ⟨-, g, _, hg, run⟩ := ObservedReach.selWalk_inlS erase route_receive run hT
  rw [show ImplV2_1.cert.prog[97]? = some ImplV2_1.t_0cc1_c97 from rfl] at hg
  cases hg
  unfold ImplV2_1.t_0cc1_c97 at run
  orsd
  iterate 10 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold ImplV2_1.t_0cd8_c97 at run
  orsd
  iterate 51 orsx
  simp only [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
    0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ] at run
  simp only [ff20_and_word] at run
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2_1.cert.prog[10]? = some ImplV2_1.t_35d8_c10 from rfl] at hg
  cases hg
  have cont : ∀ f ∈ [ImplV2_1.t_0452_c97], f.sstoreFreeIn [] = true := by
    intro f member
    have same := List.mem_singleton.mp member
    subst f
    decide +kernel
  unfold ImplV2_1.t_35d8_c10 at run
  orsd
  orsx
  orsld
  iterate 7 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2_1.t_3662_c10 at run
  orsd
  iterate 13 orsx
  orsld
  iterate 6 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2_1.t_36e3_c10 at run
  orsd
  iterate 13 orsx
  orsld
  iterate 6 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2_1.t_3764_c10 at run
  orsd
  iterate 11 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2_1.cert.prog[67]? = some ImplV2_1.t_4469_c67 from rfl] at hg
  cases hg
  exact ⟨_, _, _, _, run⟩


abbrev authLine := V2TransferWithAuthorizationReach.authLine

/-- Every successful receive-authorization store is attributed to its original entry and hashes. -/
theorem successfulSstore_source {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV2_1.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0xef55bec6)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    V2_1TransferWithAuthorizationReach.ActualSource root node (Sevm.dataWord root.sevm 4).toAdr
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
  exact V2_1TransferWithAuthorizationReach.actualSource_of_observed ok found source

end Blanc.Lift.Usdc.V2_1ReceiveWithAuthorizationReach
