import Blanc.Lift.Usdc.V22TransferWithAuthorizationReach
import Blanc.Lift.CursorReturnToward

/-! Original V2.2 receive-authorization stores with observed helper returns. -/
namespace Blanc.Lift.Usdc.V22ReceiveWithAuthorizationReach
open Jaune Blanc Blanc.Lift
variable {observe : Conf → Conf → Prop}

/-- The receive path preserves the checked authorization and balance writer suffix. -/
theorem signature_result_eq : Impl.t_467d_c95 = Impl.t_467d_c90 := rfl

/-- Only the additional caller guard precedes this validity/signature path. -/
theorem caller_guard_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {nonce amount signature before after : B256}
    {b : Devm} {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (signature :: nonce :: before :: after :: amount ::
        recipient.toB256 :: owner.toB256 :: S) M G, Impl.t_4571_c95, K⟩ T)
    (hT : AtSstore T) :
    ∃ b' M' G', ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b' (signature :: nonce :: before :: after :: amount ::
        recipient.toB256 :: owner.toB256 :: S) M' G', Impl.t_45df_c95, K⟩ T := by
  unfold Impl.t_4571_c95 at run
  orsd
  iterate 6 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree_halting run.forget hT
      (by decide +kernel) (by decide +kernel)).elim
  exact ⟨_, _, _, run⟩

/-- The internal entry passes the original arguments below the validity helper's frame. -/
theorem validity_call_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {nonce amount signature before after : B256}
    {b : Devm} {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (signature :: nonce :: before :: after :: amount ::
        recipient.toB256 :: owner.toB256 :: S) M G, Impl.t_45df_c95, K⟩ T)
    (hT : AtSstore T) :
    ∃ b' M' G', ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b' (before :: after :: nonce :: owner.toB256 :: 0x45eb ::
        signature :: nonce :: before :: after :: amount ::
        recipient.toB256 :: owner.toB256 :: S) M' G', Impl.t_4dc8_c112,
        Impl.t_45eb_c95 :: K⟩ T := by
  unfold Impl.t_45df_c95 at run
  orsd
  iterate 6 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[112]? = some Impl.t_4dc8_c112 from rfl] at hg
  cases hg
  exact ⟨_, _, _, run⟩

/-- Signature preparation preserves the original transfer arguments below validation. -/
theorem signature_call_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {signature nonce amount before after : B256}
    {b : Devm} {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (signature :: nonce :: before :: after :: amount ::
        recipient.toB256 :: owner.toB256 :: S) M G, Impl.t_45eb_c95, K⟩ T)
    (hT : AtSstore T) :
    ∃ b' hash M' G', ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b' (signature :: hash :: owner.toB256 :: 0x467d ::
        signature :: nonce :: before :: after :: amount ::
        recipient.toB256 :: owner.toB256 :: S) M' G', Impl.t_4e88_c111,
        Impl.t_467d_c95 :: K⟩ T := by
  unfold Impl.t_45eb_c95 at run
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
        recipient.toB256 :: owner.toB256 :: S) M G, Impl.t_4571_c95, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    V22TransferWithAuthorizationReach.AuthSource Q observe sevm owner nonce T ∨
      V22TransferReach.ObservedSource Q observe sevm owner recipient T := by
  obtain ⟨b₀, M₀, G₀, run⟩ := caller_guard_reach_observed erase run hT
  obtain ⟨b', M', G', run⟩ := validity_call_reach_observed erase run hT
  obtain ⟨D, returned, _, run⟩ := ObservedReach.return_of_sstoreFree
    V22TransferWithAuthorizationReach.validity_sstoreFree (by decide +kernel) run hT
  have stack := V22TransferWithAuthorizationReach.validity_return_stack erase hsg returned
  rw [St.self' D, stack] at run
  obtain ⟨b'', hash, M'', G'', run⟩ := signature_call_reach_observed erase run hT
  obtain ⟨D, returned, _, run⟩ := ObservedReach.return_of_sstoreFree
    V22TransferWithAuthorizationReach.signature_sstoreFree (by decide +kernel) run hT
  have stack := V22TransferWithAuthorizationReach.signature_return_stack erase hsg returned
  rw [St.self' D, stack] at run
  exact V22TransferWithAuthorizationReach.writes_reach_observed erase run hT cont

/-- The original ABI's signature words are packed without losing the six transfer fields. -/
theorem pack_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {nonce amount sigS sigR sigV before after : B256}
    {b : Devm} {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (sigS :: sigR :: sigV :: nonce :: before :: after :: amount ::
        recipient.toB256 :: owner.toB256 :: S) M G, Impl.t_4c83_c84, K⟩ T)
    (hT : AtSstore T) :
    ∃ b' signature S' M' G', ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b' (signature :: nonce :: before :: after :: amount ::
        recipient.toB256 :: owner.toB256 :: S') M' G', Impl.t_4571_c95,
        Impl.t_2d6f_c84 :: K⟩ T := by
  unfold Impl.t_4c83_c84 at run
  orsd
  iterate 52 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[95]? = some Impl.t_4571_c95 from rfl] at hg
  cases hg
  exact ⟨_, _, _, _, _, run⟩


/-- The checked dispatcher routes receive authorization through its original ABI wrapper. -/
theorem route_receive : SFunc.selWalk 0xef55bec6
    (.next (.reg (.dup 0)) (.next (.push [0x84, 0x56, 0xcb, 0x59] (by decide))
      (.next (.reg .gt) (.next (.push [0x01, 0xd3] (by decide))
        (.branch Impl.t_002b_c0 Impl.t_01d3_c0))))) =
    .inl (Bytes.toB256 [0xef, 0x55, 0xbe, 0xc6], 125) := by
  decide +kernel

/-- The original static signature ABI is unchanged. -/
abbrev args := V2TransferWithAuthorizationReach.args

/-- Original dispatcher, ABI and public guards reach the internal signed-transfer body. -/
theorem entry_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0xef55bec6)
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b S M G, Impl.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    ∃ b' S' M' G', ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b' (args sevm ++ S') M' G', Impl.t_4c83_c84,
        [Impl.t_39e4_c15, Impl.t_0489_c125]⟩ T := by
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
      0xef55bec6 := selected
  rw [word] at run
  obtain ⟨-, g, _, hg, run⟩ := ObservedReach.selWalk_inlS erase route_receive run hT
  rw [show Impl.cert.prog[125]? = some Impl.t_1122_c125 from rfl] at hg
  cases hg
  unfold Impl.t_1122_c125 at run
  orsd
  iterate 10 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold Impl.t_1139_c125 at run
  orsd
  iterate 51 orsx
  simp only [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
    0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ] at run
  simp only [ff20_and_word] at run
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[15]? = some Impl.t_3aa2_c15 from rfl] at hg
  cases hg
  have cont : ∀ f ∈ [Impl.t_0489_c125], f.sstoreFreeIn [] = true := by
    intro f member
    have same := List.mem_singleton.mp member
    subst f
    decide +kernel
  unfold Impl.t_3aa2_c15 at run
  orsd
  orsx
  orsld
  iterate 7 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold Impl.t_3b2c_c15 at run
  orsd
  iterate 4 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[83]? = some Impl.t_3f6a_c83 from rfl] at hg
  cases hg
  obtain ⟨_, _, _, _, run⟩ := V22TransferReach.blacklist_reach_observed erase run hT
  unfold Impl.t_3b36_c15 at run
  orsd
  iterate 2 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold Impl.t_3b8c_c15 at run
  orsd
  iterate 4 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[83]? = some Impl.t_3f6a_c83 from rfl] at hg
  cases hg
  obtain ⟨_, _, _, _, run⟩ := V22TransferReach.blacklist_reach_observed erase run hT
  unfold Impl.t_3b96_c15 at run
  orsd
  iterate 2 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold Impl.t_3bec_c15 at run
  orsd
  iterate 11 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[84]? = some Impl.t_4c83_c84 from rfl] at hg
  cases hg
  exact ⟨_, _, _, _, run⟩

/-- Every successful receive-authorization store retains its original entry and successful hashes. -/
theorem successfulSstore_source {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = Impl.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0xef55bec6)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    V22TransferWithAuthorizationReach.ActualSource root node (Sevm.dataWord root.sevm 4).toAdr
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
  exact V22TransferWithAuthorizationReach.actualSource_of_observed ok found source

end Blanc.Lift.Usdc.V22ReceiveWithAuthorizationReach
