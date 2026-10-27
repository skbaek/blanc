import Blanc.Lift.Usdc.V22ReceiveWithAuthorizationBytesReach

/-! Original-entry V2.2 bytes-signature transfer stores and hash provenance. -/
namespace Blanc.Lift.Usdc.V22TransferWithAuthorizationBytesReach
open Jaune Blanc Blanc.Lift
variable {observe : Conf → Conf → Prop}

/-- The checked dispatcher routes transfer authorization through its original ABI wrapper. -/
theorem route_transfer_bytes : SFunc.selWalk 0xcf092995
    (.next (.reg (.dup 0)) (.next (.push [0x84, 0x56, 0xcb, 0x59] (by decide))
      (.next (.reg .gt) (.next (.push [0x01, 0xd3] (by decide))
        (.branch Impl.t_002b_c0 Impl.t_01d3_c0))))) =
    .inl (Bytes.toB256 [0xcf, 0x09, 0x29, 0x95], 138) := by
  decide +kernel

/-- Both bytes-signature overloads preserve the same six original fields. -/
abbrev args := V22ReceiveWithAuthorizationBytesReach.args

/-- Original dispatcher, ABI and public guards reach the internal signed-transfer body. -/
theorem entry_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0xcf092995)
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b S M G, Impl.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    ∃ b' signature S' M' G', ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b' (args sevm signature ++ S') M' G', Impl.t_4b49_c90,
        [Impl.t_2d6f_c30, Impl.t_0489_c138]⟩ T := by
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
      0xcf092995 := selected
  rw [word] at run
  obtain ⟨-, g, _, hg, run⟩ := ObservedReach.selWalk_inlS erase route_transfer_bytes run hT
  rw [show Impl.cert.prog[138]? = some Impl.t_0e80_c138 from rfl] at hg
  cases hg
  unfold Impl.t_0e80_c138 at run
  orsd
  iterate 10 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold Impl.t_0e96_c138 at run
  orsd
  iterate 49 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold Impl.t_0eef_c138 at run
  orsd
  iterate 9 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold Impl.t_0f01_c138 at run
  orsd
  iterate 19 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold Impl.t_0f23_c138 at run
  orsd
  iterate 54 orsx
  simp only [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
    0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ] at run
  simp only [ff20_and_word] at run
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[30]? = some Impl.t_3549_c30 from rfl] at hg
  cases hg
  have cont : ∀ f ∈ [Impl.t_0489_c138], f.sstoreFreeIn [] = true := by
    intro f member
    have same := List.mem_singleton.mp member
    subst f
    decide +kernel
  unfold Impl.t_3549_c30 at run
  orsd
  orsx
  orsld
  iterate 7 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold Impl.t_35d3_c30 at run
  orsd
  iterate 4 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[83]? = some Impl.t_3f6a_c83 from rfl] at hg
  cases hg
  obtain ⟨_, _, _, _, run⟩ := V22TransferReach.blacklist_reach_observed erase run hT
  unfold Impl.t_35dd_c30 at run
  orsd
  iterate 2 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold Impl.t_3633_c30 at run
  orsd
  iterate 4 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[83]? = some Impl.t_3f6a_c83 from rfl] at hg
  cases hg
  obtain ⟨_, _, _, _, run⟩ := V22TransferReach.blacklist_reach_observed erase run hT
  unfold Impl.t_363d_c30 at run
  orsd
  iterate 2 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold Impl.t_3693_c30 at run
  orsd
  iterate 9 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[90]? = some Impl.t_4b49_c90 from rfl] at hg
  cases hg
  exact ⟨_, _, _, _, _, run⟩

/-- Every successful bytes-signature transfer store retains its original entry and successful hashes. -/
theorem successfulSstore_source {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = Impl.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0xcf092995)
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
  obtain ⟨b, signature, S, M, G, run⟩ := entry_reach_observed (fun h => StepIn.toRun h) selected reach target
  have source := V22TransferWithAuthorizationReach.body_reach_observed (fun h => StepIn.toRun h) hsg run target
    (by intro f member
        rcases List.mem_cons.mp member with rfl | member
        · decide +kernel
        have same := List.mem_singleton.mp member
        subst f
        decide +kernel)
  exact V22TransferWithAuthorizationReach.actualSource_of_observed ok found source

end Blanc.Lift.Usdc.V22TransferWithAuthorizationBytesReach
