import Blanc.Lift.Usdc.V22TransferFromCallee
import Blanc.Lift.Usdc.OldTransferFromEntry

/-! Original V2.2 transferFrom dispatch, ABI decoding, and public guards. -/
namespace Blanc.Lift.Usdc.V22TransferFromEntry
open Jaune Blanc Blanc.Lift OldTransferFromEntry
variable {observe : Conf → Conf → Prop}

/-- The selected prefix enters the balance body with the actual saved caller words. -/
theorem public_to_body {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm} {amount : B256}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (amount :: recipient.toB256 :: owner.toB256 :: S) M G,
        Impl.t_1437_c68, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ∃ b' M' G', ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b' (amount :: recipient.toB256 :: owner.toB256 :: 0x1678 ::
        guardedStack sevm owner recipient amount S) M' G',
        Impl.t_3f98_c93, Impl.t_1678_c68 :: K⟩ T := by
  unfold Impl.t_1437_c68 at run
  orsd
  orsx
  orsld
  iterate 9 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold Impl.t_14c4_c68 at run
  orsd
  iterate 4 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[83]? = some Impl.t_3f6a_c83 from rfl] at hg
  cases hg
  obtain ⟨b', value, M', G', run⟩ := V22TransferReach.blacklist_reach_observed erase run hT
  unfold Impl.t_14ce_c68 at run
  orsd
  iterate 2 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold Impl.t_1524_c68 at run
  orsd
  iterate 4 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[83]? = some Impl.t_3f6a_c83 from rfl] at hg
  cases hg
  obtain ⟨b', value, M', G', run⟩ := V22TransferReach.blacklist_reach_observed erase run hT
  unfold Impl.t_152e_c68 at run
  orsd
  iterate 2 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold Impl.t_1584_c68 at run
  orsd
  iterate 4 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[83]? = some Impl.t_3f6a_c83 from rfl] at hg
  cases hg
  obtain ⟨b', value, M', G', run⟩ := V22TransferReach.blacklist_reach_observed erase run hT
  unfold Impl.t_158e_c68 at run
  orsd
  iterate 2 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold Impl.t_15e4_c68 at run
  orsd
  iterate 24 orsx
  orsld
  iterate 4 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold Impl.t_166d_c68 at run
  orsd
  iterate 5 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[93]? = some Impl.t_3f98_c93 from rfl] at hg
  cases hg
  exact ⟨_, _, _, run⟩

/-- The checked dispatcher selects the exact transferFrom ABI wrapper. -/
theorem route_transferFrom : SFunc.selWalk 0x23b872dd
    (.next (.reg (.dup 0)) (.next (.push [0x84, 0x56, 0xcb, 0x59] (by decide))
      (.next (.reg .gt) (.next (.push [0x01, 0xd3] (by decide))
        (.branch Impl.t_002b_c0 Impl.t_01d3_c0))))) =
    .inl (Bytes.toB256 [0x23, 0xb8, 0x72, 0xdd], 175) := by
  decide +kernel

/-- The original root reaches the balance callee without assuming final frame success. -/
theorem entry_to_body {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0x23b872dd)
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b S M G, Impl.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    ∃ S' b' M' G', ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b' (Sevm.dataWord sevm 68 :: (Sevm.dataWord sevm 36).toAdr.toB256 ::
        (Sevm.dataWord sevm 4).toAdr.toB256 :: 0x1678 ::
        guardedStack sevm (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr
          (Sevm.dataWord sevm 68) S') M' G', Impl.t_3f98_c93,
        [Impl.t_1678_c68, Impl.t_0428_c175]⟩ T := by
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
      0x23b872dd := selected
  rw [word] at run
  obtain ⟨-, g, _, hg, run⟩ := ObservedReach.selWalk_inlS erase route_transferFrom run hT
  rw [show Impl.cert.prog[175]? = some Impl.t_048b_c175 from rfl] at hg
  cases hg
  unfold Impl.t_048b_c175 at run
  orsd
  iterate 10 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold Impl.t_04a1_c175 at run
  orsd
  iterate 19 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl] at run
  rw [ff20_and_word, ff20_and_word] at run
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[68]? = some Impl.t_1437_c68 from rfl] at hg
  cases hg
  obtain ⟨b', M', G', run⟩ := public_to_body erase run hT
    (by intro f member; have same := List.mem_singleton.mp member; subst f; decide +kernel)
  exact ⟨_, b', M', G', run⟩

end Blanc.Lift.Usdc.V22TransferFromEntry
