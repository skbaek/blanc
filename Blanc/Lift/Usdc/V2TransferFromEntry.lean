import Blanc.Lift.Usdc.V2TransferFromCallee

/-! Original V2 transferFrom dispatch and guards retain the actual caller stack. -/
namespace Blanc.Lift.Usdc.V2TransferFromEntry

open Jaune Blanc Blanc.Lift
variable {observe : Conf → Conf → Prop}

/-- The public checks leave these words below the internal transfer call. -/
def guardedStack (sevm : Sevm) (owner recipient : Adr) (amount : B256)
    (S : List B256) : List B256 :=
  recipient.toB256 :: owner.toB256 :: sevm.caller.toB256 :: 0 ::
    amount :: recipient.toB256 :: owner.toB256 :: S

/-- Any later store passes the actual public checks and enters the balance callee. -/
theorem public_to_body {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm} {amount : B256}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b (amount :: recipient.toB256 :: owner.toB256 :: S) M G,
        ImplV2.t_11f1_c59, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ∃ b' M' G', ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b' (amount :: recipient.toB256 :: owner.toB256 :: 0x147d ::
        guardedStack sevm owner recipient amount S) M' G',
        ImplV2.t_3ef8_c74, ImplV2.t_147d_c59 :: K⟩ T := by
  unfold ImplV2.t_11f1_c59 at run
  orsd
  orsx
  orsld
  iterate 9 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2.t_127e_c59 at run
  orsd
  iterate 11 orsx
  orsld
  iterate 4 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2.t_12e7_c59 at run
  orsd
  iterate 13 orsx
  orsld
  iterate 6 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2.t_1368_c59 at run
  orsd
  iterate 13 orsx
  orsld
  iterate 6 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2.t_13e9_c59 at run
  orsd
  iterate 24 orsx
  orsld
  iterate 4 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold ImplV2.t_1472_c59 at run
  orsd
  iterate 5 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2.cert.prog[74]? = some ImplV2.t_3ef8_c74 from rfl] at hg
  cases hg
  exact ⟨_, _, _, run⟩

/-- The checked dispatcher routes transferFrom through its original ABI wrapper. -/
theorem route_transferFrom : SFunc.selWalk 0x23b872dd
    (.next (.reg (.dup 0)) (.next (.push [0x8a, 0x6d, 0xb9, 0xc3] (by decide))
      (.next (.reg .gt) (.next (.push [0x01, 0xbd] (by decide))
        (.branch ImplV2.t_002b_c0 ImplV2.t_01bd_c0))))) =
    .inl (Bytes.toB256 [0x23, 0xb8, 0x72, 0xdd], 147) := by
  decide +kernel

/-- Follow the selected prefix to its store; the final frame outcome is unrestricted. -/
theorem entry_to_body {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0x23b872dd)
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b S M G, ImplV2.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    ∃ S' b' M' G', ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b' (Sevm.dataWord sevm 68 :: (Sevm.dataWord sevm 36).toAdr.toB256 ::
        (Sevm.dataWord sevm 4).toAdr.toB256 :: 0x147d ::
        guardedStack sevm (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr
          (Sevm.dataWord sevm 68) S') M' G', ImplV2.t_3ef8_c74,
        [ImplV2.t_147d_c59, ImplV2.t_0407_c147]⟩ T := by
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
      0x23b872dd := selected
  rw [word] at run
  obtain ⟨-, g, _, hg, run⟩ := ObservedReach.selWalk_inlS erase route_transferFrom run hT
  rw [show ImplV2.cert.prog[147]? = some ImplV2.t_0472_c147 from rfl] at hg
  cases hg
  unfold ImplV2.t_0472_c147 at run
  orsd
  iterate 10 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold ImplV2.t_0488_c147 at run
  orsd
  iterate 19 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl] at run
  rw [ff20_and_word, ff20_and_word] at run
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2.cert.prog[59]? = some ImplV2.t_11f1_c59 from rfl] at hg
  cases hg
  have cont : ∀ f ∈ [ImplV2.t_0407_c147], f.sstoreFreeIn [] = true := by
    intro f member
    have same := List.mem_singleton.mp member
    subst f
    decide +kernel
  obtain ⟨b', M', G', run⟩ := public_to_body erase run hT cont
  exact ⟨_, b', M', G', run⟩

end Blanc.Lift.Usdc.V2TransferFromEntry
