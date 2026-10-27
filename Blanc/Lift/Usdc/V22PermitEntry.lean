import Blanc.Lift.Usdc.V2PermitReach
import Blanc.Lift.Usdc.Impl.Check

/-! Both original V2.2 permit decoders retain their allowance arguments. -/
namespace Blanc.Lift.Usdc.V22PermitEntry
open Jaune Blanc Blanc.Lift
variable {observe : Conf → Conf → Prop}

/-- The checked dispatcher routes permit through its original ABI wrapper. -/
theorem route_vrs : SFunc.selWalk 0xd505accf
    (.next (.reg (.dup 0)) (.next (.push [0x84, 0x56, 0xcb, 0x59] (by decide))
      (.next (.reg .gt) (.next (.push [0x01, 0xd3] (by decide))
        (.branch Impl.t_002b_c0 Impl.t_01d3_c0))))) =
    .inl (Bytes.toB256 [0xd5, 0x05, 0xac, 0xcf], 132) := by
  decide +kernel

/-- The checked dispatcher routes permit through its original ABI wrapper. -/
theorem route_bytes : SFunc.selWalk 0x9fd5a6cf
    (.next (.reg (.dup 0)) (.next (.push [0x84, 0x56, 0xcb, 0x59] (by decide))
      (.next (.reg .gt) (.next (.push [0x01, 0xd3] (by decide))
        (.branch Impl.t_002b_c0 Impl.t_01d3_c0))))) =
    .inl (Bytes.toB256 [0x9f, 0xd5, 0xa6, 0xcf], 149) := by
  decide +kernel

/-- Original dispatcher, ABI and public guards reach the internal permit body. -/
theorem vrs_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0xd505accf)
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b S M G, Impl.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    ∃ b' S' M' G', ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b' (V2PermitReach.args sevm ++ S') M' G', Impl.t_4be7_c88,
        [Impl.t_373b_c24, Impl.t_0489_c132]⟩ T := by
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
      0xd505accf := selected
  rw [word] at run
  obtain ⟨-, g, _, hg, run⟩ := ObservedReach.selWalk_inlS erase route_vrs run hT
  rw [show Impl.cert.prog[132]? = some Impl.t_0f64_c132 from rfl] at hg
  cases hg
  unfold Impl.t_0f64_c132 at run
  orsd
  iterate 10 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold Impl.t_0f7a_c132 at run
  orsd
  iterate 41 orsx
  simp only [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
    0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ] at run
  simp only [ff20_and_word] at run
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[24]? = some Impl.t_36a2_c24 from rfl] at hg
  cases hg
  have cont : ∀ f ∈ [Impl.t_0489_c132], f.sstoreFreeIn [] = true := by
    intro f member
    have same := List.mem_singleton.mp member
    subst f
    decide +kernel
  unfold Impl.t_36a2_c24 at run
  orsd
  orsx
  orsld
  iterate 7 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold Impl.t_372c_c24 at run
  orsd
  iterate 9 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[88]? = some Impl.t_4be7_c88 from rfl] at hg
  cases hg
  exact ⟨_, _, _, _, run⟩

/-- Original dispatcher, ABI and public guards reach the internal permit body. -/
theorem bytes_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0x9fd5a6cf)
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b S M G, Impl.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    ∃ b' signature S' M' G', ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b' (signature :: Sevm.dataWord sevm 100 :: Sevm.dataWord sevm 68 ::
        (Sevm.dataWord sevm 36).toAdr.toB256 :: (Sevm.dataWord sevm 4).toAdr.toB256 :: S') M' G', Impl.t_4692_c94,
        [Impl.t_2ab7_c41, Impl.t_0489_c149]⟩ T := by
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
      0x9fd5a6cf := selected
  rw [word] at run
  obtain ⟨-, g, _, hg, run⟩ := ObservedReach.selWalk_inlS erase route_bytes run hT
  rw [show Impl.cert.prog[149]? = some Impl.t_0b82_c149 from rfl] at hg
  cases hg
  unfold Impl.t_0b82_c149 at run
  orsd
  iterate 10 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold Impl.t_0b98_c149 at run
  orsd
  iterate 39 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold Impl.t_0be5_c149 at run
  orsd
  iterate 9 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold Impl.t_0bf7_c149 at run
  orsd
  iterate 19 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold Impl.t_0c19_c149 at run
  orsd
  iterate 54 orsx
  simp only [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
    0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ] at run
  simp only [ff20_and_word] at run
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[41]? = some Impl.t_2e53_c41 from rfl] at hg
  cases hg
  have cont : ∀ f ∈ [Impl.t_0489_c149], f.sstoreFreeIn [] = true := by
    intro f member
    have same := List.mem_singleton.mp member
    subst f
    decide +kernel
  unfold Impl.t_2e53_c41 at run
  orsd
  orsx
  orsld
  iterate 7 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold Impl.t_2edd_c41 at run
  orsd
  iterate 7 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[94]? = some Impl.t_4692_c94 from rfl] at hg
  cases hg
  exact ⟨_, _, _, _, _, run⟩

/-- Packing the static signature keeps the original allowance arguments below it. -/
theorem pack_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner spender : Adr} {sigS sigR sigV deadline value : B256}
    {b : Devm} {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (sigS :: sigR :: sigV :: deadline :: value ::
        spender.toB256 :: owner.toB256 :: S) M G, Impl.t_4be7_c88, K⟩ T)
    (hT : AtSstore T) :
    ∃ b' signature S' M' G', ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b' (signature :: deadline :: value :: spender.toB256 :: owner.toB256 :: S') M' G',
        Impl.t_4692_c94, Impl.t_373b_c88 :: K⟩ T := by
  unfold Impl.t_4be7_c88 at run
  orsd
  iterate 50 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[94]? = some Impl.t_4692_c94 from rfl] at hg
  cases hg
  exact ⟨_, _, _, _, _, run⟩

/-- The domain-separator helper has no own-frame store, including its name loop. -/
theorem domain_sstoreFree :
    SstoreFreeSet Impl.cert.prog [6, 76, 77, 78, 106, 107] = true := by
  decide +kernel

/-- The checked helper returns one word above the untouched caller stack. -/
theorem domain_return_stack {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} (hsg : sevm.benvStat.rules.stateGas = none)
    {b D : Devm} {tag : B256} {S : List B256} {M : Mem} {G : Nat}
    (run : SFunc.RunP Q Impl.cert.prog sevm
      (St b (tag :: S) M G) Impl.t_4276_c78 (.returned D)) :
    ∃ domain, D.stack = domain :: S := by
  obtain ⟨Y, stack, len⟩ := run.entry_stack_below_noStateGas erase Impl.cert_check hsg
    (k := 78) (e := ⟨0x4276, [.ret], 1⟩) rfl rfl
    (ρ := tag) (X := [tag]) (R := S) rfl (.cons rfl .nil)
  rcases Y with _ | ⟨domain, Y⟩
  · cases len
  rcases Y with _ | ⟨extra, Y⟩
  · exact ⟨domain, stack⟩
  · simp only [List.length_cons] at len
    omega

/-- After the deadline guard, the actual returning domain call preserves permit arguments. -/
theorem domain_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} (hsg : sevm.benvStat.rules.stateGas = none)
    {b : Devm} {flag signature deadline value : B256} {owner spender : Adr}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (flag :: signature :: deadline :: value :: spender.toB256 :: owner.toB256 :: S)
        M G, Impl.t_46c0_c8, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ∃ b' domain M' G', ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b' (domain :: 0x47d3 :: 0 :: signature :: deadline :: value ::
        spender.toB256 :: owner.toB256 :: S) M' G', Impl.t_4738_c8, K⟩ T := by
  unfold Impl.t_46c0_c8 at run
  orsd
  orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold Impl.t_472b_c8 at run
  orsd
  iterate 4 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[78]? = some Impl.t_4276_c78 from rfl] at hg
  cases hg
  obtain ⟨D, returned, _, run⟩ := ObservedReach.return_of_sstoreFree
    domain_sstoreFree (by decide +kernel) run hT
  obtain ⟨domain, stack⟩ := domain_return_stack erase hsg returned
  rw [St.self' D, stack] at run
  exact ⟨_, domain, _, _, run⟩

/-- Both deadline paths join at the same original domain call. -/
theorem deadline_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} (hsg : sevm.benvStat.rules.stateGas = none)
    {b : Devm} {signature deadline value : B256} {owner spender : Adr}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (signature :: deadline :: value :: spender.toB256 :: owner.toB256 :: S)
        M G, Impl.t_4692_c94, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ∃ b' domain M' G', ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b' (domain :: 0x47d3 :: 0 :: signature :: deadline :: value ::
        spender.toB256 :: owner.toB256 :: S) M' G', Impl.t_4738_c8, K⟩ T := by
  unfold Impl.t_4692_c94 at run
  orsd
  iterate 5 orsx
  rcases ObservedReach.rs_branchTo run hT with ⟨-, _, run⟩ | ⟨-, g, _, hg, run⟩
  · unfold Impl.t_46bb_c94 at run
    orsx
    obtain ⟨d', step, run⟩ := ObservedReach.rs_next run hT
    obtain ⟨_, rfl⟩ := ri_timestamp (erase step)
    iterate 3 orsx
    exact domain_reach_observed erase hsg run hT cont
  · rw [show Impl.cert.prog[8]? = some Impl.t_46c0_c8 from rfl] at hg
    cases hg
    exact domain_reach_observed erase hsg run hT cont

/-- The nonce store has its original hash input; crossing it keeps every permit argument. -/
theorem nonce_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {domain signature deadline value : B256} {owner spender : Adr}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (domain :: 0x47d3 :: 0 :: signature :: deadline :: value ::
        spender.toB256 :: owner.toB256 :: S) M G, Impl.t_4738_c8, K⟩ T)
    (hT : AtSstore T) :
    V2_1PermitReach.NonceSource Q observe sevm owner T ∨
      ∃ b' oldNonce M' G', ObservedReach Q observe Impl.cert.prog sevm
        ⟨St b' (oldNonce :: 32 :: 64 :: owner.toB256 :: ff20 :: domain :: 0x47d3 :: 0 ::
          signature :: deadline :: value :: spender.toB256 :: owner.toB256 :: S) M' G',
          SFunc.lineDrop 27 Impl.t_4738_c8, K⟩ T := by
  unfold Impl.t_4738_c8 at run
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
  exact .inr ⟨_, _, _, _, run⟩

end Blanc.Lift.Usdc.V22PermitEntry
