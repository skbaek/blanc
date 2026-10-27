import Blanc.Lift.Usdc.V2AllowanceSetterReach
import Blanc.Lift.Usdc.V2TransferWithAuthorizationReach

/-! Original-store provenance for V2 approval, increase and decrease authorizations. -/
namespace Blanc.Lift.Usdc.V2OwnerAuthorizationReach

open Jaune Blanc Blanc.Lift ModernCallerReach

variable {observe : Conf → Conf → Prop}

def selector : Action → B256
  | .approve => 0xe1560fd3
  | .increase => 0xc237108f
  | .decrease => 0xb0086095

def wrapperEntry : Action → Nat
  | .approve => 103
  | .increase => 109
  | .decrease => 113

def wrapperReturn : Action → SFunc
  | .approve => ImplV2.t_0470_c103
  | .increase => ImplV2.t_0470_c109
  | .decrease => ImplV2.t_0470_c113

def body : Action → SFunc
  | .approve => ImplV2.t_4976_c66
  | .increase => ImplV2.t_4625_c70
  | .decrease => ImplV2.t_4456_c72

def bodyReturn : Action → SFunc
  | .approve => ImplV2.t_31d0_c14
  | .increase => ImplV2.t_31d0_c21
  | .decrease => ImplV2.t_31d0_c25

theorem route (action : Action) : SFunc.selWalk (selector action)
    (.next (.reg (.dup 0)) (.next (.push [0x8a, 0x6d, 0xb9, 0xc3] (by decide))
      (.next (.reg .gt) (.next (.push [0x01, 0xbd] (by decide))
        (.branch ImplV2.t_002b_c0 ImplV2.t_01bd_c0))))) =
    .inl (selector action, wrapperEntry action) := by
  cases action <;> decide +kernel

theorem entry_reach_observed (action : Action) {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = selector action)
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b S M G, ImplV2.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    ∃ b' S' M' G', ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b' (V2TransferWithAuthorizationReach.args sevm ++ S') M' G', body action,
        [bodyReturn action, wrapperReturn action]⟩ T := by
  have routeHere := route action
  cases action
  all_goals
    simp only [selector, wrapperEntry, wrapperReturn, body, bodyReturn] at selected routeHere ⊢
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
    have word : Sevm.dataWord sevm (Bytes.toB256 [0]) >>> (Bytes.toB256 [0xe0]).toNat = _ := selected
    rw [word] at run
    obtain ⟨-, g, _, hg, run⟩ := ObservedReach.selWalk_inlS erase routeHere run hT
    first
    | rw [show ImplV2.cert.prog[103]? = some ImplV2.t_0cd7_c103 from rfl] at hg
    | rw [show ImplV2.cert.prog[109]? = some ImplV2.t_0b52_c109 from rfl] at hg
    | rw [show ImplV2.cert.prog[113]? = some ImplV2.t_0a9b_c113 from rfl] at hg
    cases hg
    first
    | unfold ImplV2.t_0cd7_c103 at run
    | unfold ImplV2.t_0b52_c109 at run
    | unfold ImplV2.t_0a9b_c113 at run
    orsd
    iterate 10 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
        (fun _ h => by cases h)).elim
    first
    | unfold ImplV2.t_0cee_c103 at run
    | unfold ImplV2.t_0b69_c109 at run
    | unfold ImplV2.t_0ab2_c113 at run
    orsd
    iterate 51 orsx
    simp only [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
      ] at run
    simp only [ff20_and_word] at run
    obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
    first
    | rw [show ImplV2.cert.prog[14]? = some ImplV2.t_3761_c14 from rfl] at hg
    | rw [show ImplV2.cert.prog[21]? = some ImplV2.t_328f_c21 from rfl] at hg
    | rw [show ImplV2.cert.prog[25]? = some ImplV2.t_3033_c25 from rfl] at hg
    cases hg
    have cont103 : ∀ f ∈ [ImplV2.t_0470_c103], f.sstoreFreeIn [] = true := by
      intro f member; have same := List.mem_singleton.mp member; subst f; decide +kernel
    first
    | unfold ImplV2.t_3761_c14 at run
    | unfold ImplV2.t_328f_c21 at run
    | unfold ImplV2.t_3033_c25 at run
    orsd
    orsx
    orsld
    iterate 7 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont103).elim
    first
    | unfold ImplV2.t_37eb_c14 at run
    | unfold ImplV2.t_3319_c21 at run
    | unfold ImplV2.t_30bd_c25 at run
    orsd
    iterate 13 orsx
    orsld
    iterate 6 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont103).elim
    first
    | unfold ImplV2.t_386c_c14 at run
    | unfold ImplV2.t_339a_c21 at run
    | unfold ImplV2.t_313e_c25 at run
    orsd
    iterate 13 orsx
    orsld
    iterate 6 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont103).elim
    first
    | unfold ImplV2.t_38ed_c14 at run
    | unfold ImplV2.t_341b_c21 at run
    | unfold ImplV2.t_31bf_c25 at run
    orsd
    iterate 11 orsx
    obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
    first
    | rw [show ImplV2.cert.prog[66]? = some ImplV2.t_4976_c66 from rfl] at hg
    | rw [show ImplV2.cert.prog[70]? = some ImplV2.t_4625_c70 from rfl] at hg
    | rw [show ImplV2.cert.prog[72]? = some ImplV2.t_4456_c72 from rfl] at hg
    cases hg
    exact ⟨_, _, _, _, run⟩


theorem body_source (action : Action)
    {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} (hsg : sevm.benvStat.rules.stateGas = none)
    {owner spender : Adr} {nonce value sigS sigR sigV before after : B256}
    {b : Devm} {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b (sigS :: sigR :: sigV :: nonce :: before :: after :: value ::
        spender.toB256 :: owner.toB256 :: S) M G, body action, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    V2TransferWithAuthorizationReach.AuthSource Q observe sevm owner nonce T ∨
      ApprovalSource Q observe .v2 sevm owner spender T := by
  cases action
  all_goals
    simp only [body] at run
    first
    | unfold ImplV2.t_4976_c66 at run
    | unfold ImplV2.t_4625_c70 at run
    | unfold ImplV2.t_4456_c72 at run
    orsd
    iterate 6 orsx
    obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
    rw [show ImplV2.cert.prog[83]? = some ImplV2.t_4d9e_c83 from rfl] at hg
    cases hg
    obtain ⟨D, returned, _, run⟩ := ObservedReach.return_of_sstoreFree
      V2TransferWithAuthorizationReach.validity_sstoreFree (by decide +kernel) run hT
    have stack := V2TransferWithAuthorizationReach.validity_return_stack erase hsg returned
    rw [St.self' D, stack] at run
    first
    | unfold ImplV2.t_4982_c66 at run
    | unfold ImplV2.t_4631_c70 at run
    | unfold ImplV2.t_4462_c72 at run
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
    obtain ⟨D, returned, _, run⟩ := ObservedReach.return_of_sstoreFree
      V2TransferWithAuthorizationReach.signature_sstoreFree (by decide +kernel) run hT
    obtain ⟨result, stack⟩ := V2TransferWithAuthorizationReach.signature_return_stack erase hsg returned
    rw [St.self' D, stack] at run
    first
    | unfold ImplV2.t_4a15_c66 at run
    | unfold ImplV2.t_46c4_c70 at run
    | unfold ImplV2.t_44f5_c72 at run
    orsd
    iterate 4 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
    first
    | unfold ImplV2.t_4a97_c66 at run
    | unfold ImplV2.t_4746_c70 at run
    | unfold ImplV2.t_4577_c72 at run
    orsd
    iterate 4 orsx
    obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
    rw [show ImplV2.cert.prog[85]? = some ImplV2.t_4e5e_c85 from rfl] at hg
    cases hg
    rcases V2TransferWithAuthorizationReach.auth_reach_observed erase run hT with found | ⟨b', M', G', run⟩
    · exact .inl found
    first
    | unfold ImplV2.t_4aa1_c66 at run
    | unfold ImplV2.t_4750_c70 at run
    | unfold ImplV2.t_4581_c72 at run
    orsd
    iterate 5 orsx
    obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
    apply Or.inr
    first
    | rw [show ImplV2.cert.prog[81]? = some ImplV2.t_3db1_c81 from rfl] at hg
      cases hg
      apply approval_core_source erase run hT
    | rw [show ImplV2.cert.prog[79]? = some ImplV2.t_41b3_c79 from rfl] at hg
      cases hg
      apply V2AllowanceSetterReach.increase_source erase hsg run hT
    | rw [show ImplV2.cert.prog[75]? = some ImplV2.t_43fa_c75 from rfl] at hg
      cases hg
      apply V2AllowanceSetterReach.decrease_source erase hsg run hT
    intro f member
    rcases List.mem_cons.mp member with rfl | member
    · decide +kernel
    exact cont f member

def ActualSource (root node : Exec.Deriv) (owner spender : Adr) (nonce key : B256) : Prop :=
  (node.pc = 0x4eb8 ∧ key = mapSlot nonce (mapSlot owner.toB256 16) ∧
    KeccakPairBefore root node (owner.toB256.toBytes ++ (16 : B256).toBytes)
      (nonce.toBytes ++ (mapSlot owner.toB256 16).toBytes)) ∨
  (node.pc ≠ 0x4eb8 ∧ key = allowSlot owner spender ∧
    KeccakPairBefore root node (owner.toB256.toBytes ++ (10 : B256).toBytes)
      (spender.toB256.toBytes ++ (mapSlot owner.toB256 10).toBytes))

theorem successfulSstore_source (action : Action) {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV2.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Sevm.selector root.sevm = selector action)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    ActualSource root node (Sevm.dataWord root.sevm 4).toAdr
      (Sevm.dataWord root.sevm 36).toAdr (Sevm.dataWord root.sevm 164) write.key := by
  obtain ⟨decoded, rest, targetStack⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, reach, ok⟩ :=
    observed_reach_of_parentPrefix_noStateGas ImplV2.cert_check pc code hsg chain
  obtain ⟨g, tree, _⟩ := ok.tree_of_sstore decoded
  have atStore : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  change ObservedReach (StepIn root) (Cursor.RawEdgeAt ImplV2.code ImplV2.cert root node)
    ImplV2.cert.prog root.sevm ⟨root.devm, ImplV2.t_0000_c0, []⟩ (κ.conf node.devm) at reach
  rw [St.self' root.devm] at reach
  obtain ⟨b, S, M, G, run⟩ := entry_reach_observed action (fun h => StepIn.toRun h) selected reach atStore
  have source := body_source action (fun h => StepIn.toRun h) hsg run atStore (by
    intro f member
    rcases List.mem_cons.mp member with rfl | member
    · cases action <;> decide +kernel
    have same := List.mem_singleton.mp member
    subst f
    cases action <;> decide +kernel)
  rcases source with ⟨⟨other, keyStack⟩, ⟨tail, shape⟩, hashes⟩ |
      ⟨⟨other, keyStack⟩, ⟨tail, shape⟩, hashes⟩
  · have location := ok.pc_eq_of_prefix_singleton V2TransferWithAuthorizationReach.authLine tail shape
      (suffix := []) (by simp only [List.append_nil]) (by decide)
      V2TransferWithAuthorizationReach.authPattern_occurrences
    exact .inl ⟨location, (List.cons.inj (targetStack.symm.trans keyStack)).1, hashes.actual⟩
  · have bytes := ok.bytesAt_of_prefix approvalLine tail shape
    have different : node.pc ≠ 0x4eb8 := by
      intro equal
      rw [equal] at bytes
      have actual : bytesAt ImplV2.code 0x4eb8 (approvalLine.flatMap Ninst.toBytes) = false := by decide +kernel
      rw [actual] at bytes
      contradiction
    exact .inr ⟨different, (List.cons.inj (targetStack.symm.trans keyStack)).1, hashes.actual⟩

end Blanc.Lift.Usdc.V2OwnerAuthorizationReach
