import Blanc.Lift.Usdc.V22PermitEntry
import Blanc.Lift.CallEffects

/-! The original signature-library path retains the V2.2 permit allowance arguments. -/
namespace Blanc.Lift.Usdc.V22PermitReach
open Jaune Blanc Blanc.Lift
variable {observe : Conf → Conf → Prop}

/-- The actual library instruction preserves the caller stack below its six operands;
the following guards and approval setter retain the same owner and spender. -/
theorem library_tail_source {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} (hsg : sevm.benvStat.rules.stateGas = none)
    {b : Devm} {gas library ii is oi os y0 y1 y2 y3 y4 y5 value : B256}
    {owner spender : Adr} {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (gas :: library :: ii :: is :: oi :: os :: y0 :: y1 :: y2 :: y3 :: y4 :: y5 ::
        value :: spender.toB256 :: owner.toB256 :: S) M G,
        SFunc.lineDrop 3 Impl.t_48ac_c9, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ModernCallerReach.ApprovalSource Q observe .v2_2 sevm owner spender T := by
  change ObservedReach Q observe Impl.cert.prog sevm
    ⟨_, .next (.exec .delegatecall) _, _⟩ T at run
  obtain ⟨D, step, run⟩ := ObservedReach.rs_next run hT
  obtain ⟨result, stack⟩ :=
    (CallEffects.call6_run_effects (Or.inl rfl) hsg rfl (erase step)).1
  rw [St.self' D, stack] at run
  iterate 4 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold Impl.t_48c0_c9 at run
  orsd
  iterate 6 orsx
  obtain ⟨d', step, run⟩ := ObservedReach.rs_next run hT
  obtain ⟨_, rfl⟩ := ri_returndatasize (erase step)
  iterate 5 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold Impl.t_48d6_c9 at run
  orsd
  iterate 3 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold Impl.t_4943_c9 at run
  orsd
  iterate 5 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[81]? = some Impl.t_3e18_c81 from rfl] at hg
  cases hg
  apply ModernCallerReach.approval_core_source erase run hT
  intro f member
  rcases List.mem_cons.mp member with rfl | member
  · decide +kernel
  exact cont f member

/-- Both copy-loop exits retain the words passed to the allowance setter. -/
theorem copy_exit_source {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} (hsg : sevm.benvStat.rules.stateGas = none)
    {b : Devm} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 hash signature deadline value : B256}
    {owner spender : Adr} {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 ::
        x12 :: x13 :: hash :: signature :: deadline :: value :: spender.toB256 :: owner.toB256 :: S)
        M G, Impl.t_4860_c80, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ModernCallerReach.ApprovalSource Q observe .v2_2 sevm owner spender T := by
  unfold Impl.t_4860_c80 at run
  orsd
  iterate 15 orsx
  rcases ObservedReach.rs_branchTo run hT with ⟨-, _, run⟩ | ⟨-, g, _, hg, run⟩
  all_goals
    first
    | (unfold Impl.t_4874_c80 at run; iterate 20 orsx)
    | (rw [show Impl.cert.prog[9]? = some Impl.t_488d_c9 from rfl] at hg; cases hg)
  all_goals
    unfold Impl.t_488d_c9 at run
    orsd
    iterate 16 orsx
    obtain ⟨D, step, run⟩ := ObservedReach.rs_next run hT
    obtain ⟨X, stack, matched⟩ := Cursor.absNinst_run_stack_noStateGas
      (a := [.unk]) (a' := [.unk]) (ρ := 0) hsg rfl rfl (.cons trivial .nil) (erase step)
    obtain ⟨word, rfl⟩ : ∃ word, X = [word] := by
      match X, List.Forall₂.length_eq matched with
      | [word], _ => exact ⟨word, rfl⟩
    rw [St.self' D, stack] at run
    iterate 4 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
    unfold Impl.t_48ac_c9 at run
    orsd
    orsx
    obtain ⟨D, step, run⟩ := ObservedReach.rs_next run hT
    obtain ⟨X, stack, matched⟩ := Cursor.absNinst_run_stack_noStateGas
      (a := []) (a' := [.unk]) (ρ := 0) hsg rfl rfl .nil (erase step)
    obtain ⟨word, rfl⟩ : ∃ word, X = [word] := by
      match X, List.Forall₂.length_eq matched with
      | [word], _ => exact ⟨word, rfl⟩
    rw [St.self' D, stack] at run
    exact library_tail_source erase hsg run hT cont

/-- Every actual copy-loop pass either exits or strictly advances the same raw prefix. -/
theorem copy_loop_source {root stop : Exec.Deriv}
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    {b : Devm} {i x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 hash signature deadline value : B256}
    {owner spender : Adr} {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach (StepIn root) (Cursor.RawEdgeAt Impl.code Impl.cert root stop)
      Impl.cert.prog root.sevm
      ⟨St b (i :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 ::
        x12 :: x13 :: hash :: signature :: deadline :: value :: spender.toB256 :: owner.toB256 :: S)
        M G, Impl.t_4848_c80, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ModernCallerReach.ApprovalSource (StepIn root) (Cursor.RawEdgeAt Impl.code Impl.cert root stop)
      .v2_2 root.sevm owner spender T := by
  let erase : ∀ {s d n d'}, StepIn root s d n d' → Ninst.Run s d n d' := fun h => StepIn.toRun h
  induction measure : (St b (i :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 ::
      x12 :: x13 :: hash :: signature :: deadline :: value :: spender.toB256 :: owner.toB256 :: S)
      M G).gasMeasure using Nat.strong_induction_on generalizing b i M G with
  | _ fuel ih =>
    have run := run.withPrefix
    unfold Impl.t_4848_c80 at run
    orsd
    iterate 5 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · unfold Impl.t_4851_c80 at run
      iterate 11 orsx
      rcases Relation.ReflTransGen.cases_head run with same | ⟨next, edge, run⟩
      · rw [← same] at hT
        obtain ⟨f, impossible⟩ := hT
        cases impossible
      · rcases edge with ⟨primitive, observed, earlier⟩
        have smaller := Cursor.RawEdgeAt.gasMeasure_lt observed
        have before := ObservedReach.raw_gasMeasure_le earlier
        cases primitive with
        | jump tag lookup pop =>
          rw [show Impl.cert.prog[80]? = some Impl.t_4848_c80 from rfl] at lookup
          cases lookup
          have shape := (St.of_pop1 pop).2
          rw [shape] at run smaller
          refine ih _ ?_
            (Relation.ReflTransGen.mono (fun _ _ h => ⟨h.1, h.2.1⟩) _ _ run) rfl
          rw [← measure]
          exact Nat.lt_of_lt_of_le smaller before
    · exact copy_exit_source erase hsg
        (Relation.ReflTransGen.mono (fun _ _ h => ⟨h.1, h.2.1⟩) _ _ run) hT cont

/-- The typed-data hash helper returns one word above the untouched permit fields. -/
theorem typed_hash_return_stack {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} (hsg : sevm.benvStat.rules.stateGas = none)
    {b D : Devm} {hash domain tag : B256} {S : List B256} {M : Mem} {G : Nat}
    (run : SFunc.RunP Q Impl.cert.prog sevm
      (St b (hash :: domain :: tag :: S) M G) Impl.t_508b_c79 (.returned D)) :
    ∃ word, D.stack = word :: S := by
  obtain ⟨Y, stack, len⟩ := run.entry_stack_below_noStateGas erase Impl.cert_check hsg
    (k := 79) (e := ⟨0x508b, [.unk, .unk, .ret], 1⟩) rfl rfl
    (ρ := tag) (X := [hash, domain, tag]) (R := S) rfl
    (.cons trivial (.cons trivial (.cons rfl .nil)))
  rcases Y with _ | ⟨word, Y⟩
  · cases len
  rcases Y with _ | ⟨extra, Y⟩
  · exact ⟨word, stack⟩
  · simp only [List.length_cons] at len
    omega

/-- The nonce suffix's actual digest and encoding join the observed copy loop. -/
theorem post_nonce_source {root stop : Exec.Deriv}
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    {b : Devm} {oldNonce domain signature deadline value : B256} {owner spender : Adr}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach (StepIn root) (Cursor.RawEdgeAt Impl.code Impl.cert root stop)
      Impl.cert.prog root.sevm
      ⟨St b (oldNonce :: 32 :: 64 :: owner.toB256 :: ff20 :: domain :: 0x47d3 :: 0 ::
        signature :: deadline :: value :: spender.toB256 :: owner.toB256 :: S) M G,
        SFunc.lineDrop 27 Impl.t_4738_c8, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ModernCallerReach.ApprovalSource (StepIn root) (Cursor.RawEdgeAt Impl.code Impl.cert root stop)
      .v2_2 root.sevm owner spender T := by
  let erase : ∀ {s d n d'}, StepIn root s d n d' → Ninst.Run s d n d' := fun h => StepIn.toRun h
  dsimp only [SFunc.lineDrop, Impl.t_4738_c8] at run
  iterate 63 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[79]? = some Impl.t_508b_c79 from rfl] at hg
  cases hg
  obtain ⟨D, returned, _, run⟩ := ObservedReach.return_of_sstoreFree
    (E := [79]) (by decide +kernel) (by decide +kernel) run hT
  obtain ⟨word, stack⟩ := typed_hash_return_stack erase hsg returned
  rw [St.self' D, stack] at run
  unfold Impl.t_47d3_c8 at run
  orsd
  iterate 59 orsx
  exact copy_loop_source hsg run hT cont

/-- Both permit overloads share this original nonce and signature path. -/
theorem body_source {root stop : Exec.Deriv}
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    {b : Devm} {signature deadline value : B256} {owner spender : Adr}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach (StepIn root) (Cursor.RawEdgeAt Impl.code Impl.cert root stop)
      Impl.cert.prog root.sevm
      ⟨St b (signature :: deadline :: value :: spender.toB256 :: owner.toB256 :: S)
        M G, Impl.t_4692_c94, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    V2_1PermitReach.NonceSource (StepIn root) (Cursor.RawEdgeAt Impl.code Impl.cert root stop)
        root.sevm owner T ∨
      ModernCallerReach.ApprovalSource (StepIn root) (Cursor.RawEdgeAt Impl.code Impl.cert root stop)
        .v2_2 root.sevm owner spender T := by
  obtain ⟨b', domain, M', G', run⟩ :=
    V22PermitEntry.deadline_reach_observed (fun h => StepIn.toRun h) hsg run hT cont
  rcases V22PermitEntry.nonce_reach_observed (fun h => StepIn.toRun h) run hT with source |
      ⟨b'', oldNonce, M'', G'', run⟩
  · exact .inl source
  · exact .inr (post_nonce_source hsg run hT cont)

theorem noncePattern_occurrences :
    BytePattern.occurrences (V2_1PermitReach.nonceLine.flatMap Ninst.toBytes) Impl.code.toList =
      [0x476b] := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

def ActualSource (root node : Exec.Deriv) (owner spender : Adr) (key : B256) : Prop :=
  (node.pc = 0x476b ∧ key = nonceSlot owner ∧
    ∃ hashPc, KeccakBefore root node (owner.toB256.toBytes ++ (17 : B256).toBytes) hashPc) ∨
  (node.pc ≠ 0x476b ∧ key = allowSlot owner spender ∧
    KeccakPairBefore root node (owner.toB256.toBytes ++ (10 : B256).toBytes)
      (spender.toB256.toBytes ++ (mapSlot owner.toB256 10).toBytes))

/-- Locate the original nonce store or the approval store with its ordered hash inputs. -/
theorem actualSource_of_observed {root node : Exec.Deriv} {κ : Cursor}
    {owner spender : Adr} {write : Exec.StorageWrite}
    (ok : CursorOK Impl.code Impl.cert node κ)
    (found : Exec.Deriv.successfulSstore? node = some write)
    (source : V2_1PermitReach.NonceSource (StepIn root) (Cursor.RawEdgeAt Impl.code Impl.cert root node)
        root.sevm owner (κ.conf node.devm) ∨
      ModernCallerReach.ApprovalSource (StepIn root) (Cursor.RawEdgeAt Impl.code Impl.cert root node)
        .v2_2 root.sevm owner spender (κ.conf node.devm)) :
    ActualSource root node owner spender write.key := by
  obtain ⟨_, _, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  rcases source with ⟨⟨other, keyStack⟩, ⟨tail, shape⟩, hash⟩ |
      ⟨⟨other, keyStack⟩, ⟨tail, shape⟩, hashes⟩
  · have location := ok.pc_eq_of_prefix_singleton V2_1PermitReach.nonceLine tail shape
      (suffix := []) (by simp only [List.append_nil]) (by decide) noncePattern_occurrences
    obtain ⟨occ, next, here, instruction, result, before, edge, after, _, _, hashStack, read⟩ :=
      hash.actual
    exact .inl ⟨location, (List.cons.inj (stack.symm.trans keyStack)).1,
      _, occ, next, rfl, instruction, result, before, edge, after, hashStack, read⟩
  · have bytes := ok.bytesAt_of_prefix ModernCallerReach.approvalLine tail shape
    have different : node.pc ≠ 0x476b := by
      intro same
      rw [same] at bytes
      have actual : bytesAt Impl.code 0x476b
          (ModernCallerReach.approvalLine.flatMap Ninst.toBytes) = false := by decide +kernel
      rw [actual] at bytes
      contradiction
    exact .inr ⟨different, (List.cons.inj (stack.symm.trans keyStack)).1, hashes.actual⟩

/-- Every selected original successful store retains its decoded arguments and actual hashes,
including a store in a frame that later reverts. -/
theorem successfulSstore_source {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = Impl.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Sevm.selector root.sevm ∈ [0xd505accf, 0x9fd5a6cf])
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    ActualSource root node (Sevm.dataWord root.sevm 4).toAdr
      (Sevm.dataWord root.sevm 36).toAdr write.key := by
  obtain ⟨decoded, _, _⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, reach, ok⟩ :=
    observed_reach_of_parentPrefix_noStateGas Impl.cert_check pc code hsg chain
  obtain ⟨g, tree, _⟩ := ok.tree_of_sstore decoded
  have target : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  change ObservedReach (StepIn root) (Cursor.RawEdgeAt Impl.code Impl.cert root node)
    Impl.cert.prog root.sevm ⟨root.devm, Impl.t_0000_c0, []⟩ (κ.conf node.devm) at reach
  rw [St.self' root.devm] at reach
  apply actualSource_of_observed ok found
  rcases List.mem_cons.mp selected with selected | selected
  · obtain ⟨b, S, M, G, run⟩ :=
      V22PermitEntry.vrs_reach_observed (fun h => StepIn.toRun h) selected reach target
    obtain ⟨b', signature, S', M', G', run⟩ :=
      V22PermitEntry.pack_reach_observed (fun h => StepIn.toRun h) run target
    apply body_source hsg run target
    intro f member
    rcases List.mem_cons.mp member with rfl | member
    · decide +kernel
    rcases List.mem_cons.mp member with rfl | member
    · decide +kernel
    have same := List.mem_singleton.mp member
    subst f
    decide +kernel
  · have selected := List.mem_singleton.mp selected
    obtain ⟨b, signature, S, M, G, run⟩ :=
      V22PermitEntry.bytes_reach_observed (fun h => StepIn.toRun h) selected reach target
    apply body_source hsg run target
    intro f member
    rcases List.mem_cons.mp member with rfl | member
    · decide +kernel
    have same := List.mem_singleton.mp member
    subst f
    decide +kernel

end Blanc.Lift.Usdc.V22PermitReach
