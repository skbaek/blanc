import Blanc.Corpus.Freeze.DepositLedger
import Blanc.Composition.DepositPendingPass
namespace Blanc.Composition.DepositLedgerMirrors
open Jaune JauneConsensus JauneConsensus.Facts
open Blanc.Corpus.Freeze.Deposit
variable {P : Preset} {f : CFork}
private theorem epochMirror (ctx : Ctx) (state : BeaconState P f) (tq : TQueue)
    (aligned : (do pure (← state.pendingDeposits).toArray.toList) =
      (.ok (tq.map Prod.snd) : M _))
    {state' : BeaconState P f}
    (actual : processEpoch ctx state = .ok state') :
    ∃ tq' ap, processEpochTagged ctx state tq = .ok (state', tq', ap) ∧
      (do pure (← state'.pendingDeposits).toArray.toList) =
        (.ok (tq'.map Prod.snd) : M _) := by
  have hf : f.atLeast .electra = true := by
    cases f <;> first | rfl | cases aligned
  rw [processEpoch_split_queues hf] at actual
  obtain ⟨pre, hpre, actual⟩ := bind_ok_elim actual
  obtain ⟨passed, hpass, actual⟩ := bind_ok_elim actual
  obtain ⟨consolidated, hcon, hpost⟩ := bind_ok_elim actual
  have preAligned : (do pure (← pre.pendingDeposits).toArray.toList) =
      (.ok (tq.map Prod.snd) : M _) := by
    simpa only [BeaconState.pendingDeposits, (epochPreQueues_csub hf ctx.cfg hpre).pd_eq] using aligned
  obtain ⟨tq', ap, tagged, finalAligned⟩ := DepositPendingPass.passMirror ctx pre tq preAligned passed hpass
  have suffix : epochAfterDeposits ctx passed = .ok state' := by
    simp only [epochAfterDeposits, hcon, ok_bind', hpost]
  refine ⟨tq', ap, ?_, ?_⟩
  · have same : processEpochTagged ctx state tq = (do
        let pre ← epochPreQueues ctx.cfg state
        let (passed, tq', ap) ← processPendingDepositsTagged ctx pre tq
        let final ← epochAfterDeposits ctx passed
        pure (final, tq', ap)) := by
      by_cases hfulu : f.atLeast .fulu = true <;>
        simp only [processEpochTagged, epochPreQueues, epochAfterDeposits, epochPostQueues,
          hf, hfulu, Bool.false_eq_true, ite_true, ite_false, bind_assoc, pure_bind]
    simp only [same, hpre, tagged, suffix, ok_bind']
    rfl
  · simpa only [BeaconState.pendingDeposits,
      (epochAfterDeposits_pendingDeposits hf ctx suffix).1] using finalAligned

private theorem slotsLoopMirror (ctx : Ctx) (spe : U64) (n : Nat) :
    ∀ (start : Nat) (state : BeaconState P f) (tq : TQueue) (ap : List (Applied P f))
      (state' : BeaconState P f),
    (do pure (← state.pendingDeposits).toArray.toList) = (.ok (tq.map Prod.snd) : M _) →
    forIn (List.range' start n) state (fun (_ : Nat) st => do
      let st ← processSlot st
      let next ← st.slot.add? U64.one "process_slots: state.slot + 1"
      let rem ← next.mod? spe "process_slots: (state.slot + 1) % SLOTS_PER_EPOCH"
      if rem.toNat == 0 then
        let st ← processEpoch ctx st
        pure (ForInStep.yield { st with slot := next })
      else pure (ForInStep.yield { st with slot := next })) = .ok state' →
    ∃ tq' ap', slotsLoopTagged ctx spe n state tq ap = .ok (state', tq', ap') ∧
      (do pure (← state'.pendingDeposits).toArray.toList) = (.ok (tq'.map Prod.snd) : M _) := by
  induction n with
  | zero =>
    intro start state tq ap state' aligned actual
    simp only [List.range'_zero, List.forIn_nil] at actual
    have hstate : state = state' := Except.ok.inj actual
    subst state'
    exact ⟨tq, ap, rfl, aligned⟩
  | succ n ih =>
    intro start state tq ap state' aligned actual
    rw [List.range'_succ, List.forIn_cons] at actual
    obtain ⟨r, hr, actual⟩ := bind_ok_elim actual
    obtain ⟨st, hslot, hr⟩ := bind_ok_elim hr
    obtain ⟨next, hnext, hr⟩ := bind_ok_elim hr
    obtain ⟨rem, hrem, hr⟩ := bind_ok_elim hr
    have slotAligned : (do pure (← st.pendingDeposits).toArray.toList) =
        (.ok (tq.map Prod.snd) : M _) := by
      simpa only [BeaconState.pendingDeposits,
        (processSlot_cpres_and_frame hslot).2.2.2.2.2.2] using aligned
    by_cases hz : (rem.toNat == 0) = true
    · simp only [hz, ite_true] at hr
      obtain ⟨ep, hepoch, hr⟩ := bind_ok_elim hr
      have hr' : r = .yield { ep with slot := next } := (Except.ok.inj hr).symm
      subst r
      obtain ⟨tqE, apE, htagged, epAligned⟩ := epochMirror ctx st tq slotAligned hepoch
      obtain ⟨tq', ap', htail, finalAligned⟩ :=
        ih (start + 1) { ep with slot := next } tqE (ap ++ apE) state' epAligned actual
      refine ⟨tq', ap', ?_, finalAligned⟩
      simpa only [slotsLoopTagged, hslot, hnext, hrem, hz, ite_true, htagged, ok_bind', pure_bind] using htail
    · simp only [hz] at hr
      have hr' : r = .yield { st with slot := next } := (Except.ok.inj hr).symm
      subst r
      obtain ⟨tq', ap', htail, finalAligned⟩ :=
        ih (start + 1) { st with slot := next } tq ap state' slotAligned actual
      refine ⟨tq', ap', ?_, finalAligned⟩
      simpa only [slotsLoopTagged, hslot, hnext, hrem, hz, Bool.false_eq_true, ite_false, ok_bind', pure_bind] using htail

/-- The frozen tagged slot runner preserves the exact actual post-state. -/
theorem slotsMirror : SlotsMirror := by
  intro P f ctx state slot tq aligned state' actual
  unfold processSlots processSlotsWith at actual
  obtain ⟨u, hreq, actual⟩ := bind_ok_elim actual
  obtain ⟨spe, hspe, actual⟩ := bind_ok_elim actual
  obtain ⟨out, hloop, hfinal⟩ := bind_ok_elim actual
  have hout : out = state' := Except.ok.inj hfinal
  subst out
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hloop
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one] at hloop
  obtain ⟨tq', ap, htagged, finalAligned⟩ :=
    slotsLoopMirror ctx spe (slot.toNat - state.slot.toNat) 0 state tq [] state' aligned hloop
  refine ⟨tq', ap, ?_, finalAligned⟩
  simpa only [processSlotsTagged, hreq, hspe, ok_bind'] using htagged

private theorem inputMirror (ccfg : Config) (bls : Bool) (s : JointState P)
    (b : AnySignedBlock P) (tq : TQueue) {st : BeaconState P b.1}
    (aligned : pendingList s = .ok (tq.map Prod.snd))
    (actual : Blanc.jointBlockInput ccfg bls s b = .ok st) :
    ∃ tq' ap, jointBlockInputTagged ccfg bls s b tq = .ok (st, tq', ap) ∧
      (do pure (← st.pendingDeposits).toArray.toList) = (.ok (tq'.map Prod.snd) : M _) := by
  obtain ⟨sf, beacon, exec⟩ := s
  obtain ⟨bf, sb⟩ := b
  cases sf <;> cases bf
  all_goals try (simp only [Blanc.jointBlockInput, ExceptT.stM_eq, throw, throwThe,
    MonadExceptOf.throw, reduceCtorEq] at actual; done)
  · obtain ⟨tq', ap, tagged, finalAligned⟩ :=
      slotsMirror (jointCtx ccfg bls) beacon sb.message.slot tq aligned st actual
    have hlt := (processSlots_slot rfl (jointCtx ccfg bls) actual).1
    have hne : ¬ (sb.message.slot == beacon.slot) = true := by
      intro heq
      have heq' : sb.message.slot = beacon.slot := beq_iff_eq.mp heq
      have hlt' : beacon.slot.toNat < sb.message.slot.toNat := hlt
      rw [heq'] at hlt'
      exact Nat.lt_irrefl _ hlt'
    refine ⟨tq', ap.map (fun a => ⟨.electra, a⟩), ?_, finalAligned⟩
    simp only [jointBlockInputTagged, hne, tagged, ok_bind']
    rfl
  · unfold Blanc.jointBlockInput at actual
    obtain ⟨forkSlot, hfork, actual⟩ := bind_ok_elim actual
    obtain ⟨preUp, hpreUp, actual⟩ := bind_ok_elim actual
    obtain ⟨up, hup, actual⟩ := bind_ok_elim actual
    have first : ∃ tqE apE,
        (if beacon.slot < forkSlot then
          processSlotsTagged (jointCtx ccfg bls) beacon forkSlot tq
        else pure (beacon, tq, [])) = .ok (preUp, tqE, apE) ∧
        (do pure (← preUp.pendingDeposits).toArray.toList) = (.ok (tqE.map Prod.snd) : M _) := by
      by_cases hlt : beacon.slot < forkSlot
      · simp only [hlt, ite_true] at hpreUp ⊢
        exact slotsMirror (jointCtx ccfg bls) beacon forkSlot tq aligned preUp hpreUp
      · simp only [hlt, ite_false] at hpreUp ⊢
        have heq : beacon = preUp := Except.ok.inj hpreUp
        subst preUp
        exact ⟨tq, [], rfl, aligned⟩
    obtain ⟨tqE, apE, taggedE, alignedE⟩ := first
    have alignedF : (do pure (← up.pendingDeposits).toArray.toList) =
        (.ok (tqE.map Prod.snd) : M _) := by
      have hcopy := upgradeToFulu_pendingDepositsList ccfg hup
      simp only [pendingDepositsList_eq_get (f := .electra) rfl,
        pendingDepositsList_eq_get (f := .fulu) rfl] at hcopy
      simp only [BeaconState.pendingDeposits] at alignedE ⊢
      exact (congrArg Except.ok hcopy).trans alignedE
    have second : ∃ tqF apF,
        (if sb.message.slot == up.slot then pure (up, tqE, [])
        else processSlotsTagged (jointCtx ccfg bls) up sb.message.slot tqE) =
          .ok (st, tqF, apF) ∧
        (do pure (← st.pendingDeposits).toArray.toList) = (.ok (tqF.map Prod.snd) : M _) := by
      by_cases hat : (sb.message.slot == up.slot) = true
      · simp only [hat, ite_true] at actual ⊢
        have heq : up = st := Except.ok.inj actual
        subst st
        exact ⟨tqE, [], rfl, alignedF⟩
      · simp only [hat] at actual ⊢
        exact slotsMirror (jointCtx ccfg bls) up sb.message.slot tqE alignedF st actual
    obtain ⟨tqF, apF, taggedF, finalAligned⟩ := second
    refine ⟨tqF, apE.map (fun a => ⟨.electra, a⟩) ++ apF.map (fun a => ⟨.fulu, a⟩), ?_, finalAligned⟩
    by_cases hlt : beacon.slot < forkSlot
    all_goals
      simp only [hlt, ite_true, ite_false] at taggedE
      simp only [jointBlockInputTagged, hfork, ok_bind', hlt, ite_true, ite_false, taggedE, hup]
      by_cases hat : (sb.message.slot == up.slot) = true
      all_goals
        simp only [hat, Bool.false_eq_true, ite_true, ite_false] at taggedF
        simp only [hat, Bool.false_eq_true, ite_true, ite_false, taggedF, ok_bind']
        rfl
  · obtain ⟨tq', ap, tagged, finalAligned⟩ :=
      slotsMirror (jointCtx ccfg bls) beacon sb.message.slot tq aligned st actual
    refine ⟨tq', ap.map (fun a => ⟨.fulu, a⟩), ?_, finalAligned⟩
    simp only [jointBlockInputTagged, tagged, ok_bind']
    rfl

private theorem tagAppended_shape (drs : List DepositRequest) (slot : Slot)
    (hs : slot ≠ GENESIS_SLOT) (pre post : List PendingDeposit)
    (hpre : ∀ d ∈ pre, d.slot = GENESIS_SLOT)
    (hpost : ∀ d ∈ post, d.slot = GENESIS_SLOT) :
    tagAppended drs (pre ++ drs.map (requestPending · slot) ++ post) =
      pre.map (fun d => (none, d)) ++
        drs.map (fun dr => (some dr.index.toNat, requestPending dr slot)) ++
        post.map (fun d => (none, d)) := by
  induction pre with
  | nil =>
    simp only [List.nil_append, List.map_nil]
    induction drs with
    | nil =>
      simp only [List.map_nil, List.nil_append]
      induction post with
      | nil => rfl
      | cons d rest ih =>
        have hd : d.slot = GENESIS_SLOT := hpost d (List.mem_cons_self)
        have ht : ∀ e ∈ rest, e.slot = GENESIS_SLOT :=
          fun e he => hpost e (List.mem_cons_of_mem d he)
        simp only [tagAppended, hd, ne_eq, not_true_eq_false, ite_false, List.map_cons]
        exact congrArg (List.cons (none, d)) (ih ht)
    | cons dr rest ih =>
      have hd : (requestPending dr slot).slot ≠ GENESIS_SLOT := hs
      simp only [List.map_cons, List.cons_append, tagAppended]
      rw [ite_eq_left hd]
      exact congrArg (List.cons (some dr.index.toNat, requestPending dr slot)) ih
  | cons d rest ih =>
    have hd : d.slot = GENESIS_SLOT := hpre d (List.mem_cons_self)
    have ht : ∀ e ∈ rest, e.slot = GENESIS_SLOT :=
      fun e he => hpre e (List.mem_cons_of_mem d he)
    simp only [List.cons_append, List.map_cons, tagAppended, hd, ne_eq, not_true_eq_false, ite_false]
    exact congrArg (List.cons (none, d)) (ih ht)

private theorem tagAppended_spec (drs : List DepositRequest) (slot : Slot)
    (hs : slot ≠ GENESIS_SLOT) (pre post : List PendingDeposit)
    (hpre : ∀ d ∈ pre, d.slot = GENESIS_SLOT)
    (hpost : ∀ d ∈ post, d.slot = GENESIS_SLOT) :
    (tagAppended drs (pre ++ drs.map (requestPending · slot) ++ post)).filter
        (fun e => e.1.isSome) =
      drs.map (fun dr => (some dr.index.toNat, requestPending dr slot)) ∧
    ∀ e ∈ tagAppended drs (pre ++ drs.map (requestPending · slot) ++ post),
      e.1 = none → e.2.slot = GENESIS_SLOT := by
  rw [tagAppended_shape drs slot hs pre post hpre hpost]
  constructor
  · simp only [List.filter_append, List.filter_map, Function.comp_def, Option.isSome_none,
      Option.isSome_some, List.filter_false, List.filter_true, List.map_nil, List.nil_append,
      List.append_nil]
  · intro e he hn
    simp only [List.mem_append, List.mem_map] at he
    rcases he with (he | he) | he
    · obtain ⟨d, hd, heq⟩ := he
      subst e
      exact hpre d hd
    · obtain ⟨dr, _, heq⟩ := he
      subst e
      cases hn
    · obtain ⟨d, hd, heq⟩ := he
      subst e
      exact hpost d hd

private theorem finishStep {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (D : Blanc.JointRunStep (P := P) cfg ccfg bls) (tq tqS : TQueue)
    (ap : List (AppliedAt P)) (st post : BeaconState P D.block.1)
    (hf : D.block.1.atLeast .electra = true)
    (tagged : jointBlockInputTagged ccfg bls D.pre D.block tq = .ok (st, tqS, ap))
    (alignedS : (do pure (← st.pendingDeposits).toArray.toList) =
      (.ok (tqS.map Prod.snd) : M _))
    (actual : processBlock (jointCtx ccfg bls) st D.block.2.message = .ok post)
    (finalList : pendingList D.post = .ok (pendingDepositsList post)) :
    ∃ tq' ap', stepLedger D tq = .ok (tq', ap') ∧ pendingList D.post = .ok (tq'.map Prod.snd) ∧
      ∃ st tqS tqA, jointBlockInputTagged ccfg bls D.pre D.block tq = .ok (st, tqS, ap') ∧
        tq' = tqS ++ tqA ∧
        tqA.filter (fun e => e.1.isSome) = (stepDepositRequests D).map
          (fun dr => (some dr.index.toNat, requestPending dr D.block.2.message.slot)) ∧
        ∀ e ∈ tqA, e.1 = none → e.2.slot = GENESIS_SLOT := by
  obtain ⟨_, hs, pre, tail, splitQueue, _, hpre, htail⟩ :=
    processBlock_pendingDeposits_split hf (jointCtx ccfg bls) actual
  have inputList : pendingDepositsList st = tqS.map Prod.snd := by
    rw [pendingDepositsList_eq_get hf]
    rw [BeaconState.pendingDeposits, gated_read_get hf, ok_bind'] at alignedS
    exact Except.ok.inj alignedS
  have requests : stepDepositRequests D =
      (Gated.get hf D.block.2.message.body.execution_requests).deposits.toArray.toList := by
    unfold stepDepositRequests
    rw [gated_read_get hf]
  let xs := pre ++ (stepDepositRequests D).map (requestPending · D.block.2.message.slot) ++ tail
  let tqA := tagAppended (stepDepositRequests D) xs
  have postList : pendingDepositsList post = tqS.map Prod.snd ++ xs := by
    simpa only [inputList, ← requests, requestPending, depositRequestPending, List.append_assoc, xs]
      using splitQueue
  have erase : tqA.map Prod.snd = xs := by
    dsimp only [tqA, xs]
    rw [tagAppended_shape _ _ hs pre tail hpre htail]
    simp only [List.map_append, List.map_map, Function.comp_def, List.map_id_fun']
    rfl
  have spec := tagAppended_spec (stepDepositRequests D) D.block.2.message.slot hs pre tail hpre htail
  obtain ⟨q, hq, hqList⟩ := bind_ok_elim finalList
  have hqList : q.toArray.toList = pendingDepositsList post := Except.ok.inj hqList
  have drop : q.toArray.toList.drop tqS.length = xs := by
    rw [hqList, postList]
    simpa only [List.length_map] using
      (List.drop_left (l₁ := tqS.map Prod.snd) (l₂ := xs))
  refine ⟨tqS ++ tqA, ap, ?_, ?_, st, tqS, tqA, tagged, rfl, spec.1, spec.2⟩
  · simp only [stepLedger, tagged, hq, ok_bind', drop]
    rfl
  · simp only [finalList, postList, List.map_append, erase]

/-- Every actual valid ingress step has the frozen occurrence-preserving tagged mirror. -/
theorem stepMirror : StepMirror := by
  intro P cfg ccfg bls D tq valid aligned
  obtain ⟨pre, post, block, trace⟩ := D
  rcases valid with ⟨_, ordinary | activation⟩
  · obtain ⟨sf, beacon, exec⟩ := pre
    obtain ⟨bf, sb⟩ := block
    cases sf <;> cases bf
    all_goals try (simp only [jointStep, ExceptT.stM_eq, throw, throwThe,
      MonadExceptOf.throw, reduceCtorEq] at ordinary; done)
    · obtain ⟨_, req, beacon', exec', _, _, hbeacon, rfl⟩ := jointStep_electra_ok_iff.mp ordinary
      obtain ⟨st, hslots, hblock⟩ := Blanc.stateTransition_processBlock_post hbeacon
      obtain ⟨tqS, ap, tagged, alignedS⟩ := inputMirror ccfg bls
        ⟨.electra, beacon, exec⟩ ⟨.electra, sb⟩ tq aligned hslots
      exact finishStep ⟨_, _, _, trace⟩ tq tqS ap st beacon' rfl tagged alignedS hblock rfl
    · obtain ⟨_, _, req, forkSlot, preUp, up, beacon', exec', hfork, hslots, hup, _, _, hbeacon,
        rfl⟩ := jointStep_cross_ok_iff.mp ordinary
      by_cases hat : (sb.message.slot == up.slot) = true
      · rw [ite_eq_left hat] at hbeacon
        obtain ⟨_, _, hbeacon⟩ := bind_ok_elim hbeacon
        obtain ⟨_, _, hbeacon⟩ := bind_ok_elim hbeacon
        obtain ⟨postBlock, hblock, hbeacon⟩ := bind_ok_elim hbeacon
        obtain ⟨_, _, hbeacon⟩ := bind_ok_elim hbeacon
        have heq : postBlock = beacon' := Except.ok.inj hbeacon
        subst postBlock
        have input : Blanc.jointBlockInput ccfg bls ⟨.electra, beacon, exec⟩ ⟨.fulu, sb⟩ = .ok up := by
          simp only [Blanc.jointBlockInput, hfork, hslots, hup, hat, ite_true, ok_bind']
          rfl
        obtain ⟨tqS, ap, tagged, alignedS⟩ := inputMirror ccfg bls
          ⟨.electra, beacon, exec⟩ ⟨.fulu, sb⟩ tq aligned input
        exact finishStep ⟨_, _, _, trace⟩ tq tqS ap up beacon' rfl tagged alignedS hblock rfl
      · rw [ite_eq_right hat] at hbeacon
        obtain ⟨st, hslotsF, hblock⟩ := Blanc.stateTransition_processBlock_post hbeacon
        have input : Blanc.jointBlockInput ccfg bls ⟨.electra, beacon, exec⟩ ⟨.fulu, sb⟩ = .ok st := by
          simp only [Blanc.jointBlockInput, hfork, hslots, hup, hat, ok_bind']
          exact hslotsF
        obtain ⟨tqS, ap, tagged, alignedS⟩ := inputMirror ccfg bls
          ⟨.electra, beacon, exec⟩ ⟨.fulu, sb⟩ tq aligned input
        exact finishStep ⟨_, _, _, trace⟩ tq tqS ap st beacon' rfl tagged alignedS hblock rfl
    · obtain ⟨req, beacon', exec', _, _, hbeacon, rfl⟩ := jointStep_fulu_ok_iff.mp ordinary
      obtain ⟨st, hslots, hblock⟩ := Blanc.stateTransition_processBlock_post hbeacon
      obtain ⟨tqS, ap, tagged, alignedS⟩ := inputMirror ccfg bls
        ⟨.fulu, beacon, exec⟩ ⟨.fulu, sb⟩ tq aligned hslots
      exact finishStep ⟨_, _, _, trace⟩ tq tqS ap st beacon' rfl tagged alignedS hblock rfl
  · obtain ⟨beacon, beacon', exec, exec', sb, hpre, hpost, hblock, _, _, htransition⟩ := activation
    dsimp only at hpre hpost hblock
    subst pre post block
    obtain ⟨req, _, _, hbeacon⟩ := jointTransitionAt_ok_iff.mp htransition
    by_cases hat : (sb.message.slot == beacon.slot) = true
    · rw [ite_eq_left hat] at hbeacon
      obtain ⟨_, _, hbeacon⟩ := bind_ok_elim hbeacon
      obtain ⟨_, _, hbeacon⟩ := bind_ok_elim hbeacon
      obtain ⟨postBlock, hblock, hbeacon⟩ := bind_ok_elim hbeacon
      obtain ⟨_, _, hbeacon⟩ := bind_ok_elim hbeacon
      have heq : postBlock = beacon' := Except.ok.inj hbeacon
      subst postBlock
      have tagged : jointBlockInputTagged ccfg bls ⟨.electra, beacon, exec⟩ ⟨.electra, sb⟩ tq =
          .ok (beacon, tq, []) := by
        simp only [jointBlockInputTagged, hat, ite_true]
        rfl
      exact finishStep ⟨_, _, _, trace⟩ tq tq [] beacon beacon' rfl tagged aligned hblock rfl
    · rw [ite_eq_right hat] at hbeacon
      obtain ⟨st, hslots, hblock⟩ := Blanc.stateTransition_processBlock_post hbeacon
      obtain ⟨tqS, ap, tagged, alignedS⟩ := inputMirror ccfg bls
        ⟨.electra, beacon, exec⟩ ⟨.electra, sb⟩ tq aligned hslots
      exact finishStep ⟨_, _, _, trace⟩ tq tqS ap st beacon' rfl tagged alignedS hblock rfl
end Blanc.Composition.DepositLedgerMirrors
