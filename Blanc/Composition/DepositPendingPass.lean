import Blanc.Corpus.Freeze.DepositLedger
import JauneConsensus.Facts.PendingDeposits
import JauneConsensus.Facts.SlotEpochFrames

/-! Exact occurrence-preserving simulation of the frozen pending-deposit pass. -/
namespace Blanc.Composition.DepositPendingPass

open Jaune JauneConsensus JauneConsensus.Facts
open Blanc.Corpus.Freeze.Deposit

variable {P : Preset} {f : CFork}

/-- Forget ghost metadata, retaining the existing G1 loop accumulator. -/
private def erasePass (r : PassResult P f) : PendingDepositsAcc P f :=
  (r.processed, r.next, (r.postponed.map Prod.snd).toArray,
    decide (r.stop = some .churn), r.state)

/-- The new occurrences of an actual loop result, relative to its input accumulators. -/
private def LoopFacts (ctx : Ctx) (nextEpoch : Epoch) (tq : TQueue) (i : Nat)
    (state : BeaconState P f) (post : TQueue) (ap : List (Applied P f))
    (r : PassResult P f) : Prop :=
  ∃ (k : Nat) (fresh : List (Applied P f)) (postponed : TQueue),
    k ≤ tq.length ∧ r.next = i + k ∧ r.applied = ap ++ fresh ∧
    r.postponed = post ++ postponed ∧
    PassPartition (tq.take k) (fresh.map fun a => (a.tag, a.deposit)) postponed ∧
    (fresh.head?.map Applied.pre).getD r.state = state ∧
    (∀ idx a, fresh[idx]? = some a → applyPendingDeposit ctx a.pre a.deposit =
      .ok ((fresh[idx + 1]?.map Applied.pre).getD r.state)) ∧
    List.foldlM (applyPendingDeposit ctx) state (fresh.map Applied.deposit) = .ok r.state ∧
    ∀ e ∈ postponed, ∃ j v, findValidatorIndex state e.2.pubkey = some j ∧
      state.validators.toArray[j]? = some v ∧ v.exit_epoch < FAR_FUTURE_EPOCH ∧
      nextEpoch ≤ v.withdrawable_epoch

private theorem loopFacts_stop (ctx : Ctx) (nextEpoch : Epoch) (tq : TQueue)
    (i : Nat) (processed : U64) (state : BeaconState P f) (post : TQueue)
    (ap : List (Applied P f)) (stop : Option PassStop) :
    LoopFacts ctx nextEpoch tq i state post ap ⟨state, i, processed, post, ap, stop⟩ := by
  refine ⟨0, [], [], Nat.zero_le _, by simp only [Nat.add_zero],
    by simp only [List.append_nil], by simp only [List.append_nil], ?_, rfl, ?_, rfl, ?_⟩
  · simpa only [List.take_zero, List.map_nil] using PassPartition.nil
  · intro idx a h
    simp only [List.getElem?_nil] at h
    cases h
  · intro e h
    cases h

private theorem loopFacts_apply (ctx : Ctx) (nextEpoch : Epoch) (rest : TQueue)
    (e : Tag × PendingDeposit) (i : Nat) (state mid : BeaconState P f)
    (post : TQueue) (ap : List (Applied P f)) (route : ApplyRoute) (r : PassResult P f)
    (happly : applyPendingDeposit ctx state e.2 = .ok mid)
    (h : LoopFacts ctx nextEpoch rest (i + 1) mid post
      (ap ++ [⟨e.1, e.2, state, route⟩]) r) :
    LoopFacts ctx nextEpoch (e :: rest) i state post ap r := by
  obtain ⟨k, fresh, postponed, hk, hi, ha, hp, hpart, hhead, hchain, hfold, hpost⟩ := h
  refine ⟨k + 1, ⟨e.1, e.2, state, route⟩ :: fresh, postponed, ?_, ?_, ?_, hp,
    ?_, rfl, ?_, ?_, ?_⟩
  · simpa only [List.length_cons] using Nat.add_le_add_right hk 1
  · omega
  · simpa only [List.append_assoc, List.singleton_append] using ha
  · simpa only [List.take_succ_cons, List.map_cons] using PassPartition.apply e hpart
  · intro idx a hidx
    cases idx with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hidx
      subst a
      simpa only [List.getElem?_cons_succ, List.head?_eq_getElem?] using happly.trans (congrArg Except.ok hhead.symm)
    | succ idx =>
      simp only [List.getElem?_cons_succ] at hidx ⊢
      exact hchain idx a hidx
  · simpa only [List.map_cons, List.foldlM_cons, happly, ok_bind'] using hfold
  · intro x hx
    obtain ⟨j, v, hj, hv, he, hw⟩ := hpost x hx
    have hsingle : List.foldlM (applyPendingDeposit ctx) state [e.2] = .ok mid := by
      simp only [List.foldlM_cons, happly, ok_bind', List.foldlM_nil]
      rfl
    obtain ⟨hj', hv', he'⟩ :=
      (foldlM_applyPendingDeposit_exiting_iff ctx [e.2] hsingle x.2.pubkey j v).mp ⟨hj, hv, he⟩
    exact ⟨j, v, hj', hv', he', hw⟩

private theorem loopFacts_postpone (ctx : Ctx) (nextEpoch : Epoch) (rest : TQueue)
    (e : Tag × PendingDeposit) (i : Nat) (state : BeaconState P f)
    (post : TQueue) (ap : List (Applied P f)) (r : PassResult P f)
    (guard : ∃ j v, findValidatorIndex state e.2.pubkey = some j ∧
      state.validators.toArray[j]? = some v ∧ v.exit_epoch < FAR_FUTURE_EPOCH ∧
      nextEpoch ≤ v.withdrawable_epoch)
    (h : LoopFacts ctx nextEpoch rest (i + 1) state (post ++ [e]) ap r) :
    LoopFacts ctx nextEpoch (e :: rest) i state post ap r := by
  obtain ⟨k, fresh, postponed, hk, hi, ha, hp, hpart, hhead, hchain, hfold, hpost⟩ := h
  refine ⟨k + 1, fresh, e :: postponed, ?_, ?_, ha, ?_, ?_, hhead, hchain, hfold, ?_⟩
  · simpa only [List.length_cons] using Nat.add_le_add_right hk 1
  · omega
  · simpa only [List.append_assoc, List.singleton_append] using hp
  · simpa only [List.take_succ_cons] using PassPartition.postpone e hpart
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact guard
    · exact hpost x hx

private theorem loopSimulation_normal (ctx : Ctx) (nextEpoch : Epoch) (available : U64)
    (finalizedSlot : Slot) (requestsStart : U64) (rest : TQueue)
    (ih : ∀ (i : Nat) (processed : U64) (state : BeaconState P f) (post : TQueue)
      (ap : List (Applied P f)),
      (passLoop ctx nextEpoch available finalizedSlot requestsStart rest i processed state post ap).map
        erasePass = pendingDepositsLoop ctx nextEpoch available finalizedSlot requestsStart
          (rest.map Prod.snd) (processed, i, (post.map Prod.snd).toArray, false, state) ∧
      ∀ r, passLoop ctx nextEpoch available finalizedSlot requestsStart rest i processed state post ap =
        .ok r → LoopFacts ctx nextEpoch rest i state post ap r)
    (t : Tag) (d : PendingDeposit) (i : Nat) (processed : U64) (state : BeaconState P f)
    (post : TQueue) (ap : List (Applied P f)) :
    ((do
      let sum ← processed.add? d.amount "process_pending_deposits"
      if sum > available then return (⟨state, i, processed, post, ap, some .churn⟩ : PassResult P f)
      let mid ← applyPendingDeposit ctx state d
      passLoop ctx nextEpoch available finalizedSlot requestsStart rest (i + 1) sum mid post
        (ap ++ [(⟨t, d, state, .churn⟩ : Applied P f)])).map erasePass =
      (do
        let step ← (do
          let sum ← processed.add? d.amount "process_pending_deposits"
          if decide (sum > available) = true then
            return ForInStep.done (processed, i, (post.map Prod.snd).toArray, true, state)
          let mid ← applyPendingDeposit ctx state d
          pure (ForInStep.yield (sum, i + 1, (post.map Prod.snd).toArray, false, mid)))
        match step with
        | .done a => pure a
        | .yield a => pendingDepositsLoop ctx nextEpoch available finalizedSlot requestsStart (rest.map Prod.snd) a)) ∧
    ∀ r, (do
      let sum ← processed.add? d.amount "process_pending_deposits"
      if sum > available then return (⟨state, i, processed, post, ap, some .churn⟩ : PassResult P f)
      let mid ← applyPendingDeposit ctx state d
      passLoop ctx nextEpoch available finalizedSlot requestsStart rest (i + 1) sum mid post
        (ap ++ [(⟨t, d, state, .churn⟩ : Applied P f)])) = .ok r →
      LoopFacts ctx nextEpoch ((t, d) :: rest) i state post ap r := by
    cases hadd : processed.add? d.amount "process_pending_deposits" with
    | error err => exact ⟨rfl, fun r h => by cases h⟩
    | ok sum =>
      simp only [ok_bind']
      by_cases hsum : sum > available
      · simp only [hsum, decide_true, ite_true, pure_bind, Except.map]
        exact ⟨rfl, fun r h => by cases h; exact loopFacts_stop ..⟩
      · simp only [hsum, decide_false, ite_false]
        cases ha : applyPendingDeposit ctx state d with
        | error err => exact ⟨rfl, fun r h => by cases h⟩
        | ok mid =>
          simp only [ok_bind']
          exact ⟨(ih (i + 1) sum mid post (ap ++ [⟨t, d, state, .churn⟩])).1,
            fun r h => loopFacts_apply ctx nextEpoch rest (t, d) i state mid post ap
              .churn r ha ((ih ..).2 r h)⟩

private theorem passLoop_simulation (ctx : Ctx) (nextEpoch : Epoch) (available : U64)
    (finalizedSlot : Slot) (requestsStart : U64) (tq : TQueue) :
    ∀ (i : Nat) (processed : U64) (state : BeaconState P f) (post : TQueue)
      (ap : List (Applied P f)),
      (passLoop ctx nextEpoch available finalizedSlot requestsStart tq i processed state post ap).map
          erasePass =
        pendingDepositsLoop ctx nextEpoch available finalizedSlot requestsStart (tq.map Prod.snd)
          (processed, i, (post.map Prod.snd).toArray, false, state) ∧
      ∀ r, passLoop ctx nextEpoch available finalizedSlot requestsStart tq i processed state post ap =
        .ok r → LoopFacts ctx nextEpoch tq i state post ap r := by
  induction tq with
  | nil =>
    intro i processed state post ap
    constructor
    · simp only [passLoop, Except.map, erasePass]
      rfl
    · intro r h
      cases h
      exact loopFacts_stop ctx nextEpoch [] i processed state post ap none
  | cons e rest ih =>
    intro i processed state post ap
    rcases e with ⟨t, d⟩
    simp only [passLoop, List.map_cons, pendingDepositsLoop, pendingDepositStep]
    by_cases hb : (!f.atLeast .fulu && decide (d.slot > GENESIS_SLOT) &&
        decide (state.eth1_deposit_index < requestsStart)) = true
    · simp only [hb, ite_true, pure_bind, Except.map]
      exact ⟨rfl, fun r h => by cases h; exact loopFacts_stop ..⟩
    · simp only [hb]
      by_cases hf : d.slot > finalizedSlot
      · simp only [hf, ite_true, pure_bind, Except.map]
        exact ⟨rfl, fun r h => by cases h; exact loopFacts_stop ..⟩
      · simp only [hf, ite_false]
        by_cases hc : i ≥ P.MAX_PENDING_DEPOSITS_PER_EPOCH
        · simp only [hc, ite_true, pure_bind, Except.map]
          exact ⟨rfl, fun r h => by cases h; exact loopFacts_stop ..⟩
        · simp only [hc, ite_false]
          cases hfind : findValidatorIndex state d.pubkey with
          | none =>
            simp only [pure_bind, Bool.false_eq_true, ite_false]
            exact loopSimulation_normal ctx nextEpoch available finalizedSlot requestsStart rest ih
              t d i processed state post ap
          | some j =>
            dsimp only
            cases hv : state.validators.get j "process_pending_deposits" with
            | error err => exact ⟨rfl, fun r h => by cases h⟩
            | ok v =>
              simp only [ok_bind', pure_bind]
              by_cases hw : v.withdrawable_epoch < nextEpoch
              · simp only [hw, decide_true, Bool.false_eq_true, ite_true, ite_false]
                cases ha : applyPendingDeposit ctx state d with
                | error err => exact ⟨rfl, fun r h => by cases h⟩
                | ok mid =>
                  simp only [ok_bind', pure_bind]
                  exact ⟨(ih (i + 1) processed mid post
                    (ap ++ [⟨t, d, state, .withdrawn⟩])).1,
                    fun r h => loopFacts_apply ctx nextEpoch rest (t, d) i state mid post ap
                      .withdrawn r ha ((ih ..).2 r h)⟩
              · simp only [hw, decide_false, Bool.false_eq_true, ite_false]
                by_cases he : v.exit_epoch < FAR_FUTURE_EPOCH
                · simp only [he, decide_true, ite_true, pure_bind]
                  constructor
                  · simpa only [List.map_append, List.map_singleton, List.push_toArray] using
                      (ih (i + 1) processed state (post ++ [(t, d)]) ap).1
                  · intro r h
                    exact loopFacts_postpone ctx nextEpoch rest (t, d) i state post ap r
                      ⟨j, v, hfind, (getAt_ok_iff.mp hv), he, Nat.le_of_not_lt hw⟩
                      ((ih ..).2 r h)
                · simp only [he, decide_false, Bool.false_eq_true, ite_false]
                  exact loopSimulation_normal ctx nextEpoch available finalizedSlot requestsStart rest ih
                    t d i processed state post ap

/-- Every successful original pending pass has an aligned tagged execution with the same state. -/
theorem passMirror : PassMirror := by
  intro P f ctx state tq hqueue state' hrun
  obtain ⟨pending, hpending, hqueue⟩ := bind_ok_elim hqueue
  have hqueue : pending.toArray.toList = tq.map Prod.snd := Except.ok.inj hqueue
  rw [processPendingDeposits_eq] at hrun
  dsimp only at hrun
  obtain ⟨epoch, hepoch, hrun⟩ := bind_ok_elim hrun
  obtain ⟨nextEpoch, hnextEpoch, hrun⟩ := bind_ok_elim hrun
  obtain ⟨db, hdb, hrun⟩ := bind_ok_elim hrun
  obtain ⟨churn, hchurn, hrun⟩ := bind_ok_elim hrun
  obtain ⟨available, havailable, hrun⟩ := bind_ok_elim hrun
  obtain ⟨finalizedSlot, hfinalizedSlot, hrun⟩ := bind_ok_elim hrun
  obtain ⟨requestsStart, hrequestsStart, hrun⟩ := bind_ok_elim hrun
  rw [hpending, ok_bind', hqueue] at hrun
  obtain ⟨acc, hloop, hrun⟩ := bind_ok_elim hrun
  have hmap := (passLoop_simulation ctx nextEpoch available finalizedSlot requestsStart tq
    0 U64.zero state [] []).1
  simp only [List.map_nil] at hmap
  rw [hloop] at hmap
  cases htagged : passLoop ctx nextEpoch available finalizedSlot requestsStart tq
      0 U64.zero state [] [] with
  | error err => simp only [htagged, Except.map] at hmap; cases hmap
  | ok r =>
    have herase : erasePass r = acc := by
      simpa only [htagged, Except.map, Except.ok.injEq] using hmap
    subst acc
    have hparams : passParams ctx state = .ok (nextEpoch, available, finalizedSlot, requestsStart) := by
      simp only [passParams, hepoch, hnextEpoch, hdb, hchurn, havailable, hfinalizedSlot,
        hrequestsStart, ok_bind']
      rfl
    dsimp only [erasePass] at hrun
    have hrest : pending.toArray.extract r.next pending.length ++ (r.postponed.map Prod.snd).toArray =
        ((tq.drop r.next ++ r.postponed).map Prod.snd).toArray := by
      apply Array.toList_inj.mp
      simp only [Array.toList_append, Array.toList_extract, SszList.length,
        List.extract_eq_take_drop, List.map_append, List.map_drop]
      have hlen : pending.toArray.size = (tq.map Prod.snd).length := by
        rw [← hqueue, Array.length_toList]
      rw [hqueue, hlen, ← List.length_drop, List.take_length]
    rw [hrest] at hrun
    obtain ⟨q, hq, hrun⟩ := bind_ok_elim hrun
    obtain ⟨mid, hmid, hfinal⟩ := bind_ok_elim hrun
    have hfinal' : (if r.stop = some .churn then do
        let amount ← available.sub? r.processed "process_pending_deposits"
        mid.setDepositBalanceToConsume amount
      else mid.setDepositBalanceToConsume U64.zero) = .ok state' := by
      simpa only [decide_eq_true_eq] using hfinal
    refine ⟨tq.drop r.next ++ r.postponed, r.applied, ?_, ?_⟩
    · simp only [processPendingDepositsTagged, hparams, htagged, hq, hmid, ok_bind']
      by_cases hs : r.stop = some .churn
      · simp only [hs, ite_true] at hfinal' ⊢
        obtain ⟨amount, hamount, hst⟩ := bind_ok_elim hfinal'
        rw [hamount, ok_bind', hst]
        rfl
      · simp only [hs, ite_false] at hfinal' ⊢
        rw [hfinal']
        rfl
    · have hfields : state'.pending_deposits = mid.pending_deposits := by
        split at hfinal'
        · obtain ⟨_, _, h⟩ := bind_ok_elim hfinal'
          exact (setDepositBalanceToConsume_fields h).2.2
        · exact (setDepositBalanceToConsume_fields hfinal').2.2
      unfold BeaconState.setPendingDeposits at hmid
      obtain ⟨g, hg, hmid⟩ := bind_ok_elim hmid
      cases hmid
      have hread : state'.pendingDeposits = .ok q := by
        unfold BeaconState.pendingDeposits
        rw [hfields]
        exact gated_write_read hg
      rw [hread, ok_bind']
      unfold SszList.ofArray at hq
      split at hq
      · cases hq
        rfl
      · cases hq

private theorem partition_tags_nodup {tq applied postponed : TQueue} {k : Nat}
    (h : PassPartition (tq.take k) applied postponed)
    (hn : (tq.filterMap Prod.fst).Nodup) :
    (applied.filterMap Prod.fst ++ (tq.drop k ++ postponed).filterMap Prod.fst).Nodup := by
  have hm : IsMerge applied postponed (tq.take k) := by
    generalize heq : tq.take k = consumed at h ⊢
    clear heq
    induction h with
    | nil => exact .nil
    | apply e _ ih => exact .left e ih
    | postpone e _ ih => exact .right e ih
  have hp : (applied ++ postponed).Perm (tq.take k) := by
    generalize heq : tq.take k = consumed at hm ⊢
    clear h heq
    induction hm with
    | nil => exact .refl []
    | left e _ ih => exact ih.cons e
    | right e _ ih => exact List.perm_middle.trans (ih.cons e)
  have hs : (applied ++ (tq.drop k ++ postponed)).Perm ((applied ++ postponed) ++ tq.drop k) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁ := tq.drop k) (l₂ := postponed)).append_left applied
  have hp' := hs.trans (hp.append_right (tq.drop k))
  rw [List.take_append_drop] at hp'
  have ht := (hp'.filterMap Prod.fst).nodup_iff.mpr hn
  simpa only [List.filterMap_append] using ht

/-- The exact ordered, occurrence-preserving safety statement for the same frozen pass. -/
theorem d9Pass : D9Pass := by
  intro P f ctx state tq state' tq' ap hrun
  unfold processPendingDepositsTagged at hrun
  obtain ⟨⟨nextEpoch, available, finalizedSlot, requestsStart⟩, hparams, hrun⟩ := bind_ok_elim hrun
  obtain ⟨r, hloop, hrun⟩ := bind_ok_elim hrun
  obtain ⟨q, _, hrun⟩ := bind_ok_elim hrun
  obtain ⟨mid, _, hrun⟩ := bind_ok_elim hrun
  have hresult : r.applied = ap ∧ tq' = tq.drop r.next ++ r.postponed := by
    split at hrun
    · obtain ⟨amount, _, hrun⟩ := bind_ok_elim hrun
      obtain ⟨st, _, hrun⟩ := bind_ok_elim hrun
      cases hrun
      exact ⟨rfl, rfl⟩
    · obtain ⟨st, _, hrun⟩ := bind_ok_elim hrun
      cases hrun
      exact ⟨rfl, rfl⟩
  obtain ⟨k, fresh, postponed, hk, hi, ha, hp, hpart, _, hchain, _, hpost⟩ :=
    (passLoop_simulation ctx nextEpoch available finalizedSlot requestsStart tq
      0 U64.zero state [] []).2 r hloop
  simp only [Nat.zero_add, List.nil_append] at hi ha hp
  subst k
  rcases hresult with ⟨hap, htq⟩
  subst ap tq'
  subst fresh postponed
  refine ⟨nextEpoch, available, finalizedSlot, requestsStart, r, hparams, hloop,
    rfl, hk, rfl, hpart, hchain, ?_, ?_⟩
  · intro hn
    simpa only [List.filterMap_map, Function.comp_def, id_eq] using partition_tags_nodup hpart hn
  · intro e he
    obtain ⟨j, v, hj, hv, hexit, hwithdraw⟩ := hpost e he
    exact ⟨j, hj, v, getAt_ok_iff.mpr hv, hexit, hwithdraw⟩

end Blanc.Composition.DepositPendingPass
