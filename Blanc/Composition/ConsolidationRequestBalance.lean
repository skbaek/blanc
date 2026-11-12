import Batteries.Tactic.OpenPrivate
import Blanc.Composition.ConsolidationRequestJoint
import JauneConsensus.Facts.SlotEpochFrames

namespace Blanc.Composition.ConsolidationRequestBalance

open Jaune JauneConsensus Blanc ExecutionTrace
open Blanc.Corpus.Freeze.ConsolidationJoint
open Blanc.Composition.ConsolidationRequestPublic
open Blanc.Composition.ConsolidationRequestJoint

open private canonical_classified outcome_means joint_trace_step
  from Blanc.Composition.ConsolidationRequestJoint

variable {P : Preset} {f : CFork}

/-! ## The local law of `process_pending_consolidations` -/

theorem electra_of_queue {w : BeaconState P f} {q : SszList PendingConsolidation P.PENDING_CONSOLIDATIONS_LIMIT}
    (h : w.pendingConsolidations = .ok q) : f.atLeast .electra = true := by
  unfold BeaconState.pendingConsolidations at h
  cases f <;> first | rfl | (exfalso; cases h)

theorem queue_get {w : BeaconState P f} {q : SszList PendingConsolidation P.PENDING_CONSOLIDATIONS_LIMIT}
    (hf : f.atLeast .electra = true) (h : w.pendingConsolidations = .ok q) :
    q = Gated.get hf w.pending_consolidations := by
  unfold BeaconState.pendingConsolidations at h
  rw [Facts.gated_read_get hf] at h
  exact (Except.ok.inj h).symm

theorem transfers_of_moves {u mid u' : BeaconState P f} {pc : PendingConsolidation} {src : Validator}
    {bal : Gwei}
    (hbal : u.balances.toArray[pc.source_index.toNat]? = some bal)
    (hdec : decreaseBalance u pc.source_index
      (if bal < src.effective_balance then bal else src.effective_balance) = .ok mid)
    (hinc : increaseBalance mid pc.target_index
      (if bal < src.effective_balance then bal else src.effective_balance) = .ok u') :
    Transfers u u' pc src := by
  obtain ⟨b0, b1, hb0, hb1, hjd, hmid⟩ := Facts.decreaseBalance_spec hdec
  obtain ⟨c0, c1, hc0, hadd, hji, hu'⟩ := Facts.increaseBalance_spec hinc
  refine ⟨bal, hbal, ?_, ?_, ?_⟩
  · have h1 : u'.validators = mid.validators := congrArg (·.validators) hu'
    have h2 : mid.validators = u.validators := congrArg (·.validators) hmid
    exact h1.trans h2
  · intro i hs ht
    rw [hji, ite_eq_right ht, hjd, ite_eq_right hs]
  · intro hne
    obtain ⟨_, ⟨b', hb', hbn⟩, ⟨tb, tb', htb, htb', htbn⟩, _, _⟩ :=
      Facts.consolidation_balance_moved hne hbal hdec hinc
    exact ⟨tb, b', tb', htb, hb', htb', by rw [hbn, U64.toNat_min], by rw [htbn, U64.toNat_min]⟩

theorem pendingConsolidationsLaw : PendingConsolidationsLaw := by
  intro P f cfg w w' pending current nextEpoch run queue epoch next
  have hf : f.atLeast .electra = true := electra_of_queue queue
  obtain ⟨e0, ne, d, mid, us, he0, hne, hd, hlen, hus0, husd, hvals, hval, hbal, hpcl, hsteps, hstop⟩ :=
    Facts.processPendingConsolidations_full_law hf run
  have hcur : e0 = current := Except.ok.inj (he0.symm.trans epoch)
  subst hcur
  have hnext : nextEpoch = ne :=
    Facts.u64_eq_of_toNat_eq (by rw [hne, U64.toNat_add? next]; rfl)
  subst hnext
  have hq := queue_get hf queue
  have hpend : pending.toArray.toList = Facts.pendingConsolidationsList w := by
    rw [Facts.pendingConsolidationsList_eq_get hf, hq]
  have hsize : pending.toArray.size = (Facts.pendingConsolidationsList w).length := by
    rw [← hpend, Array.length_toList]
  refine ⟨d, us, hsize ▸ hd, hlen, hus0, ?_, ?_, ?_⟩
  · refine ⟨mid, Gated.get hf w'.pending_consolidations, husd, Facts.gated_read_get hf _ _, ?_, hbal, hval⟩
    rw [← Facts.pendingConsolidationsList_eq_get hf, hpcl, hpend]
  · intro i hi pc u u' hpc hu hu'
    rw [← Array.getElem?_toList, hpend] at hpc
    obtain ⟨pc', u0, u0', src, hpc', hu0, hu0', hsrc, hcase⟩ := hsteps i hi
    have e1 : pc' = pc := Option.some.inj (hpc'.symm.trans hpc)
    have e2 : u0 = u := Option.some.inj (hu0.symm.trans hu)
    have e3 : u0' = u' := Option.some.inj (hu0'.symm.trans hu')
    subst e1 e2 e3
    have hv := hvals u0 (List.mem_of_getElem? hu0)
    rw [hv] at hsrc
    refine ⟨src, hsrc, ?_⟩
    rcases hcase with ⟨hsl, heq⟩ | ⟨hsl, hnw, bal, ms, hb, hdec, hinc⟩
    · exact Or.inl ⟨hsl, heq⟩
    · exact Or.inr ⟨hsl, hnw, transfers_of_moves hb hdec hinc⟩
  · intro pc hpc
    rw [← Array.getElem?_toList, hpend] at hpc
    have hlt : d < (Facts.pendingConsolidationsList w).length := by
      have := (List.getElem?_eq_some_iff.mp hpc).1
      exact this
    obtain ⟨pc', src, hpc', hsrc, hsl, hgt⟩ := hstop hlt
    have e1 : pc' = pc := Option.some.inj (hpc'.symm.trans hpc)
    subst e1
    exact ⟨src, hsrc, hsl, hgt⟩

/-! ## The window every call sees -/

theorem pendingList_of_not_electra (h : f.atLeast .electra = false) (st : BeaconState P f) :
    pendingList st = [] := by
  unfold pendingList BeaconState.pendingConsolidations
  cases f <;> first | rfl | (exfalso; revert h; decide)

theorem pendingList_eq_get (hf : f.atLeast .electra = true) (st : BeaconState P f) :
    pendingList st = (Gated.get hf st.pending_consolidations).toArray.toList :=
  Facts.pendingConsolidationsList_eq_get hf st

theorem epochBefore_eq (ctx : Ctx) (s : BeaconState P f) :
    epochBeforeConsolidations ctx s = Facts.epochBeforeConsolidations ctx s := by
  unfold epochBeforeConsolidations Facts.epochBeforeConsolidations Facts.epochPreQueues
  simp only [bind_assoc]

theorem epochAfter_eq (ctx : Ctx) (s : BeaconState P f) :
    epochAfterConsolidations ctx s = Facts.epochPostQueues ctx s := rfl

theorem processEpoch_split (hf : f.atLeast .electra = true) (ctx : Ctx) (s : BeaconState P f) :
    processEpoch ctx s = (do
      let w ← epochBeforeConsolidations ctx s
      let w' ← processPendingConsolidations ctx.cfg w
      epochAfterConsolidations ctx w') := by
  rw [Facts.processEpoch_split_queues hf, epochBefore_eq, Facts.epochBeforeConsolidations]
  simp only [bind_assoc]
  rfl

theorem pendingList_with_slot (s : BeaconState P f) (n : Slot) :
    pendingList ({ s with slot := n } : BeaconState P f) = pendingList s := rfl

theorem epochBefore_queue (hf : f.atLeast .electra = true) {ctx : Ctx} {s w : BeaconState P f}
    (h : epochBeforeConsolidations ctx s = .ok w) : pendingList w = pendingList s := by
  rw [epochBefore_eq] at h
  exact Facts.pendingConsolidationsList_congr
    (Facts.epochBeforeConsolidations_pendingConsolidations hf ctx h).1

theorem processSlot_queue {s s1 : BeaconState P f} (h : processSlot s = .ok s1) :
    pendingList s1 = pendingList s :=
  Facts.pendingConsolidationsList_congr (Facts.processSlot_cpres_and_frame h).2.2.2.2.2.1

theorem pending_drop (hf : f.atLeast .electra = true) {cfg : Config} {w w' : BeaconState P f}
    (h : processPendingConsolidations cfg w = .ok w') :
    ∃ d, pendingList w' = (pendingList w).drop d := by
  obtain ⟨_, _, d, _, _, _, _, _, _, _, _, _, _, _, hpcl, _, _⟩ := Facts.processPendingConsolidations_full_law hf h
  exact ⟨d, hpcl⟩

theorem epoch_queue_drop (hf : f.atLeast .electra = true) {ctx : Ctx} {s1 s2 : BeaconState P f}
    (h : processEpoch ctx s1 = .ok s2) : ∃ d, pendingList s2 = (pendingList s1).drop d := by
  rw [processEpoch_split hf] at h
  obtain ⟨w, hw, h⟩ := Facts.bind_eq_ok_iff.mp h
  obtain ⟨w', hw', h⟩ := Facts.bind_eq_ok_iff.mp h
  obtain ⟨d, hd⟩ := pending_drop hf hw'
  refine ⟨d, ?_⟩
  rw [epochAfter_eq] at h
  have e1 : pendingList s2 = pendingList w' :=
    Facts.pendingConsolidationsList_congr (Facts.epochPostQueues_csub ctx h).pc_eq
  rw [e1, hd, epochBefore_queue hf hw]

theorem pendingConsolidationsWindow : PendingConsolidationsWindow := by
  refine ⟨?_, ?_⟩
  · intro P f ctx st w n h
    by_cases hf : f.atLeast .electra = true
    · induction h with
      | here slot succ perEpoch rem boundary input =>
        exact ⟨0, by rw [List.drop_zero, epochBefore_queue hf input, processSlot_queue slot]⟩
      | afterEpoch slot succ perEpoch rem boundary epoch later ih =>
        obtain ⟨d, hd⟩ := epoch_queue_drop hf epoch
        obtain ⟨d', hd'⟩ := ih
        refine ⟨d + d', ?_⟩
        rw [hd', pendingList_with_slot, hd, processSlot_queue slot, List.drop_drop, Nat.add_comm]
      | afterSlot slot succ perEpoch rem inside later ih =>
        obtain ⟨d', hd'⟩ := ih
        exact ⟨d', by rw [hd', pendingList_with_slot, processSlot_queue slot]⟩
    · have hf' : f.atLeast .electra = false := Bool.eq_false_iff.mpr hf
      exact ⟨0, by rw [pendingList_of_not_electra hf', pendingList_of_not_electra hf']; rfl⟩
  · intro P ccfg pre post h
    exact (Facts.upgradeToFulu_cpres_and_frame ccfg h).2.2.2.2.2.2.1

/-! ## The exact chronological calls of `process_slots` -/

theorem slotsCalls_append {ctx : Ctx} {n : Nat} {a b : BeaconState P f}
    {c1 : List (BeaconState P f × BeaconState P f)}
    (h1 : SlotsConsolidationCalls ctx n a b c1) :
    ∀ {m : Nat} {c : BeaconState P f} {c2 : List (BeaconState P f × BeaconState P f)},
      SlotsConsolidationCalls ctx m b c c2 →
      SlotsConsolidationCalls ctx (n + m) a c (c1 ++ c2) := by
  induction h1 with
  | zero =>
    intro m c c2 h2
    rw [Nat.zero_add]
    exact h2
  | epoch slot succ perEpoch rem boundary before call after rest ih =>
    intro m c c2 h2
    rw [Nat.add_right_comm]
    exact SlotsConsolidationCalls.epoch slot succ perEpoch rem boundary before call after (ih h2)
  | nonBoundary slot succ perEpoch rem inside rest ih =>
    intro m c c2 h2
    rw [Nat.add_right_comm]
    exact SlotsConsolidationCalls.nonBoundary slot succ perEpoch rem inside (ih h2)

theorem processSlots_calls (hf : f.atLeast .electra = true) {ctx : Ctx} {s s' : BeaconState P f}
    {slot : Slot} (h : processSlots ctx s slot = .ok s') :
    ∃ calls, ProcessSlotsCalls ctx s slot s' calls := by
  have hslot := (Facts.processSlots_slot hf ctx h)
  have horig := h
  unfold processSlots processSlotsWith at h
  obtain ⟨_, hreq, h⟩ := Facts.bind_eq_ok_iff.mp h
  have hlt : s.slot < slot := of_decide_eq_true (require_eq_ok_iff.mp hreq)
  obtain ⟨slotsPerEpoch, hspe, h⟩ := Facts.bind_eq_ok_iff.mp h
  obtain ⟨s_out, hloop, hpure⟩ := Facts.bind_eq_ok_iff.mp h
  have hs_eq : s_out = s' := Except.ok.inj hpure
  rw [hs_eq] at hloop
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hloop
  have hsz : [:slot.toNat - s.slot.toNat].size = slot.toNat - s.slot.toNat := by
    simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one, Nat.div_one]
  dsimp only [] at hloop
  rw [hsz] at hloop
  have key := Facts.list_forIn_rel
    (fun a b : BeaconState P f =>
      ∃ n calls, SlotsConsolidationCalls ctx n a b calls ∧ b.slot.toNat = a.slot.toNat + n)
    (fun b => ⟨0, [], .zero, rfl⟩)
    (fun a b c ⟨n1, c1, h1, s1⟩ ⟨n2, c2, h2, s2⟩ =>
      ⟨n1 + n2, c1 ++ c2, slotsCalls_append h1 h2, by omega⟩)
    _ ?_ (List.range' 0 (slot.toNat - s.slot.toNat)) s s' hloop
  · obtain ⟨n, calls, hcalls, hn⟩ := key
    have hlt_nat : s.slot.toNat < slot.toNat := hlt
    have hslot_nat : s'.slot.toNat = slot.toNat := by rw [hslot.2]
    have hn' : n = slot.toNat - s.slot.toNat := by omega
    subst hn'
    exact ⟨calls, hlt, horig, hcalls⟩
  · intro k st r hr
    obtain ⟨st1, hslot1, hr⟩ := Facts.bind_eq_ok_iff.mp hr
    obtain ⟨hsl1, _⟩ := Facts.processSlot_slot_and_header hslot1
    obtain ⟨next, hnext, hr⟩ := Facts.bind_eq_ok_iff.mp hr
    have hn : next.toNat = st.slot.toNat + 1 := by
      rw [U64.toNat_add? hnext, hsl1]; rfl
    obtain ⟨rem, hrem, hr⟩ := Facts.bind_eq_ok_iff.mp hr
    split at hr
    · rename_i hcond
      have hb : rem.toNat = 0 := beq_iff_eq.mp hcond
      obtain ⟨st2, hep, hr⟩ := Facts.bind_eq_ok_iff.mp hr
      have hr_eq : ForInStep.yield ({ st2 with slot := next } : BeaconState P f) = r :=
        Except.ok.inj hr
      subst hr_eq
      rw [processEpoch_split hf] at hep
      obtain ⟨w, hw, hep⟩ := Facts.bind_eq_ok_iff.mp hep
      obtain ⟨w', hw', hep⟩ := Facts.bind_eq_ok_iff.mp hep
      exact ⟨1, [(w, w')],
        SlotsConsolidationCalls.epoch hslot1 hnext hspe hrem hb hw hw' hep .zero,
        hn⟩
    · rename_i hcond
      have hb : rem.toNat ≠ 0 := fun heq => hcond (beq_iff_eq.mpr heq)
      have hr_eq : ForInStep.yield ({ st1 with slot := next } : BeaconState P f) = r :=
        Except.ok.inj hr
      subst hr_eq
      exact ⟨1, [],
        SlotsConsolidationCalls.nonBoundary hslot1 hnext hspe hrem hb .zero,
        hn⟩

/-! ## Call consolidation effects and fork-crossing call traces -/

private theorem unguarded_of_transfers {u u' : BeaconState P f}
    {pc : PendingConsolidation} {source : Validator}
    (transfers : Transfers u u' pc source) (distinct : pc.source_index ≠ pc.target_index) :
    UnguardedTransfers u u' pc source := by
  obtain ⟨sb, hsb, hval, hother, hmoved⟩ := transfers
  obtain ⟨tb, sb', tb', htb, hsb', htb', hs, ht⟩ := hmoved distinct
  exact ⟨sb, tb, sb', tb', hsb, htb, hsb', htb', hval, hother, hs, ht⟩

private theorem callConsolidationEffect_of_ok {cfg : Config} {w w' : BeaconState P f}
    (hrun : processPendingConsolidations cfg w = .ok w')
    (hdist : PendingDistinct w) :
    ∃ consumed,
      CallConsolidationEffect cfg w w' consumed ∧
      PendingDistinct w' := by
  have heq := hrun
  rw [Facts.processPendingConsolidations_eq] at heq
  dsimp only at heq
  obtain ⟨current, he0, heq⟩ := Facts.bind_eq_ok_iff.mp heq
  obtain ⟨nextEpoch, hne, heq⟩ := Facts.bind_eq_ok_iff.mp heq
  obtain ⟨pending, hq, _⟩ := Facts.bind_eq_ok_iff.mp heq
  obtain ⟨n, us, hn, hus_len, hus0, ⟨last, rest, husn, hq', hrest, hbal, hval⟩, hsteps, hstop⟩ :=
    pendingConsolidationsLaw cfg hrun hq he0 hne
  have hpl_w : pendingList w = pending.toArray.toList := by simp only [pendingList, hq]
  have hpl_w' : pendingList w' = rest.toArray.toList := by simp only [pendingList, hq']
  have hdrop : pendingList w' = (pendingList w).drop n := by rw [hpl_w', hrest, hpl_w]
  let consumed := (pendingList w).take n
  have hsplit : pendingList w = consumed ++ pendingList w' := by
    rw [hdrop]
    exact (List.take_append_drop n (pendingList w)).symm
  have hdist' : PendingDistinct w' := fun pc hpc =>
    hdist pc (by rw [hsplit]; exact List.mem_append_right _ hpc)
  have hclen : consumed.length = n := by
    dsimp only [consumed]
    rw [hpl_w]
    exact List.length_take_of_le (by simpa only [Array.length_toList] using hn)
  refine ⟨consumed, ⟨hrun, hsplit, hdist, current, nextEpoch, us, he0, hne,
    hclen ▸ hus_len, hus0, ⟨last, hclen ▸ husn, hbal, hval⟩, ?_, ?_⟩, hdist'⟩
  · intro i hi_c pc u u' hc_i hu hu'
    have hi : i < n := hclen ▸ hi_c
    have hpc_arr : pending.toArray[i]? = some pc := by
      rw [← Array.getElem?_toList, ← hpl_w, ← List.getElem?_take_of_lt hi]
      exact hc_i
    have hpc_ne : pc.source_index ≠ pc.target_index :=
      hdist pc (by rw [hsplit]; exact List.mem_append_left _ (List.mem_of_getElem? hc_i))
    obtain ⟨source, hsrc, hcase⟩ := hsteps i hi pc u u' hpc_arr hu hu'
    rcases hcase with ⟨hsl, heq_u⟩ | ⟨hsl, hnw, htr⟩
    · exact ⟨source, hsrc, Or.inl ⟨hsl, heq_u⟩⟩
    · exact ⟨source, hsrc, Or.inr ⟨hsl, hnw, htr, unguarded_of_transfers htr hpc_ne⟩⟩
  · intro pc h0
    rw [hdrop, List.getElem?_drop, Nat.add_zero, hpl_w, Array.getElem?_toList] at h0
    exact hstop pc h0

private inductive CallsTrace (ccfg : Config) :
    List PendingConsolidation → List (AnyConsolidationCall P) →
    List (List PendingConsolidation) → List PendingConsolidation → Prop
  | nil (q : List PendingConsolidation) : CallsTrace ccfg q [] [] q
  | cons {q₀ q_out : List PendingConsolidation} {c : AnyConsolidationCall P}
      {rest : List (AnyConsolidationCall P)} {cs : List PendingConsolidation}
      {cs_rest : List (List PendingConsolidation)}
      (hpre : pendingList c.pre = q₀)
      (heff : CallConsolidationEffect ccfg c.pre c.post cs)
      (hrest : CallsTrace ccfg (pendingList c.post) rest cs_rest q_out) :
      CallsTrace ccfg q₀ (c :: rest) (cs :: cs_rest) q_out

private theorem CallsTrace.length {ccfg : Config}
    {q₀ q_out : List PendingConsolidation}
    {stepCalls : List (AnyConsolidationCall P)}
    {perCallConsumed : List (List PendingConsolidation)}
    (htr : CallsTrace ccfg q₀ stepCalls perCallConsumed q_out) :
    perCallConsumed.length = stepCalls.length := by
  induction htr with
  | nil _ => rfl
  | cons _ _ _ ih => simp only [List.length_cons, ih]

private theorem CallsTrace.queue_eq {ccfg : Config}
    {q₀ q_out : List PendingConsolidation}
    {stepCalls : List (AnyConsolidationCall P)}
    {perCallConsumed : List (List PendingConsolidation)}
    (htr : CallsTrace ccfg q₀ stepCalls perCallConsumed q_out) :
    q₀ = perCallConsumed.flatten ++ q_out := by
  induction htr with
  | nil _ => rfl
  | cons hpre heff _ ih =>
    rw [← hpre, heff.2.1, ih, List.flatten_cons, List.append_assoc]

private theorem CallsTrace.append {ccfg : Config}
    {q₀ q₁ q₂ : List PendingConsolidation}
    {c₁ c₂ : List (AnyConsolidationCall P)}
    {cs₁ cs₂ : List (List PendingConsolidation)}
    (h₁ : CallsTrace ccfg q₀ c₁ cs₁ q₁)
    (h₂ : CallsTrace ccfg q₁ c₂ cs₂ q₂) :
    CallsTrace ccfg q₀ (c₁ ++ c₂) (cs₁ ++ cs₂) q₂ := by
  induction h₁ with
  | nil _ => exact h₂
  | cons hpre heff _ ih => exact .cons hpre heff (ih h₂)

private theorem CallsTrace.at_idx {ccfg : Config}
    {q₀ q_out : List PendingConsolidation}
    {stepCalls : List (AnyConsolidationCall P)}
    {perCallConsumed : List (List PendingConsolidation)}
    (htr : CallsTrace ccfg q₀ stepCalls perCallConsumed q_out) :
    ∀ {m : Nat} {c : AnyConsolidationCall P} {cs : List PendingConsolidation},
      stepCalls[m]? = some c → perCallConsumed[m]? = some cs →
      q₀ = (perCallConsumed.take m).flatten ++ pendingList c.pre ∧
      q₀ = (perCallConsumed.take (m + 1)).flatten ++ pendingList c.post ∧
      CallConsolidationEffect ccfg c.pre c.post cs := by
  induction htr with
  | nil _ =>
    intro m _ _ hm _
    nomatch hm
  | @cons q₀ _ c₀ rest cs₀ cs_rest hpre heff _ ih =>
    intro m c cs hm_c hm_cs
    cases m with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hm_c hm_cs
      subst hm_c hm_cs
      refine ⟨?_, ?_, heff⟩
      · simp only [List.take_zero, List.flatten_nil, List.nil_append, hpre]
      · simp only [List.take_succ_cons, List.take_zero, List.flatten_cons, List.flatten_nil,
          List.append_nil, ← hpre, heff.2.1]
    | succ m' =>
      simp only [List.getElem?_cons_succ] at hm_c hm_cs
      obtain ⟨h1, h2, h3⟩ := ih hm_c hm_cs
      have hq0 : q₀ = cs₀ ++ pendingList c₀.post := hpre.symm.trans heff.2.1
      refine ⟨?_, ?_, h3⟩
      · rw [hq0, h1, List.take_succ_cons, List.flatten_cons, List.append_assoc]
      · rw [hq0, h2, List.take_succ_cons, List.flatten_cons, List.append_assoc]

private theorem slotsCalls_trace (hf : f.atLeast .electra = true) {ctx : Ctx}
    {n : Nat} {st st' : BeaconState P f} {calls : List (BeaconState P f × BeaconState P f)}
    (h : SlotsConsolidationCalls ctx n st st' calls)
    (hdist : PendingDistinct st) :
    ∃ perCallConsumed,
      CallsTrace ctx.cfg (pendingList st) (liftCalls calls) perCallConsumed (pendingList st') ∧
      PendingDistinct st' := by
  induction h with
  | zero => exact ⟨[], .nil _, hdist⟩
  | nonBoundary slot succ perEpoch rem inside rest ih =>
    rename_i n' s0 s1 _ next _ _ _
    have hq1 : pendingList ({ s1 with slot := next } : BeaconState P f) = pendingList s0 :=
      (pendingList_with_slot s1 next).trans (processSlot_queue slot)
    have hd1 : PendingDistinct ({ s1 with slot := next } : BeaconState P f) :=
      fun pc hpc => hdist pc (hq1 ▸ hpc)
    obtain ⟨cs, htr, hdist'⟩ := ih hd1
    rw [hq1] at htr
    exact ⟨cs, htr, hdist'⟩
  | epoch slot succ perEpoch rem boundary before call after rest ih =>
    rename_i n' s0 s1 w w' s2 _ next _ _ _
    have hqw : pendingList w = pendingList s0 :=
      (epochBefore_queue hf before).trans (processSlot_queue slot)
    have hdw : PendingDistinct w := fun pc hpc => hdist pc (hqw ▸ hpc)
    obtain ⟨cs0, heff, hdw'⟩ := callConsolidationEffect_of_ok call hdw
    have hafter := after
    rw [epochAfter_eq] at hafter
    have hqs2 : pendingList ({ s2 with slot := next } : BeaconState P f) = pendingList w' :=
      (pendingList_with_slot s2 next).trans
        (Facts.pendingConsolidationsList_congr (Facts.epochPostQueues_csub ctx hafter).pc_eq)
    have hds2 : PendingDistinct ({ s2 with slot := next } : BeaconState P f) :=
      fun pc hpc => hdw' pc (hqs2 ▸ hpc)
    obtain ⟨cs_rest, htr, hdist'⟩ := ih hds2
    rw [hqs2] at htr
    exact ⟨cs0 :: cs_rest, .cons hqw heff htr, hdist'⟩

private theorem jointStep_calls_and_block {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s s' : JointState P} {b : AnySignedBlock P}
    (actual : jointStep cfg ccfg bls s b = .ok s')
    (hdist : PendingDistinct s.beacon) :
    ∃ (stIn post_blk : BeaconState P b.1) (exec' : BlockChain)
      (stepCalls : List (AnyConsolidationCall P))
      (perCallConsumed : List (List PendingConsolidation)),
      jointBlockInput ccfg bls s b = .ok stIn ∧
      StepConsolidationCalls ccfg bls s b stIn stepCalls ∧
      CallsTrace ccfg (pendingList s.beacon) stepCalls perCallConsumed (pendingList stIn) ∧
      PendingDistinct stIn ∧
      processBlock (jointCtx ccfg bls) stIn b.2.message = .ok post_blk ∧
      s' = ⟨b.1, post_blk, exec'⟩ := by
  obtain ⟨sf, beacon, exec⟩ := s
  obtain ⟨bf, sb⟩ := b
  cases sf <;> cases bf
  all_goals try (simp only [jointStep, ExceptT.stM_eq, throw, throwThe, MonadExceptOf.throw,
    reduceCtorEq] at actual; done)
  · obtain ⟨-, _, beacon', exec', -, -, hbeacon, hs'_eq⟩ := jointStep_electra_ok_iff.mp actual
    obtain ⟨stIn, hst, hpb⟩ := stateTransition_processBlock_post hbeacon
    obtain ⟨calls, hc⟩ := processSlots_calls rfl hst
    obtain ⟨cs, htr, hdIn⟩ := slotsCalls_trace rfl hc.2.2 hdist
    exact ⟨stIn, beacon', exec', liftCalls calls, cs, hst, .electra hc, htr, hdIn, hpb, hs'_eq⟩
  · obtain ⟨-, -, _, forkSlot, preUp, postUp, beacon', exec', hforkSlot, hslots, hup, -, -,
      hbeacon, hs'_eq⟩ := jointStep_cross_ok_iff.mp actual
    have hpre : ∃ electraCalls csE,
        ((beacon.slot < forkSlot ∧
            ProcessSlotsCalls (jointCtx ccfg bls) beacon forkSlot preUp electraCalls) ∨
          (¬ beacon.slot < forkSlot ∧ preUp = beacon ∧ electraCalls = [])) ∧
        CallsTrace ccfg (pendingList beacon) (liftCalls electraCalls) csE (pendingList preUp) ∧
        PendingDistinct preUp := by
      by_cases hlt : beacon.slot < forkSlot
      · have hslots' := hslots
        rw [ite_eq_left hlt] at hslots'
        obtain ⟨cE, hcE⟩ := processSlots_calls rfl hslots'
        obtain ⟨csE, htrE, hdE⟩ := slotsCalls_trace rfl hcE.2.2 hdist
        exact ⟨cE, csE, Or.inl ⟨hlt, hcE⟩, htrE, hdE⟩
      · have hslots' := hslots
        rw [ite_eq_right hlt] at hslots'
        have hpeq : preUp = beacon := (Except.ok.inj hslots').symm
        subst hpeq
        exact ⟨[], [], Or.inr ⟨hlt, rfl, rfl⟩, .nil _, hdist⟩
    obtain ⟨cE, csE, hpre_or, htrE, hdE⟩ := hpre
    have hup_q : pendingList postUp = pendingList preUp := pendingConsolidationsWindow.2 ccfg hup
    have hd_postUp : PendingDistinct postUp := fun pc hpc => hdE pc (hup_q ▸ hpc)
    by_cases hat : (sb.message.slot == postUp.slot) = true
    · have hbeacon' := hbeacon
      rw [ite_eq_left hat] at hbeacon'
      obtain ⟨hpb, _⟩ := Facts.atSlot_block_split hbeacon'
      have hin : jointBlockInput ccfg bls ⟨.electra, beacon, exec⟩ ⟨.fulu, sb⟩ = .ok postUp := by
        simp only [jointBlockInput, hforkSlot, Except.bind_ok, hslots, hup, hat, ↓reduceIte]
        rfl
      have htrF : CallsTrace ccfg (pendingList preUp)
          (liftCalls ([] : List (BeaconState P .fulu × BeaconState P .fulu))) []
          (pendingList postUp) := by
        rw [← hup_q]; exact .nil _
      exact ⟨postUp, beacon', exec', liftCalls cE ++ liftCalls [], csE ++ [],
        hin, .cross hforkSlot hpre_or hup (Or.inl ⟨hat, rfl, rfl⟩),
        htrE.append htrF, hd_postUp, hpb, hs'_eq⟩
    · have hat_f : (sb.message.slot == postUp.slot) = false := Bool.eq_false_iff.mpr hat
      have hbeacon' := hbeacon
      rw [ite_eq_right hat] at hbeacon'
      obtain ⟨stIn, hps2, hpb⟩ := stateTransition_processBlock_post hbeacon'
      obtain ⟨cF, hcF⟩ := processSlots_calls rfl hps2
      obtain ⟨csF, htrF, hdF⟩ := slotsCalls_trace rfl hcF.2.2 hd_postUp
      rw [hup_q] at htrF
      have hin : jointBlockInput ccfg bls ⟨.electra, beacon, exec⟩ ⟨.fulu, sb⟩ = .ok stIn := by
        simp only [jointBlockInput, hforkSlot, Except.bind_ok, hslots, hup, hat]
        exact hps2
      exact ⟨stIn, beacon', exec', liftCalls cE ++ liftCalls cF, csE ++ csF,
        hin, .cross hforkSlot hpre_or hup (Or.inr ⟨hat_f, hcF⟩),
        htrE.append htrF, hdF, hpb, hs'_eq⟩
  · obtain ⟨_, beacon', exec', -, -, hbeacon, hs'_eq⟩ := jointStep_fulu_ok_iff.mp actual
    obtain ⟨stIn, hst, hpb⟩ := stateTransition_processBlock_post hbeacon
    obtain ⟨calls, hc⟩ := processSlots_calls rfl hst
    obtain ⟨cs, htr, hdIn⟩ := slotsCalls_trace rfl hc.2.2 hdist
    exact ⟨stIn, beacon', exec', liftCalls calls, cs, hst, .fulu hc, htr, hdIn, hpb, hs'_eq⟩

/-! ## Block consolidation trace, `stepAccepted`, and `runAcceptedRecords` -/

private def traceAcceptedEntry (cfg : Config) (tr : List (BeaconState P f))
    (crs : List ConsolidationRequest) (k : Nat) : Option PendingConsolidation :=
  match tr[k]?, crs[k]? with
  | some m, some cr =>
    match classify cfg m cr with
    | .ok (.pendingConsolidation s t) => some { source_index := s, target_index := t }
    | _ => none
  | _, _ => none

private theorem traceAccepted_map_snd (cfg : Config) (tr : List (BeaconState P f))
    (crs : List ConsolidationRequest) :
    (traceAccepted cfg tr crs).map Prod.snd =
      (List.range crs.length).filterMap (traceAcceptedEntry cfg tr crs) := by
  unfold traceAccepted traceAcceptedEntry
  rw [List.map_filterMap]
  congr 1
  funext k
  cases tr[k]? <;> cases crs[k]? <;> try rfl
  dsimp only
  cases classify cfg _ _ with
  | error _ => rfl
  | ok o => cases o <;> rfl

private theorem filterMap_cons_toList {α β : Type _} (g : α → Option β) (x : α) (xs : List α) :
    List.filterMap g (x :: xs) = (g x).toList ++ List.filterMap g xs := by
  rw [List.filterMap_cons]
  cases g x <;> rfl

private theorem consolidationTrace_pendingList (hf : f.atLeast .electra = true) (cfg : Config) :
    ∀ (crs : List ConsolidationRequest) (st : BeaconState P f) (tr : List (BeaconState P f))
      (hne : tr ≠ []),
      consolidationTrace cfg st crs = .ok tr →
      pendingList (tr.getLast hne) = pendingList st ++ (traceAccepted cfg tr crs).map Prod.snd ∧
      (∀ pc ∈ (traceAccepted cfg tr crs).map Prod.snd, pc.source_index ≠ pc.target_index)
  | [], st, tr, hne, h => by
    unfold consolidationTrace at h
    have htr : tr = [st] := (Except.ok.inj h).symm
    subst htr
    exact ⟨(List.append_nil _).symm, fun _ hm => nomatch hm⟩
  | cr :: rest, st, tr, hne, h => by
    unfold consolidationTrace at h
    obtain ⟨st', hp, h⟩ := Facts.bind_eq_ok_iff.mp h
    obtain ⟨tr', htr', hpure⟩ := Facts.bind_eq_ok_iff.mp h
    have htr_eq : tr = st :: tr' := (Except.ok.inj hpure).symm
    subst htr_eq
    have hne' : tr' ≠ [] := by
      intro he
      have := (Facts.stepTrace_spec
        (fun s c => processConsolidationRequest cfg s c) (consolidationTrace cfg)
        (fun _ => rfl) (fun _ _ _ => rfl) rest st' tr' htr').1
      rw [he] at this
      nomatch this
    obtain ⟨hq_rest, hd_rest⟩ := consolidationTrace_pendingList hf cfg rest st' tr' hne' htr'
    obtain ⟨o_can, _, hc_can, _, _, _, _, _, _, _, hdist1, hpc1, _, _⟩ :=
      Facts.processConsolidationRequest_frame_and_queues hf hp
    have hp_cls := hp
    rw [classifySound] at hp_cls
    obtain ⟨o, hcls, _⟩ := Facts.bind_eq_ok_iff.mp hp_cls
    have hocan : o_can = canonicalOutcome o :=
      Except.ok.inj (hc_can.symm.trans (canonical_classified hcls))
    subst hocan
    have hent0 : traceAcceptedEntry cfg (st :: tr') (cr :: rest) 0 =
        Facts.acceptedConsolidation (canonicalOutcome o) := by
      simp only [traceAcceptedEntry, List.getElem?_cons_zero, hcls]
      cases o <;> rfl
    have hmap_cons : (traceAccepted cfg (st :: tr') (cr :: rest)).map Prod.snd =
        (Facts.acceptedConsolidation (canonicalOutcome o)).toList ++
          (traceAccepted cfg tr' rest).map Prod.snd := by
      rw [traceAccepted_map_snd, traceAccepted_map_snd, List.length_cons, List.range_succ_eq_map,
        filterMap_cons_toList, List.filterMap_map, hent0]
      rfl
    have hq_st' : pendingList st' =
        pendingList st ++ (Facts.acceptedConsolidation (canonicalOutcome o)).toList := by
      rw [pendingList_eq_get hf st', pendingList_eq_get hf st]
      exact hpc1
    refine ⟨?_, ?_⟩
    · rw [List.getLast_cons hne', hq_rest, hq_st', hmap_cons, List.append_assoc]
    · intro pc hpc
      rw [hmap_cons] at hpc
      rcases List.mem_append.mp hpc with h1 | h2
      · cases ho : Facts.acceptedConsolidation (canonicalOutcome o) with
        | none => rw [ho] at h1; nomatch h1
        | some pc0 =>
          rw [ho, Option.toList_some, List.mem_singleton] at h1
          subst h1
          exact hdist1 pc ho
      · exact hd_rest pc h2

private theorem blockBefore_withdrawn_queue (hf : f.atLeast .electra = true) {ctx : Ctx}
    {stIn before pre withdrawn : BeaconState P f} {blk : BeaconBlock P f}
    {wrs : List WithdrawalRequest}
    (hbefore : Facts.blockBeforeOps ctx stIn blk = .ok before)
    (hpre : Facts.preRequests ctx before blk.body = .ok pre)
    (hwd : Facts.foldWithdrawalRequests ctx.cfg pre wrs = .ok withdrawn) :
    pendingList withdrawn = pendingList stIn := by
  unfold Facts.blockBeforeOps Facts.blockAfterWithdrawals at hbefore
  simp only [bind_assoc] at hbefore
  obtain ⟨s1, h1, hbefore⟩ := Facts.bind_eq_ok_iff.mp hbefore
  obtain ⟨s2, h2, hbefore⟩ := Facts.bind_eq_ok_iff.mp hbefore
  obtain ⟨s3, h3, hbefore⟩ := Facts.bind_eq_ok_iff.mp hbefore
  obtain ⟨s4, h4, h5⟩ := Facts.bind_eq_ok_iff.mp hbefore
  have c1 := Facts.processBlockHeader_corpusPres h1
  have c2 := Facts.processWithdrawals_csub h2
  have c3 := Facts.processExecutionPayload_corpusPres ctx h3
  have c4 := Facts.processRandao_csub ctx h4
  have c5 := Facts.processEth1Data_csub h5
  rw [Facts.preRequests_eq_preDeposits_fold ctx before blk.body hf] at hpre
  obtain ⟨o1, ho1, ho2⟩ := Facts.bind_eq_ok_iff.mp hpre
  have co1 := Facts.preDeposits_cpres_and_frame hf ctx ho1
  obtain ⟨_, _, hfr_o2⟩ := Facts.foldDepositRequests_spec hf _ ho2
  have hpc_o2 : pre.pending_consolidations = o1.pending_consolidations := by rw [hfr_o2]
  have cwd := Facts.foldWithdrawalRequests_csub ctx.cfg hwd
  apply Facts.pendingConsolidationsList_congr
  rw [cwd.pc_eq, hpc_o2, co1.2.2.2.2.1, c5.pc_eq, c4.pc_eq, c3.2.2.2.1, c2.pc_eq, c1.2.2.2.1]

private theorem jointState_pendingList {s : JointState P} {b : BeaconState P f} {e : BlockChain}
    (h : s = ⟨f, b, e⟩) : pendingList s.beacon = pendingList b := by
  subst h; rfl

private theorem jointState_pendingDistinct {s : JointState P} {b : BeaconState P f} {e : BlockChain}
    (h : s = ⟨f, b, e⟩) : PendingDistinct s.beacon ↔ PendingDistinct b := by
  subst h; exact Iff.rfl

private theorem step_full_summary {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (D : JointRunStep (P := P) cfg ccfg bls)
    (actual : jointStep cfg ccfg bls D.pre D.block = .ok D.post)
    (hdist : PendingDistinct D.pre.beacon) :
    ∃ (stIn : BeaconState P D.block.1)
      (stepCalls : List (AnyConsolidationCall P))
      (perCallConsumed : List (List PendingConsolidation)),
      jointBlockInput ccfg bls D.pre D.block = .ok stIn ∧
      StepConsolidationCalls ccfg bls D.pre D.block stIn stepCalls ∧
      CallsTrace ccfg (pendingList D.pre.beacon) stepCalls perCallConsumed (pendingList stIn) ∧
      pendingList D.pre.beacon = perCallConsumed.flatten ++ pendingList stIn ∧
      pendingList D.post.beacon = pendingList stIn ++ stepAccepted D ∧
      PendingDistinct D.post.beacon := by
  obtain ⟨stIn, post_blk, exec', stepCalls, perCallConsumed, hin, hsc, htr, hdIn, hpb, hpost_eq⟩ :=
    jointStep_calls_and_block actual hdist
  have fork : D.block.1.atLeast .electra = true := by
    rcases (jointStep_engine actual).1 with h | h <;> rw [h] <;> rfl
  obtain ⟨requests, read, _⟩ := D.exists_executionRequests
  have reqeq : Gated.get fork D.block.2.message.body.execution_requests = requests :=
    Except.ok.inj ((Facts.gated_read_get fork _ _).symm.trans read)
  change processBlockWith (jointCtx ccfg bls) stIn D.block.2.message = .ok post_blk at hpb
  rw [Facts.processBlockWith_split] at hpb
  obtain ⟨before, beforeEq, rest⟩ := Except.bind_eq_ok hpb
  obtain ⟨afterOps, opsEq, sync⟩ := Except.bind_eq_ok rest
  rw [Facts.processOperations_split _ _ _ fork] at opsEq
  obtain ⟨pre, preEq, rest⟩ := Except.bind_eq_ok opsEq
  obtain ⟨withdrawn, withdrawalEq, postEq⟩ := Except.bind_eq_ok rest
  rw [reqeq] at withdrawalEq
  rw [Facts.postRequests_eq_foldConsolidationRequests _ _ _ fork, reqeq] at postEq
  obtain ⟨tr, hne, trace, last⟩ := Facts.stepTrace_of_foldlM
    (fun s cr => processConsolidationRequest ccfg s cr) (consolidationTrace ccfg)
    (fun _ => rfl) (fun _ _ _ => rfl) _ _ _ postEq
  have hjtr : jointConsolidationTrace ccfg bls D.pre D.block = .ok tr := by
    simp only [jointConsolidationTrace, hin, Except.bind_ok, beforeEq,
      preEq, read, withdrawalEq, trace]
  have hcrs : stepConsolidationRequests D = requests.consolidations.toArray.toList := by
    simp only [stepConsolidationRequests, read]
  have hsa : stepAccepted D =
      (traceAccepted ccfg tr requests.consolidations.toArray.toList).map Prod.snd := by
    simp only [stepAccepted, stepAcceptedWithPos, hjtr, hcrs]
  obtain ⟨hq_tr, hd_acc⟩ := consolidationTrace_pendingList fork ccfg
    requests.consolidations.toArray.toList withdrawn tr hne trace
  rw [last, blockBefore_withdrawn_queue fork beforeEq preEq withdrawalEq, ← hsa] at hq_tr
  rw [← hsa] at hd_acc
  have hq_post_blk : pendingList post_blk = pendingList stIn ++ stepAccepted D := by
    have csync := Facts.processSyncAggregate_csub (jointCtx ccfg bls) sync
    exact (Facts.pendingConsolidationsList_congr csync.pc_eq).trans hq_tr
  have hq_post : pendingList D.post.beacon = pendingList stIn ++ stepAccepted D :=
    (jointState_pendingList hpost_eq).trans hq_post_blk
  have hd_post : PendingDistinct D.post.beacon := by
    rw [jointState_pendingDistinct hpost_eq]
    intro pc hpc
    rw [hq_post_blk] at hpc
    rcases List.mem_append.mp hpc with h1 | h2
    · exact hdIn pc h1
    · exact hd_acc pc h2
  exact ⟨stIn, stepCalls, perCallConsumed, hin, hsc, htr, htr.queue_eq, hq_post, hd_post⟩

/-! ## Strict `(step, request)` order, acceptance witnesses, and global stream -/

private theorem pairwise_lt_range : ∀ n, List.Pairwise (· < ·) (List.range n)
  | 0 => .nil
  | n + 1 => by
    rw [List.range_succ, List.pairwise_append]
    exact ⟨pairwise_lt_range n, .cons (fun _ h => nomatch h) .nil,
      fun a ha b hb => by
        simp only [List.mem_singleton] at hb
        subst hb
        exact List.mem_range.mp ha⟩

private theorem pairwise_filterMap_fst {γ : Type _} (g : Nat → Option (Nat × γ))
    (hg : ∀ k y, g k = some y → y.1 = k) :
    ∀ {xs : List Nat}, List.Pairwise (· < ·) xs →
      List.Pairwise (fun a b : Nat × γ => a.1 < b.1) (xs.filterMap g)
  | [], _ => .nil
  | x :: xs, .cons hrel hpw => by
    simp only [List.filterMap_cons]
    cases hx : g x with
    | none => exact pairwise_filterMap_fst g hg hpw
    | some y =>
      refine .cons ?_ (pairwise_filterMap_fst g hg hpw)
      intro z hz
      obtain ⟨x', hx', hx'z⟩ := List.mem_filterMap.mp hz
      rw [hg x y hx, hg x' z hx'z]
      exact hrel x' hx'

private theorem pairwise_flatMap_nat {α : Type _} (R : α → α → Prop) (f : Nat → List α)
    (hinner : ∀ j, List.Pairwise R (f j))
    (hcross : ∀ j₁ j₂, j₁ < j₂ → ∀ a ∈ f j₁, ∀ b ∈ f j₂, R a b) :
    ∀ {xs : List Nat}, List.Pairwise (· < ·) xs → List.Pairwise R (xs.flatMap f)
  | [], _ => .nil
  | j :: js, .cons hrel hpw => by
    rw [List.flatMap_cons, List.pairwise_append]
    refine ⟨hinner j, pairwise_flatMap_nat R f hinner hcross hpw, ?_⟩
    intro a ha b hb
    obtain ⟨j₂, hj₂, hb₂⟩ := List.mem_flatMap.mp hb
    exact hcross j j₂ (hrel j₂ hj₂) a ha b hb₂

private theorem stepAcceptedWithPos_pairwise {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (D : JointRunStep (P := P) cfg ccfg bls) :
    List.Pairwise (fun a b : Nat × PendingConsolidation => a.1 < b.1) (stepAcceptedWithPos D) := by
  unfold stepAcceptedWithPos
  cases jointConsolidationTrace ccfg bls D.pre D.block with
  | error _ => exact .nil
  | ok tr =>
    unfold traceAccepted
    refine pairwise_filterMap_fst _ ?_ (pairwise_lt_range _)
    intro k y hy
    cases hm : tr[k]? with
    | none => rw [hm] at hy; nomatch hy
    | some m =>
      rw [hm] at hy
      cases hcr : (stepConsolidationRequests D)[k]? with
      | none => rw [hcr] at hy; nomatch hy
      | some cr =>
        rw [hcr] at hy
        dsimp only at hy
        cases hcls : classify ccfg m cr with
        | error _ => rw [hcls] at hy; nomatch hy
        | ok o =>
          rw [hcls] at hy
          cases o with
          | ignored _ => nomatch hy
          | switchToCompounding _ => nomatch hy
          | pendingConsolidation _ _ =>
            exact (congrArg Prod.fst (Option.some.inj hy)).symm

private theorem runAcceptedRecords_pairwise {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ s : JointState P} (run : JointRun cfg ccfg bls s₀ s) :
    List.Pairwise
      (fun a b : Nat × Nat × PendingConsolidation =>
        a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2.1 < b.2.1))
      (runAcceptedRecords run) := by
  unfold runAcceptedRecords runAcceptedRecordsUpTo
  refine pairwise_flatMap_nat _ _ ?_ ?_ (pairwise_lt_range _)
  · intro j'
    cases run.steps[j']? with
    | none => exact .nil
    | some D =>
      rw [List.pairwise_map]
      exact (stepAcceptedWithPos_pairwise D).imp fun h => Or.inr ⟨rfl, h⟩
  · intro j₁ j₂ hlt a ha b hb
    have ha1 : a.1 = j₁ := by
      cases hs1 : run.steps[j₁]? with
      | none => rw [hs1] at ha; nomatch ha
      | some D =>
        rw [hs1] at ha
        obtain ⟨_, _, rfl⟩ := List.mem_map.mp ha
        rfl
    have hb1 : b.1 = j₂ := by
      cases hs2 : run.steps[j₂]? with
      | none => rw [hs2] at hb; nomatch hb
      | some D =>
        rw [hs2] at hb
        obtain ⟨_, _, rfl⟩ := List.mem_map.mp hb
        rfl
    exact Or.inl (by omega)

private theorem runAcceptedRecords_ordered {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ s : JointState P} (run : JointRun cfg ccfg bls s₀ s)
    {idx₁ idx₂ j₁ k₁ j₂ k₂ : Nat} {pc₁ pc₂ : PendingConsolidation}
    (hlt : idx₁ < idx₂)
    (h1 : (runAcceptedRecords run)[idx₁]? = some (j₁, k₁, pc₁))
    (h2 : (runAcceptedRecords run)[idx₂]? = some (j₂, k₂, pc₂)) :
    j₁ < j₂ ∨ (j₁ = j₂ ∧ k₁ < k₂) := by
  obtain ⟨hi1, he1⟩ := List.getElem?_eq_some_iff.mp h1
  obtain ⟨hi2, he2⟩ := List.getElem?_eq_some_iff.mp h2
  have hpw := List.pairwise_iff_getElem.mp (runAcceptedRecords_pairwise run) idx₁ idx₂ hi1 hi2 hlt
  rw [he1, he2] at hpw
  exact hpw

private theorem runAcceptedRecords_witness {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ s : JointState P} (run : JointRun cfg ccfg bls s₀ s)
    {idx j k : Nat} {pc : PendingConsolidation}
    (h : (runAcceptedRecords run)[idx]? = some (j, k, pc)) :
    AcceptedRecordWitness run j k pc := by
  have hmem := List.mem_of_getElem? h
  unfold runAcceptedRecords runAcceptedRecordsUpTo at hmem
  obtain ⟨j', _, hj'⟩ := List.mem_flatMap.mp hmem
  cases hstep : run.steps[j']? with
  | none => rw [hstep] at hj'; nomatch hj'
  | some D =>
    rw [hstep] at hj'
    obtain ⟨⟨k0, pc0⟩, hkpc, heq⟩ := List.mem_map.mp hj'
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    unfold stepAcceptedWithPos at hkpc
    cases htr : jointConsolidationTrace ccfg bls D.pre D.block with
    | error _ => rw [htr] at hkpc; nomatch hkpc
    | ok tr =>
      rw [htr] at hkpc
      unfold traceAccepted at hkpc
      obtain ⟨k1, _, hk1⟩ := List.mem_filterMap.mp hkpc
      cases hmid : tr[k1]? with
      | none => rw [hmid] at hk1; nomatch hk1
      | some m =>
        rw [hmid] at hk1
        cases hcr : (stepConsolidationRequests D)[k1]? with
        | none => rw [hcr] at hk1; nomatch hk1
        | some cr =>
          rw [hcr] at hk1
          dsimp only at hk1
          cases hcls : classify ccfg m cr with
          | error _ => rw [hcls] at hk1; nomatch hk1
          | ok o =>
            rw [hcls] at hk1
            cases o with
            | ignored _ => nomatch hk1
            | switchToCompounding _ => nomatch hk1
            | pendingConsolidation src tgt =>
              simp only [Option.some.injEq, Prod.mk.injEq] at hk1
              obtain ⟨rfl, rfl⟩ := hk1
              unfold stepConsolidationRequests at hcr
              cases hread : Gated.read D.block.2.message.body.execution_requests
                  "NewPayloadRequest: execution_requests" with
              | error _ => rw [hread] at hcr; nomatch hcr
              | ok requests =>
                rw [hread, Array.getElem?_toList] at hcr
                obtain ⟨m', hnext, hproc⟩ := joint_trace_step hread htr hcr hmid
                rw [classifySound, hcls] at hproc
                exact ⟨D, requests, cr, tr, m, m', hstep, hread, hcr, htr, hmid, hnext,
                  hcls, hproc, outcome_means hcls hproc⟩

private theorem range_flatMap_take {α β : Type _} (g : α → List β) :
    ∀ (xs : List α) (j : Nat),
      ((List.range (min j xs.length)).flatMap fun j' =>
        match xs[j']? with
        | some x => g x
        | none => []) = (xs.take j).flatMap g
  | [], j => by
    simp only [List.length_nil, Nat.min_zero, List.range_zero, List.flatMap_nil, List.take_nil]
  | x :: rest, 0 => by
    simp only [Nat.zero_min, List.range_zero, List.flatMap_nil, List.take_zero]
  | x :: rest, j' + 1 => by
    have hmin : min (j' + 1) (rest.length + 1) = min j' rest.length + 1 := by omega
    rw [List.length_cons, hmin, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.take_succ_cons,
      List.flatMap_cons]
    congr 1
    exact range_flatMap_take g rest j'

private theorem runAcceptedUpTo_eq {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ s : JointState P} (run : JointRun cfg ccfg bls s₀ s) (j : Nat) :
    runAcceptedUpTo run j = (run.steps.take j).flatMap stepAccepted := by
  unfold runAcceptedUpTo runAcceptedRecordsUpTo
  rw [List.map_flatMap, ← range_flatMap_take stepAccepted run.steps j]
  congr 1
  funext j'
  cases run.steps[j']? with
  | none => rfl
  | some D =>
    rw [List.map_map]
    rfl

private theorem runAccepted_eq {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ s : JointState P} (run : JointRun cfg ccfg bls s₀ s) :
    runAccepted run = run.steps.flatMap stepAccepted := by
  unfold runAccepted
  rw [runAcceptedUpTo_eq, List.take_length]

private theorem getElem?_append_singleton_last {α : Type _} {xs : List α} {x y : α} {j : Nat}
    (hj : ¬ j < xs.length) (h : (xs ++ [x])[j]? = some y) : j = xs.length ∧ y = x := by
  rw [List.getElem?_append_right (by omega)] at h
  cases hk : j - xs.length with
  | zero =>
    rw [hk, List.getElem?_cons_zero, Option.some.injEq] at h
    exact ⟨by omega, h.symm⟩
  | succ k =>
    rw [hk, List.getElem?_cons_succ, List.getElem?_nil] at h
    nomatch h

private theorem run_consumed_trace {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ : JointState P} (h0 : PendingDistinct s₀.beacon) :
    ∀ {s : JointState P} (run : JointRun cfg ccfg bls s₀ s),
      ∃ runConsumed : List (List (List PendingConsolidation)),
        runConsumed.length = run.steps.length ∧
        (∀ {j : Nat} {D : JointRunStep (P := P) cfg ccfg bls}
            {perCallConsumed : List (List PendingConsolidation)},
          run.steps[j]? = some D →
          runConsumed[j]? = some perCallConsumed →
          let consumedBefore := ((runConsumed.take j).flatten).flatten
          acceptedStreamUpTo run j = consumedBefore ++ pendingList D.pre.beacon ∧
          PendingDistinct D.pre.beacon ∧
          ∃ (stIn : BeaconState P D.block.1) (stepCalls : List (AnyConsolidationCall P)),
            jointBlockInput ccfg bls D.pre D.block = .ok stIn ∧
            StepConsolidationCalls ccfg bls D.pre D.block stIn stepCalls ∧
            perCallConsumed.length = stepCalls.length ∧
            (∀ (m : Nat), m < stepCalls.length →
              ∀ (c : AnyConsolidationCall P) (cs : List PendingConsolidation),
              stepCalls[m]? = some c → perCallConsumed[m]? = some cs →
              acceptedStreamUpTo run j =
                (consumedBefore ++ (perCallConsumed.take m).flatten) ++ pendingList c.pre ∧
              acceptedStreamUpTo run j =
                (consumedBefore ++ (perCallConsumed.take (m + 1)).flatten) ++ pendingList c.post ∧
              CallConsolidationEffect ccfg c.pre c.post cs) ∧
            pendingList D.pre.beacon = perCallConsumed.flatten ++ pendingList stIn ∧
            pendingList D.post.beacon = pendingList stIn ++ stepAccepted D) ∧
        acceptedStream run = (runConsumed.flatten).flatten ++ pendingList s.beacon ∧
        PendingDistinct s.beacon
  | _, .nil => by
    refine ⟨[], rfl, ?_, List.append_nil _, h0⟩
    intro _ _ _ _ hcs
    rw [List.getElem?_nil] at hcs
    nomatch hcs
  | _, .snoc run b step bound => by
    obtain ⟨rc, hrc_len, hrc_step, hrc_end, hdist_s⟩ := run_consumed_trace h0 run
    let D_last : JointRunStep (P := P) cfg ccfg bls :=
      ⟨_, _, b, JointStepTrace.choose step bound⟩
    obtain ⟨stIn, stepCalls, cs_last, hin, hsc, htr, hq_pre, hq_post, hd_post⟩ :=
      step_full_summary D_last step hdist_s
    refine ⟨rc ++ [cs_last], ?_, ?_, ?_, hd_post⟩
    · rw [JointRun.steps_snoc, List.length_append, List.length_append, hrc_len]
      rfl
    · intro j D perCallConsumed hD hcs
      rw [JointRun.steps_snoc] at hD
      by_cases hj : j < run.steps.length
      · rw [List.getElem?_append_left hj] at hD
        rw [List.getElem?_append_left (hrc_len ▸ hj)] at hcs
        have htake_rc : (rc ++ [cs_last]).take j = rc.take j :=
          List.take_append_of_le_length (by omega)
        have hstream_eq : acceptedStreamUpTo (run.snoc b step bound) j = acceptedStreamUpTo run j := by
          simp only [acceptedStreamUpTo, runAcceptedUpTo_eq, JointRun.steps_snoc,
            List.take_append_of_le_length (Nat.le_of_lt hj)]
        dsimp only
        rw [htake_rc, hstream_eq]
        exact hrc_step hD hcs
      · obtain ⟨rfl, hD_eq⟩ := getElem?_append_singleton_last hj hD
        cases hD_eq
        obtain ⟨_, hcs_eq⟩ := getElem?_append_singleton_last (hrc_len ▸ hj) hcs
        cases hcs_eq
        have htake_rc : (rc ++ [cs_last]).take run.steps.length = rc := by
          rw [← hrc_len, List.take_left]
        have hstream_eq : acceptedStreamUpTo (run.snoc b step bound) run.steps.length =
            acceptedStream run := by
          simp only [acceptedStreamUpTo, acceptedStream, runAcceptedUpTo_eq, runAccepted_eq,
            JointRun.steps_snoc, List.take_left]
        dsimp only
        rw [htake_rc, hstream_eq]
        refine ⟨hrc_end, hdist_s, stIn, stepCalls, hin, hsc, htr.length, ?_, hq_pre, hq_post⟩
        intro m _ c cs hm_c hm_cs
        obtain ⟨h1, h2, h3⟩ := htr.at_idx hm_c hm_cs
        refine ⟨?_, ?_, h3⟩
        · rw [hrc_end, h1, List.append_assoc]
        · rw [hrc_end, h2, List.append_assoc]
    · simp only [acceptedStream, runAccepted_eq, JointRun.steps_snoc, List.flatMap_append,
        List.flatMap_cons, List.flatMap_nil, List.append_nil]
      have hrc_flat : ((rc ++ [cs_last]).flatten).flatten =
          (rc.flatten).flatten ++ cs_last.flatten := by
        rw [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.flatten_append]
      rw [← List.append_assoc, ← runAccepted_eq, ← acceptedStream, hrc_end, hq_pre, hrc_flat]
      simp only [List.append_assoc]
      congr 2
      exact hq_post.symm

/-- **C-S9 balance.** -/
theorem c_s9_balance : C_S9_balance := by
  refine ⟨pendingConsolidationsLaw, pendingConsolidationsWindow, ?_⟩
  intro P cfg ccfg bls checkpoint anchor final v
  exact ⟨fun _ _ _ _ _ _ _ _ hlt h1 h2 => runAcceptedRecords_ordered v.run hlt h1 h2,
    fun _ _ _ _ h => runAcceptedRecords_witness v.run h,
    run_consumed_trace v.pendingDistinct v.run⟩

end Blanc.Composition.ConsolidationRequestBalance
