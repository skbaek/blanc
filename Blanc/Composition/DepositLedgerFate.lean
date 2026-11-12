import Blanc.Composition.DepositLedgerMirrors
import Blanc.Composition.DepositConsensusOutcomes

/-! Occurrence fate and Nat principal conservation for the existing frozen ledger. -/
namespace Blanc.Composition.DepositLedgerFate

open Jaune JauneConsensus JauneConsensus.Facts
open Blanc.Corpus.Freeze.Deposit

variable {P : Preset} {f : CFork}

private theorem partition_perm {tq ap post : TQueue} (h : PassPartition tq ap post) :
    (ap ++ post).Perm tq := by
  induction h with
  | nil => exact .refl []
  | apply e _ ih => exact ih.cons e
  | postpone e _ ih => exact List.perm_middle.trans (ih.cons e)

private theorem passFacts (ctx : Ctx) (state : BeaconState P f) (tq : TQueue)
    (state' : BeaconState P f) (tq' : TQueue) (ap : List (Applied P f))
    (h : processPendingDepositsTagged ctx state tq = .ok (state', tq', ap)) :
    ((ap.map fun a => (a.tag, a.deposit)) ++ tq').Perm tq ∧
      ∀ a ∈ ap, ∃ post, applyPendingDeposit ctx a.pre a.deposit = .ok post := by
  obtain ⟨_, _, _, _, r, _, _, _, _, rest, partition, calls, _, _⟩ :=
    DepositPendingPass.d9Pass ctx state tq state' tq' ap h
  constructor
  · rw [rest]
    have reorder : ((ap.map fun a => (a.tag, a.deposit)) ++
        (tq.drop r.next ++ r.postponed)).Perm
        (((ap.map fun a => (a.tag, a.deposit)) ++ r.postponed) ++ tq.drop r.next) := by
      simpa only [List.append_assoc] using
        (List.perm_append_comm (l₁ := tq.drop r.next) (l₂ := r.postponed)).append_left
          (ap.map fun a => (a.tag, a.deposit))
    have moved := reorder.trans ((partition_perm partition).append_right (tq.drop r.next))
    simpa only [List.take_append_drop] using moved
  · intro a ha
    obtain ⟨idx, hi⟩ := List.mem_iff_getElem?.mp ha
    exact ⟨_, calls idx a hi⟩

private theorem epochFacts (ctx : Ctx) (state : BeaconState P f) (tq : TQueue)
    (state' : BeaconState P f) (tq' : TQueue) (ap : List (Applied P f))
    (h : processEpochTagged ctx state tq = .ok (state', tq', ap)) :
    ((ap.map fun a => (a.tag, a.deposit)) ++ tq').Perm tq ∧
      ∀ a ∈ ap, ∃ post, applyPendingDeposit ctx a.pre a.deposit = .ok post := by
  unfold processEpochTagged at h
  obtain ⟨s1, _, h⟩ := bind_ok_elim h
  obtain ⟨s2, _, h⟩ := bind_ok_elim h
  obtain ⟨s3, _, h⟩ := bind_ok_elim h
  obtain ⟨s4, _, h⟩ := bind_ok_elim h
  obtain ⟨s5, _, h⟩ := bind_ok_elim h
  obtain ⟨s6, _, h⟩ := bind_ok_elim h
  by_cases hf : f.atLeast .electra = true
  all_goals
    simp only [hf, ite_true] at h
    first
    | obtain ⟨⟨passed, tqP, apP⟩, hp, h⟩ := bind_ok_elim h
      obtain ⟨consolidated, _, h⟩ := bind_ok_elim h
      have facts := passFacts ctx s6 tq passed tqP apP hp
    | have facts : (([].map fun a : Applied P f => (a.tag, a.deposit)) ++ tq).Perm tq ∧
          ∀ a ∈ ([] : List (Applied P f)),
            ∃ post, applyPendingDeposit ctx a.pre a.deposit = .ok post :=
        ⟨.refl _, fun a ha => by cases ha⟩
  all_goals
    simp only [pure_bind] at h
    obtain ⟨s7, _, h⟩ := bind_ok_elim h
    obtain ⟨s8, _, h⟩ := bind_ok_elim h
    obtain ⟨s9, _, h⟩ := bind_ok_elim h
    obtain ⟨s10, _, h⟩ := bind_ok_elim h
    obtain ⟨s11, _, h⟩ := bind_ok_elim h
    obtain ⟨s12, _, h⟩ := bind_ok_elim h
    split at h
    · obtain ⟨s13, _, h⟩ := bind_ok_elim h
      cases h
      exact facts
    · cases h
      exact facts

private theorem slotsLoopFacts (ctx : Ctx) (spe : U64) (n : Nat) :
    ∀ (state : BeaconState P f) (tq : TQueue) (acc : List (Applied P f))
      (state' : BeaconState P f) (tq' : TQueue) (ap : List (Applied P f)),
    slotsLoopTagged ctx spe n state tq acc = .ok (state', tq', ap) →
    ∃ fresh, ap = acc ++ fresh ∧
      ((fresh.map fun a => (a.tag, a.deposit)) ++ tq').Perm tq ∧
      ∀ a ∈ fresh, ∃ post, applyPendingDeposit ctx a.pre a.deposit = .ok post := by
  induction n with
  | zero =>
    intro state tq acc state' tq' ap h
    cases h
    exact ⟨[], (List.append_nil _).symm, .refl _, fun a ha => by cases ha⟩
  | succ n ih =>
    intro state tq acc state' tq' ap h
    unfold slotsLoopTagged at h
    obtain ⟨slotState, _, h⟩ := bind_ok_elim h
    obtain ⟨next, _, h⟩ := bind_ok_elim h
    obtain ⟨rem, _, h⟩ := bind_ok_elim h
    split at h
    · obtain ⟨⟨ep, tqE, apE⟩, he, h⟩ := bind_ok_elim h
      simp only [pure_bind] at h
      obtain ⟨tail, hap, hperm, hcalls⟩ := ih _ tqE (acc ++ apE) state' tq' ap h
      obtain ⟨eperm, ecalls⟩ := epochFacts ctx slotState tq ep tqE apE he
      refine ⟨apE ++ tail, ?_, ?_, ?_⟩
      · simpa only [List.append_assoc] using hap
      · simpa only [List.map_append, List.append_assoc] using
          (hperm.append_left (apE.map fun a => (a.tag, a.deposit))).trans eperm
      · intro a ha
        exact (List.mem_append.mp ha).elim (ecalls a) (hcalls a)
    · simp only [pure_bind] at h
      exact ih _ tq acc state' tq' ap h

private theorem slotsFacts (ctx : Ctx) (state : BeaconState P f) (slot : Slot)
    (tq : TQueue) (state' : BeaconState P f) (tq' : TQueue) (ap : List (Applied P f))
    (h : processSlotsTagged ctx state slot tq = .ok (state', tq', ap)) :
    ((ap.map fun a => (a.tag, a.deposit)) ++ tq').Perm tq ∧
      ∀ a ∈ ap, ∃ post, applyPendingDeposit ctx a.pre a.deposit = .ok post := by
  unfold processSlotsTagged at h
  obtain ⟨_, _, h⟩ := bind_ok_elim h
  obtain ⟨spe, _, h⟩ := bind_ok_elim h
  obtain ⟨fresh, hap, hperm, hcalls⟩ := slotsLoopFacts ctx spe _ state tq [] state' tq' ap h
  simp only [List.nil_append] at hap
  subst fresh
  exact ⟨hperm, hcalls⟩

private theorem forkFacts (ctx : Ctx) (tq tq' : TQueue) (ap : List (Applied P f))
    (facts : ((ap.map fun a => (a.tag, a.deposit)) ++ tq').Perm tq ∧
      ∀ a ∈ ap, ∃ post, applyPendingDeposit ctx a.pre a.deposit = .ok post) :
    (((ap.map fun a => (⟨f, a⟩ : AppliedAt P)).map fun a => (a.2.tag, a.2.deposit)) ++ tq').Perm tq ∧
      ∀ a ∈ ap.map (fun a => (⟨f, a⟩ : AppliedAt P)),
        ∃ post, applyPendingDeposit ctx a.2.pre a.2.deposit = .ok post := by
  refine ⟨?_, ?_⟩
  · simpa only [List.map_map, Function.comp_def] using facts.1
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact facts.2 b hb

private theorem inputFacts (ccfg : Config) (bls : Bool) (s : JointState P)
    (b : AnySignedBlock P) (tq : TQueue) (st : BeaconState P b.1) (tq' : TQueue)
    (ap : List (AppliedAt P))
    (h : jointBlockInputTagged ccfg bls s b tq = .ok (st, tq', ap)) :
    ((ap.map fun a => (a.2.tag, a.2.deposit)) ++ tq').Perm tq ∧
      ∀ a ∈ ap, ∃ post, applyPendingDeposit (jointCtx ccfg bls) a.2.pre a.2.deposit = .ok post := by
  obtain ⟨sf, beacon, exec⟩ := s
  obtain ⟨bf, sb⟩ := b
  cases sf <;> cases bf
  all_goals try (simp only [jointBlockInputTagged, ExceptT.stM_eq, throw, throwThe,
    MonadExceptOf.throw, reduceCtorEq] at h; done)
  · simp only [jointBlockInputTagged] at h
    split at h
    · cases h
      exact ⟨.refl _, fun a ha => by cases ha⟩
    · obtain ⟨⟨mid, tqM, apM⟩, hs, h⟩ := bind_ok_elim h
      cases h
      exact forkFacts _ _ _ apM (slotsFacts _ beacon sb.message.slot tq _ _ apM hs)
  · simp only [jointBlockInputTagged] at h
    obtain ⟨forkSlot, _, h⟩ := bind_ok_elim h
    have first : ∃ (before : BeaconState P .electra) (tqE : TQueue)
        (apE : List (Applied P .electra)),
        (((apE.map fun a => (⟨.electra, a⟩ : AppliedAt P)).map fun a =>
          (a.2.tag, a.2.deposit)) ++ tqE).Perm tq ∧
        (∀ a ∈ apE.map (fun a => (⟨.electra, a⟩ : AppliedAt P)),
          ∃ post, applyPendingDeposit (jointCtx ccfg bls) a.2.pre a.2.deposit = .ok post) ∧
        (do
          let up ← upgradeToFulu ccfg before
          if sb.message.slot == up.slot then
            pure (up, tqE, apE.map fun a => (⟨.electra, a⟩ : AppliedAt P))
          else do
            let (mid, tqF, apF) ← processSlotsTagged (jointCtx ccfg bls) up sb.message.slot tqE
            pure (mid, tqF, apE.map (fun a => (⟨.electra, a⟩ : AppliedAt P)) ++
              apF.map fun a => (⟨.fulu, a⟩ : AppliedAt P))) = .ok (st, tq', ap) := by
      by_cases hlt : beacon.slot < forkSlot
      · simp only [hlt, ite_true] at h
        obtain ⟨⟨before, tqE, apE⟩, he, h⟩ := bind_ok_elim h
        have efacts := forkFacts (jointCtx ccfg bls) tq tqE apE
          (slotsFacts _ beacon forkSlot tq before tqE apE he)
        refine ⟨before, tqE, apE, efacts.1, efacts.2, ?_⟩
        simpa only [pure_bind, List.map_nil, List.append_nil] using h
      · simp only [hlt, ite_false, pure_bind] at h
        refine ⟨beacon, tq, [], .refl _, (fun a ha => by cases ha), ?_⟩
        simpa only [pure_bind, List.map_nil, List.append_nil] using h
    obtain ⟨before, tqE, apE, ep, ec, h⟩ := first
    have efacts := And.intro ep ec
    obtain ⟨up, _, h⟩ := bind_ok_elim h
    have second : ∃ apF : List (Applied P .fulu),
        ap = apE.map (fun a => (⟨.electra, a⟩ : AppliedAt P)) ++
          apF.map (fun a => (⟨.fulu, a⟩ : AppliedAt P)) ∧
        ((apF.map fun a => (a.tag, a.deposit)) ++ tq').Perm tqE ∧
        ∀ a ∈ apF, ∃ post, applyPendingDeposit (jointCtx ccfg bls) a.pre a.deposit = .ok post := by
      split at h
      · cases h
        exact ⟨[], (List.append_nil _).symm, .refl _, fun a ha => by cases ha⟩
      · obtain ⟨⟨mid, tqF, apF⟩, hs, h⟩ := bind_ok_elim h
        cases h
        obtain ⟨hp, hc⟩ := slotsFacts _ up sb.message.slot tqE _ _ apF hs
        exact ⟨apF, rfl, hp, hc⟩
    obtain ⟨apF, rfl, pf, cf⟩ := second
    have ffacts := forkFacts (jointCtx ccfg bls) tqE tq' apF ⟨pf, cf⟩
    constructor
    · simpa only [List.map_append, List.append_assoc] using
        (ffacts.1.append_left ((apE.map fun a => (⟨.electra, a⟩ : AppliedAt P)).map
          fun a => (a.2.tag, a.2.deposit))).trans efacts.1
    · intro a ha
      exact (List.mem_append.mp ha).elim (efacts.2 a) (ffacts.2 a)
  · simp only [jointBlockInputTagged] at h
    obtain ⟨⟨mid, tqM, apM⟩, hs, h⟩ := bind_ok_elim h
    cases h
    exact forkFacts _ _ _ apM (slotsFacts _ beacon sb.message.slot tq _ _ apM hs)

private def tagged (tq : TQueue) : TQueue := tq.filter fun e => e.1.isSome

private def appliedEntries (ap : List (Nat × AppliedAt P)) : TQueue :=
  ap.map fun x => (x.2.2.tag, x.2.2.deposit)

private def requestEntries {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (D : JointRunStep (P := P) cfg ccfg bls) : TQueue :=
  (stepDepositRequests D).map fun dr =>
    (some dr.index.toNat, requestPending dr D.block.2.message.slot)

private theorem stepFacts {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (D : JointRunStep (P := P) cfg ccfg bls) (tq : TQueue)
    (valid : ValidIngressStep cfg ccfg bls D)
    (aligned : pendingList D.pre = .ok (tq.map Prod.snd)) :
    ∃ tq' ap, stepLedger D tq = .ok (tq', ap) ∧
      pendingList D.post = .ok (tq'.map Prod.snd) ∧
      (tagged ((ap.map fun a => (a.2.tag, a.2.deposit)) ++ tq')).Perm
        (tagged tq ++ requestEntries D) ∧
      (∀ a ∈ ap, ∃ post, applyPendingDeposit (jointCtx ccfg bls) a.2.pre a.2.deposit = .ok post) ∧
      ∀ a ∈ ap, ∀ i, a.2.tag = some i → i ∈ tq.filterMap Prod.fst := by
  obtain ⟨tq', ap, hs, aligned', st, tqS, tqA, hi, rfl, ha, _⟩ :=
    DepositLedgerMirrors.stepMirror D tq valid aligned
  obtain ⟨hp, hc⟩ := inputFacts ccfg bls D.pre D.block tq st tqS ap hi
  refine ⟨tqS ++ tqA, ap, hs, aligned', ?_, hc, ?_⟩
  · have hf := (hp.filter fun e => e.1.isSome).append_right (requestEntries D)
    simpa only [tagged, List.filter_append, List.append_assoc, ha, requestEntries] using hf
  · intro a ha i ht
    apply List.mem_filterMap.mpr
    refine ⟨(some i, a.2.deposit), ?_, rfl⟩
    apply hp.mem_iff.mp
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨a, ha, by rw [ht]⟩

private theorem appliedAmounts (ccfg : Config) (bls : Bool)
    (ap : List (Nat × AppliedAt P))
    (calls : ∀ x ∈ ap, ∃ post,
      applyPendingDeposit (jointCtx ccfg bls) x.2.2.pre x.2.2.deposit = .ok post) :
    creditedTotal (jointCtx ccfg bls) ap + uncreditedTotal (jointCtx ccfg bls) ap =
      taggedTotal (appliedEntries ap) := by
  induction ap with
  | nil => rfl
  | cons x xs ih =>
    have tail := ih (fun a ha => calls a (List.mem_cons_of_mem x ha))
    obtain ⟨post, hp⟩ := calls x List.mem_cons_self
    obtain ⟨o, hc, _⟩ := DepositConsensusOutcomes.applyOutcome_of_success ccfg bls
      x.2.2.pre post x.2.2.deposit hp
    by_cases ht : x.2.2.tag.isSome = true
    · cases o <;>
        simp only [creditedTotal, uncreditedTotal, appliedEntries, taggedTotal,
          List.filter_cons, List.map_cons, ht, ite_true, List.foldr_cons,
          hc, ApplyOutcome.credited, List.sum_cons] at tail ⊢ <;> omega
    · simp only [creditedTotal, uncreditedTotal, appliedEntries, taggedTotal,
        List.filter_cons, List.map_cons, ht] at tail ⊢
      exact tail

private theorem principal {cfg : ChainConfig} (ccfg : Config) (bls : Bool)
    (ds : List (JointRunStep (P := P) cfg ccfg bls)) (tq tqF : TQueue)
    (ap : List (Nat × AppliedAt P))
    (moved : (tagged (appliedEntries ap ++ tqF)).Perm
      (tagged tq ++ ds.flatMap requestEntries))
    (calls : ∀ x ∈ ap, ∃ post,
      applyPendingDeposit (jointCtx ccfg bls) x.2.2.pre x.2.2.deposit = .ok post) :
    creditedTotal (jointCtx ccfg bls) ap + uncreditedTotal (jointCtx ccfg bls) ap +
      taggedTotal tqF = taggedTotal tq +
        ((ds.flatMap stepDepositRequests).map fun dr => dr.amount.toNat).sum := by
  rw [appliedAmounts ccfg bls ap calls]
  have amount := (moved.map fun e => e.2.amount.toNat).sum_eq
  have requests : ((ds.flatMap requestEntries).map fun e => e.2.amount.toNat) =
      ((ds.flatMap stepDepositRequests).map fun dr => dr.amount.toNat) := by
    simp only [List.map_flatMap, requestEntries, List.map_map, Function.comp_def, requestPending]
  simpa only [tagged, taggedTotal, List.filter_append, List.map_append, List.sum_append,
    requests] using amount

private theorem ledgerRun {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (ds : List (JointRunStep (P := P) cfg ccfg bls)) :
    ∀ (j : Nat) (cur final : JointState P) (tq : TQueue) (acc : List (Nat × AppliedAt P)),
      ds.map JointRunStep.pre ++ [final] = cur :: ds.map JointRunStep.post →
      (∀ D ∈ ds, ValidIngressStep cfg ccfg bls D) →
      pendingList cur = .ok (tq.map Prod.snd) →
      ((tagged tq ++ ds.flatMap requestEntries).map Prod.fst).Nodup →
      ∃ tqF fresh,
        runLedger j ds tq acc = .ok (tqF, acc ++ fresh) ∧
        pendingList final = .ok (tqF.map Prod.snd) ∧
        (tagged (appliedEntries fresh ++ tqF)).Perm
          (tagged tq ++ ds.flatMap requestEntries) ∧
        ((tagged (appliedEntries fresh ++ tqF)).map Prod.fst).Nodup ∧
        (∀ x ∈ fresh, j ≤ x.1 ∧ ∃ post,
          applyPendingDeposit (jointCtx ccfg bls) x.2.2.pre x.2.2.deposit = .ok post) ∧
        (∀ k D dr, ds[k]? = some D → dr ∈ stepDepositRequests D →
          ∀ x ∈ fresh, x.2.2.tag = some dr.index.toNat → j + k < x.1) ∧
        creditedTotal (jointCtx ccfg bls) fresh + uncreditedTotal (jointCtx ccfg bls) fresh +
          taggedTotal tqF = taggedTotal tq +
            ((ds.flatMap stepDepositRequests).map fun dr => dr.amount.toNat).sum := by
  induction ds with
  | nil =>
    intro j cur final tq acc linked valid aligned fresh
    simp only [List.map_nil, List.nil_append, List.cons.injEq] at linked
    rcases linked with ⟨rfl, _⟩
    refine ⟨tq, [], ?_, aligned, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [runLedger, List.append_nil]
      rfl
    · simpa only [appliedEntries, List.map_nil, List.nil_append, List.flatMap_nil,
        List.append_nil] using List.Perm.refl (tagged tq)
    · simpa only [appliedEntries, List.map_nil, List.nil_append, List.flatMap_nil,
        List.append_nil] using fresh
    · intro x hx
      cases hx
    · intro k D dr h
      cases h
    · simp only [creditedTotal, uncreditedTotal, List.filter_nil, List.foldr_nil,
        List.flatMap_nil, List.map_nil, List.sum_nil, Nat.zero_add, Nat.add_zero]
  | cons D ds ih =>
    intro j cur final tq acc linked valid aligned fresh
    simp only [List.map_cons, List.cons_append, List.cons.injEq] at linked
    rcases linked with ⟨rfl, linked⟩
    obtain ⟨tqN, apN, step, alignedN, movedN, callsN, fromN⟩ :=
      stepFacts D tq (valid D List.mem_cons_self) aligned
    have freshN : ((tagged tqN ++ ds.flatMap requestEntries).map Prod.fst).Nodup := by
      have hn := ((movedN.map Prod.fst).append_right
        ((ds.flatMap requestEntries).map Prod.fst)).nodup_iff.mpr
          (by simpa only [List.map_append, List.flatMap_cons, List.append_assoc] using fresh)
      simp only [tagged, List.filter_append, List.map_append, List.append_assoc] at hn
      simpa only [tagged, List.map_append] using hn.of_append_right
    obtain ⟨tqF, tail, run, alignedF, movedTail, _, callsTail, chronoTail, _⟩ :=
      ih (j + 1) D.post final tqN (acc ++ apN.map fun a => (j, a)) linked
        (fun E hE => valid E (List.mem_cons_of_mem D hE)) alignedN freshN
    let stamped := apN.map fun a => (j, a)
    let result := stamped ++ tail
    have moved : (tagged (appliedEntries result ++ tqF)).Perm
        (tagged tq ++ (D :: ds).flatMap requestEntries) := by
      have h1 := movedTail.append_left
        (tagged (apN.map fun a => (a.2.tag, a.2.deposit)))
      have h2 := movedN.append_right (ds.flatMap requestEntries)
      have h2' : (tagged (apN.map fun a => (a.2.tag, a.2.deposit)) ++
          (tagged tqN ++ ds.flatMap requestEntries)).Perm
          (tagged tq ++ requestEntries D ++ ds.flatMap requestEntries) := by
        simpa only [tagged, List.filter_append, List.append_assoc] using h2
      simpa only [result, stamped, tagged, appliedEntries, List.map_append,
        List.map_map, Function.comp_def, List.filter_append, List.flatMap_cons,
        List.append_assoc] using h1.trans h2'
    have calls : ∀ x ∈ result, j ≤ x.1 ∧ ∃ post,
        applyPendingDeposit (jointCtx ccfg bls) x.2.2.pre x.2.2.deposit = .ok post := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
        exact ⟨Nat.le_refl _, callsN a ha⟩
      · obtain ⟨hj, hc⟩ := callsTail x hx
        exact ⟨by omega, hc⟩
    have noFuture : ∀ a ∈ apN, ∀ dr ∈ (D :: ds).flatMap stepDepositRequests,
        a.2.tag ≠ some dr.index.toNat := by
      intro a ha dr hdr ht
      obtain ⟨e, he, htag⟩ := List.mem_filterMap.mp (fromN a ha _ ht)
      have hi : some dr.index.toNat ∈ (tagged tq).map Prod.fst := by
        exact List.mem_map.mpr ⟨e, List.mem_filter.mpr
          ⟨he, by rw [htag]; rfl⟩, htag⟩
      obtain ⟨E, hE, hdr⟩ := List.mem_flatMap.mp hdr
      have ho : some dr.index.toNat ∈ ((D :: ds).flatMap requestEntries).map Prod.fst := by
        exact List.mem_map.mpr ⟨(some dr.index.toNat,
          requestPending dr E.block.2.message.slot), List.mem_flatMap.mpr
            ⟨E, hE, List.mem_map.mpr ⟨dr, hdr, rfl⟩⟩, rfl⟩
      have disjoint := List.disjoint_of_nodup_append
        (show ((tagged tq).map Prod.fst ++
          ((D :: ds).flatMap requestEntries).map Prod.fst).Nodup from
            by simpa only [List.map_append] using fresh)
      exact List.disjoint_left.mp disjoint hi ho
    refine ⟨tqF, result, ?_, alignedF, moved, (moved.map Prod.fst).nodup_iff.mpr fresh,
      calls, ?_, principal ccfg bls (D :: ds) tq tqF result moved (fun x hx => (calls x hx).2)⟩
    · simp only [runLedger, step, ok_bind']
      simpa only [result, List.append_assoc] using run
    · intro k E dr hE hdr x hx ht
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
        exact False.elim (noFuture a ha dr
          (List.mem_flatMap.mpr ⟨E, List.mem_of_getElem? hE, hdr⟩) ht)
      · cases k with
        | zero =>
          have lower := (callsTail x hx).1
          omega
        | succ k =>
          have hc := chronoTail k E dr hE hdr x hx ht
          omega

private theorem ingressFacts {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {anchor final : JointState P} (ingress : JointRunIngress cfg ccfg bls anchor final)
    (postGenesis : ∀ D ∈ ingress.steps, D.block.2.message.slot ≠ GENESIS_SLOT) :
    (ingress.steps.map JointRunStep.pre ++ [final] =
      anchor :: ingress.steps.map JointRunStep.post) ∧
    ∀ D ∈ ingress.steps, ValidIngressStep cfg ccfg bls D := by
  cases ingress with
  | standard run =>
    refine ⟨run.steps_linked, ?_⟩
    intro D hd
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hd
    exact ⟨postGenesis D hd, .inl (run.steps_jointStep hj)⟩
  | atElectraSlot sb pg le before first bound tail =>
    constructor
    · simpa only [JointRunIngress.steps, List.map_cons, List.cons_append,
        List.cons.injEq, true_and] using tail.steps_linked
    · intro D hd
      refine ⟨postGenesis D hd, ?_⟩
      simp only [JointRunIngress.steps, List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact .inr ⟨_, _, _, _, sb, rfl, rfl, rfl, le, before, first⟩
      · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hd
        exact .inl (tail.steps_jointStep hj)

private theorem sourceTags {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (ds : List (JointRunStep (P := P) cfg ccfg bls)) (tq : TQueue) :
    (tagged tq ++ ds.flatMap requestEntries).map Prod.fst =
      (tq.filterMap Prod.fst ++ (ds.flatMap stepDepositRequests).map
        fun dr => dr.index.toNat).map some := by
  have queue : (tagged tq).map Prod.fst = (tq.filterMap Prod.fst).map some := by
    rw [List.map_filterMap_some_eq_filter_map_isSome]
    simp only [tagged, List.filter_map, Function.comp_def]
  simp only [List.map_append, queue, List.map_flatMap, requestEntries, List.map_map,
    Function.comp_def]

/-- Literal frozen Nat principal conservation for the existing occurrence ledger. -/
theorem depositConservation : Blanc.Corpus.Freeze.Deposit.D9Conservation := by
  intro P cfg ccfg anchor final ingress tq₀ postGenesis anchorLedger fresh
  obtain ⟨linked, valid⟩ := ingressFacts ingress postGenesis
  have sourceFresh : ((tagged tq₀ ++ ingress.steps.flatMap requestEntries).map Prod.fst).Nodup := by
    rw [sourceTags]
    exact List.Nodup.map (Option.some_injective Nat) fresh
  obtain ⟨tqF, ap, run, _, _, _, _, _, amount⟩ :=
    ledgerRun ingress.steps 0 anchor final tq₀ [] linked valid anchorLedger.1 sourceFresh
  exact ⟨tqF, ap, run, amount⟩

/-- Literal frozen request fate, including exact unique applied or pending indices. -/
theorem depositFate : Blanc.Corpus.Freeze.Deposit.D9Fate := by
  intro P cfg ccfg anchor final ingress tq₀ postGenesis anchorLedger fresh
  obtain ⟨linked, valid⟩ := ingressFacts ingress postGenesis
  have sourceFresh : ((tagged tq₀ ++ ingress.steps.flatMap requestEntries).map Prod.fst).Nodup := by
    rw [sourceTags]
    exact List.Nodup.map (Option.some_injective Nat) fresh
  obtain ⟨tqF, ap, run, alignedF, moved, uniqueTags, calls, chrono, _⟩ :=
    ledgerRun ingress.steps 0 anchor final tq₀ [] linked valid anchorLedger.1 sourceFresh
  refine ⟨tqF, ap, run, alignedF, ?_⟩
  intro j D k dr hD hdr
  let d := requestPending dr D.block.2.message.slot
  let all := appliedEntries ap ++ tqF
  have pairwise : all.Pairwise (fun a b =>
      a.1.isSome → b.1.isSome → a.1 ≠ b.1) := by
    change List.Pairwise (fun a b : Tag => a ≠ b)
      ((tagged all).map Prod.fst) at uniqueTags
    rw [List.pairwise_map, tagged, List.pairwise_filter] at uniqueTags
    exact uniqueTags
  have unique : ∀ {p p' : Nat} {e e' : Tag × PendingDeposit},
      all[p]? = some e → all[p']? = some e' →
      e.1 = some dr.index.toNat → e'.1 = some dr.index.toNat → p = p' := by
    intro p p' e e' he he' ht ht'
    obtain ⟨hp, rfl⟩ := List.getElem?_eq_some_iff.mp he
    obtain ⟨hp', rfl⟩ := List.getElem?_eq_some_iff.mp he'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact (List.pairwise_iff_getElem.mp pairwise p p' hp hp' hlt
        (by rw [ht]; rfl) (by rw [ht']; rfl)) (ht.trans ht'.symm)
    · exact (List.pairwise_iff_getElem.mp pairwise p' p hp' hp hgt
        (by rw [ht']; rfl) (by rw [ht]; rfl)) (ht'.trans ht.symm)
  have atApplied : ∀ {p : Nat} {x : Nat × AppliedAt P}, ap[p]? = some x →
      all[p]? = some (x.2.2.tag, x.2.2.deposit) := by
    intro p x hx
    have hp := (List.getElem?_eq_some_iff.mp hx).1
    rw [List.getElem?_append_left (by simpa only [appliedEntries, List.length_map] using hp)]
    simp only [appliedEntries, List.getElem?_map, hx, Option.map_some]
  have atPending : ∀ {p : Nat} {e : Tag × PendingDeposit}, tqF[p]? = some e →
      all[ap.length + p]? = some e := by
    intro p e he
    rw [List.getElem?_append_right (by simp only [appliedEntries, List.length_map]; omega)]
    simpa only [appliedEntries, List.length_map, Nat.add_sub_cancel_left] using he
  have present : (some dr.index.toNat, d) ∈ all := by
    have source : (some dr.index.toNat, d) ∈ tagged tq₀ ++
        ingress.steps.flatMap requestEntries := by
      exact List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨D, List.mem_of_getElem? hD, List.mem_map.mpr
          ⟨dr, List.mem_of_getElem? hdr, rfl⟩⟩)
    exact (List.mem_filter.mp (moved.mem_iff.mpr source)).1
  rcases List.mem_append.mp present with applied | pending
  · obtain ⟨⟨j', a⟩, ha, he⟩ := List.mem_map.mp applied
    have ht : a.2.tag = some dr.index.toNat := (Prod.mk.inj he).1
    have hd : a.2.deposit = d := (Prod.mk.inj he).2
    obtain ⟨apIdx, hap⟩ := List.mem_iff_getElem?.mp ha
    have later : j < j' := by
      simpa only [Nat.zero_add] using chrono j D dr hD (List.mem_of_getElem? hdr)
        (j', a) ha ht
    have hAll := atApplied hap
    refine Or.inl ⟨?_, apIdx, j', a, hap, ht, later, ?_, hd, ?_⟩
    · intro p hp
      cases he : tqF[p]? with
      | none => simp only [he, Option.map_none, reduceCtorEq] at hp
      | some e =>
        have ht' : e.1 = some dr.index.toNat := by
          simpa only [he, Option.map_some, Option.some.injEq] using hp
        have same := unique hAll (atPending he) ht ht'
        have bound := (List.getElem?_eq_some_iff.mp hap).1
        omega
    · intro apIdx' j'' a' hap' ht'
      exact unique (atApplied hap') hAll ht' ht
    · obtain ⟨post, applied⟩ := (calls (j', a) ha).2
      obtain ⟨o, outcome⟩ := DepositConsensusOutcomes.applyOutcome_of_success ccfg true
        a.2.pre post a.2.deposit applied
      refine ⟨o, post, ?_⟩
      change ApplyOutcomeSpec ccfg true a.2.pre post d o
      rw [← hd]
      exact outcome
  · obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp pending
    have hAll := atPending hp
    refine Or.inr ⟨?_, p, hp, ?_⟩
    · intro apIdx j' a hap ht
      have same := unique (atApplied hap) hAll ht rfl
      have bound := (List.getElem?_eq_some_iff.mp hap).1
      omega
    · intro p' hp'
      cases he : tqF[p']? with
      | none => simp only [he, Option.map_none, reduceCtorEq] at hp'
      | some e =>
        have ht' : e.1 = some dr.index.toNat := by
          simpa only [he, Option.map_some, Option.some.injEq] using hp'
        have same := unique (atPending he) hAll ht' rfl
        omega

end Blanc.Composition.DepositLedgerFate
