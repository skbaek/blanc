import JauneConsensus.Facts.Gloas.InvariantsWithdrawals

/-!
# Guarded pending-builder withdrawal prefixes and actual apply positions

The prefix comes from successful processWithdrawals, including its actual early/full guard.
The positional application laws split the original applyWithdrawals loop; the singleton
law retains the literal builder modification and saturating amount update. Builder sweeps
are not pending-prefix occurrences. No replay or final-correctness premise is introduced.
-/

namespace Blanc.GloasWithdrawalPrefix
open JauneConsensus JauneConsensus.Facts JauneConsensus.Facts.Gloas JauneConsensus.Facts.Gloas.Inv
variable {P : Preset}
theorem full_prefix {s t : Gloas.BeaconState P}
    (hc : (s.latest_block_hash != s.latest_execution_payload_bid.block_hash) = false)
    (h : Gloas.processWithdrawals s = .ok t) :
    ∃ ex a, Gloas.getExpectedWithdrawals s = .ok ex ∧
      Gloas.applyWithdrawals s ex.withdrawals = .ok a ∧ t.builders = a.builders ∧
      t.builder_pending_withdrawals.toArray.toList =
        s.builder_pending_withdrawals.toArray.toList.drop ex.processed_builder_withdrawals_count.toNat := by
  unfold Gloas.processWithdrawals at h
  simp only [hc, Bool.false_eq_true, ite_false] at h
  obtain ⟨ex, hex, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨a, ha, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨t2, h2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨t6, h6, h⟩ := bind_eq_ok_iff.mp h
  have q1 := applyWithdrawals_qe _ _ _ ha
  have q2 := updateNextWithdrawalIndex_bq _ _ _ h2
  have q6 := updateNextWithdrawalBuilderIndex_bq _ _ _ h6
  have q7 := updateNextWithdrawalValidatorIndex_bq _ _ _ h
  refine ⟨ex, a, hex, ha, q7.1.trans (q6.1.trans q2.1), ?_⟩
  rw [q7.2.1, q6.2.1]
  simp only [Gloas.updatePendingPartialWithdrawals, Gloas.updateBuilderPendingWithdrawals,
    Gloas.updatePayloadExpectedWithdrawals]
  rw [q2.2.1, q1.1]
  simp only [ProgressiveListS.ofArray, Array.toList_extract, List.extract_eq_take_drop,
    List.take_eq_self_iff, List.length_drop, Array.length_toList, Std.le_refl]

theorem expected_prefix {s : Gloas.BeaconState P} {ex : Gloas.ExpectedWithdrawals}
    (hex : Gloas.getExpectedWithdrawals s = .ok ex) :
    ex.processed_builder_withdrawals_count.toNat ≤ s.builder_pending_withdrawals.toArray.size ∧
    ∀ k, k < ex.processed_builder_withdrawals_count.toNat → ∃ e w,
      s.builder_pending_withdrawals.toArray[k]? = some e ∧
      ex.withdrawals.toList[k]? = some w ∧ w.address = e.fee_recipient ∧ w.amount = e.amount ∧
      Gloas.convertBuilderIndexToValidatorIndex e.builder_index = .ok w.validator_index := by
  obtain ⟨bw, pw, sw, vw, p2, p3, p4, i1, i2, i3, i4, n2, n3, n4, hbw, -, -, -, hws⟩ :=
    getExpectedWithdrawals_parts hex
  obtain ⟨hn, hp⟩ := getBuilderWithdrawals_provenance hbw
  have bound : bw.size ≤ s.builder_pending_withdrawals.toArray.size := by
    by_contra h
    obtain ⟨e, he, -⟩ := hp s.builder_pending_withdrawals.toArray.size (by omega)
    have := (Array.getElem?_eq_some_iff.mp he).1
    omega
  refine ⟨by omega, ?_⟩
  intro k hk
  have hk' : k < bw.size := by omega
  obtain ⟨e, he, ha, hm, hi⟩ := hp k hk'
  refine ⟨e, bw[k], he, ?_, ha, hm, hi⟩
  rw [hws]
  simp only [List.append_assoc]
  rw [List.getElem?_append_left (by simpa only [Array.length_toList] using hk')]
  simp only [Array.length_toList, hk', getElem?_pos, Array.getElem_toList]

/-- The actual guarded pending-prefix/read/apply seam; no input trace is assumed. -/
def PrefixSpec (s t : Gloas.BeaconState P) (ws : Array Withdrawal) (d : Nat) : Prop :=
  d ≤ s.builder_pending_withdrawals.toArray.size ∧
  t.builder_pending_withdrawals.toArray.toList = s.builder_pending_withdrawals.toArray.toList.drop d ∧
  (((s.latest_block_hash != s.latest_execution_payload_bid.block_hash) = true ∧
      t = s ∧ ws = #[] ∧ d = 0) ∨
    ((s.latest_block_hash != s.latest_execution_payload_bid.block_hash) = false ∧
      ∃ ex a, Gloas.getExpectedWithdrawals s = .ok ex ∧ ws = ex.withdrawals ∧
        d = ex.processed_builder_withdrawals_count.toNat ∧
        Gloas.applyWithdrawals s ws = .ok a ∧ t.builders = a.builders)) ∧
  ∀ k, k < d → ∃ e w, s.builder_pending_withdrawals.toArray[k]? = some e ∧
    ws.toList[k]? = some w ∧ w.address = e.fee_recipient ∧ w.amount = e.amount ∧
    Gloas.convertBuilderIndexToValidatorIndex e.builder_index = .ok w.validator_index

theorem processWithdrawals_prefix {s t : Gloas.BeaconState P}
    (h : Gloas.processWithdrawals s = .ok t) :
    ∃ ws d, PrefixSpec s t ws d := by
  unfold PrefixSpec
  cases hc : (s.latest_block_hash != s.latest_execution_payload_bid.block_hash) with
  | false =>
    obtain ⟨ex, a, he, ha, hb, hq⟩ := full_prefix hc h
    obtain ⟨bound, hp⟩ := expected_prefix he
    exact ⟨ex.withdrawals, ex.processed_builder_withdrawals_count.toNat, bound, hq,
      Or.inr ⟨rfl, ex, a, he, rfl, rfl, ha, hb⟩, hp⟩
  | true =>
    have ht : s = t := by simpa only [Gloas.processWithdrawals, hc, ite_true, pure, Except.pure, Except.ok.injEq] using h
    subst t
    refine ⟨#[], 0, Nat.zero_le _, by simp only [List.drop_zero], Or.inl ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
    intro k hk
    omega
private theorem forIn_singletons {α β ε : Type} (body : α → β → Except ε (ForInStep β))
    (hy : ∀ x a r, body x a = .ok r → ∃ b, r = .yield b)
    (xs : List α) (s : β) :
    forIn xs s body = xs.foldlM (fun a x => forIn [x] a body) s := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.forIn_cons, List.forIn_nil, List.foldlM_cons]
    cases he : body x s with
    | error e => rfl
    | ok r =>
      obtain ⟨b, rfl⟩ := hy x s r he
      simpa only [List.forIn_cons, List.forIn_nil, bind, Except.bind, pure, Except.pure] using ih b
theorem applyWithdrawals_fold (s : Gloas.BeaconState P) (ws : Array Withdrawal) :
    Gloas.applyWithdrawals s ws =
      ws.toList.foldlM (fun a w => Gloas.applyWithdrawals a #[w]) s := by
  unfold Gloas.applyWithdrawals
  simp only [← Array.forIn_toList, bind_pure]
  apply forIn_singletons
  intro w a r hr
  split at hr
  · obtain ⟨bi, hbi, hr⟩ := bind_eq_ok_iff.mp hr
    obtain ⟨bs, hbs, hr⟩ := bind_eq_ok_iff.mp hr
    simp only [pure, Except.pure, Except.ok.injEq] at hr
    exact ⟨_, hr.symm⟩
  · obtain ⟨b, hb, hr⟩ := bind_eq_ok_iff.mp hr
    simp only [pure, Except.pure, Except.ok.injEq] at hr
    exact ⟨_, hr.symm⟩

theorem applyWithdrawals_append (s : Gloas.BeaconState P) (xs ys : Array Withdrawal) :
    Gloas.applyWithdrawals s (xs ++ ys) =
      (Gloas.applyWithdrawals s xs >>= fun a => Gloas.applyWithdrawals a ys) := by
  rw [applyWithdrawals_fold s (xs ++ ys), Array.toList_append, List.foldlM_append,
    ← applyWithdrawals_fold s xs]
  congr 1
  funext a
  exact (applyWithdrawals_fold a ys).symm

theorem applyWithdrawals_at {s t : Gloas.BeaconState P} {ws : Array Withdrawal}
    (h : Gloas.applyWithdrawals s ws = .ok t) (k : Nat) (hk : k < ws.size) :
    ∃ a b w, ws[k]? = some w ∧
      Gloas.applyWithdrawals s (ws.toList.take k).toArray = .ok a ∧
      Gloas.applyWithdrawals a #[w] = .ok b ∧
      Gloas.applyWithdrawals b (ws.toList.drop (k + 1)).toArray = .ok t := by
  have hs : ws = (ws.toList.take k).toArray ++ #[ws[k]] ++ (ws.toList.drop (k + 1)).toArray := by
    apply Array.toList_inj.mp
    simp only [Array.toList_append]
    have hh := List.take_append_drop k ws.toList
    rw [List.drop_eq_getElem_cons (by simpa only [Array.length_toList] using hk)] at hh
    simpa only [List.append_assoc, List.singleton_append, Array.getElem_toList] using hh.symm
  rw [hs, applyWithdrawals_append, applyWithdrawals_append] at h
  obtain ⟨b, hab, ht⟩ := bind_eq_ok_iff.mp h
  obtain ⟨a, ha, hb⟩ := bind_eq_ok_iff.mp hab
  exact ⟨a, b, ws[k], Array.getElem?_eq_getElem hk, ha, hb, ht⟩

theorem applyWithdrawals_pending_singleton {a b : Gloas.BeaconState P}
    {e : Gloas.BuilderPendingWithdrawal} {w : Withdrawal}
    (h : Gloas.applyWithdrawals a #[w] = .ok b)
    (hm : w.amount = e.amount)
    (hr : Gloas.convertBuilderIndexToValidatorIndex e.builder_index = .ok w.validator_index)
    (range : e.builder_index.toNat < 2 ^ 40) :
    Gloas.isBuilderIndex w.validator_index = true ∧
      Gloas.convertValidatorIndexToBuilderIndex w.validator_index = .ok e.builder_index ∧
      ∃ bs, a.builders.modify e.builder_index.toNat
          (fun x => do pure {x with balance := ← Gloas.saturatingSubGwei x.balance e.amount})
          "apply_withdrawals" = .ok bs ∧ b = {a with builders := bs} := by
  have hib := isBuilderIndex_of_routes hr
  have hc := convertValidatorIndexToBuilderIndex_of_routes hr range
  refine ⟨hib, hc, ?_⟩
  unfold Gloas.applyWithdrawals at h
  simp only [← Array.forIn_toList, List.forIn_cons, List.forIn_nil,
    hib, ite_true, hc, hm, bind_assoc, pure_bind, bind_pure] at h
  change (do
    let bs ← a.builders.modify e.builder_index.toNat
      (fun x => do pure {x with balance := ← Gloas.saturatingSubGwei x.balance e.amount})
      "apply_withdrawals"
    pure {a with builders := bs}) = .ok b at h
  obtain ⟨bs, hbs, hb⟩ := bind_eq_ok_iff.mp h
  exact ⟨bs, hbs, (Except.ok.inj hb).symm⟩
end Blanc.GloasWithdrawalPrefix
