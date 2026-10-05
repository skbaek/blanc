import Blanc.Lift.Weth9.CommittedHistory

/-!
# WETH9 side of the Uniswap V2 composition: a holder's balance does not shrink

The exhibit pair (USDC/WETH9) observes its WETH9 balance through `balanceOf` and lowers it only
through its own `transfer`s.  This module states, over WETH9's own model and its committed history,
why no other actor can lower the pair's WETH9 balance:

* `Ledger.step_holder` / `Ledger.run_holder` (model): for a holder `p` whose allowances are all zero,
  every call keeps them zero, and `p`'s balance falls by at most the amounts `p` itself transfers
  away (`holderOut`), provided the calls `p` makes are `transfer`s or deposits (`HolderCalls`, the
  pair-side input) and the booked total plus the ether deposited stays a word (`l.total + inflowSum`).
* `weth9_history_holder_noShrink` (history): the same over the settlement-committed WETH9 writer
  invocations of a configured history (`weth9_history_committed`), read back at the storage words of
  the checkpoint and the future state.  The pair-side input is the named hypothesis `HolderCalls`
  over the committed invocations; the wrap budget is the WETH9 ether at the checkpoint plus the ether
  the committed deposits bring in.

The Pair-side half (that the pair's balance is at least `reserve1` after each committed Pair state
change) needs the Pair's history replay and is not stated here.
-/

namespace Blanc.Composition.UniswapV2PairWeth9

open Jaune Blanc Blanc.Lift Blanc.Lift.Weth9 Blanc.ExecutionTrace

/-- The message sender of a model call. -/
def callCaller : Call → Adr
  | .deposit who _ => who
  | .withdraw who _ => who
  | .transfer who _ _ => who
  | .transferFrom who _ _ _ => who
  | .approve who _ _ => who

/-- A call made by `p` is a `transfer` or a deposit (the payable fallback). -/
def HolderCall (p : Adr) (c : Call) : Prop :=
  callCaller c = p → (∃ dst w, c = .transfer p dst w) ∨ ∃ v, c = .deposit p v

/-- Every call of the list made by `p` is a `transfer` or a deposit. -/
def HolderCalls (p : Adr) (cs : List Call) : Prop := ∀ c ∈ cs, HolderCall p c

/-- The amount `p` sends away by one of its own `transfer`s (zero for every other call). -/
def holderDebit (p : Adr) : Call → Nat
  | .transfer who dst w => if who = p ∧ dst ≠ p then w.toNat else 0
  | _ => 0

/-- The total `p` sends away by its own `transfer`s. -/
def holderOut (p : Adr) (cs : List Call) : Nat := (cs.map (holderDebit p)).sum

/-- The ether the deposits of a call list bring in. -/
def inflowSum (cs : List Call) : Nat := (cs.map Call.inflow).sum

/-- Every allowance granted by `p` is zero. -/
def AllowZero (p : Adr) (l : Ledger) : Prop := ∀ g, l.allow p g = 0

section Model

theorem bal_add_bal_le_total (l : Ledger) {a b : Adr} (h : a ≠ b) :
    (l.bal a).toNat + (l.bal b).toNat ≤ l.total :=
  add_le_sum_of_ne l.bal h

theorem bal_le_total (l : Ledger) (a : Adr) : (l.bal a).toNat ≤ l.total := le_sum

theorem xfer_allow (l : Ledger) (src dst : Adr) (wad : B256) : (l.xfer src dst wad).allow = l.allow :=
  rfl

theorem setBal_apply_self (l : Ledger) (a : Adr) (w : B256) : (l.setBal a w).bal a = w := by
  simp only [Ledger.setBal_bal, Function.update_self]

theorem setBal_apply_ne (l : Ledger) {a b : Adr} (h : b ≠ a) (w : B256) :
    (l.setBal a w).bal b = l.bal b := by
  simp only [Ledger.setBal_bal, Function.update_of_ne h]

/-- A balance move lowers `p`'s balance by at most what `p` itself sends to another holder, when the
booked total fits a word. -/
theorem xfer_holder (l : Ledger) (p src dst : Adr) {wad : B256} (hle : wad ≤ l.bal src)
    (fit : l.total < 2 ^ 256) :
    (l.bal p).toNat ≤ ((l.xfer src dst wad).bal p).toNat +
      (if src = p ∧ dst ≠ p then wad.toNat else 0) := by
  have hsub : (l.bal src - wad).toNat = (l.bal src).toNat - wad.toNat :=
    B256.toNat_sub_eq_of_le _ _ hle
  have hwle : wad.toNat ≤ (l.bal src).toNat := B256.toNat_le_toNat hle
  unfold Ledger.xfer
  by_cases hs : src = p
  · subst hs
    by_cases hd : dst = src
    · subst hd
      have hnof : B256.Nof (l.bal dst - wad) wad := by
        unfold B256.Nof
        rw [hsub]
        have := B256.toNat_lt (l.bal dst)
        omega
      simp only [setBal_apply_self, ne_eq, not_true_eq_false, and_false, ↓reduceIte, Nat.add_zero]
      rw [B256.toNat_add_eq_of_nof _ _ hnof, hsub]
      omega
    · simp only [setBal_apply_ne _ (Ne.symm hd), setBal_apply_self, ne_eq, hd, not_false_eq_true,
        and_self, ↓reduceIte]
      rw [hsub]
      omega
  · have hif : (if src = p ∧ dst ≠ p then wad.toNat else 0) = 0 := by
      simp only [hs, false_and, ↓reduceIte]
    rw [hif, Nat.add_zero]
    by_cases hd : dst = p
    · subst hd
      have hnof : B256.Nof (l.bal dst) wad := by
        unfold B256.Nof
        have := bal_add_bal_le_total l hs
        omega
      simp only [setBal_apply_self, setBal_apply_ne _ (Ne.symm hs)]
      rw [B256.toNat_add_eq_of_nof _ _ hnof]
      omega
    · simp only [setBal_apply_ne _ (Ne.symm hd), setBal_apply_ne _ (Ne.symm hs), Nat.le_refl]

theorem setAllow_allowZero {l : Ledger} {p o q : Adr} {w : B256} (hz : AllowZero p l)
    (h : o = p → w = 0) : AllowZero p (l.setAllow o q w) := by
  intro g
  unfold Ledger.setAllow
  by_cases ho : p = o
  · subst ho
    simp only [Function.update_self]
    by_cases hg : g = q
    · subst hg
      simp only [Function.update_self]
      exact h rfl
    · simp only [Function.update_of_ne hg]
      exact hz g
  · simp only [Function.update_of_ne ho]
    exact hz g

theorem zero_sub_of_le_zero {wad : B256} (h : wad ≤ 0) : (0 : B256) - wad = 0 := by
  apply B256.toNat_inj
  rw [B256.toNat_sub_eq_of_le _ _ h, B256.toNat_zero, Nat.zero_sub]

/-- `transfer` (a self-sourced `transferFrom`) keeps the allowances and lowers `p`'s balance by at most
`p`'s own debit. -/
theorem transfer_holder {l l' : Ledger} {p who dst : Adr} {wad : B256}
    (h : l.transferFrom who who dst wad = some l') (fit : l.total < 2 ^ 256) :
    l'.allow = l.allow ∧
      (l.bal p).toNat ≤ (l'.bal p).toNat + holderDebit p (.transfer who dst wad) := by
  unfold Ledger.transferFrom at h
  by_cases hlt : l.bal who < wad
  · simp only [hlt, ↓reduceIte, reduceCtorEq] at h
  · simp only [hlt, ↓reduceIte, ne_eq, not_true_eq_false, false_and, Option.some.injEq] at h
    subst h
    exact ⟨rfl, xfer_holder l p who dst (B256.not_lt.mp hlt) fit⟩

/-- A `transferFrom` called by someone other than `p` keeps `p`'s allowances zero and does not lower
`p`'s balance. -/
theorem transferFrom_holder {l l' : Ledger} {p who src dst : Adr} {wad : B256}
    (hz : AllowZero p l) (hwho : who ≠ p)
    (h : l.transferFrom who src dst wad = some l') (fit : l.total < 2 ^ 256) :
    AllowZero p l' ∧ (l.bal p).toNat ≤ (l'.bal p).toNat := by
  unfold Ledger.transferFrom at h
  by_cases hlt : l.bal src < wad
  · simp only [hlt, ↓reduceIte, reduceCtorEq] at h
  · have hle : wad ≤ l.bal src := B256.not_lt.mp hlt
    simp only [hlt, ↓reduceIte] at h
    by_cases hc : src ≠ who ∧ l.allow src who ≠ maxAllowance
    · simp only [hc, ne_eq, not_false_eq_true, and_self, ↓reduceIte] at h
      by_cases hlt2 : l.allow src who < wad
      · simp only [hlt2, ↓reduceIte, reduceCtorEq] at h
      · simp only [hlt2, ↓reduceIte, Option.some.injEq] at h
        subst h
        have hfit : (l.setAllow src who (l.allow src who - wad)).total < 2 ^ 256 := fit
        have hmove := xfer_holder (l.setAllow src who (l.allow src who - wad)) p src dst
          (wad := wad) hle hfit
        by_cases hs : src = p
        · subst hs
          have hzero : l.allow src who = 0 := hz who
          have hw0 : wad ≤ 0 := by
            rw [← hzero]
            exact B256.not_lt.mp hlt2
          have hwn : wad.toNat = 0 := by
            have := B256.toNat_le_toNat hw0
            rw [B256.toNat_zero] at this
            omega
          refine ⟨?_, ?_⟩
          · rw [AllowZero, xfer_allow]
            exact setAllow_allowZero hz (fun _ => by rw [hzero]; exact zero_sub_of_le_zero hw0)
          · have hb : (l.setAllow src who (l.allow src who - wad)).bal src = l.bal src := rfl
            rw [hb] at hmove
            by_cases hd : dst ≠ src
            · simp only [ne_eq, hd, not_false_eq_true, and_self, ↓reduceIte, hwn,
                Nat.add_zero] at hmove
              exact hmove
            · simp only [hd, and_false, ↓reduceIte, Nat.add_zero] at hmove
              exact hmove
        · refine ⟨?_, ?_⟩
          · rw [AllowZero, xfer_allow]
            exact setAllow_allowZero hz (fun h' => absurd h' hs)
          · have hb : (l.setAllow src who (l.allow src who - wad)).bal p = l.bal p := rfl
            simp only [hs, false_and, ↓reduceIte, Nat.add_zero, hb] at hmove
            exact hmove
    · simp only [hc, ↓reduceIte, Option.some.injEq] at h
      subst h
      have hmove := xfer_holder l p src dst hle fit
      refine ⟨fun g => by rw [xfer_allow]; exact hz g, ?_⟩
      by_cases hs : src = p
      · subst hs
        have hsw : src ≠ who := fun h' => hwho h'.symm
        have hmax : l.allow src who ≠ maxAllowance := by
          rw [hz who]
          decide
        exact absurd ⟨hsw, hmax⟩ hc
      · simp only [hs, false_and, ↓reduceIte, Nat.add_zero] at hmove
        exact hmove

/-- **One call keeps `p`'s allowances zero and lowers `p`'s balance by at most `p`'s own transfer.**
The call is any WETH9 writer call that is a `transfer` or a deposit when `p` makes it; the booked
total plus the ether the call deposits fits a word. -/
theorem Ledger.step_holder {l l' : Ledger} {p : Adr} {c : Call} (hz : AllowZero p l)
    (hc : HolderCall p c) (fit : l.total + c.inflow < 2 ^ 256) (h : l.step c = some l') :
    AllowZero p l' ∧ (l.bal p).toNat ≤ (l'.bal p).toNat + holderDebit p c := by
  have fit0 : l.total < 2 ^ 256 := by omega
  cases c with
  | deposit who v =>
    rw [Ledger.step_deposit, Option.some.injEq] at h
    subst h
    refine ⟨hz, ?_⟩
    simp only [holderDebit, Nat.add_zero]
    by_cases hw : p = who
    · subst hw
      have hnof : B256.Nof (l.bal p) v := by
        unfold B256.Nof
        have := bal_le_total l p
        simp only [Call.inflow] at fit
        omega
      rw [setBal_apply_self, B256.toNat_add_eq_of_nof _ _ hnof]
      omega
    · rw [setBal_apply_ne _ hw]
  | withdraw who w =>
    have hwho : who ≠ p := by
      intro hw
      rcases hc hw with ⟨_, _, he⟩ | ⟨_, he⟩ <;> cases he
    rw [Ledger.step_withdraw] at h
    by_cases hlt : l.bal who < w
    · simp only [hlt, ↓reduceIte, reduceCtorEq] at h
    · simp only [hlt, ↓reduceIte, Option.some.injEq] at h
      subst h
      refine ⟨hz, ?_⟩
      simp only [holderDebit, Nat.add_zero]
      rw [setBal_apply_ne _ (Ne.symm hwho)]
  | transfer who dst w =>
    rw [Ledger.step_transfer] at h
    obtain ⟨hallow, hbal⟩ := transfer_holder (p := p) h fit0
    exact ⟨fun g => by rw [hallow]; exact hz g, hbal⟩
  | transferFrom who src dst w =>
    have hwho : who ≠ p := by
      intro hw
      rcases hc hw with ⟨_, _, he⟩ | ⟨_, he⟩ <;> cases he
    rw [Ledger.step_transferFrom] at h
    obtain ⟨hz', hbal⟩ := transferFrom_holder hz hwho h fit0
    exact ⟨hz', by simp only [holderDebit, Nat.add_zero]; exact hbal⟩
  | approve who g w =>
    have hwho : who ≠ p := by
      intro hw
      rcases hc hw with ⟨_, _, he⟩ | ⟨_, he⟩ <;> cases he
    rw [Ledger.step_approve, Option.some.injEq] at h
    subst h
    refine ⟨setAllow_allowZero hz (fun h' => absurd h' hwho), ?_⟩
    simp only [holderDebit, Nat.add_zero, Ledger.setAllow_bal, Nat.le_refl]

/-- **A run keeps `p`'s allowances zero and lowers `p`'s balance by at most `p`'s own transfers.** -/
theorem Ledger.run_holder {p : Adr} {cs : List Call} :
    ∀ {l l' : Ledger}, AllowZero p l → HolderCalls p cs →
      l.total + inflowSum cs < 2 ^ 256 → l.run cs = some l' →
      AllowZero p l' ∧ (l.bal p).toNat ≤ (l'.bal p).toNat + holderOut p cs := by
  induction cs with
  | nil =>
    intro l l' hz _ _ h
    rw [Ledger.run_nil, Option.some.injEq] at h
    subst h
    exact ⟨hz, by simp only [holderOut, List.map_nil, List.sum_nil, Nat.add_zero, Nat.le_refl]⟩
  | cons c cs ih =>
    intro l l' hz hcs fit h
    rw [Ledger.run_cons] at h
    cases hs : l.step c with
    | none => rw [hs] at h; cases h
    | some m =>
      rw [hs, Option.bind_some] at h
      have hsum : inflowSum (c :: cs) = c.inflow + inflowSum cs := by
        simp only [inflowSum, List.map_cons, List.sum_cons]
      have hout : holderOut p (c :: cs) = holderDebit p c + holderOut p cs := by
        simp only [holderOut, List.map_cons, List.sum_cons]
      rw [hsum] at fit
      obtain ⟨hzm, hm⟩ := Ledger.step_holder hz (hcs c List.mem_cons_self) (by omega) hs
      have htot : m.total ≤ l.total + c.inflow := Ledger.step_total_le hs
      obtain ⟨hz', h'⟩ := ih hzm (fun c' hc' => hcs c' (List.mem_cons_of_mem c hc')) (by omega) h
      rw [hout]
      exact ⟨hz', by omega⟩

end Model

/-! ## The history reading -/

theorem ledger_allowZero {K : Key → Prop} {s : Stor} {p : Adr}
    (h : ∀ g, K (.allow p g) → s.get (allowSlot p g) = 0) : AllowZero p (ledger K s) := by
  intro g
  by_cases hk : K (.allow p g)
  · exact (trackedAllow_self hk).trans (h g hk)
  · exact trackedAllow_of_not hk

/-- **No actor but the holder lowers its WETH9 balance, over WETH9's committed history.**  In a
configured history from a checkpoint with the footprint `K₀` (the WETH9 code installed, keys fresh, as
in `weth9_history_committed`), let `p` be a holder whose balance row is tracked and whose tracked
allowances are zero at the checkpoint.  If every committed WETH9 writer invocation that `p` makes is a
`transfer` or a deposit (`pairCalls`, the pair-side input) and the WETH9 ether at the checkpoint plus
the ether the committed deposits bring in fits a word (`budget`), then at the future state `p`'s
allowances are still zero and its balance word is at least the checkpoint's minus exactly what `p`'s
own committed `transfer`s sent to other holders. -/
theorem weth9_history_holder_noShrink {ca p : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : Key → Prop}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode ca).toList = weth9Sem.image)
    (sumNof : SumNof checkpoint.state.bal)
    (initial : FootInv K₀ (checkpoint.state.getStor ca) (checkpoint.state.bal ca))
    (fresh : KeysFresh K₀ (historyTouchedKeys ca trace))
    (holderTracked : K₀ (.bal p))
    (allowZero : ∀ g, K₀ (.allow p g) → (checkpoint.state.getStor ca).get (allowSlot p g) = 0)
    (pairCalls : HolderCalls p (replayCalls (committedInvocations ca trace)))
    (budget : (checkpoint.state.bal ca).toNat +
      inflowSum (replayCalls (committedInvocations ca trace)) < 2 ^ 256) :
    ((checkpoint.state.getStor ca).get (balSlot p)).toNat ≤
        ((future.state.getStor ca).get (balSlot p)).toNat +
          holderOut p (replayCalls (committedInvocations ca trace)) ∧
      ∀ g, historyKeyUniverse ca trace K₀ (.allow p g) →
        (future.state.getStor ca).get (allowSlot p g) = 0 := by
  obtain ⟨-, -, -, hrun, -⟩ := weth9_history_committed trace installed sumNof initial fresh
  have hfit : (ledger K₀ (checkpoint.state.getStor ca)).total +
      inflowSum (replayCalls (committedInvocations ca trace)) < 2 ^ 256 := by
    have hb : (ledger K₀ (checkpoint.state.getStor ca)).total ≤ (checkpoint.state.bal ca).toNat :=
      initial.backed
    omega
  obtain ⟨hz, hbal⟩ := Ledger.run_holder (ledger_allowZero allowZero) pairCalls hfit hrun
  have hU : historyKeyUniverse ca trace K₀ (.bal p) := Or.inl holderTracked
  have h0 : (ledger K₀ (checkpoint.state.getStor ca)).bal p =
      (checkpoint.state.getStor ca).get (balSlot p) := tracked_self holderTracked
  have h1 : (ledger (historyKeyUniverse ca trace K₀) (future.state.getStor ca)).bal p =
      (future.state.getStor ca).get (balSlot p) := tracked_self hU
  rw [h0, h1] at hbal
  refine ⟨hbal, fun g hg => ?_⟩
  have := hz g
  rw [show (ledger (historyKeyUniverse ca trace K₀) (future.state.getStor ca)).allow p g =
    (future.state.getStor ca).get (allowSlot p g) from trackedAllow_self hg] at this
  exact this

/-! ## Statement controls (WETH9 model; kernel-checked counterexamples to each dropped premise) -/

/-- The ledger in which every balance and every allowance is one. -/
def controlLedger : Ledger := ⟨fun _ => 1, fun _ _ => 1⟩

/-- **Control: the zero-allowance premise is needed.**  With a nonzero allowance granted by `p`, a
`transferFrom` by someone else lowers `p`'s balance although `p` makes no call. -/
theorem control_allowZero_needed :
    ∃ l', controlLedger.step (.transferFrom 1 0 1 1) = some l' ∧ HolderCall 0 (.transferFrom 1 0 1 1) ∧
      holderDebit 0 (.transferFrom 1 0 1 1) = 0 ∧ (l'.bal 0).toNat < (controlLedger.bal 0).toNat := by
  refine ⟨_, rfl, fun h => absurd h (by decide), rfl, ?_⟩
  decide

/-- The ledger in which every balance is one and every allowance is zero. -/
def controlLedgerZero : Ledger := ⟨fun _ => 1, fun _ _ => 0⟩

/-- **Control: the pair-side call shape is needed.**  With every allowance zero, a `withdraw` by `p`
itself (a call `HolderCall` excludes) lowers `p`'s balance with no `transfer` debit to account for it. -/
theorem control_holderCall_needed :
    ∃ l', controlLedgerZero.step (.withdraw 0 1) = some l' ∧ AllowZero 0 controlLedgerZero ∧
      holderDebit 0 (.withdraw 0 1) = 0 ∧ (l'.bal 0).toNat < (controlLedgerZero.bal 0).toNat := by
  refine ⟨_, rfl, fun _ => rfl, rfl, ?_⟩
  decide

end Blanc.Composition.UniswapV2PairWeth9
