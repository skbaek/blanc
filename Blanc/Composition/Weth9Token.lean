import Blanc.Lift.Token.Holder
import Blanc.Lift.Weth9.CommittedHistory
import Blanc.Lift.Weth9.LiveWriters
import Blanc.BalanceAlgebra

/-!
# WETH9 as the first instance of the token core (C2, composition stratum)

The WETH9 book reads the existing pure model (`Weth9.Ledger`, `Ledger.step`) through the dispatcher's
own decoder (`decodeCall`), as natural numbers; a ledger is good while its total fits a word.
`Weth9Hist` is exactly the trace-local premise set of `weth9_history_committed`.

The C2 control: a mutated model whose `transferFrom` skips the allowance check violates the core's
holder law (`control_mutant_not_laws`).
-/

namespace Blanc.Composition.Weth9Token

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Weth9 Blanc.Lift.Token

/-- What a WETH9 entry frame asks, read through the dispatcher's own decoder. -/
def weth9Op (e : Sevm) : Op :=
  if ¬ shortCall e ∧ Sevm.selector e = 0x70a08231 then .balanceOf (Sevm.dataWord e 4).toAdr
  else match decodeCall e with
    | some (.deposit _ v) => if v = 0 then .credit else .other
    | some (.transfer _ dst wad) => .transfer dst wad.toNat
    | some (.transferFrom _ src dst wad) => .transferFrom src dst wad.toNat
    | some (.approve _ guy wad) => .approve guy wad.toNat
    | _ => .other

/-- The WETH9 book: the existing pure model, read as natural numbers; a ledger is good while its
total stays a word (what the history's ETH backing gives at every position). -/
def weth9Book : Book where
  Ledger := Weth9.Ledger
  step l e := match decodeCall e with
    | none => some l
    | some c => l.step c
  op := weth9Op
  bal l a := (l.bal a).toNat
  allow l o p := (l.allow o p).toNat
  Good l := l.total < 2 ^ 256

/-- The WETH9 trace-local premises: exactly those of `weth9_history_committed`. -/
def Weth9Hist (ca : Adr) (K₀ : Key → Prop) {cfg : ChainConfig} {checkpoint future : BlockChain}
    (tr : ConfiguredHistoryTrace cfg checkpoint future) : Prop :=
  some (checkpoint.state.getCode ca).toList = weth9Sem.image ∧ SumNof checkpoint.state.bal ∧
    FootInv K₀ (checkpoint.state.getStor ca) (checkpoint.state.bal ca) ∧
    KeysFresh K₀ (historyTouchedKeys ca tr)


/-! ## The book laws -/

/-- The message sender of a model call. -/
def callWho : Call → Adr
  | .deposit who _ => who
  | .withdraw who _ => who
  | .transfer who _ _ => who
  | .transferFrom who _ _ _ => who
  | .approve who _ _ => who

/-- The decoded call's sender is the frame's caller. -/
theorem callWho_decodeCall {e : Sevm} {c : Call} (h : decodeCall e = some c) :
    callWho c = e.caller := by
  unfold decodeCall at h
  split_ifs at h <;> cases h <;> rfl

theorem bal_add_bal_le_total (l : Weth9.Ledger) {a b : Adr} (h : a ≠ b) :
    (l.bal a).toNat + (l.bal b).toNat ≤ l.total :=
  add_le_sum_of_ne l.bal h

theorem setBal_apply_self (l : Weth9.Ledger) (a : Adr) (w : B256) : (l.setBal a w).bal a = w := by
  simp only [Ledger.setBal_bal, Function.update_self]

theorem setBal_apply_ne (l : Weth9.Ledger) {a b : Adr} (h : b ≠ a) (w : B256) :
    (l.setBal a w).bal b = l.bal b := by
  simp only [Ledger.setBal_bal, Function.update_of_ne h]

theorem setAllow_apply (l : Weth9.Ledger) (o p h g : Adr) (w : B256) :
    (l.setAllow o p w).allow h g = if h = o ∧ g = p then w else l.allow h g := by
  unfold Ledger.setAllow
  by_cases ho : h = o
  · subst ho
    by_cases hg : g = p
    · subst hg
      simp only [Function.update_self, and_self, ↓reduceIte]
    · simp only [Function.update_self, Function.update_of_ne hg, hg, and_false, ↓reduceIte]
  · simp only [Function.update_of_ne ho, ho, false_and, ↓reduceIte]

/-- A balance move lowers `p`'s balance by at most what `p` itself sends to another holder, when the
booked total fits a word. -/
theorem xfer_holder (l : Weth9.Ledger) (p src dst : Adr) {wad : B256} (hle : wad ≤ l.bal src)
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

/-- A move to someone else debits the source exactly. -/
theorem xfer_src (l : Weth9.Ledger) {src dst : Adr} {wad : B256} (hle : wad ≤ l.bal src)
    (hd : dst ≠ src) : ((l.xfer src dst wad).bal src).toNat + wad.toNat = (l.bal src).toNat := by
  unfold Ledger.xfer
  simp only [setBal_apply_ne _ (Ne.symm hd), setBal_apply_self]
  rw [B256.toNat_sub_eq_of_le _ _ hle]
  have := B256.toNat_le_toNat hle
  omega

/-- The shapes of a successful `transferFrom`: a plain move, or a move after an allowance debit
(only when the source is not the caller and the allowance is not maximal, and covers the amount). -/
theorem transferFrom_cases {l l' : Weth9.Ledger} {who src dst : Adr} {wad : B256}
    (h : l.transferFrom who src dst wad = some l') :
    wad ≤ l.bal src ∧
      ((l' = l.xfer src dst wad ∧ (src = who ∨ l.allow src who = maxAllowance)) ∨
        (src ≠ who ∧ wad ≤ l.allow src who ∧
          l' = (l.setAllow src who (l.allow src who - wad)).xfer src dst wad)) := by
  unfold Ledger.transferFrom at h
  by_cases hlt : l.bal src < wad
  · simp only [hlt, ↓reduceIte, reduceCtorEq] at h
  · simp only [hlt, ↓reduceIte] at h
    refine ⟨B256.not_lt.mp hlt, ?_⟩
    by_cases hc : src ≠ who ∧ l.allow src who ≠ maxAllowance
    · simp only [hc, ne_eq, not_false_eq_true, and_self, ↓reduceIte] at h
      by_cases hlt2 : l.allow src who < wad
      · simp only [hlt2, ↓reduceIte, reduceCtorEq] at h
      · simp only [hlt2, ↓reduceIte, Option.some.injEq] at h
        exact Or.inr ⟨hc.1, B256.not_lt.mp hlt2, h.symm⟩
    · simp only [hc, ↓reduceIte, Option.some.injEq] at h
      refine Or.inl ⟨h.symm, ?_⟩
      by_cases hs : src = who
      · exact Or.inl hs
      · exact Or.inr (Classical.byContradiction fun hm => hc ⟨hs, hm⟩)

theorem toNat_pos_of_lt {x y : B256} (h : x.toNat < y.toNat) : 0 < y.toNat := by omega

/-- **Holder law of the model.** -/
theorem step_holder_only {l l' : Weth9.Ledger} {c : Call} {h : Adr} (fit : l.total < 2 ^ 256)
    (hs : l.step c = some l') (lower : (l'.bal h).toNat < (l.bal h).toNat) :
    callWho c = h ∨ 0 < (l.allow h (callWho c)).toNat := by
  have moveCase : ∀ {m : Weth9.Ledger} {src dst : Adr} {wad : B256}, wad ≤ m.bal src →
      m.total < 2 ^ 256 → m.bal h = l.bal h →
      ((m.xfer src dst wad).bal h).toNat < (l.bal h).toNat → src = h ∧ 0 < wad.toNat := by
    intro m src dst wad hle mfit hm hlt
    have := xfer_holder m h src dst hle mfit
    rw [hm] at this
    by_cases hc : src = h ∧ dst ≠ h
    · obtain ⟨rfl, hd⟩ := hc
      simp only [ne_eq, hd, not_false_eq_true, and_self, ↓reduceIte] at this
      exact ⟨rfl, by omega⟩
    · simp only [hc, ↓reduceIte, Nat.add_zero] at this
      omega
  cases c with
  | deposit who v =>
    simp only [Ledger.step, Option.some.injEq] at hs
    subst hs
    by_cases hw : who = h
    · exact Or.inl hw
    · rw [setBal_apply_ne _ (Ne.symm hw)] at lower
      exact absurd lower (Nat.lt_irrefl _)
  | withdraw who w =>
    simp only [Ledger.step] at hs
    split at hs
    · cases hs
    · simp only [Option.some.injEq] at hs
      subst hs
      by_cases hw : who = h
      · exact Or.inl hw
      · rw [setBal_apply_ne _ (Ne.symm hw)] at lower
        exact absurd lower (Nat.lt_irrefl _)
  | transfer who dst w =>
    simp only [Ledger.step] at hs
    obtain ⟨hle, (⟨rfl, -⟩ | ⟨hne, -⟩)⟩ := transferFrom_cases hs
    · exact Or.inl (moveCase hle fit rfl lower).1
    · exact absurd rfl hne
  | transferFrom who src dst w =>
    simp only [Ledger.step] at hs
    obtain ⟨hle, (⟨rfl, hcase⟩ | ⟨-, hal, rfl⟩)⟩ := transferFrom_cases hs
    · obtain ⟨rfl, -⟩ := moveCase hle fit rfl lower
      rcases hcase with hw | hm
      · exact Or.inl hw.symm
      · refine Or.inr ?_
        change 0 < (l.allow src who).toNat
        rw [hm]
        decide
    · obtain ⟨rfl, hpos⟩ := moveCase hle fit rfl lower
      refine Or.inr ?_
      change 0 < (l.allow src who).toNat
      have := B256.toNat_le_toNat hal
      omega
  | approve who g w =>
    simp only [Ledger.step, Option.some.injEq] at hs
    subst hs
    exact absurd lower (Nat.lt_irrefl _)

/-- **Owner law of the model**: only the owner raises its allowances. -/
theorem step_allow_owner {l l' : Weth9.Ledger} {c : Call} {h g : Adr}
    (hs : l.step c = some l') (raise : (l.allow h g).toNat < (l'.allow h g).toNat) :
    callWho c = h := by
  cases c with
  | deposit who v =>
    simp only [Ledger.step, Option.some.injEq] at hs
    subst hs
    exact absurd raise (Nat.lt_irrefl _)
  | withdraw who w =>
    simp only [Ledger.step] at hs
    split at hs
    · cases hs
    · simp only [Option.some.injEq] at hs
      subst hs
      exact absurd raise (Nat.lt_irrefl _)
  | transfer who dst w =>
    simp only [Ledger.step] at hs
    obtain ⟨-, (⟨rfl, -⟩ | ⟨hne, -⟩)⟩ := transferFrom_cases hs
    · exact absurd raise (Nat.lt_irrefl _)
    · exact absurd rfl hne
  | transferFrom who src dst w =>
    simp only [Ledger.step] at hs
    obtain ⟨-, (⟨rfl, -⟩ | ⟨-, hal, rfl⟩)⟩ := transferFrom_cases hs
    · exact absurd raise (Nat.lt_irrefl _)
    · change (l.allow h g).toNat < ((l.setAllow src who (l.allow src who - w)).allow h g).toNat
        at raise
      rw [setAllow_apply] at raise
      by_cases hc : h = src ∧ g = who
      · obtain ⟨rfl, rfl⟩ := hc
        simp only [and_self, ↓reduceIte] at raise
        rw [B256.toNat_sub_eq_of_le _ _ hal] at raise
        omega
      · simp only [hc, ↓reduceIte] at raise
        exact absurd raise (Nat.lt_irrefl _)
  | approve who g' w =>
    simp only [Ledger.step, Option.some.injEq] at hs
    subst hs
    rw [setAllow_apply] at raise
    by_cases hc : h = who ∧ g = g'
    · exact hc.1.symm
    · simp only [hc, ↓reduceIte] at raise
      exact absurd raise (Nat.lt_irrefl _)

/-- The calls a holder-safe operation decodes to: none (a view), the caller's own `transfer`, or
a zero-value deposit. -/
theorem weth9Op_safe {e : Sevm} (hsafe : (weth9Op e).HolderSafe) :
    decodeCall e = none ∨
      (∃ dst wad, decodeCall e = some (.transfer e.caller dst wad) ∧
        weth9Op e = .transfer dst wad.toNat) ∨
      decodeCall e = some (.deposit e.caller 0) := by
  unfold weth9Op at hsafe ⊢
  by_cases hb : ¬ shortCall e ∧ Sevm.selector e = 0x70a08231
  · refine Or.inl ?_
    unfold decodeCall
    rw [ite_eq_right hb.1, hb.2, ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_left (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]
  · rw [ite_eq_right hb] at hsafe ⊢
    cases hd : decodeCall e with
    | none => exact Or.inl rfl
    | some c =>
      have who := callWho_decodeCall hd
      rw [hd] at hsafe
      cases c with
      | deposit w v =>
        by_cases hv : v = 0
        · subst hv
          change w = e.caller at who
          subst who
          exact Or.inr (Or.inr rfl)
        · simp only [hv, ↓reduceIte, Op.HolderSafe] at hsafe
      | withdraw => simp only [Op.HolderSafe] at hsafe
      | transfer w dst wad =>
        change w = e.caller at who
        subst who
        exact Or.inr (Or.inl ⟨dst, wad, rfl, rfl⟩)
      | transferFrom => simp only [Op.HolderSafe] at hsafe
      | approve => simp only [Op.HolderSafe] at hsafe

/-- A decoded `transfer` operation is the caller's model `transfer`. -/
theorem weth9Op_transfer {e : Sevm} {dst : Adr} {v : Nat} (h : weth9Op e = .transfer dst v) :
    ∃ wad, decodeCall e = some (.transfer e.caller dst wad) ∧ v = wad.toNat := by
  rcases weth9Op_safe (by rw [h]; trivial : (weth9Op e).HolderSafe) with
    hd | ⟨dst', wad, hd, hop⟩ | hd
  · unfold weth9Op at h
    split at h
    · cases h
    · rw [hd] at h
      cases h
  · rw [h] at hop
    cases hop
    exact ⟨wad, hd, rfl⟩
  · unfold weth9Op at h
    split at h
    · cases h
    · rw [hd] at h
      cases h

theorem weth9Book_step_some {l : weth9Book.Ledger} {e : Sevm} {c : Call}
    (hd : decodeCall e = some c) : weth9Book.step l e = Weth9.Ledger.step l c := by
  change (match decodeCall e with | none => some l | some c => l.step c) = _
  rw [hd]

theorem weth9Book_step_none {l : weth9Book.Ledger} {e : Sevm} (hd : decodeCall e = none) :
    weth9Book.step l e = some l := by
  change (match decodeCall e with | none => some l | some c => l.step c) = _
  rw [hd]

/-- A zero-value deposit leaves the ledger alone. -/
theorem step_deposit_zero (l : Weth9.Ledger) (h : Adr) : l.step (.deposit h 0) = some l := by
  change some (l.setBal h (l.bal h + 0)) = some l
  rw [B256.add_zero]
  unfold Ledger.setBal
  rw [Function.update_eq_self]

theorem weth9Book_laws : BookLaws weth9Book where
  holder_only := by
    intro l l' a h good hs lower
    cases hd : decodeCall a with
    | none =>
      rw [weth9Book_step_none hd, Option.some.injEq] at hs
      subst hs
      exact absurd lower (Nat.lt_irrefl _)
    | some c =>
      rw [weth9Book_step_some hd] at hs
      have := step_holder_only good hs lower
      rw [callWho_decodeCall hd] at this
      rcases this with h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
  allow_owner := by
    intro l l' a h g _ hs raise
    cases hd : decodeCall a with
    | none =>
      rw [weth9Book_step_none hd, Option.some.injEq] at hs
      subst hs
      exact absurd raise (Nat.lt_irrefl _)
    | some c =>
      rw [weth9Book_step_some hd] at hs
      rw [← callWho_decodeCall hd]
      exact step_allow_owner hs raise
  holder_debit := by
    intro l l' a h good hs hcaller hsafe
    subst hcaller
    rcases weth9Op_safe hsafe with hd | ⟨dst, wad, hd, hop⟩ | hd
    · rw [weth9Book_step_none hd, Option.some.injEq] at hs
      subst hs
      exact Nat.le_add_right _ _
    · rw [weth9Book_step_some hd] at hs
      obtain ⟨hle, (⟨rfl, -⟩ | ⟨hne, -⟩)⟩ := transferFrom_cases hs
      · change (l.bal a.caller).toNat ≤ ((l.xfer a.caller dst wad).bal a.caller).toNat +
          (weth9Op a).debit a.caller
        rw [hop]
        change _ ≤ _ + wad.toNat
        have := xfer_holder l a.caller a.caller dst hle good
        split at this <;> omega
      · exact absurd rfl hne
    · rw [weth9Book_step_some hd] at hs
      obtain rfl := Option.some.inj (hs.symm.trans (step_deposit_zero l a.caller))
      exact Nat.le_add_right _ _
  transfer_exact := by
    intro l l' a dst v _ hs hop hne
    obtain ⟨wad, hd, rfl⟩ := weth9Op_transfer hop
    rw [weth9Book_step_some hd] at hs
    obtain ⟨hle, (⟨rfl, -⟩ | ⟨hne', -⟩)⟩ := transferFrom_cases hs
    · exact xfer_src l hle hne
    · exact absurd rfl hne'
  allow_safe := by
    intro l l' a h g _ hs hcaller hsafe
    rcases weth9Op_safe hsafe with hd | ⟨dst, wad, hd, -⟩ | hd
    · rw [weth9Book_step_none hd, Option.some.injEq] at hs
      subst hs
      exact Nat.le_refl _
    · rw [weth9Book_step_some hd] at hs
      obtain ⟨-, (⟨rfl, -⟩ | ⟨hne, -⟩)⟩ := transferFrom_cases hs
      · exact Nat.le_refl _
      · exact absurd rfl hne
    · rw [weth9Book_step_some hd] at hs
      obtain rfl := Option.some.inj (hs.symm.trans (step_deposit_zero l a.caller))
      exact Nat.le_refl _


/-! ## The transfer liveness facet -/

/-- A decoded `transfer` is the `transfer` selector past the short-call test, reading its two
argument words. -/
theorem decodeCall_transfer_inv {e : Sevm} {w dst : Adr} {wad : B256}
    (hd : decodeCall e = some (.transfer w dst wad)) :
    ¬ shortCall e ∧ Sevm.selector e = 0xa9059cbb ∧ w = e.caller ∧
      dst = (Sevm.dataWord e 4).toAdr ∧ wad = Sevm.dataWord e 36 := by
  unfold decodeCall at hd
  split_ifs at hd with h1 h2 h3 <;> (try cases hd)
  exact ⟨h1, h3, rfl, rfl, rfl⟩

/-- A successful run of the lifted program on a `transfer` frame leaves every balance alone. -/
theorem transfer_run_bal {sevm : Sevm} {pre post : Devm} (hrun : SProg.RunExact prog sevm pre post)
    (hd : decodeCall sevm =
      some (.transfer sevm.caller (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36))) :
    post.getBal = pre.getBal := by
  obtain ⟨f, hf, run⟩ := hrun
  rcases weth9_route (P := Ninst.Run) (fun h => h) ⟨f, hf, run.toRun⟩ with
    ⟨hmiss, -⟩ | ⟨l, hl, hshort, hsel, g, d', hg, hs, run'⟩
  · rw [decode_miss hmiss] at hd
    cases hd
  · rcases decode_hit hshort hl hsel with ⟨-, hd'⟩ | ⟨-, hd'⟩ | ⟨hk, -⟩ | ⟨-, hd'⟩ | ⟨-, hd'⟩ |
        ⟨-, hd'⟩ <;> (try (rw [hd'] at hd; cases hd))
    rw [hk] at hg
    have hok := Weth9.transfer_wrapper_okX hg (run'.mono (fun h => h))
    exact hok.1.1.trans hs.bal.symm

/-- The deployed bytes as a code word. -/
theorem code_eq_of_image {c : ByteArray} (h : some c.toList = weth9Sem.image) : c = code := by
  have h' : c.toList = code.toList := Option.some.inj h
  cases hs : c with
  | mk d =>
    cases hk : code with
    | mk d' =>
      rw [hs, hk] at h'
      rw [ByteArray.toList_eq_toList_data, ByteArray.toList_eq_toList_data] at h'
      exact congrArg ByteArray.mk (Array.toList_inj.mp h')

/-- The `transfer` charge does not read the machine registers. -/
theorem transferGas_St (sevm : Sevm) (pre : Devm) (G : Nat) :
    transferGas sevm (St pre [] Mem.empty G) = transferGas sevm pre := by
  have hs : ∀ (b : Devm) (m : Mach) (k : B256), sloadCost sevm (b.setMach m) k = sloadCost sevm b k :=
    fun _ _ _ => rfl
  unfold transferGas xferGasSelf xfTailGas St tT3 tV2 tT2 tT1 tV1 pB1
  simp only [afterSload_setMach, afterSstore_setMach, Devm.getStorVal_setMach, sstoreCost_setMach, hs]

/-- WETH9's frame-level transfer liveness facet, from `weth9_transfer_runExact`. -/
noncomputable def weth9TransferLive (ca : Adr) (U : Key → Prop) : TransferLive ca weth9Book where
  WorldOk w := some (w.getCode ca).toList = weth9Sem.image ∧ FootInv U (w.getStor ca) (w.bal ca)
  FrameOk sevm _ := (∀ k ∈ frameKeys sevm, U k) ∧ sevm.data.length < 2 ^ 256
  ledgerAt w := ledger U (w.getStor ca)
  cost sevm pre := transferGas sevm pre
  live := by
    intro sevm pre G dst v htarget _ hcode ⟨hkeys, hlen'⟩ hfork hvalue hstatic _ ⟨hinst, hinv⟩ hop
      hbal hcost hmargin
    obtain ⟨wad, hd, rfl⟩ := weth9Op_transfer hop
    obtain ⟨hshort, hsel, -, hdst, hwad⟩ := decodeCall_transfer_inv hd
    subst hdst hwad
    have hlen : 4 ≤ sevm.data.length := by
      have hn := B256.toNat_le_toNat (B256.not_lt.mp hshort)
      rw [B256.toNat_toB256_of_lt hlen'] at hn
      exact hn
    have hcodeEq : sevm.code = code := hcode.trans (code_eq_of_image hinst)
    have hcaller : U (.bal sevm.caller) := hkeys _ List.mem_cons_self
    have hdstU : U (.bal (Sevm.dataWord sevm 4).toAdr) :=
      hkeys _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have hle : Sevm.dataWord sevm 36 ≤
        (St pre [] Mem.empty G).getStorVal sevm.currentTarget (balSlot sevm.caller) := by
      change (Sevm.dataWord sevm 36).toNat ≤ (tracked U (pre.state.getStor ca) sevm.caller).toNat
        at hbal
      rw [tracked_self hcaller] at hbal
      rw [htarget]
      refine B256.not_lt.mp (fun hlt => ?_)
      have := B256.toNat_lt_toNat hlt
      change ((pre.state.getStor ca).get (balSlot sevm.caller)).toNat <
        (Sevm.dataWord sevm 36).toNat at this
      omega
    obtain ⟨post, hrun, hg, ho⟩ := weth9_transfer_runExact hfork hstatic hvalue
      (hsel.trans trSel_eq.symm) hlen hlen' St.stack St.memory hle
      (G := G - transferGas sevm pre)
      (by rw [transferGas_St, St.gasLeft]; omega)
      (Nat.lt_add_right _ (by unfold gCallStipend at hmargin ⊢; omega))
    have hexec := exec_of_runExact hcodeEq hfork hrun
    have heff := writer_effect hfork hrun hd (by intro who w h; cases h)
    have hbalEq := transfer_run_bal hrun hd
    rw [htarget] at heff hle
    have hcodePost : post.state.getCode ca = pre.state.getCode ca := by
      obtain ⟨run⟩ := hexec
      have hrel := Exec.effect codePreserve_refl_trans.1 codePreserve_refl_trans.2
        Ninst.codePreserve_effectRec Jinst.codePreserve_effect Linst.codePreserve_effect run
      exact hrel ca (fun hnil => weth9Sem.ne_nil hinst.symm hnil)
    have hpostStor : post.getStor ca =
        xferStor (pre.state.getStor ca) sevm.caller (Sevm.dataWord sevm 4).toAdr
          (Sevm.dataWord sevm 36) := by
      have h := heff
      change xferStorStep (pre.state.getStor ca) sevm.caller sevm.caller
        (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36) = some (post.getStor ca) at h
      have hleS := (xferStorStep_ok h).1
      unfold xferStorStep at h
      rw [ite_eq_right (B256.not_lt.mpr hleS), ite_eq_right (fun hc => hc.1 rfl)] at h
      exact (Option.some.inj h).symm
    have hstep := Call.stor_ledger hinv.inj (K := U)
      (by
        intro k hk
        simp only [Call.keys, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl
        · exact hcaller
        · exact hdstU) heff
    have hmodel : (ledger U (pre.state.getStor ca)).transferFrom sevm.caller sevm.caller
        (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36) = some (ledger U (post.getStor ca)) :=
      hstep
    obtain ⟨hleL, (⟨hL, -⟩ | ⟨hne, -⟩)⟩ := transferFrom_cases hmodel
    swap
    · exact absurd rfl hne
    refine ⟨post, hexec, by rw [hg]; omega, by rw [ho]; rfl, ⟨?_, ?_⟩, ?_⟩
    · rw [hcodePost]
      exact hinst
    · refine ⟨?_, hinv.inj, hinv.apart, ?_⟩
      · change Support U (post.getStor ca)
        rw [hpostStor]
        exact (hinv.support.set hcaller _).set hdstU _
      · have htot := Ledger.sum_xfer_le (ledger U (pre.state.getStor ca)) sevm.caller
          (Sevm.dataWord sevm 4).toAdr hleL
        rw [← hL] at htot
        have hb := hinv.backed
        have hbca : post.state.bal ca = pre.state.bal ca := congrFun hbalEq ca
        change trackedSum U (post.getStor ca) ≤ trackedSum U (pre.state.getStor ca) at htot
        rw [hbca]
        exact Nat.le_trans htot hb
    · intro hne
      change ((ledger U (post.getStor ca)).bal sevm.caller).toNat + (Sevm.dataWord sevm 36).toNat =
        ((ledger U (pre.state.getStor ca)).bal sevm.caller).toNat
      rw [hL]
      exact xfer_src _ hleL hne

/-- The C2 control's mutant: `transferFrom` that skips the allowance check. -/
def mutantTransferFrom (l : Weth9.Ledger) (_who src dst : Adr) (wad : B256) : Option Weth9.Ledger :=
  if l.bal src < wad then none else some (l.xfer src dst wad)

def mutantBook : Book :=
  { weth9Book with
    step := fun l e => match decodeCall e with
      | some (.transferFrom who src dst wad) => mutantTransferFrom l who src dst wad
      | none => some l
      | some c => l.step c }

/-! ## The control witness -/

/-- The empty ledger. -/
def zeroLedger : Weth9.Ledger := ⟨fun _ => 0, fun _ _ => 0⟩

/-- A ledger in which only `a` holds one unit and nobody has granted an allowance. -/
def oneLedger (a : Adr) : Weth9.Ledger := zeroLedger.setBal a 1

theorem oneLedger_total (a : Adr) : (oneLedger a).total ≤ 1 := by
  have h := Ledger.sum_deposit_le zeroLedger a 1
  have hz : zeroLedger.total = 0 := sumBelow_zero _
  have hb : zeroLedger.bal a + 1 = 1 := by
    show (0 : B256) + 1 = 1
    decide
  rw [hb] at h
  change (oneLedger a).total ≤ zeroLedger.total + (1 : B256).toNat at h
  rw [hz] at h
  exact h

/-- The control's message: `transferFrom(1, 2, 1)` called by address `0`. -/
def mutantWitness : Sevm :=
  { (default : Sevm) with
    data := [0x23, 0xb8, 0x72, 0xdd] ++ List.replicate 31 0 ++ [1] ++ List.replicate 31 0 ++ [2] ++
      List.replicate 31 0 ++ [1] }

theorem mutantWitness_decode :
    decodeCall mutantWitness = some (.transferFrom 0 1 2 1) := by
  have short : ¬ shortCall mutantWitness := by decide +kernel
  have sel : Sevm.selector mutantWitness = 0x23b872dd := by decide +kernel
  have w4 : (Sevm.dataWord mutantWitness 4).toAdr = 1 := by decide +kernel
  have w36 : (Sevm.dataWord mutantWitness 36).toAdr = 2 := by decide +kernel
  have w68 : Sevm.dataWord mutantWitness 68 = 1 := by decide +kernel
  have caller : mutantWitness.caller = 0 := rfl
  unfold decodeCall
  rw [ite_eq_right short, sel, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl, w4, w36, w68, caller]

/-- **C2 control.**  The mutated model violates the core's holder law. -/
theorem control_mutant_not_laws : ¬ BookLaws mutantBook := by
  intro laws
  have good : mutantBook.Good (oneLedger 1) := by
    change (oneLedger 1).total < 2 ^ 256
    have := oneLedger_total 1
    omega
  have step : mutantBook.step (oneLedger 1) mutantWitness =
      some ((oneLedger 1).xfer 1 2 1) := by
    have h : mutantBook.step (oneLedger 1) mutantWitness =
        mutantTransferFrom (oneLedger 1) 0 1 2 1 := by
      unfold mutantBook
      dsimp only
      rw [mutantWitness_decode]
    rw [h]
    unfold mutantTransferFrom
    rw [ite_eq_right (by decide +kernel)]
  have lower : mutantBook.bal ((oneLedger 1).xfer 1 2 1) 1 < mutantBook.bal (oneLedger 1) 1 := by
    decide +kernel
  rcases laws.holder_only good step lower with h | h
  · exact absurd h (by decide)
  · exact absurd h (by decide +kernel)

end Blanc.Composition.Weth9Token
