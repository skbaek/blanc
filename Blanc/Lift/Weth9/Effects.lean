import Blanc.Lift.Weth9.Route
import Blanc.Lift.Weth9.Ledger
import Blanc.Lift.Weth9.FootFrame

/-!
# What a successful WETH9 frame does to the ledger

`decodeCall` reads the call a frame runs from its calldata, message sender and callvalue, by the same
table as the dispatcher (`Route.lean`): a view selector is no writer; the payable fallback — calldata
shorter than four bytes or an unmatched selector — is `deposit`.  `Call.stor` is the storage-level effect
of a writer (exactly the runtime's, including the allowance sentinel), `Call.stor_ledger` says it is the
model's `Ledger.step` at the tracked keys, and `weth9_frame_effect` says a successful frame that runs no
external instruction (every writer but `withdraw`) has exactly that effect.
-/

namespace Blanc.Lift.Weth9

open Jaune Blanc Blanc.Lift

/-! ## The call a frame runs -/

instance (e : Sevm) : Decidable (shortCall e) := inferInstanceAs (Decidable (_ < _))

/-- The writer call a frame runs, `none` for a view.  Calldata shorter than four bytes and an unmatched
selector are the payable fallback, which is `deposit`. -/
def decodeCall (e : Sevm) : Option Call :=
  if shortCall e then some (.deposit e.caller e.value)
  else if Sevm.selector e = 0x2e1a7d4d then some (.withdraw e.caller (Sevm.dataWord e 4))
  else if Sevm.selector e = 0xa9059cbb then
    some (.transfer e.caller (Sevm.dataWord e 4).toAdr (Sevm.dataWord e 36))
  else if Sevm.selector e = 0x23b872dd then
    some (.transferFrom e.caller (Sevm.dataWord e 4).toAdr (Sevm.dataWord e 36).toAdr
      (Sevm.dataWord e 68))
  else if Sevm.selector e = 0x095ea7b3 then
    some (.approve e.caller (Sevm.dataWord e 4).toAdr (Sevm.dataWord e 36))
  else if Sevm.selector e = 0xd0e30db0 then some (.deposit e.caller e.value)
  else if Sevm.selector e = 0x06fdde03 ∨ Sevm.selector e = 0x18160ddd ∨
      Sevm.selector e = 0x313ce567 ∨ Sevm.selector e = 0x70a08231 ∨
      Sevm.selector e = 0x95d89b41 ∨ Sevm.selector e = 0xdd62ed3e then none
  else some (.deposit e.caller e.value)

/-- The keys a call may read or write. -/
def Call.keys : Call → List Key
  | .deposit who _ => [.bal who]
  | .withdraw who _ => [.bal who]
  | .transfer who dst _ => [.bal who, .bal dst]
  | .transferFrom who src dst _ => [.bal src, .bal dst, .allow src who]
  | .approve who g _ => [.allow who g]

/-- The decoded call's keys are among the frame's (uniform) keys. -/
theorem decodeCall_keys {e : Sevm} {c : Call} (h : decodeCall e = some c) :
    ∀ k ∈ c.keys, k ∈ frameKeys e := by
  unfold decodeCall at h
  split_ifs at h <;> (try cases h) <;> simp only [Call.keys, List.mem_cons, List.not_mem_nil, or_false, frameKeys, forall_eq, Key.bal.injEq, reduceCtorEq, or_self, true_or, forall_eq_or_imp, or_true, and_self, Key.allow.injEq]

/-! ## The storage effect of a call -/

/-- The storage effect of `transferFrom(src, dst, wad)` called by `who`, `none` when it reverts: the
balance `require`; the allowance `require` and debit unless `src` is the caller or the allowance is the
maximal word; then the two balance writes. -/
def xferStorStep (s : Stor) (who src dst : Adr) (wad : B256) : Option Stor :=
  if s.get (balSlot src) < wad then none
  else if src ≠ who ∧ s.get (allowSlot src who) ≠ B256.max then
    if s.get (allowSlot src who) < wad then none
    else some (xferStor (s.set (allowSlot src who) (s.get (allowSlot src who) - wad)) src dst wad)
  else some (xferStor s src dst wad)

/-- The storage-level effect of a writer call, `none` when it reverts.  For `withdraw` it is the debit,
which precedes the ETH send. -/
def Call.stor (s : Stor) : Call → Option Stor
  | .deposit who v => some (s.set (balSlot who) (s.get (balSlot who) + v))
  | .withdraw who w =>
      if s.get (balSlot who) < w then none
      else some (s.set (balSlot who) (s.get (balSlot who) - w))
  | .transfer who dst w => xferStorStep s who who dst w
  | .transferFrom who src dst w => xferStorStep s who src dst w
  | .approve who g w => some (s.set (allowSlot who g) w)

theorem toB256_inj {a b : Adr} (h : a.toB256 = b.toB256) : a = b := by
  have := congrArg B256.toAdr h
  rwa [toAdr_toB256, toAdr_toB256] at this

/-! ## The ledger bridge -/

section Bridge

variable {K : Key → Prop} {s : Stor}

theorem ledger_xferStor (hK : KeyInj K) {src dst : Adr} (hsrc : K (.bal src))
    (hdst : K (.bal dst)) (wad : B256) :
    ledger K (xferStor s src dst wad) = (ledger K s).xfer src dst wad := by
  have hsrcw : (ledger K s).bal src = s.get (balSlot src) := tracked_self hsrc
  have h1 : (ledger K s).setBal src ((ledger K s).bal src - wad) =
      ledger K (s.set (balSlot src) (s.get (balSlot src) - wad)) := by
    rw [ledger_set_bal hK hsrc, hsrcw]
  have h2 : (ledger K (s.set (balSlot src) (s.get (balSlot src) - wad))).bal dst =
      (s.set (balSlot src) (s.get (balSlot src) - wad)).get (balSlot dst) := tracked_self hdst
  unfold xferStor
  rw [ledger_set_bal hK hdst]
  show _ = ((ledger K s).setBal src ((ledger K s).bal src - wad)).setBal dst
    (((ledger K s).setBal src ((ledger K s).bal src - wad)).bal dst + wad)
  rw [h1, h2]

theorem xferStorStep_ledger (hK : KeyInj K) {who src dst : Adr} {wad : B256} {s' : Stor}
    (hsrc : K (.bal src)) (hdst : K (.bal dst)) (hallow : src ≠ who → K (.allow src who))
    (h : xferStorStep s who src dst wad = some s') :
    (ledger K s).transferFrom who src dst wad = some (ledger K s') := by
  have hb : (ledger K s).bal src = s.get (balSlot src) := tracked_self hsrc
  unfold xferStorStep at h
  unfold Ledger.transferFrom
  rw [hb]
  by_cases hlt : s.get (balSlot src) < wad
  · simp only [hlt, ↓reduceIte] at h
    cases h
  · simp only [hlt, ↓reduceIte] at h ⊢
    by_cases hc : src ≠ who ∧ s.get (allowSlot src who) ≠ B256.max
    · have hAK : K (.allow src who) := hallow hc.1
      have ha : (ledger K s).allow src who = s.get (allowSlot src who) := trackedAllow_self hAK
      have hc' : src ≠ who ∧ (ledger K s).allow src who ≠ maxAllowance := by
        rw [ha]
        exact hc
      simp only [hc.1, hc.2, hc'.2, ne_eq, not_false_eq_true, and_self, ↓reduceIte] at h ⊢
      by_cases hl2 : s.get (allowSlot src who) < wad
      · simp only [hl2, ↓reduceIte] at h
        cases h
      · have hl2' : ¬ (ledger K s).allow src who < wad := by
          rw [ha]
          exact hl2
        simp only [hl2, hl2', ↓reduceIte] at h ⊢
        cases h
        rw [ledger_xferStor hK hsrc hdst, ledger_set_allow hK hAK, ha]
    · have hc' : ¬ (src ≠ who ∧ (ledger K s).allow src who ≠ maxAllowance) := by
        intro h'
        apply hc
        refine ⟨h'.1, ?_⟩
        by_cases hsw : src = who
        · exact absurd hsw h'.1
        · have hAK : K (.allow src who) := hallow hsw
          have ha : (ledger K s).allow src who = s.get (allowSlot src who) :=
            trackedAllow_self hAK
          rw [← ha]
          exact h'.2
      simp only [hc, hc', ↓reduceIte] at h ⊢
      cases h
      rw [ledger_xferStor hK hsrc hdst]

/-- **A call's storage effect is the model's step at the tracked keys.** -/
theorem Call.stor_ledger (hK : KeyInj K) {s' : Stor} {c : Call} (hkeys : ∀ k ∈ c.keys, K k)
    (h : c.stor s = some s') : (ledger K s).step c = some (ledger K s') := by
  cases c with
  | deposit who v =>
    have hw : K (.bal who) := hkeys _ (by simp only [keys, List.mem_cons, List.not_mem_nil,
      or_false])
    have hb : (ledger K s).bal who = s.get (balSlot who) := tracked_self hw
    simp only [Call.stor] at h
    cases h
    rw [Ledger.step_deposit, ledger_set_bal hK hw, hb]
  | withdraw who w =>
    have hw : K (.bal who) := hkeys _ (by simp only [keys, List.mem_cons, List.not_mem_nil,
      or_false])
    have hb : (ledger K s).bal who = s.get (balSlot who) := tracked_self hw
    simp only [Call.stor] at h
    rw [Ledger.step_withdraw, hb]
    by_cases hlt : s.get (balSlot who) < w
    · simp only [hlt, ↓reduceIte] at h
      cases h
    · simp only [hlt, ↓reduceIte] at h ⊢
      cases h
      rw [ledger_set_bal hK hw]
  | transfer who dst w =>
    have hw : K (.bal who) := hkeys _ (by simp only [keys, List.mem_cons, Key.bal.injEq,
      List.not_mem_nil, or_false, true_or])
    have hd : K (.bal dst) := hkeys _ (by simp only [keys, List.mem_cons, Key.bal.injEq,
      List.not_mem_nil, or_false, or_true])
    rw [Ledger.step_transfer]
    exact xferStorStep_ledger hK hw hd (fun h => absurd rfl h) h
  | transferFrom who src dst w =>
    have hsrc : K (.bal src) := hkeys _ (by simp only [keys, List.mem_cons, Key.bal.injEq,
      reduceCtorEq, List.not_mem_nil, or_self, or_false, true_or])
    have hdst : K (.bal dst) := hkeys _ (by simp only [keys, List.mem_cons, Key.bal.injEq,
      reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true])
    have hal : K (.allow src who) := hkeys _ (by simp only [keys, List.mem_cons, reduceCtorEq,
      List.not_mem_nil, or_false, or_true])
    rw [Ledger.step_transferFrom]
    exact xferStorStep_ledger hK hsrc hdst (fun _ => hal) h
  | approve who g w =>
    have hk : K (.allow who g) := hkeys _ (by simp only [keys, List.mem_cons, List.not_mem_nil,
      or_false])
    simp only [Call.stor] at h
    cases h
    rw [Ledger.step_approve, ledger_set_allow hK hk]

end Bridge

/-! ## Decoding by the dispatcher's table -/

/-- The dispatcher's selectors as words. -/
def linkSels : List B256 := links.map fun l => Bytes.toB256 l.σ

theorem linkSels_eq : linkSels = [0x06fdde03, 0x095ea7b3, 0x18160ddd, 0x23b872dd, 0x2e1a7d4d,
    0x313ce567, 0x70a08231, 0x95d89b41, 0xa9059cbb, 0xd0e30db0, 0xdd62ed3e] := by
  decide +kernel

theorem mem_linkSels {x : B256} : x ∈ linkSels ↔ ∃ l ∈ links, Bytes.toB256 l.σ = x := by
  unfold linkSels
  simp only [List.mem_map]

/-- **No dispatcher selector matches, or the calldata is short: the fallback deposit.** -/
theorem decode_miss {e : Sevm}
    (h : shortCall e ∨ ∀ l ∈ links, Sevm.selector e ≠ Bytes.toB256 l.σ) :
    decodeCall e = some (.deposit e.caller e.value) := by
  by_cases hs : shortCall e
  · unfold decodeCall
    simp only [hs, ↓reduceIte]
  · rcases h with h | hm
    · exact absurd h hs
    have hm' : ∀ x ∈ linkSels, Sevm.selector e ≠ x := by
      intro x hx
      obtain ⟨l, hl, rfl⟩ := mem_linkSels.mp hx
      exact hm l hl
    rw [linkSels_eq] at hm'
    have n1 := hm' 0x06fdde03 (by simp only [List.mem_cons, List.not_mem_nil, or_false, true_or])
    have n2 := hm' 0x095ea7b3 (by simp only [List.mem_cons, List.not_mem_nil, or_false, true_or,
      or_true])
    have n3 := hm' 0x18160ddd (by simp only [List.mem_cons, List.not_mem_nil, or_false, true_or,
      or_true])
    have n4 := hm' 0x23b872dd (by simp only [List.mem_cons, List.not_mem_nil, or_false, true_or,
      or_true])
    have n5 := hm' 0x2e1a7d4d (by simp only [List.mem_cons, List.not_mem_nil, or_false, true_or,
      or_true])
    have n6 := hm' 0x313ce567 (by simp only [List.mem_cons, List.not_mem_nil, or_false, true_or,
      or_true])
    have n7 := hm' 0x70a08231 (by simp only [List.mem_cons, List.not_mem_nil, or_false, true_or,
      or_true])
    have n8 := hm' 0x95d89b41 (by simp only [List.mem_cons, List.not_mem_nil, or_false, true_or,
      or_true])
    have n9 := hm' 0xa9059cbb (by simp only [List.mem_cons, List.not_mem_nil, or_false, true_or,
      or_true])
    have n10 := hm' 0xd0e30db0 (by simp only [List.mem_cons, List.not_mem_nil, or_false, true_or,
      or_true])
    have n11 := hm' 0xdd62ed3e (by simp only [List.mem_cons, List.not_mem_nil, or_false, or_true])
    unfold decodeCall
    simp only [hs, ↓reduceIte, n5, n9, n4, n2, n10, n1, n3, n6, n7, n8, n11, or_self]

/-! ## The writer entries -/

/-- **A payable entry** (the fallback and the `deposit` wrapper): `dest`, two pushes, then a call of
entry 1 continued by a state-silent tree.  Its effect is the deposit's. -/
theorem depositCall_effect {sevm : Sevm} (hfork : CoveredFork sevm.benvStat.fork) {d : Devm}
    {o : Outcome} {a b : Bytes} {ha : a.length ≤ 32} {hb : b.length ≤ 32} {f : SFunc}
    (hf : f.silent = true) (hrefs : f.refs.all (· ∈ ([] : List Nat)) = true)
    (run : SFunc.Run prog sevm d (.dest (chain [.push a ha, .push b hb] (.callNext 1 f))) o) :
    Devm.getStor (Outcome.devm o) sevm.currentTarget =
        (Devm.getStor d sevm.currentTarget).set (balSlot sevm.caller)
          ((Devm.getStor d sevm.currentTarget).get (balSlot sevm.caller) + sevm.value) ∧
      (Outcome.devm o).getBal = d.getBal := by
  cases run with
  | dest burn run1 =>
  obtain ⟨d1, hl, run2⟩ := run_chain_prefix [.push a ha, .push b hb] [] run1
  have s01 : Same d d1 := Same.trans (Same.of_state burn.state)
    ⟨Line.of_inv Devm.getStor (by line_inv) hl, Line.of_inv Devm.getBal (by line_inv) hl⟩
  change SFunc.Run prog sevm d1 (.callNext 1 f) o at run2
  cases run2 with
  | callHalt dd lookup pop crun =>
    have s02 := s01.trans (Same.of_state pop.state)
    obtain ⟨hs, hbal⟩ := Weth9.deposit_effect lookup hfork crun
    exact ⟨by rw [hs, ← s02.1], by rw [hbal, ← s02.2]⟩
  | callRet dd lookup pop crun tail =>
    have s02 := s01.trans (Same.of_state pop.state)
    obtain ⟨hs, hbal⟩ := Weth9.deposit_effect lookup hfork crun
    have hst := SFunc.Run.state_of_silent silentSet_nil hf hrefs tail
    have s2o := Same.of_state hst.symm
    simp only [Outcome.devm] at hs hbal
    exact ⟨by rw [← s2o.1, hs, ← s02.1], by rw [← s2o.2, hbal, ← s02.2]⟩

theorem tree_03ca : t_03ca_c19 = .dest (chain [.push [0x03, 0xd2] (by decide),
    .push [0x04, 0x40] (by decide)] (.callNext 1 t_03d2_c19)) := rfl

/-- **The `withdraw` wrapper always runs its `CALL`.**  A successful run of entry 24 contains a step
of the external instruction (the ETH send). -/
theorem wrapper24_hasCall {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.RunP P prog sevm d t_0243_c24 o) :
    ∃ s sf : Devm, P sevm s (.exec .call) sf := by
  have h24 : t_0243_c24 = .dest (chain [.reg .callvalue, .reg .iszero,
      .push [0x02, 0x4e] (by decide)] (.branch t_024a_c24 t_024e_c24)) := rfl
  have h24e : t_024e_c24 = .dest (chain [.push [0x02, 0x64] (by decide),
      .push [0x04] (by decide), .reg (.dup 0), .reg (.dup 0), .reg .calldataload,
      .reg (.swap 0), .push [0x20] (by decide), .reg .add, .reg (.swap 0), .reg (.swap 1),
      .reg (.swap 0), .reg .pop, .reg .pop, .push [0x09, 0xd9] (by decide)]
      (.callNext 8 t_0264_c24)) := rfl
  rw [h24] at run
  cases run with
  | dest burn run =>
  obtain ⟨d1, hl, run⟩ := run_chain_prefixP [.reg .callvalue, .reg .iszero,
    .push [0x02, 0x4e] (by decide)] [] run
  change SFunc.RunP P prog sevm d1 (.branch t_024a_c24 t_024e_c24) o at run
  cases run with
  | zero _ _ run => exact absurd run not_run_revert_tail
  | succ dw w hwnz pop run =>
  rw [h24e] at run
  cases run with
  | dest burn' run =>
  obtain ⟨d2, hl2, run⟩ := run_chain_prefixP [.push [0x02, 0x64] (by decide),
      .push [0x04] (by decide), .reg (.dup 0), .reg (.dup 0), .reg .calldataload,
      .reg (.swap 0), .push [0x20] (by decide), .reg .add, .reg (.swap 0), .reg (.swap 1),
      .reg (.swap 0), .reg .pop, .reg .pop, .push [0x09, 0xd9] (by decide)] [] run
  change SFunc.RunP P prog sevm d2 (.callNext 8 t_0264_c24) o at run
  cases run with
  | callHalt dd lookup pop2 crun =>
    obtain ⟨wad, rest, d10, sf, -, -, -, -, -, -, -, -, -, hcall, -⟩ :=
      Weth9.withdraw_walk_gen hP lookup crun
    exact ⟨d10, sf, hcall⟩
  | callRet dd lookup pop2 crun tail =>
    obtain ⟨wad, rest, d10, sf, -, -, -, -, -, -, -, -, -, hcall, -⟩ :=
      Weth9.withdraw_walk_gen hP lookup crun
    exact ⟨d10, sf, hcall⟩

/-- The view wrappers keep the state. -/
theorem viewWrapper_state {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {sevm : Sevm} {d : Devm} {o : Outcome}
    {k : Nat} {g : SFunc} (hk : k ∈ [18, 21, 22, 23, 26, 28]) (hg : prog[k]? = some g)
    (run : SFunc.RunP P prog sevm d g o) : (Outcome.devm o).state = d.state := by
  have h := (List.all_eq_true.mp viewWrappers_silent) k (List.mem_append_right _ hk)
  rw [hg] at h
  simp only [Bool.and_eq_true] at h
  exact SFunc.RunP.state_of_silent hP viewWrappers_silent h.1 h.2 run

/-- **A dispatcher hit decodes by its link.** -/
theorem decode_hit {e : Sevm} (hshort : ¬ shortCall e) {l : Link} (hl : l ∈ links)
    (hsel : Sevm.selector e = Bytes.toB256 l.σ) :
    (l.k ∈ [18, 21, 22, 23, 26, 28] ∧ decodeCall e = none) ∨
    (l.k = 24 ∧ decodeCall e = some (.withdraw e.caller (Sevm.dataWord e 4))) ∨
    (l.k = 20 ∧ decodeCall e =
      some (.transfer e.caller (Sevm.dataWord e 4).toAdr (Sevm.dataWord e 36))) ∨
    (l.k = 25 ∧ decodeCall e = some (.transferFrom e.caller (Sevm.dataWord e 4).toAdr
      (Sevm.dataWord e 36).toAdr (Sevm.dataWord e 68))) ∨
    (l.k = 27 ∧ decodeCall e =
      some (.approve e.caller (Sevm.dataWord e 4).toAdr (Sevm.dataWord e 36))) ∨
    (l.k = 19 ∧ decodeCall e = some (.deposit e.caller e.value)) := by
  simp only [links, List.mem_cons, List.not_mem_nil, or_false] at hl
  unfold decodeCall
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h : Sevm.selector e = 0x06fdde03 := hsel.trans (by decide)
    left
    exact ⟨by decide, by simp (config := { decide := true }) only [hshort, ↓reduceIte, h, or_self,
      or_false]⟩
  · have h : Sevm.selector e = 0x095ea7b3 := hsel.trans (by decide)
    right; right; right; right; left
    exact ⟨rfl, by simp (config := { decide := true }) only [hshort, ↓reduceIte, h]⟩
  · have h : Sevm.selector e = 0x18160ddd := hsel.trans (by decide)
    left
    exact ⟨by decide, by simp (config := { decide := true }) only [hshort, ↓reduceIte, h, or_self,
      or_false, or_true]⟩
  · have h : Sevm.selector e = 0x23b872dd := hsel.trans (by decide)
    right; right; right; left
    exact ⟨rfl, by simp (config := { decide := true }) only [hshort, ↓reduceIte, h]⟩
  · have h : Sevm.selector e = 0x2e1a7d4d := hsel.trans (by decide)
    right; left
    exact ⟨rfl, by simp (config := { decide := true }) only [hshort, ↓reduceIte, h]⟩
  · have h : Sevm.selector e = 0x313ce567 := hsel.trans (by decide)
    left
    exact ⟨by decide, by simp (config := { decide := true }) only [hshort, ↓reduceIte, h, or_self,
      or_false, or_true]⟩
  · have h : Sevm.selector e = 0x70a08231 := hsel.trans (by decide)
    left
    exact ⟨by decide, by simp (config := { decide := true }) only [hshort, ↓reduceIte, h, or_self,
      or_false, or_true]⟩
  · have h : Sevm.selector e = 0x95d89b41 := hsel.trans (by decide)
    left
    exact ⟨by decide, by simp (config := { decide := true }) only [hshort, ↓reduceIte, h,
      or_false, or_true]⟩
  · have h : Sevm.selector e = 0xa9059cbb := hsel.trans (by decide)
    right; right; left
    exact ⟨rfl, by simp (config := { decide := true }) only [hshort, ↓reduceIte, h]⟩
  · have h : Sevm.selector e = 0xd0e30db0 := hsel.trans (by decide)
    right; right; right; right; right
    exact ⟨rfl, by simp (config := { decide := true }) only [hshort, ↓reduceIte, h]⟩
  · have h : Sevm.selector e = 0xdd62ed3e := hsel.trans (by decide)
    left
    exact ⟨by decide, by simp (config := { decide := true }) only [hshort, ↓reduceIte, h, or_true]⟩

/-- The exact effect of entry 9 is the storage step of `transferFrom`. -/
theorem xferStorStep_of_okX {sevm : Sevm} {d : Devm} {o : Outcome} {wad dstW srcW : B256}
    (h : Weth9.XferOkX sevm d o wad dstW srcW) :
    xferStorStep (Devm.getStor d sevm.currentTarget) sevm.caller srcW.toAdr dstW.toAdr wad =
      some (Devm.getStor (Outcome.devm o) sevm.currentTarget) := by
  obtain ⟨⟨-, hbranch⟩, hle⟩ := h
  have hnlt : ¬ (Devm.getStor d sevm.currentTarget).get (balSlot srcW.toAdr) < wad :=
    B256.not_lt.mpr hle
  have hA : (Devm.getStor d sevm.currentTarget).get (allowSlot srcW.toAdr sevm.caller) =
      Weth9.allowWord sevm d srcW := rfl
  unfold xferStorStep
  simp only [hnlt, ↓reduceIte]
  rcases hbranch with ⟨hc, hs⟩ | ⟨hne, hmax, hle', hs⟩
  · have hcond : ¬ (srcW.toAdr ≠ sevm.caller ∧
        (Devm.getStor d sevm.currentTarget).get (allowSlot srcW.toAdr sevm.caller) ≠ B256.max) := by
      rintro ⟨h1, h2⟩
      rcases hc with hc | hc
      · exact h1 (toB256_inj hc)
      · exact h2 (hA.trans hc)
    simp only [hcond, ↓reduceIte]
    rw [hs]
  · have hcond : srcW.toAdr ≠ sevm.caller ∧
        (Devm.getStor d sevm.currentTarget).get (allowSlot srcW.toAdr sevm.caller) ≠ B256.max :=
      ⟨fun h' => hne (by rw [h']), by rw [hA]; exact hmax⟩
    have hnlt2 : ¬ (Devm.getStor d sevm.currentTarget).get (allowSlot srcW.toAdr sevm.caller) <
        wad := by
      rw [hA]
      exact B256.not_lt.mpr hle'
    simp only [hcond, hnlt2, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
    rw [hs]
    rfl

/-- **A successful WETH9 frame's effect, by the call it decodes.**  A view keeps the storage; a writer
other than `withdraw` has exactly `Call.stor`'s effect (which includes the `require`s: `Call.stor` is
`some` only if the run does not revert); `withdraw` is not described here — its run contains the
`CALL` (`wrapper24_hasCall`), and its debit and re-entered effects are the chain analysis of
`WithdrawReach.lean`. -/
theorem weth9_frame_effect {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {sevm : Sevm} {pre post : Devm}
    (hfork : CoveredFork sevm.benvStat.fork) (hrun : SProg.RunP P prog sevm pre post) :
    (decodeCall sevm = none ∧
      Devm.getStor post sevm.currentTarget = Devm.getStor pre sevm.currentTarget) ∨
    (∃ c, decodeCall sevm = some c ∧ (∀ who w, c ≠ .withdraw who w) ∧
      c.stor (Devm.getStor pre sevm.currentTarget) = some (Devm.getStor post sevm.currentTarget)) ∨
    (∃ who w, decodeCall sevm = some (.withdraw who w) ∧ ∃ s sf : Devm, P sevm s (.exec .call) sf) := by
  rcases weth9_route hP hrun with ⟨hmiss, d', hs, run⟩ | ⟨l, hl, hshort, hsel, g, d', hg, hs, run⟩
  · right; left
    refine ⟨_, decode_miss hmiss, (fun _ _ h => by cases h), ?_⟩
    rw [tree_00af] at run
    obtain ⟨hst, -⟩ := depositCall_effect hfork (f := t_00b7_c0) (by decide) (by decide)
      (run.mono hP)
    simp only [Outcome.devm] at hst
    simp only [Call.stor]
    rw [hst, hs.stor]
  · rcases decode_hit hshort hl hsel with ⟨hk, hd⟩ | ⟨hk, hd⟩ | ⟨hk, hd⟩ | ⟨hk, hd⟩ | ⟨hk, hd⟩ |
        ⟨hk, hd⟩
    · left
      refine ⟨hd, ?_⟩
      have h := viewWrapper_state hP hk hg run
      simp only [Outcome.devm] at h
      exact (getStor_eq_of_state_eq h sevm.currentTarget).trans (congrFun hs.stor.symm _)
    · right; right
      refine ⟨_, _, hd, ?_⟩
      rw [hk] at hg
      have hg' : g = t_0243_c24 := Option.some.inj (hg.symm.trans wrapper24_lookup)
      subst hg'
      exact wrapper24_hasCall hP run
    · right; left
      refine ⟨_, hd, (fun _ _ h => by cases h), ?_⟩
      rw [hk] at hg
      have hok := (Weth9.transfer_wrapper_okX hg (run.mono hP)).of_same hs
      have := xferStorStep_of_okX hok
      simp only [Outcome.devm, toAdr_toB256] at this
      simpa only [Call.stor] using this
    · right; left
      refine ⟨_, hd, (fun _ _ h => by cases h), ?_⟩
      rw [hk] at hg
      have hok := (Weth9.transferFrom_wrapper_okX hg (run.mono hP)).of_same hs
      have := xferStorStep_of_okX hok
      simp only [Outcome.devm, toAdr_toB256] at this
      simpa only [Call.stor] using this
    · right; left
      refine ⟨_, hd, (fun _ _ h => by cases h), ?_⟩
      rw [hk] at hg
      obtain ⟨-, hst⟩ := approve_wrapper_ok hg (run.mono hP)
      simp only [Outcome.devm] at hst
      simp only [Call.stor]
      rw [hst, hs.stor]
    · right; left
      refine ⟨_, hd, (fun _ _ h => by cases h), ?_⟩
      rw [hk] at hg
      have hg' : g = t_03ca_c19 := by simpa only [prog, Cert.prog, cert, List.map_cons,
        List.map_nil, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT,
        getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero, Option.some.injEq] using
        hg.symm
      subst hg'
      rw [tree_03ca] at run
      obtain ⟨hst, -⟩ := depositCall_effect hfork (f := t_03d2_c19) (by decide) (by decide)
        (run.mono hP)
      simp only [Outcome.devm] at hst
      simp only [Call.stor]
      rw [hst, hs.stor]

end Blanc.Lift.Weth9
