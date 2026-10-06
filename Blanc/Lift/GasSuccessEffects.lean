import Blanc.Lift.GasSuccessCut

/-!
# Additional-gas transport through effectful selected paths

The reference walk supplies actual affordability and branch selection. Gas
observations and external calls are excluded by a checked selected-path fact.
-/

namespace Blanc.Lift.GasSuccess

open Jaune Blanc.Lift.Witness

theorem sload_addGas {s : Sevm} {c c' : Cfg} {f : SFunc}
    (h : sloadStep s c f = some c') (δ : Nat) :
    sloadStep s (addCfgGas c δ) f = some (addCfgGas c' δ) := by
  change sloadStep s { c with devm := addGas c.devm δ } f = _
  unfold sloadStep at h ⊢
  simp only [addGas_stack]
  cases hs : c.devm.stack with
  | nil => simp only [hs] at h; cases h
  | cons k stack =>
    simp only [hs] at h ⊢
    split at h
    · rename_i guard
      simp only [guard]
      split at h
      · rename_i warm
        simp only [warm, ite_true, addGas, Devm.withGasLeft, Devm.gasLeft, Devm.setMach]
        split at h
        · rename_i affordable
          have ha : gasWarmAccess ≤ c.devm.gasLeft + δ := by omega
          have he : c.devm.gasLeft + δ - gasWarmAccess =
              c.devm.gasLeft - gasWarmAccess + δ := by omega
          cases h
          simp only [mach', addCfgGas, addGas, Devm.withGasLeft,
            Devm.setMach, Devm.gasLeft, Devm.memory, Devm.stateGas] at *
          simp only [ha, and_self, ite_true, he]
        · cases h
      · rename_i cold
        simp only [cold, ite_false, addGas, Devm.withGasLeft, Devm.gasLeft, Devm.setMach]
        split at h
        · rename_i affordable
          have ha : gasColdSload ≤ c.devm.gasLeft + δ := by omega
          have he : c.devm.gasLeft + δ - gasColdSload =
              c.devm.gasLeft - gasColdSload + δ := by omega
          cases h
          simp only [addCfgGas, addGas, Devm.withGasLeft,
            Devm.setMach, Devm.gasLeft, Devm.memory, Devm.stateGas,
            addAccessedStorageKey, liftMachMetaPure] at *
          simp only [ha, and_self, ite_true, he]
        · cases h
    · cases h

/-- Hash input, memory expansion and hash cost do not depend on execution gas. -/
theorem keccak_addGas {c c' : Cfg} {f : SFunc}
    (h : keccakStep c f = some c') (δ : Nat) :
    keccakStep (addCfgGas c δ) f = some (addCfgGas c' δ) := by
  unfold keccakStep at h ⊢
  cases hs : c.devm.stack with
  | nil => simp only [hs] at h; cases h
  | cons i tail =>
    cases tail with
    | nil => simp only [hs] at h; cases h
    | cons sz stack =>
      simp only [hs] at h
      split at h
      · rename_i affordable
        have ha : gKeccak256 + gasKeccak256Word * ceilDiv sz.toNat 32 +
            c.devm.extCost [⟨i.toNat, sz.toNat⟩] ≤ c.devm.gasLeft + δ ∧
            stack.length < 1024 := by omega
        have he : c.devm.gasLeft + δ - (gKeccak256 + gasKeccak256Word * ceilDiv sz.toNat 32 +
            c.devm.extCost [⟨i.toNat, sz.toNat⟩]) =
            c.devm.gasLeft - (gKeccak256 + gasKeccak256Word * ceilDiv sz.toNat 32 +
            c.devm.extCost [⟨i.toNat, sz.toNat⟩]) + δ := by omega
        cases h
        simp only [addCfgGas, addGas, Devm.withGasLeft, Devm.setMach,
          Devm.stack, Devm.memory, Devm.gasLeft, Devm.stateGas, Devm.extCost] at *
        simp only [hs, ha, and_self, ite_true, he]
      · cases h

/-- Original reads, warmth, refund arithmetic and writes are identical. The
reference success supplies the state-gas restriction and SSTORE sentry. -/
theorem sstore_addGas {s : Sevm} {c c' : Cfg} {f : SFunc}
    (h : sstoreStep s c f = some c') (δ : Nat) :
    sstoreStep s (addCfgGas c δ) f = some (addCfgGas c' δ) := by
  change sstoreStep s { c with devm := addGas c.devm δ } f = _
  unfold sstoreStep at h ⊢
  simp only [addGas_stack]
  cases hs : c.devm.stack with
  | nil => simp only [hs] at h; cases h
  | cons k tail =>
    cases tail with
    | nil => simp only [hs] at h; cases h
    | cons v stack =>
      simp only [hs] at h ⊢
      split at h
      · rename_i guard
        have hg : s.benvStat.rules.stateGas.isNone ∧
            gCallStipend < c.devm.gasLeft + δ ∧ s.isStatic = false := by
          obtain ⟨hsg, hsent, hstatic⟩ := guard
          exact ⟨hsg, by omega, hstatic⟩
        simp only [addGas, Devm.withGasLeft, Devm.gasLeft, Devm.setMach] at hg ⊢
        simp only [hg, and_self, ite_true]
        by_cases warm : (s.currentTarget, k) ∈ c.keys
        · simp only [warm, ite_true] at h ⊢
          split at h
          · rename_i affordable
            have ha : sstoreValueCost (getOrigStorVal s s.currentTarget k)
                (lookupS c.stor s.currentTarget k) v ≤ c.devm.gasLeft + δ := by omega
            have he : c.devm.gasLeft + δ - sstoreValueCost (getOrigStorVal s s.currentTarget k)
                (lookupS c.stor s.currentTarget k) v =
                c.devm.gasLeft - sstoreValueCost (getOrigStorVal s s.currentTarget k)
                (lookupS c.stor s.currentTarget k) v + δ := by omega
            cases h
            simp only [addCfgGas, addGas, Devm.withGasLeft, Devm.setMach, Devm.gasLeft,
              Devm.memory, Devm.stateGas, Devm.withRefundCounter, Devm.refundCounter,
              Devm.setStorVal, Devm.withState, Devm.state] at *
            simp only [ha, ite_true, he]
            rfl
          · cases h
        · simp only [warm, ite_false] at h ⊢
          split at h
          · rename_i affordable
            have ha : gasColdSload + sstoreValueCost (getOrigStorVal s s.currentTarget k)
                (lookupS c.stor s.currentTarget k) v ≤ c.devm.gasLeft + δ := by omega
            have he : c.devm.gasLeft + δ - (gasColdSload +
                sstoreValueCost (getOrigStorVal s s.currentTarget k) (lookupS c.stor s.currentTarget k) v) =
                c.devm.gasLeft - (gasColdSload +
                sstoreValueCost (getOrigStorVal s s.currentTarget k) (lookupS c.stor s.currentTarget k) v) + δ := by omega
            cases h
            simp only [addCfgGas, addGas, Devm.withGasLeft, Devm.setMach, Devm.gasLeft,
              Devm.memory, Devm.stateGas, Devm.withRefundCounter, Devm.refundCounter,
              Devm.setStorVal, Devm.withState, Devm.state, addAccessedStorageKey,
              liftMachMetaPure] at *
            simp only [ha, ite_true, he]
            rfl
          · cases h
      · cases h

/-- LOG changes the same metadata and memory at every larger budget. -/
theorem log_addGas {s : Sevm} {c c' : Cfg} {f : SFunc} (n : Fin 5)
    (h : logStep s n c f = some c') (δ : Nat) :
    logStep s n (addCfgGas c δ) f = some (addCfgGas c' δ) := by
  unfold logStep at h ⊢
  cases hs : c.devm.stack with
  | nil => simp only [hs] at h; cases h
  | cons i tail =>
    cases tail with
    | nil => simp only [hs] at h; cases h
    | cons sz rest =>
      simp only [hs] at h
      split at h
      · rename_i affordable
        have ha : n.val ≤ rest.length ∧ s.isStatic = false ∧
            gLog + gLogdata * sz.toNat + gLogtopic * n.val +
              c.devm.extCost [⟨i.toNat, sz.toNat⟩] ≤ c.devm.gasLeft + δ := by
          obtain ⟨hn, hstatic, hcost⟩ := affordable
          exact ⟨hn, hstatic, by omega⟩
        have he : c.devm.gasLeft + δ - (gLog + gLogdata * sz.toNat + gLogtopic * n.val +
            c.devm.extCost [⟨i.toNat, sz.toNat⟩]) =
            c.devm.gasLeft - (gLog + gLogdata * sz.toNat + gLogtopic * n.val +
            c.devm.extCost [⟨i.toNat, sz.toNat⟩]) + δ := by omega
        cases h
        simp only [addCfgGas, addGas, Devm.withGasLeft, Devm.setMach,
          Devm.stack, Devm.memory, Devm.gasLeft, Devm.stateGas, Devm.extCost] at *
        simp only [hs, ha, and_self, ite_true, he]
        rfl
      · cases h

/-- CALLDATALOAD is a fixed-price unary read from the static calldata. -/
theorem calldataload_stable (pc : Nat) (s : Sevm) :
    ExecStable (fun d => Rinst.runCore pc d s .calldataload) := by
  intro d d' h δ
  simp only [Rinst.runCore] at h ⊢
  cases hp : d.pop with
  | error e => simp only [hp, bind, Except.bind] at h; cases h
  | ok out =>
    rcases out with ⟨i, d₁⟩
    rw [pop_addGas hp δ]
    simp only [hp, bind, Except.bind] at h ⊢
    cases hc : chargeGas gVerylow d₁ with
    | error e => simp only [hc] at h; cases h
    | ok d₂ =>
      rw [charge_exec_stable _ d₁ d₂ hc δ]
      simp only [hc] at h ⊢
      exact push_exec_stable _ d₂ d' h δ

/-- Additional environment reads needed by effectful paths. -/
def environment : Rinst → Bool
  | .address | .caller | .callvalue | .calldataload | .returndatasize | .timestamp => true
  | _ => false

theorem environment_stable (r : Rinst) (hr : environment r = true) (pc : Nat) (s : Sevm) :
    ExecStable (fun d => Rinst.runCore pc d s r) := by
  cases r <;> simp only [environment, Bool.false_eq_true] at hr
  case address => exact pushItem_exec_stable s.currentTarget.toB256 gBase
  case caller => exact pushItem_exec_stable s.caller.toB256 gBase
  case callvalue => exact pushItem_exec_stable s.value gBase
  case calldataload => exact calldataload_stable pc s
  case timestamp => exact pushItem_exec_stable s.benvStat.time gBase
  case returndatasize =>
    intro d d' h δ
    exact pushItem_exec_stable d.returnData.length.toB256 gBase d d' h δ

/-- A payload-returning normalized operation lifts with the same gas relation. -/
theorem lift_payload_stable {α : Type} {f : Mach → Footprint.Outcome Mach α}
    (hf : Stable f) {d d' : Devm} {v : α}
    (h : liftMach f d = .ok (v, d')) (δ : Nat) :
    liftMach f (addGas d δ) = .ok (v, addGas d' δ) := by
  rcases d with ⟨m, view, world⟩
  unfold liftMach Footprint.liftOutcome at h ⊢
  cases hp : f m with
  | error e => simp only [hp] at h; cases h
  | ok out =>
    rcases out with ⟨u, m'⟩
    simp only [hp] at h
    have he : f (addGas ⟨m, view, world⟩ δ).mach = .ok (u, addMachGas m' δ) :=
      hf m u m' hp δ
    rw [he]
    cases h
    rfl

theorem popToNat_stable : Stable Mach.popToNat := by
  intro m x m' h δ
  unfold Mach.popToNat at h ⊢
  cases hp : Mach.pop m with
  | error e => rw [hp] at h; cases h
  | ok out =>
    rcases out with ⟨v, m₁⟩
    rw [pop_stable m v m₁ hp δ]
    rw [hp] at h
    cases h
    rfl

/-- RETURN's read and output update commute with additional gas. -/
theorem return_stable (s : Sevm) : ExecStable (fun d => Linst.run s d .return_) := by
  intro d d' h δ
  simp only [Linst.run] at h ⊢
  cases hp : d.popToNat with
  | error e => simp only [hp, bind, Except.bind] at h; cases h
  | ok out =>
    rcases out with ⟨i, d₁⟩
    have hpδ : (addGas d δ).popToNat = .ok (i, addGas d₁ δ) :=
      lift_payload_stable popToNat_stable hp δ
    rw [hpδ]
    simp only [hp, bind, Except.bind] at h ⊢
    cases hq : d₁.popToNat with
    | error e => simp only [hq] at h; cases h
    | ok out =>
      rcases out with ⟨sz, d₂⟩
      have hqδ : (addGas d₁ δ).popToNat = .ok (sz, addGas d₂ δ) :=
        lift_payload_stable popToNat_stable hq δ
      rw [hqδ]
      simp only [hq] at h ⊢
      cases hc : chargeGas (d₂.extCost [⟨i, sz⟩]) d₂ with
      | error e => simp only [hc] at h; cases h
      | ok d₃ =>
        have hcost : (addGas d₂ δ).extCost [⟨i, sz⟩] = d₂.extCost [⟨i, sz⟩] := rfl
        rw [hcost, charge_exec_stable _ d₂ d₃ hc δ]
        simp only [hc] at h ⊢
        cases h
        rfl

/-- Effectful next-node support; unused successor branches remain unrestricted. -/
def effectSupported : SFunc → Bool
  | .next (.reg .sload) _ | .next (.reg .sstore) _ | .next (.reg .keccak256) _
  | .next (.reg (.log _)) _ | .last .return_ => true
  | .next (.reg r) f => environment r || supported (.next (.reg r) f)
  | f => supported f

theorem wstep_environment (fs : List SFunc) (s : Sevm) (c : Cfg) (r : Rinst) (f : SFunc)
    (hr : environment r = true) :
    wstep fs s { c with f := .next (.reg r) f } =
      match Ninst.step ⟨0, s, c.devm⟩ (.reg r) with
      | .cont _ d => .cont { c with devm := d, f := f }
      | _ => .stuck := by
  cases r <;> simp only [environment, Bool.false_eq_true] at hr
  all_goals rfl

theorem next_environment_addGas {fs : List SFunc} {s : Sevm} {c c' : Cfg}
    {r : Rinst} {f : SFunc} (hr : environment r = true)
    (h : wstep fs s { c with f := .next (.reg r) f } = .cont c') (δ : Nat) :
    wstep fs s (addCfgGas { c with f := .next (.reg r) f } δ) = .cont (addCfgGas c' δ) := by
  rw [wstep_environment fs s c r f hr] at h
  change wstep fs s { addCfgGas c δ with f := .next (.reg r) f } = _
  rw [wstep_environment fs s (addCfgGas c δ) r f hr]
  cases hs : Ninst.step ⟨0, s, c.devm⟩ (.reg r) with
  | halt out => simp only [hs] at h; cases h
  | spawn fr resume pc => simp only [hs] at h; cases h
  | cont pc d =>
    simp only [hs] at h
    cases h
    have ht := step_ofExecution_stable (environment_stable r hr 0 s)
      (by simpa only [Ninst.step_reg, Rinst.run] using hs) δ
    dsimp only [addCfgGas]
    simpa only [Ninst.step_reg, Rinst.run] using congrArg (fun x => match x with
      | .cont _ d => Res.cont { c with devm := d, f := f }
      | _ => Res.stuck) ht

/-- Continuation steps, including persistent effects, preserve every non-gas column. -/
theorem wstep_effect_addGas {fs : List SFunc} {s : Sevm} {c c' : Cfg}
    (hc : effectSupported c.f = true) (h : wstep fs s c = .cont c') (δ : Nat) :
    wstep fs s (addCfgGas c δ) = .cont (addCfgGas c' δ) := by
  by_cases old : supported c.f = true
  · exact wstep_addGas old h δ
  rcases c with ⟨d, f, K, keys, adrs, stor, acs⟩
  cases f <;> simp only [effectSupported, supported, Bool.false_eq_true] at hc old
  all_goals try contradiction
  case next n f =>
    cases n <;> simp only [ordinary, Bool.false_eq_true] at hc old
    all_goals try contradiction
    case reg r =>
      cases r <;> simp only [environment, regular, arithmetic,
        Bool.or_eq_true, Bool.false_eq_true, or_false] at hc old
      all_goals try contradiction
      case sload =>
        dsimp only [wstep, addCfgGas] at h ⊢
        cases hm : sloadStep s ⟨d, .next (.reg .sload) f, K, keys, adrs, stor, acs⟩ f with
        | none => simp only [hm] at h; cases h
        | some out =>
          simp only [hm] at h
          have ht := sload_addGas hm δ
          dsimp only [addCfgGas] at ht
          rw [ht]
          cases h
          rfl
      case sstore =>
        dsimp only [wstep, addCfgGas] at h ⊢
        cases hm : sstoreStep s ⟨d, .next (.reg .sstore) f, K, keys, adrs, stor, acs⟩ f with
        | none => simp only [hm] at h; cases h
        | some out =>
          simp only [hm] at h
          have ht := sstore_addGas hm δ
          dsimp only [addCfgGas] at ht
          rw [ht]
          cases h
          rfl
      case keccak256 =>
        dsimp only [wstep, addCfgGas] at h ⊢
        cases hm : keccakStep ⟨d, .next (.reg .keccak256) f, K, keys, adrs, stor, acs⟩ f with
        | none => simp only [hm] at h; cases h
        | some out =>
          simp only [hm] at h
          have ht := keccak_addGas hm δ
          dsimp only [addCfgGas] at ht
          rw [ht]
          cases h
          rfl
      case log n =>
        dsimp only [wstep, addCfgGas] at h ⊢
        cases hm : logStep s n ⟨d, .next (.reg (.log n)) f, K, keys, adrs, stor, acs⟩ f with
        | none => simp only [hm] at h; cases h
        | some out =>
          simp only [hm] at h
          have ht := log_addGas n hm δ
          dsimp only [addCfgGas] at ht
          rw [ht]
          cases h
          rfl
      all_goals exact next_environment_addGas (c := ⟨d, .undefined, K, keys, adrs, stor, acs⟩) rfl h δ
  case last l =>
    cases l <;> simp only [Bool.false_eq_true] at hc
    dsimp only [wstep] at h
    cases hl : Linst.run s d .return_ <;> simp only [hl, reduceCtorEq] at h

/-- This unit's supported successful terminal is RETURN. -/
def terminalSupported : SFunc → Bool
  | .last .return_ => true
  | _ => false

/-- Fund a successful RETURN, including the producing configuration. -/
theorem wstep_return_addGas {fs : List SFunc} {s : Sevm} {c cl : Cfg} {d : Devm}
    (hc : terminalSupported c.f = true) (h : wstep fs s c = .done (.halted d) cl) (δ : Nat) :
    wstep fs s (addCfgGas c δ) = .done (.halted (addGas d δ)) (addCfgGas cl δ) := by
  rcases c with ⟨d₀, f, K, keys, adrs, stor, acs⟩
  cases f <;> simp only [terminalSupported, Bool.false_eq_true] at hc
  case last l =>
    cases l <;> simp only [Bool.false_eq_true] at hc
    dsimp only [wstep, addCfgGas] at h ⊢
    cases hl : Linst.run s d₀ .return_ with
    | error e => simp only [hl] at h; cases h
    | ok out =>
      simp only [hl] at h
      cases h
      have ht : Linst.run s (addGas d₀ δ) .return_ = .ok (addGas d δ) :=
        return_stable s d₀ d hl δ
      rw [ht]

/-- Additional gas on interpreter results, retaining terminal bookkeeping. -/
def addResGas (r : Res) (δ : Nat) : Res :=
  match r with
  | .cont c => .cont (addCfgGas c δ)
  | .done (.halted d) c => .done (.halted (addGas d δ)) (addCfgGas c δ)
  | .done (.returned d) c => .done (.returned (addGas d δ)) (addCfgGas c δ)
  | .stuck => .stuck

/-- Certificate over the single selected reference path, including RETURN.
No desired alternate execution appears in this predicate. -/
def selectedEffects (fs : List SFunc) (s : Sevm) : Nat → Cfg → Bool
  | 0, _ => true
  | n + 1, c => match wstep fs s c with
    | .cont c' => effectSupported c.f && selectedEffects fs s n c'
    | .done (.halted _) _ => terminalSupported c.f
    | _ => false

/-- Every certified path succeeds with additional gas; terminal machines and
all continuation/shadow columns retain the same exact gas offset. -/
theorem wrun_effect_addGas {fs : List SFunc} {s : Sevm} {n : Nat} {c : Cfg}
    (hc : selectedEffects fs s n c = true) (δ : Nat) :
    wrun fs s n (addCfgGas c δ) = addResGas (wrun fs s n c) δ := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [selectedEffects] at hc
    cases hs : wstep fs s c with
    | stuck => simp only [hs, Bool.false_eq_true] at hc
    | cont mid =>
      simp only [hs, Bool.and_eq_true] at hc
      rw [wrun, wstep_effect_addGas hc.1 hs δ]
      simpa only [wrun, hs] using ih hc.2
    | done out cl =>
      cases out with
      | returned d => simp only [hs, Bool.false_eq_true] at hc
      | halted d =>
        simp only [hs] at hc
        rw [wrun, wstep_return_addGas hc hs δ]
        simp only [wrun, hs, addResGas]

/-- The reference certificate also excludes a stuck run. -/
theorem selectedEffects_not_stuck {fs : List SFunc} {s : Sevm} {n : Nat} {c : Cfg}
    (hc : selectedEffects fs s n c = true) : wrun fs s n c ≠ .stuck := by
  induction n generalizing c with
  | zero => intro h; cases h
  | succ n ih =>
    simp only [selectedEffects] at hc
    cases hs : wstep fs s c with
    | stuck => simp only [hs, Bool.false_eq_true] at hc
    | cont mid =>
      simp only [hs, Bool.and_eq_true] at hc
      simpa only [wrun, hs] using ih hc.2
    | done out cl =>
      simp only [wrun, hs]
      intro h
      cases h

/-- Every earlier pure-cut certificate is reusable without another reference replay. -/
theorem supported_effectSupported {f : SFunc} (h : supported f = true) :
    effectSupported f = true := by
  cases f <;> simp only [supported, effectSupported, Bool.false_eq_true] at h ⊢
  case next n f =>
    cases n <;> simp only [ordinary, Bool.false_eq_true] at h ⊢
    case reg r =>
      cases r <;> simp only [environment, regular, arithmetic, Bool.false_eq_true,
        Bool.or_true] at h ⊢

/-- Reuse a previously checked selected cut in a complete effectful frame. -/
theorem selected_to_effects {fs : List SFunc} {s : Sevm} {n : Nat} {c : Cfg}
    (h : selected fs s n c = true) : selectedEffects fs s n c = true := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [selected, Bool.and_eq_true] at h
    simp only [selectedEffects]
    cases hs : wstep fs s c with
    | stuck => simp only [hs, Bool.false_eq_true] at h; exact h.2.elim
    | done out cl => simp only [hs, Bool.false_eq_true] at h; exact h.2.elim
    | cont mid =>
      simp only [hs] at h ⊢
      rw [supported_effectSupported h.1]
      simpa only [Bool.true_and] using ih h.2

/-- Concatenate reference certificates through a previously checked continuing endpoint. -/
theorem selectedEffects_add_cont {fs : List SFunc} {s : Sevm} {n m : Nat} {c mid : Cfg}
    (hc : selectedEffects fs s n c = true) (hr : wrun fs s n c = .cont mid)
    (hm : selectedEffects fs s m mid = true) : selectedEffects fs s (n + m) c = true := by
  induction n generalizing c with
  | zero =>
    cases hr
    simpa only [Nat.zero_add] using hm
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [selectedEffects] at hc ⊢
    cases hs : wstep fs s c with
    | stuck => simp only [hs, Bool.false_eq_true] at hc
    | done out cl => simp only [wrun, hs] at hr; cases hr
    | cont next =>
      simp only [hs, Bool.and_eq_true] at hc
      simp only [wrun, hs] at hr
      simp only [hc.1, Bool.true_and]
      exact ih hc.2 hr

/-- Shadow agreement does not inspect execution gas. -/
theorem agree_addCfgGas (c : Cfg) (δ : Nat) : Agree (addCfgGas c δ) ↔ Agree c := Iff.rfl

/-- A certified complete path certifies every earlier cut without a new replay. -/
theorem selectedEffects_prefix {fs : List SFunc} {s : Sevm} {n m : Nat} {c : Cfg}
    (hm : m ≤ n) (hc : selectedEffects fs s n c = true) :
    selectedEffects fs s m c = true := by
  induction n generalizing m c with
  | zero =>
    have he : m = 0 := by omega
    subst m
    rfl
  | succ n ih =>
    cases m with
    | zero => rfl
    | succ m =>
      simp only [selectedEffects] at hc ⊢
      cases hs : wstep fs s c with
      | stuck => simp only [hs, Bool.false_eq_true] at hc
      | done out cl =>
        cases out with
        | returned d => simp only [hs, Bool.false_eq_true] at hc
        | halted d => simpa only [hs] using hc
      | cont mid =>
        simp only [hs, Bool.and_eq_true] at hc
        simp only [hc.1, Bool.true_and]
        exact ih (by omega) hc.2

end Blanc.Lift.GasSuccess
