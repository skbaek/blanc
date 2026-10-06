import Blanc.Lift.Witness

/-!
# Successful selected cuts with additional execution gas

Gas-only transport uses one successful reference path.  A selected cut must
avoid instructions that observe gas or enter an external frame.
-/

namespace Blanc.Lift.GasSuccess

open Jaune Blanc.Lift.Witness

/-- Add execution gas without changing any other machine column. -/
def addGas (d : Devm) (δ : Nat) : Devm := d.withGasLeft (d.gasLeft + δ)

theorem addGas_stack (d : Devm) (δ : Nat) : (addGas d δ).stack = d.stack := rfl

/-- The corresponding update of a normalized machine footprint. -/
def addMachGas (m : Mach) (δ : Nat) : Mach := { m with gasLeft := m.gasLeft + δ }

/-- Success transport for a normalized core, including its returned payload. -/
def Stable {α : Type} (f : Mach → Footprint.Outcome Mach α) : Prop :=
  ∀ m x m', f m = .ok (x, m') → ∀ δ,
    f (addMachGas m δ) = .ok (x, addMachGas m' δ)

theorem charge_stable (cost : Nat) : Stable (Mach.chargeGas cost) := by
  intro m x m' h δ
  unfold Mach.chargeGas safeSub at h ⊢
  by_cases affordable : cost ≤ m.gasLeft
  · have ha : cost ≤ (addMachGas m δ).gasLeft := by
      change cost ≤ m.gasLeft + δ
      omega
    simp only [affordable, ha, ite_true] at h ⊢
    cases h
    have he : m.gasLeft + δ - cost = m.gasLeft - cost + δ := by omega
    simp only [addMachGas, he]
  · simp only [affordable, ite_false] at h
    cases h

theorem push_stable (v : B256) : Stable (Mach.push v) := by
  intro m x m' h δ
  unfold Mach.push at h ⊢
  dsimp only [addMachGas] at *
  split at h
  · rename_i room
    simp only [room, ite_true]
    cases h
    rfl
  · cases h

theorem pop_stable : Stable Mach.pop := by
  intro m x m' h δ
  unfold Mach.pop at h ⊢
  simp only [addMachGas] at *
  cases hs : m.stack with
  | nil => simp only [hs] at h; cases h
  | cons v s =>
    simp only [hs] at h ⊢
    cases h
    rfl

theorem pushItem_stable (v : B256) (cost : Nat) : Stable (Mach.pushItem v cost) := by
  intro m x m' h δ
  unfold Mach.pushItem at h ⊢
  cases hc : Mach.chargeGas cost m with
  | error e => rw [hc] at h; cases h
  | ok out =>
    rcases out with ⟨u, m₁⟩
    rw [charge_stable cost m u m₁ hc δ]
    rw [hc] at h
    exact push_stable v m₁ x m' h δ

theorem unary_stable (f : B256 → B256) (cost : Nat) :
    Stable (Mach.applyUnary f cost) := by
  intro m x m' h δ
  unfold Mach.applyUnary at h ⊢
  cases hp : Mach.pop m with
  | error e => rw [hp] at h; cases h
  | ok out =>
    rcases out with ⟨v, m₁⟩
    rw [pop_stable m v m₁ hp δ]
    rw [hp] at h
    exact pushItem_stable (f v) cost m₁ x m' h δ

theorem binary_stable (f : B256 → B256 → B256) (cost : Nat) :
    Stable (Mach.applyBinary f cost) := by
  intro m x m' h δ
  unfold Mach.applyBinary at h ⊢
  cases hp : Mach.pop m with
  | error e => rw [hp] at h; cases h
  | ok out =>
    rcases out with ⟨v, m₁⟩
    rw [pop_stable m v m₁ hp δ]
    rw [hp] at h
    dsimp only at h ⊢
    cases hq : Mach.pop m₁ with
    | error e => rw [hq] at h; cases h
    | ok out =>
      rcases out with ⟨w, m₂⟩
      rw [pop_stable m₁ w m₂ hq δ]
      rw [hq] at h
      exact pushItem_stable (f v w) cost m₂ x m' h δ

/-- Success transport for a complete dynamic-state instruction. -/
def ExecStable (f : Devm → Execution) : Prop :=
  ∀ d d', f d = .ok d' → ∀ δ, f (addGas d δ) = .ok (addGas d' δ)

theorem lift_stable {f : Mach → Footprint.Outcome Mach Unit} (hf : Stable f) :
    ExecStable (liftMachExecution f) := by
  intro d d' h δ
  rcases d with ⟨m, view, world⟩
  unfold liftMachExecution liftMach Footprint.toExecution Footprint.liftOutcome at h ⊢
  cases hr : f m with
  | error e => simp only [hr] at h; cases h
  | ok out =>
    rcases out with ⟨u, m'⟩
    simp only [hr] at h
    cases h
    have he : f (addGas ⟨m, view, world⟩ δ).mach = .ok (u, addMachGas m' δ) :=
      hf m u m' hr δ
    rw [he]
    rfl

/-- Arithmetic operations whose values and prices do not inspect remaining gas. -/
def arithmetic : Rinst → Bool
  | .add | .mul | .sub | .div | .mod | .sdiv | .smod
  | .lt | .gt | .slt | .sgt | .eq | .iszero | .not
  | .and | .or | .xor | .shl | .shr | .sar | .byte | .signextend => true
  | _ => false

theorem arithmetic_stable (r : Rinst) (hr : arithmetic r = true)
    (pc : Nat) (s : Sevm) : ExecStable (fun d => Rinst.runCore pc d s r) := by
  cases r <;> simp only [arithmetic, Bool.false_eq_true] at hr
  all_goals first
    | exact lift_stable (binary_stable _ _)
    | exact lift_stable (unary_stable _ _)

theorem pushItem_exec_stable (v : B256) (cost : Nat) : ExecStable (pushItem v cost) :=
  lift_stable (pushItem_stable v cost)

theorem charge_exec_stable (cost : Nat) : ExecStable (chargeGas cost) :=
  lift_stable (charge_stable cost)

theorem push_exec_stable (v : B256) : ExecStable (Devm.push v) :=
  lift_stable (push_stable v)

theorem pop_addGas {d d' : Devm} {v : B256}
    (h : d.pop = .ok (v, d')) (δ : Nat) :
    (addGas d δ).pop = .ok (v, addGas d' δ) := by
  rcases d with ⟨m, view, world⟩
  unfold Devm.pop liftMach Footprint.liftOutcome at h ⊢
  cases hp : Mach.pop m with
  | error e => simp only [hp] at h; cases h
  | ok out =>
    rcases out with ⟨u, m'⟩
    simp only [hp] at h
    have he : Mach.pop (addGas ⟨m, view, world⟩ δ).mach =
        .ok (u, addMachGas m' δ) := pop_stable m u m' hp δ
    rw [he]
    cases h
    rfl

theorem pop_exec_stable (pc : Nat) (s : Sevm) :
    ExecStable (fun d => Rinst.runCore pc d s .pop) := by
  intro d d' h δ
  simp only [Rinst.runCore] at h ⊢
  cases hp : d.pop with
  | error e => simp only [hp, bind, Except.bind] at h; cases h
  | ok out =>
    rcases out with ⟨v, d₁⟩
    rw [pop_addGas hp δ]
    simp only [hp, bind, Except.bind] at h ⊢
    exact charge_exec_stable gBase d₁ d' h δ

theorem dup_exec_stable (k : Fin 16) (pc : Nat) (s : Sevm) :
    ExecStable (fun d => Rinst.runCore pc d s (.dup k)) := by
  intro d d' h δ
  simp only [Rinst.runCore] at h ⊢
  cases hc : chargeGas gVerylow d with
  | error e => simp only [hc, bind, Except.bind] at h; cases h
  | ok d₁ =>
    rw [charge_exec_stable gVerylow d d₁ hc δ]
    simp only [hc, bind, Except.bind] at h ⊢
    change (match d₁.stack[k]? with
      | none => Except.error (EvmError.halt (.stackUnderflow .none), addGas d₁ δ)
      | some v => (addGas d₁ δ).push v) = _
    cases hs : d₁.stack[k]? with
    | none => simp only [hs] at h; cases h
    | some v =>
      simp only [hs] at h ⊢
      exact push_exec_stable v d₁ d' h δ

theorem swap_exec_stable (k : Fin 16) (pc : Nat) (s : Sevm) :
    ExecStable (fun d => Rinst.runCore pc d s (.swap k)) := by
  intro d d' h δ
  simp only [Rinst.runCore] at h ⊢
  cases hc : chargeGas gVerylow d with
  | error e => simp only [hc, bind, Except.bind] at h; cases h
  | ok d₁ =>
    rw [charge_exec_stable gVerylow d d₁ hc δ]
    simp only [hc, bind, Except.bind] at h ⊢
    change (match Jaune.List.swap d₁.stack k.val with
      | none => Except.error (EvmError.halt (.stackUnderflow .none), addGas d₁ δ)
      | some stack => Except.ok ((addGas d₁ δ).withStack stack)) = _
    cases hs : Jaune.List.swap d₁.stack k.val with
    | none => simp only [hs] at h; cases h
    | some stack =>
      simp only [hs] at h ⊢
      cases h
      rfl

/-- Regular instruction support, excluding memory arms handled by the witness. -/
def regular : Rinst → Bool
  | .pop | .dup _ | .swap _ | .calldatasize => true
  | r => arithmetic r

theorem regular_stable (r : Rinst) (hr : regular r = true) (pc : Nat) (s : Sevm) :
    ExecStable (fun d => Rinst.runCore pc d s r) := by
  cases r <;> simp only [regular, arithmetic, Bool.false_eq_true] at hr
  all_goals first
    | exact pop_exec_stable pc s
    | exact dup_exec_stable _ pc s
    | exact swap_exec_stable _ pc s
    | exact pushItem_exec_stable s.data.length.toB256 gBase
    | exact arithmetic_stable _ rfl pc s

theorem step_ofExecution_stable {f : Devm → Execution} (hf : ExecStable f)
    {d d' : Devm} {p q : Nat} (h : Step.ofExecution p (f d) = .cont q d') (δ : Nat) :
    Step.ofExecution p (f (addGas d δ)) = .cont q (addGas d' δ) := by
  cases hr : f d with
  | error e => simp only [hr, Step.ofExecution] at h; cases h
  | ok out =>
    simp only [hr, Step.ofExecution] at h
    rw [hf d out hr δ]
    cases h
    rfl

/-- Supported ordinary next instructions; memory is checked at the witness arm. -/
def ordinary : Ninst → Bool
  | .push _ _ => true
  | .reg r => regular r
  | _ => false

theorem ordinary_step_stable {n : Ninst} (hn : ordinary n = true)
    {d d' : Devm} {s : Sevm} {p q : Nat}
    (h : Ninst.step ⟨p, s, d⟩ n = .cont q d') (δ : Nat) :
    Ninst.step ⟨p, s, addGas d δ⟩ n = .cont q (addGas d' δ) := by
  cases n with
  | reg r =>
    rw [Ninst.step_reg] at h ⊢
    exact step_ofExecution_stable (regular_stable r hn p s) h δ
  | push xs le =>
    rw [Ninst.step_push] at h ⊢
    rw [← pushItem_def] at h ⊢
    exact step_ofExecution_stable (pushItem_exec_stable _ _) h δ
  | exec x => cases hn
  | dupn x => cases hn
  | swapn x => cases hn
  | exchange x => cases hn

/-- Add gas to a witness configuration, retaining its node and all shadows. -/
def addCfgGas (c : Cfg) (δ : Nat) : Cfg := { c with devm := addGas c.devm δ }

theorem mach_addGas (d : Devm) (stack : List B256) (cost δ : Nat)
    (h : cost ≤ d.gasLeft) :
    mach' (addGas d δ) stack cost = addGas (mach' d stack cost) δ := by
  have he : d.gasLeft + δ - cost = d.gasLeft - cost + δ := by omega
  simp only [mach', addGas, Devm.withGasLeft, Devm.setMach, Devm.gasLeft,
    Devm.memory, Devm.stateGas] at *
  rw [he]

/-- Only the current node is tested; unvisited branches and future cuts are unrestricted. -/
def supported : SFunc → Bool
  | .dest _ | .jump _ | .branch _ _ | .branchTo _ _ | .callNext _ _ | .ret
  | .pcAt _ _ => true
  | .next (.reg .mload) _ | .next (.reg .mstore) _ | .next (.reg .calldatacopy) _ => true
  | .next n _ => ordinary n
  | _ => false

theorem mstore_addGas {c c' : Cfg} {f : SFunc}
    (h : mstoreStep c f = some c') (δ : Nat) :
    mstoreStep (addCfgGas c δ) f = some (addCfgGas c' δ) := by
  unfold mstoreStep at h ⊢
  cases hs : c.devm.stack with
  | nil => simp only [hs] at h; cases h
  | cons i tail =>
    cases tail with
    | nil => simp only [hs] at h; cases h
    | cons v stack =>
      simp only [hs] at h
      split at h
      · rename_i affordable
        have ha : gVerylow + c.devm.extCost [⟨i.toNat, 32⟩] ≤ c.devm.gasLeft + δ := by omega
        have he : c.devm.gasLeft + δ - (gVerylow + c.devm.extCost [⟨i.toNat, 32⟩]) =
            c.devm.gasLeft - (gVerylow + c.devm.extCost [⟨i.toNat, 32⟩]) + δ := by omega
        cases h
        simp only [addCfgGas, addGas, Devm.withGasLeft, Devm.setMach,
          Devm.stack, Devm.memory, Devm.gasLeft, Devm.stateGas, Devm.extCost] at *
        simp only [hs, ha, ite_true, he]
      · cases h

theorem mload_addGas {c c' : Cfg} {f : SFunc}
    (h : mloadStep c f = some c') (δ : Nat) :
    mloadStep (addCfgGas c δ) f = some (addCfgGas c' δ) := by
  unfold mloadStep at h ⊢
  cases hs : c.devm.stack with
  | nil => simp only [hs] at h; cases h
  | cons i stack =>
    simp only [hs] at h
    split at h
    · rename_i affordable
      have ha : gVerylow + c.devm.extCost [⟨i.toNat, 32⟩] ≤ c.devm.gasLeft + δ ∧
          stack.length < 1024 := by omega
      have he : c.devm.gasLeft + δ - (gVerylow + c.devm.extCost [⟨i.toNat, 32⟩]) =
          c.devm.gasLeft - (gVerylow + c.devm.extCost [⟨i.toNat, 32⟩]) + δ := by omega
      cases h
      simp only [addCfgGas, addGas, Devm.withGasLeft, Devm.setMach,
        Devm.stack, Devm.memory, Devm.gasLeft, Devm.stateGas, Devm.extCost] at *
      simp only [hs, ha, and_self, ite_true, he]
    · cases h

theorem calldatacopy_addGas {s : Sevm} {c c' : Cfg} {f : SFunc}
    (h : calldatacopyStep s c f = some c') (δ : Nat) :
    calldatacopyStep s (addCfgGas c δ) f = some (addCfgGas c' δ) := by
  unfold calldatacopyStep at h ⊢
  cases hs : c.devm.stack with
  | nil => simp only [hs] at h; cases h
  | cons di tail =>
    cases tail with
    | nil => simp only [hs] at h; cases h
    | cons si tail =>
      cases tail with
      | nil => simp only [hs] at h; cases h
      | cons sz stack =>
        simp only [hs] at h
        split at h
        · rename_i affordable
          have ha : gVerylow + gasCopy * ceilDiv sz.toNat 32 +
              c.devm.extCost [⟨di.toNat, sz.toNat⟩] ≤ c.devm.gasLeft + δ := by omega
          have he : c.devm.gasLeft + δ - (gVerylow + gasCopy * ceilDiv sz.toNat 32 +
              c.devm.extCost [⟨di.toNat, sz.toNat⟩]) =
              c.devm.gasLeft - (gVerylow + gasCopy * ceilDiv sz.toNat 32 +
              c.devm.extCost [⟨di.toNat, sz.toNat⟩]) + δ := by omega
          cases h
          simp only [addCfgGas, addGas, Devm.withGasLeft, Devm.setMach,
            Devm.stack, Devm.memory, Devm.gasLeft, Devm.stateGas, Devm.extCost] at *
          simp only [hs, ha, ite_true, he]
        · cases h

theorem wstep_ordinary (fs : List SFunc) (s : Sevm) (c : Cfg) (n : Ninst) (f : SFunc)
    (hn : ordinary n = true) :
    wstep fs s { c with f := .next n f } =
      match Ninst.step ⟨0, s, c.devm⟩ n with
      | .cont _ d => .cont { c with devm := d, f := f }
      | _ => .stuck := by
  cases n <;> simp only [ordinary, Bool.false_eq_true] at hn
  case reg r =>
    cases r <;> simp only [regular, arithmetic, Bool.false_eq_true] at hn
    all_goals rfl
  case push xs le => rfl

theorem next_ordinary_addGas {fs : List SFunc} {s : Sevm} {c c' : Cfg}
    {n : Ninst} {f : SFunc} (hn : ordinary n = true)
    (h : wstep fs s { c with f := .next n f } = .cont c') (δ : Nat) :
    wstep fs s (addCfgGas { c with f := .next n f } δ) = .cont (addCfgGas c' δ) := by
  rw [wstep_ordinary fs s c n f hn] at h
  change wstep fs s { addCfgGas c δ with f := .next n f } = _
  rw [wstep_ordinary fs s (addCfgGas c δ) n f hn]
  cases hs : Ninst.step ⟨0, s, c.devm⟩ n with
  | halt out => simp only [hs] at h; cases h
  | spawn fr resume pc => simp only [hs] at h; cases h
  | cont pc d =>
    simp only [hs] at h
    cases h
    dsimp only [addCfgGas]
    rw [ordinary_step_stable hn hs δ]

/-- One supported, successful step can be funded with any additional gas. -/
theorem wstep_addGas {fs : List SFunc} {s : Sevm} {c c' : Cfg}
    (hc : supported c.f = true) (h : wstep fs s c = .cont c') (δ : Nat) :
    wstep fs s (addCfgGas c δ) = .cont (addCfgGas c' δ) := by
  rcases c with ⟨d, f, K, keys, adrs, stor, acs⟩
  cases f with
  | dest f =>
    dsimp only [wstep, addCfgGas] at h ⊢
    simp only [addGas_stack]
    split at h
    · rename_i affordable
      have ha : gJumpdest ≤ (addGas d δ).gasLeft := by change gJumpdest ≤ d.gasLeft + δ; omega
      cases h
      simp only [ha, ite_true]
      rw [mach_addGas d d.stack gJumpdest δ affordable]
    · cases h
  | jump k =>
    dsimp only [wstep, addCfgGas] at h ⊢
    simp only [addGas_stack]
    cases hs : d.stack with
    | nil => simp only [hs] at h; cases h
    | cons v stack =>
      cases hf : fs[k]? with
      | none => simp only [hs, hf] at h; cases h
      | some f =>
        simp only [hs, hf] at h
        split at h
        · rename_i affordable
          have ha : gMid ≤ (addGas d δ).gasLeft := by change gMid ≤ d.gasLeft + δ; omega
          cases h
          simp only [ha, ite_true]
          rw [mach_addGas d stack gMid δ affordable]
        · cases h
  | branch f g =>
    dsimp only [wstep, addCfgGas] at h ⊢
    simp only [addGas_stack]
    cases hs : d.stack with
    | nil => simp only [hs] at h; cases h
    | cons v tail =>
      cases tail with
      | nil => simp only [hs] at h; cases h
      | cons w stack =>
        simp only [hs] at h
        split at h
        · rename_i affordable
          have ha : gHigh ≤ (addGas d δ).gasLeft := by change gHigh ≤ d.gasLeft + δ; omega
          cases h
          simp only [ha, ite_true]
          rw [mach_addGas d stack gHigh δ affordable]
        · cases h
  | branchTo f k =>
    dsimp only [wstep, addCfgGas] at h ⊢
    simp only [addGas_stack]
    cases hs : d.stack with
    | nil => simp only [hs] at h; cases h
    | cons v tail =>
      cases tail with
      | nil => simp only [hs] at h; cases h
      | cons w stack =>
        simp only [hs] at h
        split at h
        · rename_i affordable
          have ha : gHigh ≤ (addGas d δ).gasLeft := by change gHigh ≤ d.gasLeft + δ; omega
          simp only [ha, ite_true]
          rw [mach_addGas d stack gHigh δ affordable]
          split at h
          · rename_i zero
            cases h
            simp only [zero, ite_true]
          · rename_i nonzero
            simp only [nonzero, ite_false]
            cases hf : fs[k]? with
            | none => simp only [hf] at h; cases h
            | some f => simp only [hf] at h ⊢; cases h; rfl
        · cases h
  | callNext k f =>
    dsimp only [wstep, addCfgGas] at h ⊢
    simp only [addGas_stack]
    cases hs : d.stack with
    | nil => simp only [hs] at h; cases h
    | cons v stack =>
      cases hf : fs[k]? with
      | none => simp only [hs, hf] at h; cases h
      | some g =>
        simp only [hs, hf] at h
        split at h
        · rename_i affordable
          have ha : gMid ≤ (addGas d δ).gasLeft := by change gMid ≤ d.gasLeft + δ; omega
          cases h
          simp only [ha, ite_true]
          rw [mach_addGas d stack gMid δ affordable]
        · cases h
  | ret =>
    dsimp only [wstep, addCfgGas] at h ⊢
    simp only [addGas_stack]
    cases hs : d.stack with
    | nil => simp only [hs] at h; cases h
    | cons v stack =>
      simp only [hs] at h
      split at h
      · rename_i affordable
        have ha : gMid ≤ (addGas d δ).gasLeft := by change gMid ≤ d.gasLeft + δ; omega
        cases K with
        | nil => cases h
        | cons g K =>
          cases h
          simp only [ha, ite_true]
          rw [mach_addGas d stack gMid δ affordable]
      · cases h
  | pcAt p f =>
    dsimp only [wstep, addCfgGas] at h ⊢
    cases hp : Ninst.step ⟨p, s, d⟩ (.reg .pc) with
    | halt out => simp only [hp] at h; cases h
    | spawn fr resume q => simp only [hp] at h; cases h
    | cont q d' =>
      simp only [hp] at h
      have hx := hp
      rw [Ninst.step_reg] at hx
      have ht := step_ofExecution_stable (pushItem_exec_stable p.toB256 gBase) hx δ
      change Step.ofExecution (p + 1) (pushItem p.toB256 gBase (addGas d δ)) =
        .cont q (addGas d' δ) at ht
      cases h
      rw [Ninst.step_reg]
      simp only [Rinst.run, Rinst.runCore]
      rw [ht]
  | next n f =>
    cases n with
    | reg r =>
      cases r <;> simp only [supported, ordinary, regular, arithmetic, Bool.false_eq_true] at hc
      case mload =>
        dsimp only [wstep, addCfgGas] at h ⊢
        cases hm : mloadStep ⟨d, .next (.reg .mload) f, K, keys, adrs, stor, acs⟩ f with
        | none => simp only [hm] at h; cases h
        | some out =>
          simp only [hm] at h
          have ht := mload_addGas hm δ
          dsimp only [addCfgGas] at ht
          rw [ht]
          cases h
          rfl
      case mstore =>
        dsimp only [wstep, addCfgGas] at h ⊢
        cases hm : mstoreStep ⟨d, .next (.reg .mstore) f, K, keys, adrs, stor, acs⟩ f with
        | none => simp only [hm] at h; cases h
        | some out =>
          simp only [hm] at h
          have ht := mstore_addGas hm δ
          dsimp only [addCfgGas] at ht
          rw [ht]
          cases h
          rfl
      case calldatacopy =>
        dsimp only [wstep, addCfgGas] at h ⊢
        cases hm : calldatacopyStep s ⟨d, .next (.reg .calldatacopy) f, K, keys, adrs, stor, acs⟩ f with
        | none => simp only [hm] at h; cases h
        | some out =>
          simp only [hm] at h
          have ht := calldatacopy_addGas hm δ
          dsimp only [addCfgGas] at ht
          rw [ht]
          cases h
          rfl
      all_goals exact next_ordinary_addGas (c := ⟨d, .undefined, K, keys, adrs, stor, acs⟩) rfl h δ
    | push xs le => exact next_ordinary_addGas (c := ⟨d, .undefined, K, keys, adrs, stor, acs⟩) rfl h δ
    | exec x => cases x <;> cases hc
    | dupn x => cases hc
    | swapn x => cases hc
    | exchange x => cases hc
  | last l => cases l <;> cases hc
  | undefined => cases hc

/-- A finite predicate on the successful reference path only.  It inspects each
visited node and stops exactly at the chosen cut; no alternate run is evaluated. -/
def selected (fs : List SFunc) (s : Sevm) : Nat → Cfg → Bool
  | 0, _ => true
  | n + 1, c => supported c.f &&
      match wstep fs s c with
      | .cont c' => selected fs s n c'
      | _ => false

/-- One selected reference path supplies both reference and alternate success.
Every other column, including continuations and shadows, is identical. -/
theorem selected_success {fs : List SFunc} {s : Sevm} {n : Nat} {c : Cfg}
    (h : selected fs s n c = true) :
    ∃ c', wrun fs s n c = .cont c' ∧
      ∀ δ, wrun fs s n (addCfgGas c δ) = .cont (addCfgGas c' δ) := by
  induction n generalizing c with
  | zero => exact ⟨c, rfl, fun _ => rfl⟩
  | succ n ih =>
    simp only [selected, Bool.and_eq_true] at h
    cases hs : wstep fs s c with
    | stuck => simp only [hs, Bool.false_eq_true] at h; exact h.2.elim
    | done out endCfg => simp only [hs, Bool.false_eq_true] at h; exact h.2.elim
    | cont mid =>
      simp only [hs] at h
      obtain ⟨endCfg, hr, ha⟩ := ih h.2
      refine ⟨endCfg, ?_, ?_⟩
      · simp only [wrun, hs, hr]
      · intro δ
        rw [wrun, wstep_addGas h.1 hs δ]
        exact ha δ

/-- Transport to a named endpoint from its single successful checked run. -/
theorem wrun_addGas {fs : List SFunc} {s : Sevm} {n : Nat} {c c' : Cfg}
    (hc : selected fs s n c = true) (hr : wrun fs s n c = .cont c') (δ : Nat) :
    wrun fs s n (addCfgGas c δ) = .cont (addCfgGas c' δ) := by
  obtain ⟨endCfg, he, ha⟩ := selected_success hc
  rw [hr] at he
  cases he
  exact ha δ

end Blanc.Lift.GasSuccess
