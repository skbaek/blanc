import Batteries.Tactic.OpenPrivate
import Blanc.ExecutionKeptFrames
import Blanc.ExecutionCommittedCell
import Blanc.ExecutionTraceCallerExclusion

/-!
# The top-level executions of a message

`processMessageCall` runs at most one interpreter execution, on either lane of the rule record. A `Root` is that
execution; `MessageRoots` ties it to Jaune by equations, so the message determines it. Nothing here reads a gas
amount: the statements stop at the message's output.
-/

namespace Blanc

open Jaune ExecutionTrace

open private AmsterdamDelegationResult chargeNewAuthorityAmsterdam chargePaidAccountWriteAmsterdam
  chargeAuthBaseAmsterdam applyValidatedDelegationAmsterdam setDelegationAmsterdamStep setDelegationAmsterdamLoop
  setDelegationAmsterdam preparedTopLevelMsg resolveTopLevelCallAmsterdam dispatchTopLevelAmsterdam
  finishTopLevelAmsterdam runPreparedTopFrame msgCallOutputAmsterdam from Jaune.Transaction

/-! ## What preparing a machine keeps -/

/-- Preparing a machine for the authorizations `auths` leaves its stack, memory and two account sets. It leaves a
code-bearing account that is no delegation, and writes no code away from a recovered authority. -/
private structure PrepKeep (auths : List Auth) (d d' : Devm) : Prop where
  stack : d'.stack = d.stack
  memory : d'.memory = d.memory
  deletions : d'.accountsToDelete = d.accountsToDelete
  created : d'.createdAccounts = d.createdAccounts
  kept : ∀ x, (d.state.getCode x).toList ≠ [] → ¬ isValidDelegation (d.state.getCode x) →
    d'.state.get x = d.state.get x
  away : ∀ x, (∀ auth ∈ auths, recoverAuthority auth ≠ .ok x) → d'.state.getCode x = d.state.getCode x

private theorem PrepKeep.refl (auths : List Auth) (d : Devm) : PrepKeep auths d d :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩

private theorem PrepKeep.trans {auths : List Auth} {d₁ d₂ d₃ : Devm} (h : PrepKeep auths d₁ d₂)
    (k : PrepKeep auths d₂ d₃) : PrepKeep auths d₁ d₃ := by
  refine ⟨k.stack.trans h.stack, k.memory.trans h.memory, k.deletions.trans h.deletions, k.created.trans h.created,
    ?_, ?_⟩
  · intro x hc hd
    have e := h.kept x hc hd
    have ec : d₂.state.getCode x = d₁.state.getCode x := congrArg Acct.code e
    exact (k.kept x (by rw [ec]; exact hc) (by rw [ec]; exact hd)).trans e
  · intro x hx
    exact (k.away x hx).trans (h.away x hx)

/-- A charge moves only the machine's gas: stack, memory, the frame's records and its world stay. -/
private structure Charged (d d' : Devm) : Prop where
  stack : d'.stack = d.stack
  memory : d'.memory = d.memory
  records : d'.meta = d.meta
  world : d'.world = d.world

private theorem Charged.refl (d : Devm) : Charged d d := ⟨rfl, rfl, rfl, rfl⟩

private theorem Charged.trans {d₁ d₂ d₃ : Devm} (h : Charged d₁ d₂) (k : Charged d₂ d₃) : Charged d₁ d₃ :=
  ⟨k.stack.trans h.stack, k.memory.trans h.memory, k.records.trans h.records, k.world.trans h.world⟩

private theorem Charged.keep {d d' : Devm} (h : Charged d d') (auths : List Auth) : PrepKeep auths d d' := by
  have hstate : d'.state = d.state := congrArg World.state h.world
  refine ⟨h.stack, h.memory, congrArg Meta.accountsToDelete h.records, congrArg Meta.createdAccounts h.records, ?_, ?_⟩
  · intro x _ _; rw [hstate]
  · intro x _; rw [hstate]

private theorem chargeGas_charged {c : Nat} {d d' : Devm} (h : chargeGas c d = .ok d') : Charged d d' := by
  simp only [chargeGas, liftMachExecution, Footprint.toExecution, liftMach, Footprint.liftOutcome, Mach.chargeGas] at h
  cases hsub : safeSub d.mach.gasLeft c with
  | none => simp only [hsub, reduceCtorEq] at h
  | some gas =>
      simp only [hsub, Except.ok.injEq] at h
      subst h
      exact ⟨rfl, rfl, rfl, rfl⟩

private theorem chargeStateGas_charged {c : Nat} {d d' : Devm} (h : chargeStateGas c d = .ok d') : Charged d d' := by
  simp only [chargeStateGas, liftMachExecution, Footprint.toExecution, liftMach, Footprint.liftOutcome,
    Mach.chargeStateGas] at h
  by_cases h1 : c ≤ d.mach.stateGas.left
  · simp only [h1, ↓reduceIte, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl, rfl⟩
  · by_cases h2 : c - d.mach.stateGas.left ≤ d.mach.gasLeft
    · simp only [h1, h2, ↓reduceIte, Except.ok.injEq] at h
      subst h
      exact ⟨rfl, rfl, rfl, rfl⟩
    · simp only [h1, h2, ↓reduceIte, reduceCtorEq] at h

private theorem PrepKeep.widen {auths' : List Auth} {auths : List Auth} {d d' : Devm} (h : PrepKeep auths d d')
    (sub : ∀ a ∈ auths, a ∈ auths') : PrepKeep auths' d d' :=
  ⟨h.stack, h.memory, h.deletions, h.created, h.kept, fun x hx => h.away x (fun a m => hx a (sub a m))⟩

private theorem setCode_incrNonce_get (d : Devm) {a x : Adr} (c : ByteArray) (ne : a ≠ x) :
    ((d.setCode a c).incrNonce a).state.get x = d.state.get x := by
  show ((d.state.setCode a c).incrNonce a).get x = _
  rw [State.incrNonce, State.setAccount_get_ne _ ne, State.setCode, State.setAccount_get_ne _ ne]

private theorem applyValidated_keep {state : StateGasRules} {msg : Msg} {authority target : Adr} {d : Devm}
    {paid set : AdrSet} {r : AmsterdamDelegationResult} {auth : Auth}
    (recovered : recoverAuthority auth = .ok authority)
    (guard : (d.state.get authority).code.isEmpty = true ∨ isValidDelegation (d.state.get authority).code)
    (h : applyValidatedDelegationAmsterdam state msg authority target d paid set = .ok r) :
    PrepKeep [auth] d r.1 := by
  unfold applyValidatedDelegationAmsterdam at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i d₁ h₁
  have k₁ : Charged d d₁ := by
    unfold chargeNewAuthorityAmsterdam at h₁
    split at h₁
    · exact chargeStateGas_charged h₁
    · cases h₁; exact .refl _
  split at h
  · cases h
  rename_i p h₂
  obtain ⟨d₂, paid'⟩ := p
  have k₂ : Charged d₁ d₂ := by
    unfold chargePaidAccountWriteAmsterdam at h₂
    split at h₂
    · cases h₂; exact .refl _
    · simp only [bind, Except.bind] at h₂
      split at h₂
      · cases h₂
      · rename_i d' hc
        simp only [Except.ok.injEq, Prod.mk.injEq] at h₂
        rcases h₂ with ⟨rfl, -⟩
        exact chargeGas_charged hc
  split at h
  · cases h
  rename_i q h₃
  obtain ⟨d₃, set', code⟩ := q
  have k₃ : Charged d₂ d₃ := by
    unfold chargeAuthBaseAmsterdam at h₃
    split at h₃
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h₃
      rcases h₃ with ⟨rfl, -⟩
      exact .refl _
    · simp only [bind, Except.bind] at h₃
      split at h₃
      · split at h₃
        · cases h₃
        · rename_i d' hc
          simp only [Except.ok.injEq, Prod.mk.injEq] at h₃
          rcases h₃ with ⟨rfl, -⟩
          exact chargeStateGas_charged hc
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h₃
        rcases h₃ with ⟨rfl, -⟩
        exact .refl _
  simp only [Except.ok.injEq] at h
  subst h
  have k := (k₁.trans k₂).trans k₃
  have hstate : d₃.state = d.state := congrArg World.state k.world
  refine (k.keep [auth]).trans ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro x hc hd
    have ne : authority ≠ x := by
      intro same
      subst same
      rw [hstate] at hc hd
      rcases guard with empty | delegated
      · have zero : (d.state.getCode authority).size = 0 := by
          simpa only [State.getCode, ByteArray.isEmpty, beq_iff_eq] using empty
        exact (ne_wa_of_code_size_zero hc zero) rfl
      · exact hd delegated
    exact setCode_incrNonce_get d₃ code ne
  · intro x hx
    have ne : authority ≠ x := by
      intro same
      subst same
      exact hx auth List.mem_cons_self recovered
    exact congrArg Acct.code (setCode_incrNonce_get d₃ code ne)

private theorem read_keep (rules : ForkRules) (a : Adr) (d : Devm) (auths : List Auth) :
    PrepKeep auths d (d.balReadAccount rules a) := by
  refine ⟨rfl, rfl, ?_, ?_, fun _ _ _ => rfl, fun _ _ => rfl⟩ <;>
    · simp only [Devm.balReadAccount, Devm.setMeta, Devm.accountsToDelete, Devm.createdAccounts]
      split <;> rfl

private theorem warm_keep (a : Adr) (d : Devm) (auths : List Auth) : PrepKeep auths d (addAccessedAddress d a) :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩

private theorem step_keep {state : StateGasRules} {msg : Msg} {auth : Auth} {d : Devm} {paid set : AdrSet}
    {r : AmsterdamDelegationResult} (h : setDelegationAmsterdamStep state msg auth d paid set = .ok r) :
    PrepKeep [auth] d r.1 := by
  unfold setDelegationAmsterdamStep at h
  dsimp only at h
  split at h
  · cases h; exact .refl _ _
  split at h
  · cases h; exact .refl _ _
  split at h
  · cases h; exact .refl _ _
  · cases h
  · rename_i authority recovered
    have read := (warm_keep authority d [auth]).trans (read_keep msg.benv.stat.rules authority _ [auth])
    split at h
    · cases h; exact read
    split at h
    · cases h; exact read
    rename_i allowed _
    exact read.trans (applyValidated_keep recovered (Classical.byContradiction fun hn => allowed hn) h)

private theorem loop_keep {state : StateGasRules} {msg : Msg} {auths : List Auth} {d : Devm} {paid set : AdrSet}
    {r : AmsterdamDelegationResult} (h : setDelegationAmsterdamLoop state msg auths d paid set = .ok r) :
    PrepKeep auths d r.1 := by
  induction auths generalizing d paid set with
  | nil =>
      unfold setDelegationAmsterdamLoop at h
      cases h
      exact .refl _ _
  | cons auth auths ih =>
      unfold setDelegationAmsterdamLoop at h
      simp only [bind, Except.bind] at h
      split at h
      · cases h
      rename_i p hstep
      obtain ⟨d₁, paid₁, set₁⟩ := p
      exact ((step_keep hstep).widen (by
        intro a m; rw [List.mem_singleton] at m; subst m; exact List.mem_cons_self)).trans
        ((ih h).widen fun a m => List.mem_cons_of_mem _ m)

private theorem setDelegationAmsterdam_keep {state : StateGasRules} {msg : Msg} {d d' : Devm}
    (h : setDelegationAmsterdam state msg d = .ok d') : PrepKeep msg.tenv.stat.auths d d' := by
  unfold setDelegationAmsterdam at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i p hloop
  cases h
  exact loop_keep hloop

/-- What a message's preparation keeps of it, on either lane: its routing, its deletion and creation sets, every
code-bearing account that is no delegation, and all code away from a recovered authority. A call on such a target
runs that target's code. -/
private structure Prepared (msg m : Msg) : Prop where
  caller : m.caller = msg.caller
  target : m.target = msg.target
  currentTarget : m.currentTarget = msg.currentTarget
  data : m.data = msg.data
  stat : m.benv.stat = msg.benv.stat
  deletions : m.inheritedDeletions = msg.inheritedDeletions
  created : m.benv.createdAccounts = msg.benv.createdAccounts
  kept : ∀ x, (msg.benv.state.getCode x).toList ≠ [] → ¬ isValidDelegation (msg.benv.state.getCode x) →
    m.benv.state.getCode x = msg.benv.state.getCode x ∧ m.benv.state.getStor x = msg.benv.state.getStor x
  away : ∀ x, (∀ auth ∈ msg.tenv.stat.auths, recoverAuthority auth ≠ .ok x) →
    m.benv.state.getCode x = msg.benv.state.getCode x
  codeAddress : msg.target.isNone = true → m.codeAddress = msg.codeAddress
  code : msg.target.isNone = false → msg.codeAddress = some msg.currentTarget →
    msg.code = msg.benv.state.getCode msg.currentTarget →
    ¬ isValidDelegation (m.benv.state.getCode msg.currentTarget) →
    m.code = m.benv.state.getCode msg.currentTarget
  /-- A routed call to a target that is no delegation runs at the target's address. -/
  codeAt : msg.target.isNone = false → msg.codeAddress = some msg.currentTarget →
    msg.code = msg.benv.state.getCode msg.currentTarget →
    ¬ isValidDelegation (m.benv.state.getCode msg.currentTarget) → m.codeAddress = some msg.currentTarget
  /-- The preparation keeps whether value moves, and how much. -/
  transfer : m.shouldTransferValue = msg.shouldTransferValue
  value : m.value = msg.value
  /-- A code-bearing account keeps its balance through the preparation. -/
  bal : ∀ x, (msg.benv.state.getCode x).toList ≠ [] → ¬ isValidDelegation (msg.benv.state.getCode x) →
    m.benv.state.bal x = msg.benv.state.bal x

private theorem delegationCost_of_not_delegated {rules : ForkRules} {devm : Devm} {adr cA : Adr} {del : Bool} {c : Nat}
    (hcost : rules.delegationCost devm adr = (del, cA, c)) (hnot : ¬ isValidDelegation (devm.state.getCode adr)) :
    del = false ∧ cA = adr := by
  have hnone : getDelegatedCodeAddress (devm.state.getCode adr) = none := by
    simp only [getDelegatedCodeAddress, hnot, ↓reduceIte]
  simp only [ForkRules.delegationCost] at hcost
  split at hcost
  · simp only [GasSchedule.delegationCost, hnone, Prod.mk.injEq] at hcost
    exact ⟨hcost.1.symm, hcost.2.1.symm⟩
  · simp only [Prod.mk.injEq] at hcost
    exact ⟨hcost.1.symm, hcost.2.1.symm⟩

private theorem dispatch_spec {state : StateGasRules} {msg m : Msg} {devm d : Devm}
    (h : dispatchTopLevelAmsterdam state msg devm = .ok (m, d)) :
    PrepKeep [] devm d ∧ d.state = devm.state ∧
      ((m = preparedTopLevelMsg msg d ∧ msg.target.isNone = true ∧
          accountHasCodeOrNonce devm.state msg.currentTarget = false) ∨
        (∃ (cA : Adr) (code : ByteArray) (dp : Bool),
          m = {preparedTopLevelMsg msg d with codeAddress := some cA, code := code, disablePrecompiles := dp} ∧
          msg.target.isNone = false ∧
          (¬ isValidDelegation (devm.state.getCode msg.currentTarget) →
            code = devm.state.getCode msg.currentTarget) ∧
          (¬ isValidDelegation (devm.state.getCode msg.currentTarget) → cA = msg.currentTarget))) := by
  have read := read_keep msg.benv.stat.rules msg.currentTarget devm []
  unfold dispatchTopLevelAmsterdam at h
  dsimp only at h
  split at h
  · rename_i htarget
    split at h
    · cases h
    rename_i hcoll
    obtain ⟨d₁, charged, h⟩ : ∃ d₁, Charged (devm.balReadAccount msg.benv.stat.rules msg.currentTarget) d₁ ∧
        (Except.ok (preparedTopLevelMsg msg d₁, d₁) : Except (EvmError × Devm) (Msg × Devm)) = .ok (m, d) := by
      split at h
      · obtain ⟨d₁, hd₁, h⟩ := Except.bind_eq_ok h
        exact ⟨d₁, chargeStateGas_charged hd₁, h⟩
      · exact ⟨_, .refl _, h⟩
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨read.trans (charged.keep _), congrArg World.state charged.world, .inl ⟨rfl, htarget, ?_⟩⟩
    exact (Bool.not_eq_true _).mp hcoll
  · rename_i htarget
    obtain ⟨d₁, charged, h⟩ : ∃ d₁, Charged (devm.balReadAccount msg.benv.stat.rules msg.currentTarget) d₁ ∧
        resolveTopLevelCallAmsterdam msg d₁ = .ok (m, d) := by
      split at h
      · obtain ⟨d₁, hd₁, h⟩ := Except.bind_eq_ok h
        exact ⟨d₁, chargeStateGas_charged hd₁, h⟩
      · exact ⟨_, .refl _, h⟩
    have hd₁s : d₁.state = devm.state := congrArg World.state charged.world
    unfold resolveTopLevelCallAmsterdam at h
    rcases hcost : msg.benv.stat.rules.delegationCost d₁ msg.currentTarget with ⟨del, cA, c⟩
    rw [hcost] at h
    dsimp only at h
    obtain ⟨d₂, hd₂, h⟩ := Except.bind_eq_ok h
    have charged₂ := chargeGas_charged hd₂
    have hd₂s : d₂.state = d₁.state := congrArg World.state charged₂.world
    simp only [completeDelegationAccess, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have warm : PrepKeep [] d₂ (if del = true then addAccessedAddress d₂ cA else d₂) := by
      split
      · exact warm_keep _ _ _
      · exact .refl _ _
    have hwarm : (if del = true then addAccessedAddress d₂ cA else d₂).state = d₂.state := by
      split <;> rfl
    refine ⟨((read.trans (charged.keep _)).trans (charged₂.keep _)).trans
        (warm.trans (read_keep _ _ _ _)), ?_, .inr ⟨cA, _, del, rfl, ?_, ?_, ?_⟩⟩
    · exact hwarm.trans (hd₂s.trans hd₁s)
    · simpa only [Bool.not_eq_true] using htarget
    · intro hnot
      obtain ⟨rfl, rfl⟩ := delegationCost_of_not_delegated hcost (by rw [hd₁s]; exact hnot)
      show (if false = true then addAccessedAddress d₂ msg.currentTarget else d₂).state.getCode msg.currentTarget = _
      rw [hwarm, hd₂s, hd₁s]
    · intro hnot
      exact (delegationCost_of_not_delegated hcost (by rw [hd₁s]; exact hnot)).2

private theorem prepare_spec {state : StateGasRules} {msg m : Msg} {d : Devm}
    (h : prepareTopLevelAmsterdam state msg = .ok (m, d)) :
    Prepared msg m ∧ PrepKeep msg.tenv.stat.auths (initDevm msg) d ∧
      (msg.target.isNone = true → accountHasCodeOrNonce m.benv.state m.currentTarget = false) := by
  unfold prepareTopLevelAmsterdam finishTopLevelAmsterdam at h
  obtain ⟨d₁, k₁, h⟩ : ∃ d₁, PrepKeep msg.tenv.stat.auths (initDevm msg) d₁ ∧
      dispatchTopLevelAmsterdam state msg (if msg.tenv.stat.auths.isEmpty then d₁ else d₁.commitStateGas) =
        .ok (m, d) := by
    dsimp only at h
    split at h
    · rename_i he
      refine ⟨_, .refl _ _, ?_⟩
      rw [ite_eq_left he]
      exact h
    · rename_i he
      obtain ⟨d₁, hd₁, h⟩ := Except.bind_eq_ok h
      refine ⟨d₁, setDelegationAmsterdam_keep hd₁, ?_⟩
      rw [ite_eq_right he]
      exact h
  have commit : Charged d₁ (if msg.tenv.stat.auths.isEmpty then d₁ else d₁.commitStateGas) := by
    split
    · exact .refl _
    · exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨k₂, hs, shape⟩ := dispatch_spec h
  have k := (k₁.trans (commit.keep _)).trans (k₂.widen fun a m => by cases m)
  have kept : ∀ x, (msg.benv.state.getCode x).toList ≠ [] → ¬ isValidDelegation (msg.benv.state.getCode x) →
      d.state.getCode x = msg.benv.state.getCode x ∧ d.state.getStor x = msg.benv.state.getStor x :=
    fun x hc hn => ⟨congrArg Acct.code (k.kept x hc hn), congrArg Acct.stor (k.kept x hc hn)⟩
  have keptBal : ∀ x, (msg.benv.state.getCode x).toList ≠ [] → ¬ isValidDelegation (msg.benv.state.getCode x) →
      d.state.bal x = msg.benv.state.bal x :=
    fun x hc hn => congrArg Acct.bal (k.kept x hc hn)
  rcases shape with ⟨rfl, htarget, hcoll⟩ | ⟨cA, code, dp, rfl, htarget, hcode, hcA⟩
  · refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, k.created, kept, k.away, fun _ => rfl, fun hn => ?_, fun hn => ?_,
      rfl, rfl, keptBal⟩, k, fun _ => ?_⟩
    · rw [htarget] at hn; cases hn
    · rw [htarget] at hn; cases hn
    · show accountHasCodeOrNonce d.state msg.currentTarget = false
      rw [hs]
      exact hcoll
  · refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, k.created, kept, k.away, fun hn => ?_, fun _ _ _ hnot => ?_,
      fun _ _ _ hnot => ?_, rfl, rfl, keptBal⟩, k, fun hn => ?_⟩
    · rw [htarget] at hn; cases hn
    · have hnot' : ¬ isValidDelegation (d.state.getCode msg.currentTarget) := hnot
      show code = d.state.getCode msg.currentTarget
      rw [hs] at hnot' ⊢
      exact hcode hnot'
    · have hnot' : ¬ isValidDelegation (d.state.getCode msg.currentTarget) := hnot
      rw [hs] at hnot'
      show some cA = some msg.currentTarget
      rw [hcA hnot']
    · rw [htarget] at hn; cases hn

/-! ## The legacy authorization prefix -/

/-- What one legacy authorization pass keeps of a message beyond its routing fields. -/
private structure AuthFrame (auths : List Auth) (msg m : Msg) : Prop where
  data : m.data = msg.data
  deletions : m.inheritedDeletions = msg.inheritedDeletions
  created : m.benv.createdAccounts = msg.benv.createdAccounts
  away : ∀ x, (∀ auth ∈ auths, recoverAuthority auth ≠ .ok x) → m.benv.state.getCode x = msg.benv.state.getCode x

private theorem AuthFrame.refl (auths : List Auth) (msg : Msg) : AuthFrame auths msg msg :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

private theorem setDelegationStep_frame {auth : Auth} {msg m : Msg} {r r' : B256}
    (h : setDelegationStep auth msg r = .ok (m, r')) : AuthFrame [auth] msg m := by
  unfold setDelegationStep at h
  dsimp only at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, -⟩; exact .refl _ _
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, -⟩; exact .refl _ _
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, -⟩; exact .refl _ _
  · cases h
  · rename_i authority recovered
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, -⟩; exact ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, -⟩; exact ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, -⟩
    refine ⟨rfl, rfl, rfl, fun x hx => ?_⟩
    have ne : authority ≠ x := by
      intro same
      subst same
      exact hx auth List.mem_cons_self recovered
    dsimp only [Msg.incrNonce, Msg.setCode, Benv.incrNonce, Benv.clearStorageWritesIfEmpty]
    unfold State.getCode
    rw [State.incrNonce, State.setAccount_get_ne _ ne, State.setCode, State.setAccount_get_ne _ ne]

private theorem setDelegationLoop_frame {auths : List Auth} {msg m : Msg} {r r' : B256}
    (h : setDelegationLoop auths msg r = .ok (m, r')) : AuthFrame auths msg m := by
  induction auths generalizing msg r with
  | nil =>
      unfold setDelegationLoop at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, -⟩
      exact .refl _ _
  | cons auth auths ih =>
      unfold setDelegationLoop at h
      obtain ⟨⟨m₁, r₁⟩, h₁, h₂⟩ := Except.bind_eq_ok h
      have a := setDelegationStep_frame h₁
      have b := ih h₂
      refine ⟨b.data.trans a.data, b.deletions.trans a.deletions, b.created.trans a.created, fun x hx => ?_⟩
      exact (b.away x fun y my => hx y (List.mem_cons_of_mem _ my)).trans
        (a.away x fun y my => hx y (by rw [List.mem_singleton] at my; subst my; exact List.mem_cons_self))

/-- The authorization prefix of the legacy call lane: nothing happens, or the code is read after the writes. -/
private theorem legacyAuthorization_frame {msg d : Msg} {refund : Nat}
    (h : messageCallDelegation msg = .ok (d, refund)) :
    AuthFrame msg.tenv.stat.auths msg d ∧ (d = msg ∨ ∀ ca, d.codeAddress = some ca → d.code = d.benv.state.getCode ca) := by
  unfold messageCallDelegation processMessageCall.legacyAuthorization at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, -⟩
    exact ⟨.refl _ _, .inl rfl⟩
  · obtain ⟨⟨m₁, w⟩, h₁, h₂⟩ := Except.bind_eq_ok h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h₂
    rcases h₂ with ⟨rfl, -⟩
    unfold setDelegation at h₁
    obtain ⟨⟨m₂, w₂⟩, hloop, h₃⟩ := Except.bind_eq_ok h₁
    have a := setDelegationLoop_frame hloop
    dsimp only at h₃
    split at h₃
    · cases h₃
    · rename_i ca hca
      change Except.ok ({m₂ with code := m₂.benv.state.getCode ca}, w₂) = Except.ok (m₁, w) at h₃
      simp only [Except.ok.injEq, Prod.mk.injEq] at h₃
      rcases h₃ with ⟨rfl, -⟩
      refine ⟨⟨a.data, a.deletions, a.created, a.away⟩, .inr fun ca' hca' => ?_⟩
      have : ca' = ca := by
        have h' : m₂.codeAddress = some ca' := hca'
        rw [hca] at h'
        exact (Option.some.inj h').symm
      subst this
      rfl

private theorem Prepared.refl (msg : Msg) : Prepared msg msg :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ => rfl, fun _ _ hc _ => hc, fun _ hca _ _ => hca, rfl, rfl, fun _ _ _ => rfl⟩

private theorem resolve_fields (d : Msg) :
    (messageCallExecutionMessage d).data = d.data ∧
      (messageCallExecutionMessage d).inheritedDeletions = d.inheritedDeletions ∧
      (messageCallExecutionMessage d).benv = d.benv := by
  unfold messageCallExecutionMessage Msg.resolveCodeDelegation
  split <;> exact ⟨rfl, rfl, rfl⟩

private theorem resolve_transfer (d : Msg) :
    (messageCallExecutionMessage d).shouldTransferValue = d.shouldTransferValue := by
  unfold messageCallExecutionMessage Msg.resolveCodeDelegation
  split <;> rfl

private theorem resolve_value (d : Msg) : (messageCallExecutionMessage d).value = d.value := by
  unfold messageCallExecutionMessage Msg.resolveCodeDelegation
  split <;> rfl

private theorem resolve_of_not_delegated {d : Msg} (hnot : ¬ isValidDelegation d.code) :
    messageCallExecutionMessage d = d := by
  unfold messageCallExecutionMessage Msg.resolveCodeDelegation
  have hnone : d.benv.stat.rules.delegatedCodeAddress d.code = none := by
    simp only [ForkRules.delegatedCodeAddress, getDelegatedCodeAddress, hnot, ↓reduceIte, ite_self]
  rw [hnone]

private theorem prepared_legacy_call {msg d : Msg} {refund : Nat} (h : messageCallDelegation msg = .ok (d, refund))
    (target : msg.target.isNone = false) : Prepared msg (messageCallExecutionMessage d) := by
  obtain ⟨frame, shape⟩ := legacyAuthorization_frame h
  obtain ⟨hdata, hdel, hbenv⟩ := resolve_fields d
  have fields := messageCallDelegation_fields h
  refine ⟨(messageCallExecutionMessage_caller_eq d).trans fields.1,
    (messageCallExecutionMessage_target_eq d).trans fields.2.1,
    (messageCallExecutionMessage_currentTarget_eq d).trans fields.2.2.1, hdata.trans frame.data,
    (congrArg Benv.stat hbenv).trans (messageCallDelegation_benv_stat h), hdel.trans frame.deletions,
    (congrArg Benv.createdAccounts hbenv).trans frame.created, ?_, ?_, ?_, ?_, ?_,
    (resolve_transfer d).trans fields.2.2.2.1, (resolve_value d).trans fields.2.2.2.2.1, ?_⟩
  · intro x hc hd
    rw [hbenv]
    exact ⟨delegation_keeps_code_entry h rfl hc hd, messageCallDelegation_getStor_eq h x hc hd⟩
  · intro x hx
    rw [hbenv]
    exact frame.away x hx
  · intro hn
    rw [target] at hn
    cases hn
  · intro _ hca hcode hnot
    rw [hbenv] at hnot ⊢
    have hd : d.code = d.benv.state.getCode msg.currentTarget := by
      rcases shape with rfl | later
      · exact hcode
      · exact later _ (fields.2.2.2.2.2.trans hca)
    have : messageCallExecutionMessage d = d := resolve_of_not_delegated (by rw [hd]; exact hnot)
    rw [this]
    exact hd
  · intro _ hca hcode hnot
    rw [hbenv] at hnot
    have hd : d.code = d.benv.state.getCode msg.currentTarget := by
      rcases shape with rfl | later
      · exact hcode
      · exact later _ (fields.2.2.2.2.2.trans hca)
    rw [resolve_of_not_delegated (by rw [hd]; exact hnot)]
    exact fields.2.2.2.2.2.trans hca
  · intro x _ _
    rw [hbenv]
    exact congrFun (messageCallDelegation_bal_eq h) x

/-! ## The root and its message -/

/-- One top-level execution of a message: its frame, the machine it entered on, and the run of that machine. -/
structure Root where
  frame : Frame
  evm : Evm
  raw : Execution
  run : Exec evm.pc evm.sta evm.dyna raw

/-- What a root keeps at `a`: nothing if its settlement does not commit, itself if it runs at `a`, else what its
own run keeps. -/
def Root.keptAt (a : Adr) (r : Root) : List Exec.Frame :=
  if h : Frame.settlementCommits r.frame r.raw = true then
    if r.evm.sta.currentTarget = a then [Exec.Frame.ofRun r.run (Frame.raw_commits_of_settlementCommits h)]
    else Exec.keptAt a r.run
  else []

/-- The frame and machine of an ordinary frame entry, when it enters a machine. -/
def enteredFrame (f : Frame) : Option (Frame × Evm) :=
  match f.enter with
  | .run e => some (f, e)
  | .done _ => none

/-- The legacy lane's entry: a create that does not collide, or a call after authorization and code resolution. -/
def legacyEntry (msg : Msg) : Option (Frame × Evm) :=
  if msg.target.isNone then
    if messageCreateCollision msg then none else enteredFrame (Frame.ofCreate msg)
  else
    match messageCallDelegation msg with
    | .ok (d, _) => enteredFrame (Frame.ofCall (messageCallExecutionMessage d))
    | .error _ => none

/-- Entry of a prepared top frame: an ordinary entry whose machine carries the prepared meters and records. -/
def preparedEntry (f : Frame) (prepared : Devm) : Option (Frame × Evm) :=
  match f.inner.benvAfterTransfer with
  | .error _ => none
  | .ok benv =>
    match executeCode.enter (f.inner.withBenv benv) with
    | .inr _ => none
    | .inl e => some (f, {e with dyna := ((prepared.withState benv.state).withStorageWrites
        benv.storageWrites).withCreatedAccounts benv.createdAccounts})

/-- The state-gas lane's entry: the frame of the message `prepareTopLevelAmsterdam` prepared, if it prepared one. -/
def amsterdamEntry (state : StateGasRules) (msg : Msg) : Option (Frame × Evm) :=
  match prepareTopLevelAmsterdam state msg with
  | .error _ => none
  | .ok (m, devm) => preparedEntry (if msg.target.isNone then Frame.ofCreate m else Frame.ofCall m) devm

/-- The frame and machine a message enters on its lane, if any: the rule record selects the lane. -/
def messageEntry (msg : Msg) : Option (Frame × Evm) :=
  match msg.benv.stat.rules.stateGas with
  | none => legacyEntry msg
  | some state => amsterdamEntry state msg

/-- `rs` are the top-level executions `processMessageCall msg = .ok (state, out)` ran: at most one, on the frame and
machine the message determines. -/
def MessageRoots (msg : Msg) (state : State) (out : MsgCallOutput) (rs : List Root) : Prop :=
  processMessageCall msg = .ok (state, out) ∧
    rs.map (fun r => (r.frame, r.evm)) = (messageEntry msg).toList

/-! ## The message's outcome, on both lanes -/

/-- The machine a frame entered: at the frame's start, after the value transfer, with an empty stack and memory. -/
private structure Entered (f : Frame) (benv : Benv) (e : Evm) : Prop where
  transfer : f.inner.benvAfterTransfer = .ok benv
  pc : e.pc = 0
  sta : e.sta = initSevm (f.inner.withBenv benv)
  state : e.dyna.state = benv.state
  stack : e.dyna.stack = []
  memory : e.dyna.memory = Mem.empty
  deletions : e.dyna.accountsToDelete = f.inner.inheritedDeletions
  created : e.dyna.createdAccounts = benv.createdAccounts

private theorem Entered.ofInit {f : Frame} {benv : Benv} (transfer : f.inner.benvAfterTransfer = .ok benv) :
    Entered f benv (initEvm (f.inner.withBenv benv)) :=
  ⟨transfer, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The frame of a prepared message: a call, or a create that does not collide. -/
private def FrameOf (msg m : Msg) (f : Frame) : Prop :=
  (msg.target.isNone = false ∧ f = Frame.ofCall m) ∨
    (msg.target.isNone = true ∧ f = Frame.ofCreate m ∧ accountHasCodeOrNonce m.benv.state m.currentTarget = false)

/-- One settled frame of a message, with the output it renders. -/
private structure TopRun (msg m : Msg) (state : State) (out : MsgCallOutput) (f : Frame) (benv : Benv) (e : Evm)
    (raw : Execution) (s : Devm) : Prop where
  prepared : Prepared msg m
  frame : FrameOf msg m f
  entered : Entered f benv e
  settled : f.settle raw = .ok s
  state_eq : state = s.state
  deletions : ∀ x ∈ out.accountsToDelete, s.error.isNone = true ∧ x ∈ s.accountsToDelete
  /-- The message entered this frame's machine, or it entered none and ran a precompile at the frame's code address. -/
  top : messageEntry msg = some (f, e) ∨ (messageEntry msg = none ∧ ∃ adr, raw = executePrecomp e adr ∧
    (f.inner.withBenv benv).codeAddress = some adr ∧
    (!(f.inner.withBenv benv).disablePrecompiles && (f.inner.withBenv benv).benv.stat.rules.isPrecomp adr) = true)

private theorem settleMsg_error {f : Frame} {e : EvmError × State × AdrSet × Tra} {s : Devm} :
    f.settleMsg (.error e) ≠ .ok s := by
  have inner : processMessage.settle f.inner (.error e) = .error e := rfl
  have outer : processCreateMessage.settle f.outer (.error e) = .error e := rfl
  intro h
  cases hc : f.isCreate <;>
    simp only [Frame.settleMsg, hc, inner, outer, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

/-- How `executeCode.enter` and the prepared top frame's dispatch read one message. -/
private theorem enter_cases (X : Msg) :
    (executeCode.enter X = .inl (initEvm X) ∧ ∀ e : Evm,
      (match X.codeAddress with
        | none => exec e
        | some adr => if (!X.disablePrecompiles && X.benv.stat.rules.isPrecomp adr) = true then
            executePrecomp e adr else exec e) = exec e) ∨
    (∃ adr, executeCode.enter X = .inr (executePrecomp (initEvm X) adr) ∧ (∀ e : Evm,
      (match X.codeAddress with
        | none => exec e
        | some adr => if (!X.disablePrecompiles && X.benv.stat.rules.isPrecomp adr) = true then
            executePrecomp e adr else exec e) = executePrecomp e adr) ∧
      X.codeAddress = some adr ∧ (!X.disablePrecompiles && X.benv.stat.rules.isPrecomp adr) = true) := by
  unfold executeCode.enter
  dsimp only
  cases hc : X.codeAddress with
  | none => exact .inl ⟨rfl, fun _ => rfl⟩
  | some adr =>
      by_cases hp : (!X.disablePrecompiles && X.benv.stat.rules.isPrecomp adr) = true
      · refine .inr ⟨adr, ?_, fun _ => ?_, rfl, hp⟩ <;> dsimp only <;> rw [ite_eq_left hp]
      · refine .inl ⟨?_, fun _ => ?_⟩ <;> dsimp only <;> rw [ite_eq_right hp]

private theorem runFrame_cases {f : Frame} {s : Devm} (h : runFrame f = .ok s) :
    ∃ benv, f.inner.benvAfterTransfer = .ok benv ∧
      ((enteredFrame f = none ∧ ∃ adr, f.settle (executePrecomp (initEvm (f.inner.withBenv benv)) adr) = .ok s ∧
          (f.inner.withBenv benv).codeAddress = some adr ∧
          (!(f.inner.withBenv benv).disablePrecompiles &&
            (f.inner.withBenv benv).benv.stat.rules.isPrecomp adr) = true) ∨
        (enteredFrame f = some (f, initEvm (f.inner.withBenv benv)) ∧
          f.settle (exec (initEvm (f.inner.withBenv benv))) = .ok s)) := by
  unfold runFrame at h
  unfold enteredFrame
  unfold Frame.enter at h ⊢
  cases ht : f.inner.benvAfterTransfer with
  | error e =>
      rw [ht] at h
      exact (settleMsg_error h).elim
  | ok benv =>
      rw [ht] at h
      dsimp only at h ⊢
      refine ⟨benv, rfl, ?_⟩
      rcases enter_cases (f.inner.withBenv benv) with ⟨he, -⟩ | ⟨adr, he, -, hca, hp⟩
      · rw [he] at h ⊢
        exact .inr ⟨rfl, h⟩
      · rw [he] at h ⊢
        exact .inl ⟨rfl, adr, h, hca, hp⟩

private theorem runPrepared_cases {f : Frame} {prepared : Devm} {s : Devm} {benv : Benv}
    (ht : f.inner.benvAfterTransfer = .ok benv) (h : runPreparedTopFrame f prepared = .ok s) :
    let e : Evm := {pc := 0, sta := initSevm (f.inner.withBenv benv), dyna := ((prepared.withState
      benv.state).withStorageWrites benv.storageWrites).withCreatedAccounts benv.createdAccounts}
    (preparedEntry f prepared = none ∧ ∃ adr, f.settle (executePrecomp e adr) = .ok s ∧
          (f.inner.withBenv benv).codeAddress = some adr ∧
          (!(f.inner.withBenv benv).disablePrecompiles &&
            (f.inner.withBenv benv).benv.stat.rules.isPrecomp adr) = true) ∨
      (preparedEntry f prepared = some (f, e) ∧ f.settle (exec e) = .ok s) := by
  unfold runPreparedTopFrame at h
  unfold preparedEntry
  rw [ht] at h ⊢
  dsimp only at h ⊢
  rcases enter_cases (f.inner.withBenv benv) with ⟨he, hraw⟩ | ⟨adr, he, hraw, hca, hp⟩
  · rw [he]
    refine .inr ⟨rfl, ?_⟩
    rw [← hraw]
    exact h
  · rw [he]
    refine .inl ⟨rfl, adr, ?_, hca, hp⟩
    rw [← hraw]
    exact h

private theorem output_amsterdam {msg : Msg} {evm : Devm} {state : State} {out : MsgCallOutput}
    (h : msgCallOutputAmsterdam msg evm = .ok (state, out)) :
    state = evm.state ∧ ∀ x ∈ out.accountsToDelete, evm.error.isNone = true ∧ x ∈ evm.accountsToDelete := by
  unfold msgCallOutputAmsterdam at h
  dsimp only at h
  split at h <;>
  · rename_i he
    obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, fun x hx => ?_⟩
    first
      | exact ⟨he, hx⟩
      | exact absurd hx AdrSet.not_mem_empty

/-- A message's outcome: rolled back before any frame, or settled from a precompile with no root, or from the root. -/
private def Outcome (entry : Option (Frame × Evm)) (msg : Msg) (state : State) (out : MsgCallOutput) : Prop :=
  (entry = none ∧ state = msg.benv.state ∧ ∀ x, x ∉ out.accountsToDelete) ∨
    (entry = none ∧ ∃ m f benv e adr s, TopRun msg m state out f benv e (executePrecomp e adr) s) ∨
    ∃ m f benv e s, entry = some (f, e) ∧ TopRun msg m state out f benv e (exec e) s

private theorem amsterdam_top {st : StateGasRules} {msg : Msg} {frameOf : Msg → Frame} {state : State}
    {out : MsgCallOutput}
    (hf : (msg.target.isNone = false ∧ frameOf = Frame.ofCall) ∨ (msg.target.isNone = true ∧ frameOf = Frame.ofCreate))
    (h : processTopLevelAmsterdam st msg frameOf = .ok (state, out)) (lane : messageEntry msg = amsterdamEntry st msg) :
    Outcome (amsterdamEntry st msg) msg state out := by
  unfold processTopLevelAmsterdam at h
  cases hp : prepareTopLevelAmsterdam st msg with
  | error p =>
      rw [hp] at h
      rcases p with ⟨err, d⟩
      dsimp only at h
      have none : amsterdamEntry st msg = none := by
        unfold amsterdamEntry
        rw [hp]
      unfold settleTopLevelPreparationFailure at h
      split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .inl ⟨none, rfl, fun x => AdrSet.not_mem_empty⟩
      all_goals cases h
  | ok p =>
      rcases p with ⟨m, d⟩
      rw [hp] at h
      dsimp only at h
      obtain ⟨evm, hevm, hout⟩ := Except.bind_eq_ok h
      have hrun : runPreparedTopFrame (frameOf m) d = .ok evm := Except.bimap_id_eq_ok hevm
      obtain ⟨hst, hdel⟩ := output_amsterdam hout
      obtain ⟨prep, keep, coll⟩ := prepare_spec hp
      have frame : FrameOf msg m (frameOf m) := by
        rcases hf with ⟨ht, rfl⟩ | ⟨ht, rfl⟩
        · exact .inl ⟨ht, rfl⟩
        · refine .inr ⟨ht, rfl, coll ht⟩
      have hframe : (if msg.target.isNone then Frame.ofCreate m else Frame.ofCall m) = frameOf m := by
        rcases hf with ⟨ht, rfl⟩ | ⟨ht, rfl⟩ <;> simp only [ht, Bool.false_eq_true, ↓reduceIte]
      have hentry : amsterdamEntry st msg = preparedEntry (frameOf m) d := by
        unfold amsterdamEntry
        rw [hp]
        dsimp only
        rw [hframe]
      have hinner : (frameOf m).inner.inheritedDeletions = msg.inheritedDeletions := by
        rcases frame with ⟨-, hff⟩ | ⟨-, hff, -⟩ <;> rw [hff] <;> exact prep.deletions
      cases ht : (frameOf m).inner.benvAfterTransfer with
      | error e =>
          unfold runPreparedTopFrame at hrun
          rw [ht] at hrun
          exact (settleMsg_error hrun).elim
      | ok benv =>
          have entered : Entered (frameOf m) benv ⟨0, initSevm ((frameOf m).inner.withBenv benv),
              ((d.withState benv.state).withStorageWrites benv.storageWrites).withCreatedAccounts
                benv.createdAccounts⟩ :=
            ⟨ht, rfl, rfl, rfl, keep.stack, keep.memory, keep.deletions.trans hinner.symm, rfl⟩
          rw [hentry]
          rcases runPrepared_cases ht hrun with ⟨hnone, adr, hs, hca, hp⟩ | ⟨hsome, hs⟩
          · exact .inr (.inl ⟨hnone, m, _, benv, _, adr, evm,
              ⟨prep, frame, entered, hs, hst, hdel, .inr ⟨lane.trans (hentry.trans hnone), adr, rfl, hca, hp⟩⟩⟩)
          · exact .inr (.inr ⟨m, _, benv, _, evm, hsome,
              ⟨prep, frame, entered, hs, hst, hdel, .inl (lane.trans (hentry.trans hsome))⟩⟩)

private theorem legacy_create_output {msg : Msg} {evm : Devm} {state : State} {out : MsgCallOutput}
    (hsg : msg.benv.stat.rules.stateGas = none) (target : msg.target.isNone = true)
    (collision : messageCreateCollision msg = false) (core : processCreateMessage msg = .ok evm)
    (result : processMessageCall msg = .ok (state, out)) :
    state = evm.state ∧ ∀ x ∈ out.accountsToDelete, evm.error.isNone = true ∧ x ∈ evm.accountsToDelete := by
  unfold processMessageCall at result
  simp only [target, ↓reduceIte] at result
  unfold processMessageCall.create at result
  rw [hsg] at result
  unfold messageCreateCollision at collision
  simp only [collision, Bool.false_eq_true, ↓reduceIte, bind, Except.bind] at result
  rcases Except.bind_eq_ok result with ⟨actual, actualMap, tail⟩
  have actualEq : actual = evm := Except.ok.inj ((Except.bimap_id_eq_ok actualMap).symm.trans core)
  subst actual
  split at tail
  · rename_i he
    rcases Except.bind_eq_ok tail with ⟨_, _, output⟩
    have hout := Prod.mk.inj (Except.ok.inj output)
    refine ⟨hout.1.symm, fun a ha => ?_⟩
    rw [← hout.2] at ha
    exact ⟨he, ha⟩
  · have hout := Prod.mk.inj (Except.ok.inj tail)
    refine ⟨hout.1.symm, fun a ha => ?_⟩
    rw [← hout.2] at ha
    exact absurd ha AdrSet.not_mem_empty

private theorem legacy_call_output {msg delegated : Msg} {refund : Nat} {evm : Devm} {state : State}
    {out : MsgCallOutput} (hsg : msg.benv.stat.rules.stateGas = none) (target : msg.target.isNone = false)
    (delegation : messageCallDelegation msg = .ok (delegated, refund))
    (core : processMessage (messageCallExecutionMessage delegated) = .ok evm)
    (result : processMessageCall msg = .ok (state, out)) :
    state = evm.state ∧ ∀ x ∈ out.accountsToDelete, evm.error.isNone = true ∧ x ∈ evm.accountsToDelete := by
  unfold processMessageCall at result
  simp only [target, Bool.false_eq_true, ↓reduceIte] at result
  unfold processMessageCall.call at result
  simp only [hsg] at result
  rw [show processMessageCall.legacyAuthorization msg = .ok ⟨delegated, refund⟩ from delegation] at result
  simp only [Except.bind_ok] at result
  rcases Except.bind_eq_ok result with ⟨actual, actualMap, tail⟩
  have actualEq : actual = evm := Except.ok.inj ((Except.bimap_id_eq_ok actualMap).symm.trans core)
  subst actual
  split at tail
  · rename_i he
    rcases Except.bind_eq_ok tail with ⟨_, _, output⟩
    have hout := Prod.mk.inj (Except.ok.inj output)
    refine ⟨hout.1.symm, fun a ha => ?_⟩
    rw [← hout.2] at ha
    exact ⟨he, ha⟩
  · have hout := Prod.mk.inj (Except.ok.inj tail)
    refine ⟨hout.1.symm, fun a ha => ?_⟩
    rw [← hout.2] at ha
    exact absurd ha AdrSet.not_mem_empty

private theorem legacy_frame_outcome {msg m : Msg} {f : Frame} {state : State} {out : MsgCallOutput} {evm : Devm}
    (prep : Prepared msg m) (frame : FrameOf msg m f) (core : runFrame f = .ok evm)
    (hst : state = evm.state) (hdel : ∀ x ∈ out.accountsToDelete, evm.error.isNone = true ∧ x ∈ evm.accountsToDelete)
    (lane : messageEntry msg = enteredFrame f) :
    Outcome (enteredFrame f) msg state out := by
  obtain ⟨benv, ht, hcases⟩ := runFrame_cases core
  rcases hcases with ⟨hnone, adr, hs, hca, hp⟩ | ⟨hsome, hs⟩
  · exact .inr (.inl ⟨hnone, m, f, benv, _, adr, evm,
      ⟨prep, frame, .ofInit ht, hs, hst, hdel, .inr ⟨lane.trans hnone, adr, rfl, hca, hp⟩⟩⟩)
  · exact .inr (.inr ⟨m, f, benv, _, evm, hsome, ⟨prep, frame, .ofInit ht, hs, hst, hdel, .inl (lane.trans hsome)⟩⟩)

private theorem legacy_top {msg : Msg} {state : State} {out : MsgCallOutput}
    (hsg : msg.benv.stat.rules.stateGas = none) (h : processMessageCall msg = .ok (state, out)) :
    Outcome (legacyEntry msg) msg state out := by
  unfold legacyEntry
  cases target : msg.target.isNone with
  | true =>
      simp only [↓reduceIte]
      cases collision : messageCreateCollision msg with
      | true =>
          obtain ⟨hst, hdel⟩ := processMessageCall_createCollision_out_noStateGas hsg target collision h
          exact .inl ⟨by simp only [↓reduceIte], hst, hdel⟩
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          have body := h
          unfold processMessageCall at body
          simp only [target, ↓reduceIte] at body
          unfold processMessageCall.create at body
          rw [hsg] at body
          unfold messageCreateCollision at collision
          simp only [collision, Bool.false_eq_true, ↓reduceIte, bind, Except.bind] at body
          obtain ⟨evm, hevm, -⟩ := Except.bind_eq_ok body
          have core : processCreateMessage msg = .ok evm := Except.bimap_id_eq_ok hevm
          obtain ⟨hst, hdel⟩ := legacy_create_output hsg target collision core h
          exact legacy_frame_outcome (.refl msg) (.inr ⟨target, rfl, collision⟩) core hst hdel
            (by unfold messageEntry legacyEntry; rw [hsg]; simp only [target, messageCreateCollision, collision, Bool.false_eq_true, ↓reduceIte])
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have body := h
      unfold processMessageCall at body
      simp only [target, Bool.false_eq_true, ↓reduceIte] at body
      unfold processMessageCall.call at body
      rw [hsg] at body
      dsimp only at body
      obtain ⟨⟨d, refund⟩, hd, body⟩ := Except.bind_eq_ok body
      obtain ⟨evm, hevm, -⟩ := Except.bind_eq_ok body
      have core : processMessage (messageCallExecutionMessage d) = .ok evm := Except.bimap_id_eq_ok hevm
      have delegation : messageCallDelegation msg = .ok (d, refund) := hd
      rw [delegation]
      dsimp only
      obtain ⟨hst, hdel⟩ := legacy_call_output hsg target delegation core h
      exact legacy_frame_outcome (prepared_legacy_call delegation target) (.inl ⟨target, rfl⟩) core hst hdel
        (by unfold messageEntry legacyEntry; rw [hsg, delegation]; simp only [target, Bool.false_eq_true, ↓reduceIte])

private theorem message_top {msg : Msg} {state : State} {out : MsgCallOutput}
    (h : processMessageCall msg = .ok (state, out)) : Outcome (messageEntry msg) msg state out := by
  unfold messageEntry
  cases hsg : msg.benv.stat.rules.stateGas with
  | none => exact legacy_top hsg h
  | some st =>
      simp only
      unfold processMessageCall at h
      cases target : msg.target.isNone with
      | true =>
          simp only [target, ↓reduceIte] at h
          unfold processMessageCall.create at h
          rw [hsg] at h
          exact amsterdam_top (.inr ⟨target, rfl⟩) h (by unfold messageEntry; rw [hsg])
      | false =>
          simp only [target, Bool.false_eq_true, ↓reduceIte] at h
          unfold processMessageCall.call at h
          rw [hsg] at h
          exact amsterdam_top (.inl ⟨target, rfl⟩) h (by unfold messageEntry; rw [hsg])

/-! ## Settlement of a frame -/

private theorem recordTouch_deletions (rules : ForkRules) (cond : Bool) (a : Adr) (d : Devm) :
    (d.recordTouch rules cond a).accountsToDelete = d.accountsToDelete := by
  unfold Devm.recordTouch
  split <;> rfl

/-- What a clean raw execution settles to in the inner message frame. -/
private theorem settle_inner_clean {m : Msg} {raw : Execution} (c : Execution.commits raw = true) :
    ∃ inner : Devm, processMessage.settle m (executeCode.handleErrorWith m.benv.stat.rules.stateGas raw) = .ok inner ∧
      inner.state = (Execution.committedPost raw c).state ∧
      inner.accountsToDelete = (Execution.committedPost raw c).accountsToDelete ∧
      inner.error.isNone = true := by
  cases raw with
  | error err => simp only [Execution.commits, Bool.false_eq_true] at c
  | ok post =>
      have clean : post.error.isNone = true := c
      have hsome : post.error.isSome = false := by
        cases he : post.error <;> simp only [he, Option.isNone_some, Bool.false_eq_true, Option.isSome_none] at clean ⊢
      refine ⟨post.recordTouch m.benv.stat.rules true m.currentTarget, ?_, Devm.recordTouch_state .., 
        recordTouch_deletions .., ?_⟩
      · simp only [processMessage.settle, executeCode.handleErrorWith_ok, Except.bind_ok, hsome, Bool.false_eq_true,
          ↓reduceIte]
      · rw [Devm.recordTouch_error]
        exact clean

private theorem settle_ofCall_committed {m : Msg} {raw : Execution} {s : Devm}
    (settled : (Frame.ofCall m).settle raw = .ok s) (c : Execution.commits raw = true) :
    s.state = (Execution.committedPost raw c).state ∧
      s.accountsToDelete = (Execution.committedPost raw c).accountsToDelete := by
  obtain ⟨inner, hi, hs, hd, -⟩ := settle_inner_clean (m := m) c
  have : inner = s := Except.ok.inj (hi.symm.trans settled)
  subst this
  exact ⟨hs, hd⟩

private theorem settle_ofCreate_committed {m : Msg} {raw : Execution} {s : Devm}
    (settled : (Frame.ofCreate m).settle raw = .ok s) (c : Execution.commits raw = true)
    (clean : s.error.isNone = true) :
    (∀ x, m.currentTarget ≠ x → s.getCode x = (Execution.committedPost raw c).getCode x ∧
      Devm.getStor s x = Devm.getStor (Execution.committedPost raw c) x) ∧
      s.accountsToDelete = (Execution.committedPost raw c).accountsToDelete := by
  obtain ⟨inner, hi, hs, hd, hn⟩ := settle_inner_clean (m := processCreateMessage.msg m) c
  have run : processCreateMessage.settle m (.ok inner) = .ok s := by
    rw [← hi]
    exact settled
  unfold processCreateMessage.settle at run
  simp only [bind, Except.bind, hn, ↓reduceIte] at run
  cases charge : processCreateMessage.chargeCodeGas m.benv.stat.rules inner with
  | error error =>
      rw [charge] at run
      rcases error with ⟨error, charged⟩
      cases error with
      | halt reason =>
          have eq := Except.ok.inj run
          rw [← eq] at clean
          cases hsg : m.benv.stat.rules.stateGas <;>
            simp only [hsg, Devm.error, processCreateMessage.exceptionalHalt,
              processCreateMessage.exceptionalHaltAmsterdam, Devm.setMeta, Devm.withStorageWrites, Devm.setWorld,
              Option.isNone_some, Bool.false_eq_true] at clean
      | revert => cases run
      | crypto reason => cases run
      | internal reason => cases run
  | ok charged =>
      rw [charge] at run
      have eq := Except.ok.inj run
      have frame := processCreateMessage.chargeCodeGas_instructionFrame m.benv.stat.rules inner
      rw [charge] at frame
      have frame' : Devm.InstructionFrame inner charged := frame
      subst eq
      have hstate := (chargeCodeGas_state_ok charge).trans hs
      refine ⟨fun x ne => ⟨?_, ?_⟩, ?_⟩
      · rw [setCode_getCode ne]
        exact congrArg (fun st : State => st.getCode x) hstate
      · change ((charged.state.setCode m.currentTarget ⟨⟨charged.output⟩⟩).get x).stor = _
        rw [State.setCode_get_stor_ne ne]
        exact congrArg (fun st : State => st.getStor x) hstate
      · refine Eq.trans ?_ hd
        exact frame'.accountsToDelete.symm

private theorem settle_error_rollback {m : Msg} {f : Frame} (shape : f = Frame.ofCall m ∨ f = Frame.ofCreate m)
    {raw : Execution} {s : Devm} (settled : f.settle raw = .ok s) (dirty : s.error.isSome = true) :
    s.state = m.benv.state := by
  rcases shape with rfl | rfl
  · change processMessage.settle m _ = _ at settled
    generalize executeCode.handleErrorWith _ _ = result at settled
    rcases result with x | evm
    · cases settled
    · unfold processMessage.settle at settled
      dsimp only [bind, Except.bind] at settled
      by_cases he : evm.error.isSome = true
      · rw [ite_eq_left he] at settled
        rw [← Except.ok.inj settled]
        rfl
      · rw [ite_eq_right he] at settled
        rw [← Except.ok.inj settled, Devm.recordTouch_error] at dirty
        exact (he dirty).elim
  · change processCreateMessage.settle m _ = _ at settled
    generalize processMessage.settle _ _ = result at settled
    cases result with
    | error error => cases settled
    | ok inner =>
        unfold processCreateMessage.settle at settled
        simp only [bind, Except.bind] at settled
        by_cases hn : inner.error.isNone = true
        · rw [ite_eq_left hn] at settled
          cases charge : processCreateMessage.chargeCodeGas m.benv.stat.rules inner with
          | error error =>
              rw [charge] at settled
              rcases error with ⟨error, charged⟩
              cases error with
              | halt reason =>
                  have eq := Except.ok.inj settled
                  rw [← eq]
                  split <;> rfl
              | revert => cases settled
              | crypto reason => cases settled
              | internal reason => cases settled
          | ok charged =>
              rw [charge] at settled
              have eq := Except.ok.inj settled
              have err := processCreateMessage.chargeCodeGas_error_eq charge
              rw [← eq] at dirty
              change charged.error.isSome = true at dirty
              rw [err] at dirty
              cases hi : inner.error <;> simp only [hi, Option.isSome_none, Option.isNone_some, Bool.false_eq_true,
                Bool.false_eq_true] at dirty hn
        · rw [ite_eq_right hn] at settled
          rw [← Except.ok.inj settled]
          rfl

/-! ## What one settled frame does to a kept account -/

namespace TopRun

variable {msg m : Msg} {state : State} {out : MsgCallOutput} {f : Frame} {benv : Benv} {e : Evm} {raw : Execution}
  {s : Devm}

private theorem shape (t : TopRun msg m state out f benv e raw s) : f = Frame.ofCall m ∨ f = Frame.ofCreate m := by
  rcases t.frame with ⟨-, h⟩ | ⟨-, h, -⟩
  · exact .inl h
  · exact .inr h

private theorem inner_getCode (t : TopRun msg m state out f benv e raw s) (x : Adr) :
    f.inner.benv.state.getCode x = m.benv.state.getCode x := by
  rcases t.shape with rfl | rfl
  · rfl
  · exact processCreateMessage.msg_getCode m x

private theorem entry_getCode (t : TopRun msg m state out f benv e raw s) (x : Adr) :
    e.dyna.getCode x = m.benv.state.getCode x := by
  have hs : e.dyna.getCode x = benv.state.getCode x := congrArg (fun st : State => st.getCode x) t.entered.state
  exact hs.trans ((benvAfterTransfer_ok_getCode t.entered.transfer x).trans (t.inner_getCode x))

private theorem create_ne (t : TopRun msg m state out f benv e raw s) {x : Adr}
    (hc : (msg.benv.state.getCode x).toList ≠ []) (hd : ¬ isValidDelegation (msg.benv.state.getCode x))
    (create : f.isCreate = true) : msg.currentTarget ≠ x := by
  rcases t.frame with ⟨-, rfl⟩ | ⟨-, -, hcoll⟩
  · cases create
  · rw [← t.prepared.currentTarget]
    exact ne_wa_of_not_hasCodeOrNonce (by rw [(t.prepared.kept x hc hd).1]; exact hc) hcoll

private theorem entry_getStor (t : TopRun msg m state out f benv e raw s) {x : Adr}
    (hc : (msg.benv.state.getCode x).toList ≠ []) (hd : ¬ isValidDelegation (msg.benv.state.getCode x)) :
    Devm.getStor e.dyna x = msg.benv.state.getStor x := by
  have hcode : (f.inner.benv.state.getCode x).toList ≠ [] := by
    rw [t.inner_getCode, (t.prepared.kept x hc hd).1]
    exact hc
  have hs : Devm.getStor e.dyna x = benv.state.getStor x := congrArg (fun st : State => st.getStor x) t.entered.state
  rw [hs, benvAfterTransfer_ok_getStor t.entered.transfer x (Or.inr (State.Protected.of_code_ne_nil hcode))]
  rcases t.shape with hf | hf
  · subst hf
    exact (t.prepared.kept x hc hd).2
  · subst hf
    have ne : m.currentTarget ≠ x := by
      rw [t.prepared.currentTarget]
      exact t.create_ne hc hd rfl
    exact (createEntry_getStor ne).trans (t.prepared.kept x hc hd).2

private theorem commits_eq (t : TopRun msg m state out f benv e raw s) :
    Frame.settlementCommits f raw = s.error.isNone := by
  unfold Frame.settlementCommits
  rw [t.settled]

private theorem committed (t : TopRun msg m state out f benv e raw s) {x : Adr}
    (hc : (msg.benv.state.getCode x).toList ≠ []) (hd : ¬ isValidDelegation (msg.benv.state.getCode x))
    (c : Execution.commits raw = true) (clean : s.error.isNone = true) :
    state.getCode x = (Execution.committedPost raw c).getCode x ∧
      state.getStor x = Devm.getStor (Execution.committedPost raw c) x := by
  rw [t.state_eq]
  rcases t.shape with hf | hf
  · subst hf
    have := (settle_ofCall_committed t.settled c).1
    exact ⟨congrArg (fun st : State => st.getCode x) this, congrArg (fun st : State => st.getStor x) this⟩
  · subst hf
    have ne : m.currentTarget ≠ x := by
      rw [t.prepared.currentTarget]
      exact t.create_ne hc hd rfl
    exact (settle_ofCreate_committed t.settled c clean).1 x ne

private theorem deletions_committed (t : TopRun msg m state out f benv e raw s)
    (c : Execution.commits raw = true) (clean : s.error.isNone = true) :
    s.accountsToDelete = (Execution.committedPost raw c).accountsToDelete := by
  rcases t.shape with hf | hf
  · subst hf
    exact (settle_ofCall_committed t.settled c).2
  · subst hf
    exact (settle_ofCreate_committed t.settled c clean).2

private theorem rolled (t : TopRun msg m state out f benv e raw s) {x : Adr}
    (hc : (msg.benv.state.getCode x).toList ≠ []) (hd : ¬ isValidDelegation (msg.benv.state.getCode x))
    (dirty : ¬ s.error.isNone = true) :
    state.getCode x = msg.benv.state.getCode x ∧ state.getStor x = msg.benv.state.getStor x := by
  have some : s.error.isSome = true := by
    cases he : s.error
    · simp only [he, Option.isNone_none, not_true_eq_false] at dirty
    · rfl
  have back := settle_error_rollback t.shape t.settled some
  rw [t.state_eq, back]
  exact t.prepared.kept x hc hd

end TopRun

private theorem precomp_post (e : Evm) (adr : Adr) (c : Execution.commits (executePrecomp e adr) = true) :
    (Execution.committedPost _ c).state = e.dyna.state ∧
      (Execution.committedPost _ c).accountsToDelete = e.dyna.accountsToDelete := by
  revert c
  unfold executePrecomp applyPrecompResult
  cases precompileRun e adr with
  | error reason cost => intro c; simp only [Execution.commits, Bool.false_eq_true] at c
  | ok cost output => intro _; exact ⟨rfl, rfl⟩

private theorem run_post_getCode {pc : Nat} {sevm : Sevm} {pre : Devm} {raw : Execution} (run : Exec pc sevm pre raw)
    (c : Execution.commits raw = true) {x : Adr} (hne : (pre.getCode x).toList ≠ []) :
    (Execution.committedPost raw c).getCode x = pre.getCode x := by
  cases raw with
  | error err => simp only [Execution.commits, Bool.false_eq_true] at c
  | ok post => exact Exec.preserves_getCode run x hne

/-- No root ran: the account is as the message found it, and the deletions are the ones it inherited. -/
private theorem no_root_facts {msg m : Msg} {state : State} {out : MsgCallOutput} {f : Frame} {benv : Benv} {e : Evm}
    {adr : Adr} {s : Devm} (t : TopRun msg m state out f benv e (executePrecomp e adr) s) :
    (∀ x, (msg.benv.state.getCode x).toList ≠ [] → ¬ isValidDelegation (msg.benv.state.getCode x) →
      state.getCode x = msg.benv.state.getCode x ∧ state.getStor x = msg.benv.state.getStor x) ∧
      ∀ x ∈ out.accountsToDelete, x ∈ msg.inheritedDeletions := by
  have commits (clean : s.error.isNone = true) : Execution.commits (executePrecomp e adr) = true :=
    Frame.raw_commits_of_settlementCommits (t.commits_eq.trans clean)
  refine ⟨fun x hc hd => ?_, fun x hx => ?_⟩
  · by_cases clean : s.error.isNone = true
    · obtain ⟨hcode, hstor⟩ := t.committed hc hd (commits clean) clean
      have world := (precomp_post e adr (commits clean)).1
      refine ⟨hcode.trans ?_, hstor.trans ?_⟩
      · exact (congrArg (fun st : State => st.getCode x) world).trans
          ((t.entry_getCode x).trans (t.prepared.kept x hc hd).1)
      · exact (congrArg (fun st : State => st.getStor x) world).trans (t.entry_getStor hc hd)
    · exact t.rolled hc hd clean
  · obtain ⟨clean, hm⟩ := t.deletions x hx
    rw [t.deletions_committed (commits clean) clean, (precomp_post e adr (commits clean)).2,
      t.entered.deletions] at hm
    have hinner : f.inner.inheritedDeletions = msg.inheritedDeletions := by
      rcases t.shape with rfl | rfl <;> exact t.prepared.deletions
    rw [hinner] at hm
    exact hm

/-- A message's roots are none, with the facts of a message that ran no code, or one settled frame. -/
private theorem MessageRoots.cases {msg : Msg} {state : State} {out : MsgCallOutput} {rs : List Root}
    (h : MessageRoots msg state out rs) :
    (rs = [] ∧ (∀ x, (msg.benv.state.getCode x).toList ≠ [] → ¬ isValidDelegation (msg.benv.state.getCode x) →
        state.getCode x = msg.benv.state.getCode x ∧ state.getStor x = msg.benv.state.getStor x) ∧
        ∀ x ∈ out.accountsToDelete, x ∈ msg.inheritedDeletions) ∨
      ∃ r m benv s, rs = [r] ∧ TopRun msg m state out r.frame benv r.evm r.raw s := by
  obtain ⟨result, hmap⟩ := h
  rcases message_top result with ⟨hnone, hst, hdel⟩ | ⟨hnone, _, f, _, e, adr, s, t⟩ | ⟨m, f, benv, e, s, hsome, t⟩
  · rw [hnone] at hmap
    refine .inl ⟨List.map_eq_nil_iff.mp hmap, fun x _ _ => ?_, fun x hx => (hdel x hx).elim⟩
    rw [hst]
    exact ⟨rfl, rfl⟩
  · rw [hnone] at hmap
    exact .inl ⟨List.map_eq_nil_iff.mp hmap, no_root_facts t⟩
  · rw [hsome] at hmap
    cases rs with
    | nil => cases hmap
    | cons r tail =>
        simp only [Option.toList_some, List.map_cons, List.cons.injEq, Prod.mk.injEq, List.map_eq_nil_iff] at hmap
        obtain ⟨⟨hf, he⟩, rfl⟩ := hmap
        obtain ⟨frame, evm, raw, run⟩ := r
        dsimp only at hf he
        subst hf he
        have hraw : exec evm = raw := (exec_iff_exec_eq _ _ _ _).mp ⟨run⟩
        subst hraw
        exact .inr ⟨_, m, benv, s, rfl, t⟩

/-! ## The message level -/

/-- **Every successful message has its roots.** -/
theorem exists_messageRoots {msg : Msg} {state : State} {out : MsgCallOutput}
    (h : processMessageCall msg = .ok (state, out)) : ∃ rs, MessageRoots msg state out rs := by
  cases hentry : messageEntry msg with
  | none => exact ⟨[], h, by rw [hentry]; rfl⟩
  | some p =>
      obtain ⟨f, e⟩ := p
      obtain ⟨run⟩ := (exec_iff_exec_eq e.pc e.sta e.dyna (exec e)).mpr rfl
      exact ⟨[⟨f, e, exec e, run⟩], h, by rw [hentry]; rfl⟩

/-- A root is the message's entry, running the interpreter's one execution: the message determines it. -/
theorem MessageRoots.mem_entry {msg : Msg} {state : State} {out : MsgCallOutput} {rs : List Root}
    (h : MessageRoots msg state out rs) {r : Root} (hr : r ∈ rs) :
    messageEntry msg = some (r.frame, r.evm) ∧ exec r.evm = r.raw := by
  refine ⟨?_, (exec_iff_exec_eq _ _ _ _).mp ⟨r.run⟩⟩
  have mem : (r.frame, r.evm) ∈ (messageEntry msg).toList := by
    rw [← h.2]
    exact List.mem_map_of_mem hr
  cases hentry : messageEntry msg with
  | none =>
      rw [hentry] at mem
      cases mem
  | some p =>
      rw [hentry] at mem
      simp only [Option.toList_some, List.mem_singleton] at mem
      exact congrArg some mem.symm

/-- **The chain at a kept account.** With code at `a` that is no delegation, the frames the message's root keeps at
`a` run from the storage the message found to the storage it left, and the code stays. -/
theorem MessageRoots.chain {msg : Msg} {state : State} {out : MsgCallOutput} {rs : List Root}
    (h : MessageRoots msg state out rs) {a : Adr} (hc : (msg.benv.state.getCode a).toList ≠ [])
    (hd : ¬ isValidDelegation (msg.benv.state.getCode a)) :
    KeptChain a (msg.benv.state.getStor a) (rs.flatMap (Root.keptAt a)) (state.getStor a) ∧
      state.getCode a = msg.benv.state.getCode a := by
  rcases h.cases with ⟨rfl, facts, -⟩ | ⟨r, m, benv, s, rfl, t⟩
  · obtain ⟨hcode, hstor⟩ := facts a hc hd
    rw [hstor]
    exact ⟨.nil _, hcode⟩
  · rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    by_cases clean : s.error.isNone = true
    · have settles : Frame.settlementCommits r.frame r.raw = true := t.commits_eq.trans clean
      have c := Frame.raw_commits_of_settlementCommits settles
      obtain ⟨hcode, hstor⟩ := t.committed hc hd c clean
      have entryCode : r.evm.dyna.getCode a = msg.benv.state.getCode a :=
        (t.entry_getCode a).trans (t.prepared.kept a hc hd).1
      have entryStor := t.entry_getStor hc hd
      have hne : (r.evm.dyna.getCode a).toList ≠ [] := by rw [entryCode]; exact hc
      refine ⟨?_, hcode.trans ((run_post_getCode r.run c hne).trans entryCode)⟩
      rw [Root.keptAt, dite_eq_left settles, hstor]
      by_cases here : r.evm.sta.currentTarget = a
      · rw [ite_eq_left here]
        exact .cons entryStor (.nil _)
      · rw [ite_eq_right here]
        have chain := Exec.keptAt_chain r.run c here hne
        rw [entryStor] at chain
        exact chain
    · obtain ⟨hcode, hstor⟩ := t.rolled hc hd clean
      have rolled : ¬ Frame.settlementCommits r.frame r.raw = true := by
        rw [t.commits_eq]
        exact clean
      rw [Root.keptAt, dite_eq_right rolled, hstor]
      exact ⟨.nil _, hcode⟩

private theorem not_isValidDelegation_empty : ¬ isValidDelegation ByteArray.empty :=
  fun h => absurd h.1 (by decide)

/-- A root's machine starts fresh: at the first instruction, with an empty stack and an empty, word-aligned memory. -/
theorem MessageRoots.entry_machine {msg : Msg} {state : State} {out : MsgCallOutput} {rs : List Root}
    (h : MessageRoots msg state out rs) {r : Root} (hr : r ∈ rs) :
    r.evm.pc = 0 ∧ r.evm.dyna.stack = [] ∧ r.evm.dyna.memory = Mem.empty ∧ Mem.Wf r.evm.dyna.memory ∧
      r.evm.dyna.memory.size % 32 = 0 := by
  rcases h.cases with ⟨rfl, -⟩ | ⟨r', m, benv, s, rfl, t⟩
  · cases hr
  · rw [List.mem_singleton] at hr
    subst hr
    have hm := t.entered.memory
    refine ⟨t.entered.pc, t.entered.stack, hm, ?_, ?_⟩ <;> rw [hm]
    · exact Mem.wf_empty
    · rfl

/-- A root runs for the message's caller at the message's target, on its block and its calldata. -/
theorem MessageRoots.entry_routing {msg : Msg} {state : State} {out : MsgCallOutput} {rs : List Root}
    (h : MessageRoots msg state out rs) {r : Root} (hr : r ∈ rs) :
    r.evm.sta.caller = msg.caller ∧ r.evm.sta.currentTarget = msg.currentTarget ∧
      r.evm.sta.benvStat = msg.benv.stat ∧ r.evm.sta.data = msg.data := by
  rcases h.cases with ⟨rfl, -⟩ | ⟨r', m, benv, s, rfl, t⟩
  · cases hr
  · rw [List.mem_singleton] at hr
    subst hr
    rw [t.entered.sta]
    have hstat := benvAfterTransfer_stat t.entered.transfer
    rcases t.shape with hf | hf <;> rw [hf] at hstat ⊢
    · exact ⟨t.prepared.caller, t.prepared.currentTarget, hstat.trans t.prepared.stat, t.prepared.data⟩
    · exact ⟨t.prepared.caller, t.prepared.currentTarget, hstat.trans t.prepared.stat, t.prepared.data⟩

/-- A code-bearing account that is no delegation enters a root as the message found it. -/
theorem MessageRoots.entry_kept {msg : Msg} {state : State} {out : MsgCallOutput} {rs : List Root}
    (h : MessageRoots msg state out rs) {r : Root} (hr : r ∈ rs) {x : Adr}
    (hc : (msg.benv.state.getCode x).toList ≠ []) (hd : ¬ isValidDelegation (msg.benv.state.getCode x)) :
    r.evm.dyna.getCode x = msg.benv.state.getCode x ∧ Devm.getStor r.evm.dyna x = msg.benv.state.getStor x := by
  rcases h.cases with ⟨rfl, -⟩ | ⟨r', m, benv, s, rfl, t⟩
  · cases hr
  · rw [List.mem_singleton] at hr
    subst hr
    exact ⟨(t.entry_getCode x).trans (t.prepared.kept x hc hd).1, t.entry_getStor hc hd⟩

/-- An account without code that no authorization recovers to enters a root without code. -/
theorem MessageRoots.entry_empty {msg : Msg} {state : State} {out : MsgCallOutput} {rs : List Root}
    (h : MessageRoots msg state out rs) {r : Root} (hr : r ∈ rs) {S : Adr}
    (empty : msg.benv.state.getCode S = ByteArray.empty)
    (away : ∀ auth ∈ msg.tenv.stat.auths, recoverAuthority auth ≠ .ok S) :
    r.evm.dyna.getCode S = ByteArray.empty := by
  rcases h.cases with ⟨rfl, -⟩ | ⟨r', m, benv, s, rfl, t⟩
  · cases hr
  · rw [List.mem_singleton] at hr
    subst hr
    exact (t.entry_getCode S).trans ((t.prepared.away S away).trans empty)

/-- A root's code, when the message is a call whose code is its target's: a target with code that is no delegation
runs that code; a target without code that no authorization recovers to runs nothing. -/
theorem MessageRoots.entry_call_code {msg : Msg} {state : State} {out : MsgCallOutput} {rs : List Root}
    (h : MessageRoots msg state out rs) {r : Root} (hr : r ∈ rs) (call : msg.target.isNone = false)
    (hca : msg.codeAddress = some msg.currentTarget) (hcode : msg.code = msg.benv.state.getCode msg.currentTarget) :
    ((msg.benv.state.getCode msg.currentTarget).toList ≠ [] →
        ¬ isValidDelegation (msg.benv.state.getCode msg.currentTarget) →
        r.evm.sta.code = msg.benv.state.getCode msg.currentTarget) ∧
      (msg.benv.state.getCode msg.currentTarget = ByteArray.empty →
        (∀ auth ∈ msg.tenv.stat.auths, recoverAuthority auth ≠ .ok msg.currentTarget) →
        r.evm.sta.code = ByteArray.empty) := by
  rcases h.cases with ⟨rfl, -⟩ | ⟨r', m, benv, s, rfl, t⟩
  · cases hr
  · rw [List.mem_singleton] at hr
    subst hr
    have hf : r.frame = Frame.ofCall m := by
      rcases t.frame with ⟨-, hf⟩ | ⟨hn, -⟩
      · exact hf
      · rw [call] at hn; cases hn
    have hsta : r.evm.sta.code = m.code := by
      rw [t.entered.sta, hf]
      rfl
    rw [hsta]
    refine ⟨fun hc hd => ?_, fun empty away => ?_⟩
    · have hk := (t.prepared.kept _ hc hd).1
      rw [t.prepared.code call hca hcode (by rw [hk]; exact hd), hk]
    · have hk := (t.prepared.away _ away).trans empty
      rw [t.prepared.code call hca hcode (by rw [hk]; exact not_isValidDelegation_empty), hk]

/-- A create's root has the code address the message gave it, which `prepareMessage` leaves empty. -/
theorem MessageRoots.entry_create {msg : Msg} {state : State} {out : MsgCallOutput} {rs : List Root}
    (h : MessageRoots msg state out rs) {r : Root} (hr : r ∈ rs) (create : msg.target.isNone = true) :
    r.evm.sta.codeAddress = msg.codeAddress := by
  rcases h.cases with ⟨rfl, -⟩ | ⟨r', m, benv, s, rfl, t⟩
  · cases hr
  · rw [List.mem_singleton] at hr
    subst hr
    rw [t.entered.sta]
    rcases t.shape with hf | hf <;> rw [hf] <;> exact t.prepared.codeAddress create

/-- A prepared create message carries no code address. -/
theorem prepareMessage_createCodeAddress {benv : Benv} {tenv : Tenv} {tx : Tx} {msg : Msg}
    (prepared : prepareMessage benv tenv tx = .ok msg) (create : msg.target.isNone = true) :
    msg.codeAddress = none := by
  cases receiver : tx.type.receiver? with
  | none =>
      simp only [prepareMessage, receiver] at prepared
      rw [← Except.ok.inj prepared]
  | some target =>
      simp only [prepareMessage, receiver] at prepared
      rw [← Except.ok.inj prepared] at create
      cases create

/-- A root's deletion set starts as the one the message inherited; its created set adds at most a create's target. -/
theorem MessageRoots.entry_sets {msg : Msg} {state : State} {out : MsgCallOutput} {rs : List Root}
    (h : MessageRoots msg state out rs) {r : Root} (hr : r ∈ rs) :
    r.evm.dyna.accountsToDelete = msg.inheritedDeletions ∧
      ∀ x ∈ r.evm.dyna.createdAccounts, x ∈ msg.benv.createdAccounts ∨
        (msg.target.isNone = true ∧ x = msg.currentTarget) := by
  rcases h.cases with ⟨rfl, -⟩ | ⟨r', m, benv, s, rfl, t⟩
  · cases hr
  · rw [List.mem_singleton] at hr
    subst hr
    have hcreated : r.evm.dyna.createdAccounts = r.frame.inner.benv.createdAccounts :=
      t.entered.created.trans (benvAfterTransfer_ok_createdAccounts t.entered.transfer)
    refine ⟨?_, fun x hx => ?_⟩
    · rw [t.entered.deletions]
      rcases t.shape with hf | hf <;> rw [hf] <;> exact t.prepared.deletions
    · rw [hcreated] at hx
      rcases t.frame with ⟨-, hf⟩ | ⟨hn, hf, -⟩
      · rw [hf] at hx
        exact .inl (t.prepared.created ▸ hx)
      · rw [hf] at hx
        change x ∈ m.benv.createdAccounts.insert m.currentTarget at hx
        rw [Std.HashSet.mem_insert] at hx
        rcases hx with same | old
        · exact .inr ⟨hn, by rw [← t.prepared.currentTarget]; exact (beq_iff_eq.mp same).symm⟩
        · exact .inl (t.prepared.created ▸ old)

/-- **Every deletion a message reports is scheduled by a root that commits**, or was inherited. -/
theorem MessageRoots.deletions {msg : Msg} {state : State} {out : MsgCallOutput} {rs : List Root}
    (h : MessageRoots msg state out rs) {x : Adr} (hx : x ∈ out.accountsToDelete) :
    x ∈ msg.inheritedDeletions ∨ ∃ r ∈ rs, ∃ settles : Frame.settlementCommits r.frame r.raw = true,
      x ∈ (Execution.committedPost r.raw (Frame.raw_commits_of_settlementCommits settles)).accountsToDelete := by
  rcases h.cases with ⟨-, -, facts⟩ | ⟨r, m, benv, s, rfl, t⟩
  · exact .inl (facts x hx)
  · obtain ⟨clean, hm⟩ := t.deletions x hx
    have settles : Frame.settlementCommits r.frame r.raw = true := t.commits_eq.trans clean
    refine .inr ⟨r, List.mem_singleton.mpr rfl, settles, ?_⟩
    rw [← t.deletions_committed _ clean]
    exact hm

/-! ## System calls -/

/-- **A checked system call has its roots**, on the message it builds, with its post-state and output exact and no
error. -/
theorem exists_systemRoots {benv : Benv} {target : Adr} {data : Bytes} {post : State} {out : MsgCallOutput}
    (h : processCheckedSystemTransaction benv target data = .ok (post, out)) :
    out.error = none ∧ ∃ rs, MessageRoots (systemTransactionMessage benv target data) post out rs := by
  have unchecked := processCheckedSystemTransaction_to_unchecked h
  have hmessage : processMessageCall (systemTransactionMessage benv target data) = .ok (post, out) := by
    simpa only [systemTransactionMessage, processUncheckedSystemTransaction, processSystemTransaction] using unchecked
  refine ⟨?_, exists_messageRoots hmessage⟩
  unfold processCheckedSystemTransaction at h
  dsimp only at h
  split at h
  · cases h
  · obtain ⟨⟨st, o⟩, ho, h⟩ := Except.bind_eq_ok h
    split at h
    · cases h
    · rename_i none
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact none

/-- The shape of a system message, as the entry theorems read it: a call of the target's own code, without
authorizations or inherited deletions. -/
theorem systemTransactionMessage_shape (benv : Benv) (target : Adr) (data : Bytes) :
    let msg := systemTransactionMessage benv target data
    msg.target.isNone = false ∧ msg.currentTarget = target ∧ msg.codeAddress = some msg.currentTarget ∧
      msg.code = msg.benv.state.getCode msg.currentTarget ∧ msg.tenv.stat.auths = [] ∧
      msg.inheritedDeletions = .emptyWithCapacity ∧ msg.benv.state = benv.state :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Blanc
