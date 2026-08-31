import Blanc.ProxyPairUpgradePrograms

/-!
# R2 and the eager scalar migration

The selected relation protects one logical word: v1 reads it from slot 7 and
v2 reads it from slot 8.  Slot 9 and the retained v1 word are intentionally
outside the projection.  This file proves pure migration soundness and shared
logical behavior; transaction realization is kept in a separate module.
-/

namespace Blanc.ProxyPair.Upgrade

open Jaune

def storageWord (state : State) (owner : Adr) (slot : B256) : B256 :=
  (state.get owner).stor.get slot

@[simp] theorem storageWord_setStorVal_self
    (state : State) (owner : Adr) (slot value : B256) :
    storageWord (state.setStorVal owner slot value) owner slot = value := by
  unfold storageWord State.setStorVal
  rw [State.get_set_self, Stor.get_set_self]

@[simp] theorem storageWord_setStorVal_ne
    (state : State) (owner : Adr) (written read value : B256)
    (hne : written ≠ read) :
    storageWord (state.setStorVal owner written value) owner read =
      storageWord state owner read := by
  unfold storageWord State.setStorVal
  rw [State.get_set_self, Stor.get_set_ne _ hne]

/-- Eager S1-to-S2 migration followed by the independent marker write. -/
def migration (proxy : Adr) (state : State) : State :=
  (state.setStorVal proxy v2ValueSlot
      (storageWord state proxy v1ValueSlot)).setStorVal
    proxy migrationMarkerSlot migrationMarkerValue

def v1Domain (_state : State) : Prop := True

def initializedDomain (proxy : Adr) (state : State) : Prop :=
  storageWord state proxy migrationMarkerSlot = migrationMarkerValue

/-- R2: equality of the named logical projection only. -/
def upgradeRelation (proxy : Adr) (pre post : State) : Prop :=
  storageWord pre proxy v1ValueSlot =
    storageWord post proxy v2ValueSlot

def identityAdmissible (proxy : Adr) (state : State) : Prop :=
  initializedDomain proxy state ∧ upgradeRelation proxy state state

/-- Product architecture with the proxy program and owner both explicit. -/
def architecture (proxyProg : Prog) (proxy : Adr) :
    Blanc.UpgradeArchitecture State :=
  { proxyProg := proxyProg
    v1 := v1Prog
    v2 := v2Prog
    migration := migration proxy
    relation := upgradeRelation proxy }

theorem migration_reads_v1 (proxy : Adr) (state : State) :
    storageWord (migration proxy state) proxy v1ValueSlot =
      storageWord state proxy v1ValueSlot := by
  simp [migration, v1ValueSlot_ne_migrationMarkerSlot.symm,
    v1ValueSlot_ne_v2ValueSlot.symm]

theorem migration_writes_v2 (proxy : Adr) (state : State) :
    storageWord (migration proxy state) proxy v2ValueSlot =
      storageWord state proxy v1ValueSlot := by
  simp [migration, v2ValueSlot_ne_migrationMarkerSlot.symm]

theorem migration_writes_marker (proxy : Adr) (state : State) :
    storageWord (migration proxy state) proxy migrationMarkerSlot =
      migrationMarkerValue := by
  simp [migration]

theorem migration_establishes_initializedDomain
    (proxy : Adr) (state : State) :
    initializedDomain proxy (migration proxy state) := by
  exact migration_writes_marker proxy state

theorem migration_establishes_relation (proxy : Adr) (state : State) :
    upgradeRelation proxy state (migration proxy state) := by
  unfold upgradeRelation
  rw [migration_writes_v2]

/-- Pure migration soundness.  It is independent of any proxy transaction. -/
theorem migration_sound (proxyProg : Prog) (proxy : Adr) :
    Blanc.MigrationSound (architecture proxyProg proxy)
      v1Domain (initializedDomain proxy) := by
  intro pre _hDomain
  exact ⟨migration_establishes_initializedDomain proxy pre,
    migration_establishes_relation proxy pre⟩

/-! ## Shared logical behavior -/

inductive SharedCall where
  | value
  | setValue (word : B256)
deriving DecidableEq

def sharedCalldata : SharedCall → Bytes
  | .value => valueCalldata
  | .setValue word => setValueCalldata word

theorem sharedCalldata_selector (call : SharedCall) :
    match call with
    | .value => (sharedCalldata call).take 4 = valueCalldata
    | .setValue _ => (sharedCalldata call).take 4 =
        abiSelectorBytes setValueSelector := by
  cases call <;> simp [sharedCalldata, valueCalldata, setValueCalldata,
    abiSelectorBytes_length]

def sharedInput (_call : SharedCall) : Prop := True

def v1Step : SharedCall → State → State × Bytes
  | .value, state =>
      (state, (storageWord state upgradeProxy v1ValueSlot).toBytes)
  | .setValue word, state =>
      (state.setStorVal upgradeProxy v1ValueSlot word, [])

def v2Step : SharedCall → State → State × Bytes
  | .value, state =>
      (state, (storageWord state upgradeProxy v2ValueSlot).toBytes)
  | .setValue word, state =>
      (state.setStorVal upgradeProxy v2ValueSlot word, [])

theorem shared_getter_refinement (pre post : State)
    (_hInitialized : initializedDomain upgradeProxy post)
    (hRelation : upgradeRelation upgradeProxy pre post) :
    (v1Step .value pre).2 = (v2Step .value post).2 ∧
      upgradeRelation upgradeProxy
        (v1Step .value pre).1 (v2Step .value post).1 := by
  exact ⟨congrArg B256.toBytes hRelation, hRelation⟩

theorem shared_setter_refinement (pre post : State) (word : B256)
    (hInitialized : initializedDomain upgradeProxy post)
    (_hRelation : upgradeRelation upgradeProxy pre post) :
    (v1Step (.setValue word) pre).2 =
        (v2Step (.setValue word) post).2 ∧
      initializedDomain upgradeProxy (v2Step (.setValue word) post).1 ∧
      upgradeRelation upgradeProxy
        (v1Step (.setValue word) pre).1
        (v2Step (.setValue word) post).1 := by
  refine ⟨rfl, ?_, ?_⟩
  · change storageWord
      (post.setStorVal upgradeProxy v2ValueSlot word)
        upgradeProxy migrationMarkerSlot = migrationMarkerValue
    rw [storageWord_setStorVal_ne _ _ _ _ _
      v2ValueSlot_ne_migrationMarkerSlot]
    exact hInitialized
  · simp [v1Step, v2Step, upgradeRelation]

theorem v2Step_preserves_initializedDomain (post : State)
    (call : SharedCall)
    (hInitialized : initializedDomain upgradeProxy post) :
    initializedDomain upgradeProxy (v2Step call post).1 := by
  cases call with
  | value => exact hInitialized
  | setValue word =>
      change storageWord
          (post.setStorVal upgradeProxy v2ValueSlot word)
            upgradeProxy migrationMarkerSlot = migrationMarkerValue
      rw [storageWord_setStorVal_ne _ _ _ _ _
        v2ValueSlot_ne_migrationMarkerSlot]
      exact hInitialized

theorem behavioral_refinement (proxyProg : Prog) :
    Blanc.BehavioralRefinement
      (architecture proxyProg upgradeProxy)
      v1Domain (initializedDomain upgradeProxy) sharedInput v1Step v2Step := by
  intro pre post input _hV1 hV2 hRelation _hShared
  cases input with
  | value => exact shared_getter_refinement pre post hV2 hRelation
  | setValue word =>
      rcases shared_setter_refinement pre post word hV2 hRelation with
        ⟨outputs, _initialized, relation⟩
      exact ⟨outputs, relation⟩

/-! ## Concrete satisfiability and biting R2 boundary -/

def ordinaryLogicalPrestate : State :=
  State.setStorVal (.empty : State) upgradeProxy v1ValueSlot 42

theorem ordinaryLogicalPrestate_values :
    storageWord ordinaryLogicalPrestate upgradeProxy v1ValueSlot = 42 ∧
    storageWord ordinaryLogicalPrestate upgradeProxy v2ValueSlot = 0 ∧
    storageWord ordinaryLogicalPrestate upgradeProxy migrationMarkerSlot = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact storageWord_setStorVal_self _ _ _ _
  · rw [ordinaryLogicalPrestate,
      storageWord_setStorVal_ne _ _ _ _ _ v1ValueSlot_ne_v2ValueSlot]
    rfl
  · rw [ordinaryLogicalPrestate,
      storageWord_setStorVal_ne _ _ _ _ _
        v1ValueSlot_ne_migrationMarkerSlot]
    rfl

theorem relation_inhabited :
    upgradeRelation upgradeProxy ordinaryLogicalPrestate
      (migration upgradeProxy ordinaryLogicalPrestate) :=
  migration_establishes_relation _ _

theorem ordinary_not_identityAdmissible :
    ¬ identityAdmissible upgradeProxy ordinaryLogicalPrestate := by
  intro admissible
  have marker := admissible.1
  rw [initializedDomain, ordinaryLogicalPrestate_values.2.2] at marker
  exact (by decide : (0 : B256) ≠ migrationMarkerValue) marker

def wrongRelationPoststate : State :=
  (migration upgradeProxy ordinaryLogicalPrestate).setStorVal
    upgradeProxy v2ValueSlot 41

theorem wrong_relation_mutant_bites :
    ¬ upgradeRelation upgradeProxy ordinaryLogicalPrestate
      wrongRelationPoststate := by
  intro relation
  rw [upgradeRelation, ordinaryLogicalPrestate_values.1] at relation
  simp [wrongRelationPoststate] at relation
  exact (by decide : (42 : B256) ≠ 41) relation

theorem relation_does_not_protect_marker :
    upgradeRelation upgradeProxy ordinaryLogicalPrestate
        (migration upgradeProxy ordinaryLogicalPrestate) ∧
      storageWord ordinaryLogicalPrestate upgradeProxy migrationMarkerSlot ≠
        storageWord (migration upgradeProxy ordinaryLogicalPrestate)
          upgradeProxy migrationMarkerSlot := by
  refine ⟨relation_inhabited, ?_⟩
  rw [ordinaryLogicalPrestate_values.2.2, migration_writes_marker]
  decide

end Blanc.ProxyPair.Upgrade
